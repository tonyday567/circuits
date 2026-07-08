#!/bin/bash
# verify-sabela-example.sh — load one markdown notebook in Sabela and report PASS/FAIL.
# Usage: ./verify-sabela-example.sh <port> <path-to-md>
#
# Reproducible successor to the crashed version:
#   - resolves the sabela binary from PATH (globally installed), not a /tmp hardcode
#   - exports SABELA_LOCAL_PACKAGES so cells that `import Circuit` resolve the LOCAL
#     circuits package (+ satellites) instead of Hackage
#   - roots the file explorer at the circuits repo so data files (other/alice.md …) resolve
#   - cells run under `cabal repl` = the default GHC (9.14.1, what circuits is tested-with);
#     do NOT export GHC or cells build on the wrong compiler.

set -u

PORT="${1:?usage: $0 <port> <path-to-md>}"
NB="${2:?usage: $0 <port> <path-to-md>}"
BASE="http://localhost:$PORT"
WORK_DIR="${SABELA_WORK_DIR:-/Users/tonyday567/haskell/circuits}"

# Local package overlays: circuits + the satellites some examples import.
# A cell still needs `-- cabal: build-depends: circuits` to pull one in; this
# just makes the local checkouts resolvable in the generated cabal.project.
export SABELA_LOCAL_PACKAGES="${SABELA_LOCAL_PACKAGES:-\
$HOME/haskell/circuits:\
$HOME/haskell/circuits-meter:\
$HOME/haskell/circuits-mat:\
$HOME/haskell/circuits-ad:\
$HOME/haskell/circuits-parser}"

# Resolve the sabela binary: PATH first, then cabal's install dir.
SABELA_BIN="$(command -v sabela || true)"
if [ -z "$SABELA_BIN" ] && [ -x "$HOME/.cabal/bin/sabela" ]; then
  SABELA_BIN="$HOME/.cabal/bin/sabela"
fi
if [ -z "$SABELA_BIN" ]; then
  echo "FAIL: sabela binary not found on PATH or in ~/.cabal/bin (cabal install exe:sabela)"
  exit 1
fi

# Start sabela in the background: <port> <work-dir>.
"$SABELA_BIN" "$PORT" "$WORK_DIR" >/dev/null 2>&1 &
PID=$!

# Wait for the server to come up.
for i in $(seq 1 30); do
  if curl -s --max-time 1 "$BASE/api/files" >/dev/null 2>&1; then
    break
  fi
  sleep 1
done

if ! curl -s --max-time 1 "$BASE/api/files" >/dev/null 2>&1; then
  echo "FAIL: sabela server did not start on port $PORT"
  kill "$PID" 2>/dev/null
  wait "$PID" 2>/dev/null
  exit 1
fi

# Reset session, then load the notebook.
curl -s --max-time 10 -X POST "$BASE/api/reset" >/dev/null 2>&1
LOAD=$(curl -s --max-time 15 "$BASE/api/load" \
  -H 'Content-Type: application/json' \
  -d "{\"lrPath\":\"$NB\"}" 2>&1)

NCELLS=$(echo "$LOAD" | python3 -c "
import sys, json
try:
    nb = json.load(sys.stdin)
    code = [c for c in nb['nbCells'] if c['cellType'] == 'CodeCell']
    print(len(code))
except:
    print('ERR')
" 2>/dev/null | tr -d '\n')

if [ "$NCELLS" = "ERR" ] || [ -z "$NCELLS" ]; then
  echo "FAIL: could not load notebook"
  kill "$PID" 2>/dev/null
  wait "$PID" 2>/dev/null
  exit 1
fi

# Trigger execution explicitly.
curl -s --max-time 120 -X POST "$BASE/api/run-all" >/dev/null 2>&1

# Poll the notebook state until execution settles.
for i in $(seq 1 60); do
  sleep 2
  PENDING=$(curl -s --max-time 10 "$BASE/api/notebook" 2>/dev/null | python3 -c "
import sys, json
try:
    nb = json.load(sys.stdin)
    pending = 0
    for c in nb['nbCells']:
        if c['cellType'] == 'CodeCell':
            out = c.get('cellOutput', [])
            err = c.get('cellError')
            if not out and not err:
                pending += 1
    print(pending)
except:
    print('ERR')
" 2>/dev/null | tr -d '\n')
  if [ "$PENDING" = "0" ]; then
    break
  fi
done

# Collect final errors.
CELL_ERRORS=$(curl -s --max-time 10 "$BASE/api/notebook" 2>/dev/null | python3 -c "
import sys, json
try:
    nb = json.load(sys.stdin)
    for c in nb['nbCells']:
        if c['cellType'] == 'CodeCell' and c.get('cellError'):
            print(f'cell {c[\"cellId\"]}: {c[\"cellError\"][:200]}')
except Exception as e:
    print(f'could not inspect notebook: {e}')
" 2>/dev/null)

ERR_COUNT=$(printf '%s' "$CELL_ERRORS" | grep -c . 2>/dev/null || echo 0)
ERR_COUNT=$(printf '%s' "$ERR_COUNT" | tr -d '\n')

kill "$PID" 2>/dev/null
wait "$PID" 2>/dev/null

if [ "$ERR_COUNT" -gt 0 ]; then
  echo "FAIL: $ERR_COUNT cell error(s)"
  echo "$CELL_ERRORS" | sed 's/^/  /'
  exit 1
else
  echo "PASS: $NCELLS code cell(s) executed"
  exit 0
fi
