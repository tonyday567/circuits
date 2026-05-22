# Spin: build, polish, lint, seal, and send.
#
#   just build    — compile
#   just polish   — format all source
#   just lint     — hlint
#   just check    — build + polish + lint
#   just seal msg — commit with message
#   just spin msg — check + seal + push

# Default: show available recipes
default:
    @just --list

# Build the project
build:
    cabal build

# Format all Haskell source files with ormolu
polish:
    find src -name '*.hs' -exec ormolu -i {} +

# Lint the project
lint:
    hlint src/

# Full check pipeline: build, polish, lint
check: build polish lint

# Commit everything with a one-line message
seal msg:
    git add -A
    git commit -m "{{msg}}"

# Spin it through the full cycle: check, commit, push
spin msg: check
    git add -A
    git commit -m "{{msg}}"
    git push
