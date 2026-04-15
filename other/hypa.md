It is possible to define a more polymorphic Hyp:

HypA etc

But this is difficult to use in any meaningful way because of the difficulties of using arr in general, if (Arrow arr) => HypA arr is attempted.

Recursion in Haskell is also intimately related to (->). Any recursive definition in Haskell is a fixed point of a Haskell function, so the recursion itself always lives in (->). You can lift into arr via arr, and you can pass the recursive call as an argument via zipper's pattern, but the fixed point that ties the knot is always a plain Haskell function.

This means that the recursive helpers used to construct operations must target a narrower HypA (->).

A more polymorphic compose does exist:

zipper etc 

But it seems to lack an id and doesn't feel useful.

