---
name: application-is-whitespace
description: Surfacing the invisible operations hidden in Haskell syntax
---

# application is whitespace

In Haskell, `f x` is barely a token—just spacing between words. Application is so invisible it's not even syntax, it's **absence of syntax**.

When we write a GADT like Traced with an `Apply` constructor:

```haskell
Apply :: (b -> c) -> Traced a b -> Traced a c
```

We're not "deferring" application. We're **surfacing it**. Making the invisible visible. Turning whitespace into data.

The same pattern up the tower:

- **Apply** ⟜ makes application explicit (was invisible juxtaposition)
- **Compose** ⟜ makes composition explicit (was notational convenience)
- **Loop** ⟜ makes feedback explicit (was hidden inside fix/bind)

The GADT isn't about deferral. It's about **giving names to operations Haskell doesn't acknowledge**.

This is why the tower works: we're not inventing new operations. We're surfacing the ones already there, making them structurally visible so they can be manipulated, composed, and reasoned about.

Application as whitespace: the insight that lets you see what was always there.
