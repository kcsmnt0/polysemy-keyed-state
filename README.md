# polysemy-keyed-state

The `KeyedState k` effect provides access to a set of stateful values indexed by some key type `k`, where a key of type `k a` can be used to access a stateful value of type `a`.

In the most direct use case, the `KeyedState` effect can be used as an interface to low-level reference types like `IORef` and `STRef`: for example, `getAt` can be used with the type `Member (KeyedState IORef) r => IORef a -> Sem r a`.

At a higher level, key types defined as GADTs can be used with `KeyedState` to represent sets of stateful variables in a single effect. For example, with the GADT definition of `K` below, the effect `KeyedState K` provides access to an `Int` value with key `X` and a `Bool` value with key `Y`.

```haskell
data K a where
  X :: K Int
  Y :: K Bool
```

By mapping high-level keys to low-level references, the `KeyedState` effect can be used to implement a high-level interface to a set of low-level variables.

Some of the interpreters for `KeyedState` require instances of `Has` for certain typeclasses, which can be generated for most GADT key types with `deriveArgDict` from the [`constraints-extras`](https://hackage.haskell.org/package/constraints-extras) package.
