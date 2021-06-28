{-|
Module: Polysemy.State.Keyed
Copyright: (c) Katie Casamento, 2021
License: GPL-3
Maintainer: kcsmnt0@gmail.com
Stability: experimental

The @KeyedState k@ effect provides access to a set of stateful values indexed by some key type @k :: Type -> Type@, where a key of type @k a@ can be used to access a stateful value of type @a@.

In the most direct use case, the @KeyedState@ effect can be used as an interface to low-level reference types like [@IORef@](https://hackage.haskell.org/package/base/docs/Data-IORef.html#t:IORef) and [@STRef@](https://hackage.haskell.org/package/base/docs/Data-STRef.html#t:STRef): for example, @getAt@ can be used with the type @Member (KeyedState IORef) r => IORef a -> Sem r a@.

At a higher level, key types defined as GADTs can be used with @KeyedState@ to represent sets of stateful variables in a single effect. For example, with the GADT definition of @K@ below, the effect @KeyedState K@ provides access to an @Int@ value with key @X@ and a @Bool@ value with key @Y@.

@
data K a where
  X :: K Int
  Y :: K Bool
@

By mapping high-level keys to low-level references, the @KeyedState@ effect can be used to implement a high-level interface to a set of low-level variables.

Some of the interpreters for @KeyedState@ require instances of [@Has@](https://hackage.haskell.org/package/constraints-extras/docs/Data-Constraint-Extras.html#t:Has) for certain typeclasses, which can be generated for most GADT key types with [@deriveArgDict@](https://hackage.haskell.org/package/constraints-extras/docs/Data-Constraint-Extras-TH.html#v:deriveArgDict).
-}
module Polysemy.State.Keyed
  ( KeyedState(..)
  -- * Operations
  , getAt
  , putAt
  , modifyAt
  , rename
  -- * @State@ interpreters
  , runKeyedStates
  , KeyedStore(..)
  , lookupAt, updateAt, updateAtBy
  , runKeyedStateStore, runKeyedStateStoreBy
  -- * @IO@ interpreters
  , Reference, module Data.Constraint.Trivial
  , runKeyedStateRefsIO
  , runKeyedStateVarsIO, runKeyedStateVarsOfIO
  , runStorableKeyedStateVarsIO, runStorableKeyedStateVarsOfIO
  , runConstrainedKeyedStateVarsIO, runConstrainedKeyedStateVarsOfIO
  )
  where

import Data.Constraint
import Data.Constraint.Extras
import Data.Constraint.Trivial
import Data.StateVar hiding (get)
import qualified Data.StateVar as StateVar
import Data.Typeable
import Foreign.Storable
import Polysemy
import Polysemy.Input
import Polysemy.Internal
import Polysemy.Membership
import Polysemy.State

newtype UnconstrainedKey k a = UnconstrainedKey { getUnconstrainedKey :: k a }
instance ArgDict Unconstrained (UnconstrainedKey k) where
  type ConstraintsFor (UnconstrainedKey k) Unconstrained = ()
  argDict = const Dict

{-|
An interpreter for @KeyedState@ may or may not obey the following "consistency" law:

* for any @k@, @k'@, and @v@, @putAt k v *> getAt k' = if k == k' then pure v else getAt k'@

This law is relevant for most pure interpretations of @KeyedState@, but only applies when the values in the state are /disjoint/ (setting at @k@ does not modify the value at @k'@ when @k /= k'@) and /local/ (never modified by another thread or program). Some useful sets of stateful values violate this law: for example, the [@sdl2@](https://hackage.haskell.org/package/sdl2) package provides a set of [@StateVar@s](https://hackage.haskell.org/package/StateVar/docs/Data-StateVar.html#t:StateVar) for each SDL window created, which are neither disjoint nor local.
-}
data KeyedState k :: Effect where
  GetAt :: k a -> KeyedState k m a
  PutAt :: k a -> a -> KeyedState k m ()

makeSem ''KeyedState

modifyAt ::
  forall k a r.
  Member (KeyedState k) r =>
  k a -> (a -> a) -> Sem r ()
modifyAt k f = putAt k . f =<< getAt k

-- |Run a @KeyedState@ operation in the context of another @KeyedState@ effect by translating the keys.
rename ::
  forall k k' r a.
  Member (KeyedState k') r =>
  (forall x. k x -> k' x) -> Sem (KeyedState k : r) a -> Sem r a
rename h =
  transform $ \case
    GetAt k -> GetAt $ h k
    PutAt k x -> PutAt (h k) x

{-|
Distribute a @KeyedState@ effect across multiple @State@ effects by mapping each key to an effect.

Lawful if the @State@ effects are interpreted lawfully.
-}
runKeyedStates ::
  forall k r.
  (forall a. k a -> ElemOf (State a) r) ->
  InterpreterFor (KeyedState k) r
runKeyedStates h =
  interpret $ \case
    GetAt k -> subsumeUsing (h k) get
    PutAt k x -> subsumeUsing (h k) $ put x

-- |A @KeyedStore k@ is a total map over keys of type @k@.
newtype KeyedStore k = KeyedStore { runKeyedStore :: forall a. k a -> a }

-- |Retrieve a value from a @KeyedStore@.
lookupAt :: k a -> KeyedStore k -> a
lookupAt = flip runKeyedStore

-- |Update a value in a @KeyedStore@, using @Typeable@ instances to check for key type equality.
updateAt ::
  forall k a.
  (Typeable a, Has Typeable k, forall x. Eq (k x)) =>
  k a -> a -> KeyedStore k -> KeyedStore k
updateAt = updateAtBy $ \_ k' -> has @Typeable k' eqT

-- |Update an entry in a @KeyedStore@, using a specified function to check for key type equality. This can be used with functions like [@testEquality@](https://hackage.haskell.org/package/base/docs/Data-Type-Equality.html#v:testEquality) and [@geq@](https://hackage.haskell.org/package/some/docs/Data-GADT-Compare.html#v:geq) to avoid @Typeable@ constraints.
updateAtBy ::
  forall k a.
  (forall x. Eq (k x)) =>
  (forall b. k a -> k b -> Maybe (a :~: b)) ->
  k a -> a -> KeyedStore k -> KeyedStore k
updateAtBy eq k x m =
  KeyedStore $ \k' ->
    case eq k k' of
      Just Refl | k == k' -> x
      _ -> lookupAt k' m

{-|
Interpret a @KeyedState@ effect as a @State@ effect over a @KeyedStore@, using @Typeable@ instances to check for key type equality.

Lawful.
-}
runKeyedStateStore ::
  forall k r.
  (Member (State (KeyedStore k)) r, forall a. Eq (k a), Has Typeable k) =>
  InterpreterFor (KeyedState k) r
runKeyedStateStore =
  runKeyedStateStoreBy $ \k k' ->
    has @Typeable k $ has @Typeable k' eqT

{-|
Interpret a @KeyedState@ effect as a @State@ effect over a @KeyedStore@, using a specified function to check for key type equality. This can be used with functions like [@testEquality@](https://hackage.haskell.org/package/base/docs/Data-Type-Equality.html#v:testEquality) and [@geq@](https://hackage.haskell.org/package/some/docs/Data-GADT-Compare.html#v:geq) to avoid @Typeable@ constraints.

Lawful if the key type equality function always returns @Just Refl@ whenever possible (i.e. it correctly says that any two equal types are equal); otherwise, @putAt@ may silently fail to have any effect in some cases.
-}
runKeyedStateStoreBy ::
  forall k r.
  (Member (State (KeyedStore k)) r, forall a. Eq (k a)) =>
  (forall a b. k a -> k b -> Maybe (a :~: b)) ->
  InterpreterFor (KeyedState k) r
runKeyedStateStoreBy eq =
  interpret $ \case
    GetAt k -> lookupAt k <$> get
    PutAt k x -> put . updateAtBy eq k x =<< get

-- |An instance of @Reference c k@ indicates that @k@ is an @IO@ reference type (like @IORef@, @STRef@, ...) that requires values to meet the constraint @c@. For more information, see the documentation for @HasGetter@ and @HasSetter@.
class (forall a. c a => HasGetter (k a) a, forall a. c a => HasSetter (k a) a) => Reference c k
instance (forall a. c a => HasGetter (k a) a, forall a. c a => HasSetter (k a) a) => Reference c k

{-|
Interpret each key directly as an @IO@ reference. Useful with "key" types like @IORef@ and @STRef@.
 
Note that there is no way to directly interpret a @KeyedState@ effect where the "keys" are references that require @Storable@ or other constraints to modify, like @Ptr@ and @ForeignPtr@, since @PutAt@ does not have any constraints on its argument type. To use @KeyedState@ with constrained reference types, you can define a GADT key type to represent the set of references and interpret the effect with [@runStorableKeyedStateVarsIO@](#v:runStorableKeyedStateVarsIO), [@runStorableKeyedStateVarsOfIO@](#v:runStorableKeyedStateVarsOfIO), [@runConstrainedKeyedStateVarsIO@](#v:runConstrainedKeyedStateVarsIO), or [@runConstrainedKeyedStateVarsOfIO@](#v:runConstrainedKeyedStateVarsOfIO).

Lawful if all references used with @getAt@ and @putAt@ are disjoint and local.
-}
runKeyedStateRefsIO ::
  forall k r.
  (Member (Embed IO) r, Reference Unconstrained k) =>
  InterpreterFor (KeyedState k) r
runKeyedStateRefsIO = runKeyedStateVarsIO id

{-|
Interpret a @KeyedState@ effect as a set of @IO@ references by mapping each key to a reference.

Lawful if all references returned by the mapping are disjoint and local.
-}
runKeyedStateVarsIO ::
  forall ref k r.
  (Member (Embed IO) r, Reference Unconstrained ref) =>
  (forall a. k a -> ref a) ->
  InterpreterFor (KeyedState k) r
runKeyedStateVarsIO h =
  runInputConst () .
  runKeyedStateVarsOfIO (\k _ -> h k) .
  raiseUnder

{-|
Like [@runKeyedStateVarsIO@](#v:runKeyedStateVarsIO), but for references that are accessed through some pure handle, like the [window attributes](https://hackage.haskell.org/package/sdl2/docs/SDL-Video.html#g:3) in [@sdl2@](https://hackage.haskell.org/package/sdl2) package.

Lawful if all references returned by the mapping are disjoint and local.
-}
runKeyedStateVarsOfIO ::
  forall s ref k r.
  (Members [Input s, Embed IO] r, Reference Unconstrained ref) =>
  (forall a. k a -> s -> ref a) ->
  InterpreterFor (KeyedState k) r
runKeyedStateVarsOfIO h =
  runConstrainedKeyedStateVarsOfIO @s @Unconstrained (h . getUnconstrainedKey) .
  rename UnconstrainedKey .
  raiseUnder

{-|
Interpret a @KeyedState@ effect as a set of @IO@ references by mapping each key to a reference that requires a @Storable@ constraint on values.

Lawful if all references returned by the mapping are disjoint and local.
-}
runStorableKeyedStateVarsIO ::
  forall ref k r.
  (Member (Embed IO) r, Reference Storable ref, Has Storable k) =>
  (forall a. k a -> ref a) ->
  InterpreterFor (KeyedState k) r
runStorableKeyedStateVarsIO = runConstrainedKeyedStateVarsIO @Storable

{-|
Like [@runStorableKeyedStateVarsIO@](#v:runStorableKeyedStateVarsIO), but for references that are accessed through some pure handle.

Lawful if all references returned by the mapping are disjoint and local.
-}
runStorableKeyedStateVarsOfIO ::
  forall s ref k r.
  (Members [Input s, Embed IO] r, Reference Storable ref, Has Storable k) =>
  (forall a. k a -> s -> ref a) ->
  InterpreterFor (KeyedState k) r
runStorableKeyedStateVarsOfIO = runConstrainedKeyedStateVarsOfIO @s @Storable

{-|
Interpret a @KeyedState effect as a set of @IO@ references by mapping each key to a references that requires some specified constraint on values. This will usually need the @TypeApplications@ extension to disambiguate the constraint. This can be used if you have some exotic reference type that requires a constraint other than @Storable@.

Lawful if all references returned by the mapping are disjoint and local.
-}
runConstrainedKeyedStateVarsIO ::
  forall c ref k r.
  (Member (Embed IO) r, Reference c ref, Has c k) =>
  (forall a. k a -> ref a) ->
  InterpreterFor (KeyedState k) r
runConstrainedKeyedStateVarsIO h =
  runInputConst () .
  runConstrainedKeyedStateVarsOfIO @() @c (\k _ -> h k) .
  raiseUnder

{-|
Like [@runConstrainedKeyedStateVarsIO@](#v:runConstrainedKeyedStateVarsIO), but for references that are accessed through some pure handle.

Lawful if all references returned by the mapping are disjoint and local.
-}
runConstrainedKeyedStateVarsOfIO ::
  forall s c ref k r.
  (Members [Input s, Embed IO] r, Reference c ref, Has c k) =>
  (forall a. k a -> s -> ref a) ->
  InterpreterFor (KeyedState k) r
runConstrainedKeyedStateVarsOfIO h =
  interpret $ \case
    GetAt k -> has @c k $ input >>= StateVar.get . h k
    PutAt k x -> has @c k $ input >>= \s -> h k s $= x
