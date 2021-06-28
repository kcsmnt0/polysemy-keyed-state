module Polysemy.State.Keyed.Law where

import Data.Constraint.Extras
import Data.GADT.Compare
import Data.GADT.Show
import Data.Some
import Data.Type.Equality
import Polysemy
import Polysemy.Law
import Polysemy.State.Keyed

prop_lawfulKeyedState ::
  forall k r.
  MakeLaw (KeyedState k) r =>
  (forall a. Eq a => Eq (k a), GEq k, GShow k) =>
  (Has Show k, Has Eq k, Has Arbitrary k, Arbitrary (Some k)) =>
  InterpreterFor (KeyedState k) r -> Property
prop_lawfulKeyedState f = runLaw f law_consistency

newtype KeyValuePair k a = KeyValuePair (k a, a)

instance GEq k => GEq (KeyValuePair k) where
  geq (KeyValuePair (x,_)) (KeyValuePair (y,_)) = geq x y

instance (Has Arbitrary k, Arbitrary (Some k)) => Arbitrary (Some (KeyValuePair k)) where
  arbitrary =
    withSomeM arbitrary $ \(k :: k a) ->
      has @Arbitrary k $ Some . KeyValuePair . (k,) <$> arbitrary

instance (Has Show k, GShow k) => GShow (KeyValuePair k) where
  gshowsPrec i (KeyValuePair (k, x)) s =
    has @Show k $ concat ["(", gshowsPrec i k "", ", ", showsPrec i x "", ")", s]

law_consistency ::
  forall k r.
  MakeLaw (KeyedState k) r =>
  (forall a. Eq a => Eq (k a), GEq k, GShow k) =>
  (Has Show k, Has Eq k, Has Arbitrary k, Arbitrary (Some k)) =>
  Law (KeyedState k) r
law_consistency =
  mkLaw @_ @_ @_ @(_ -> _ -> Sem _ (Some (KeyValuePair k)))
    "uncurry putAt %1 *> getAt %2"
    (\(Some (KeyValuePair (k, x))) (Some k') ->
      putAt k x *> (Some . KeyValuePair . (k',) <$> getAt k'))
    "if fst %1 == %2 then pure (snd %1) else getAt %2"
    (\(Some (KeyValuePair (k, x))) (Some k') ->
      case geq k k' of
        Just Refl | has @Eq k $ k == k' -> pure $ Some $ KeyValuePair (k, x)
        _ -> Some . KeyValuePair . (k',) <$> getAt k')
