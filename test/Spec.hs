-- import Data.Constraint
import Data.Constraint.Extras
import Data.Constraint.Extras.TH
import Data.IORef
import Data.GADT.Compare
import Data.GADT.Show
import Data.Kind
import Data.Some
import Data.StateVar (($=))
import Data.Typeable
-- import Data.Type.Equality
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Polysemy
-- import Polysemy.Internal
import Polysemy.Membership
import Polysemy.State
import Polysemy.State.Keyed
import Polysemy.State.Keyed.Law
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck as QuickCheck
import Test.QuickCheck.Monadic as QuickCheck

data TestKey :: Type -> Type where
  A, B :: TestKey Int
  C :: TestKey Double
  D :: TestKey Bool

deriveArgDict ''TestKey

deriving instance Eq (TestKey a)
deriving instance Show (TestKey a)

instance GShow TestKey where
  gshowsPrec = showsPrec

instance GEq TestKey where
  geq (k :: TestKey a) (k' :: TestKey b) =
    has @Typeable k $ has @Typeable k' $ eqT @a @b

instance Arbitrary (Some TestKey) where
  arbitrary = elements [Some A, Some B, Some C, Some D]

propertyM :: Applicative m => Property -> PropertyM m ()
propertyM = MkPropertyM . const . pure . pure

spec :: Spec
spec = do
  describe "runKeyedStates" $ do
    prop "obeys the KeyedState laws" $
      \(a :: Int) (b :: Int) (c :: Double) (d :: Bool) -> do
        prop_lawfulKeyedState @_ @'[Embed IO] $
          evalState d .
          evalState c .
          evalState b .
          evalState a .
          runKeyedStates (\case A -> Here; B -> There Here; C -> There $ There Here; D -> There $ There $ There Here) .
          subsume_

  describe "runKeyedStateStore" $ do
    prop "obeys the KeyedState laws" $
      \(a :: Int) (b :: Int) (c :: Double) (d :: Bool) -> do
        prop_lawfulKeyedState @_ @'[Embed IO] $
          evalState (KeyedStore (\case A -> a; B -> b; C -> c; D -> d)) .
          runKeyedStateStore @TestKey .
          raiseUnder

  describe "runKeyedStateVarsIO" $ do
    prop "obeys the KeyedState laws with IORef storage" $
      \(a :: Int) (b :: Int) (c :: Double) (d :: Bool) -> monadicIO $ do
        (refA,refB,refC,refD) <- QuickCheck.run $ (,,,) <$> newIORef a <*> newIORef b <*> newIORef c <*> newIORef d
        propertyM $ prop_lawfulKeyedState @_ @'[Embed IO] $
          runKeyedStateVarsIO @IORef $ \case A -> refA; B -> refB; C -> refC; D -> refD

  describe "runStorableKeyedStateVarsIO" $ do
    prop "obeys the KeyedState laws with Ptr storage" $
      \(a :: Int) (b :: Int) (c :: Double) (d :: Bool) -> monadicIO $ do
        (refA,refB,refC,refD) <- QuickCheck.run $ (,,,) <$> malloc <*> malloc <*> malloc <*> malloc
        refA $= a; refB $= b; refC $= c; refD $= d
        propertyM $ prop_lawfulKeyedState @_ @'[Embed IO] $
          runStorableKeyedStateVarsIO @Ptr $ \case A -> refA; B -> refB; C -> refC; D -> refD
        QuickCheck.run $ do free refA; free refB; free refC; free refD
        
main :: IO ()
main = hspec spec
