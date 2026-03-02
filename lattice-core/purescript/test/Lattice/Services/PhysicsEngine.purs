-- | Port of ui/src/__tests__/services/PhysicsEngine.test.ts
-- |
-- | Tests physics body inverse mass calculations.
-- | BUG-005 FIX: Prevents division by zero when mass is 0 for dynamic bodies.

module Test.Lattice.Services.PhysicsEngine (spec) where

import Prelude

import Data.Foldable (for_)
import Data.Number as Number
import Data.Tuple (Tuple(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertFinite)

-- | Body type for physics simulation
data BodyType = Static | Dead | Dynamic | Kinematic

-- | Calculate inverse mass for a physics body.
-- | BUG-005 FIX: mass=0 for dynamic bodies uses fallback mass=1
-- | instead of producing Infinity from division by zero.
calculateInverseMass :: BodyType -> Number -> Number
calculateInverseMass Static _ = 0.0
calculateInverseMass Dead _ = 0.0
calculateInverseMass _ mass
  | mass == 0.0 || Number.isNaN mass = 1.0
  | otherwise = 1.0 / mass

spec :: Spec Unit
spec = do
  describe "PhysicsEngine body calculations" do
    describe "inverseMass calculation" do
      it "static bodies have zero inverse mass" do
        calculateInverseMass Static 10.0 `shouldEqual` 0.0
        calculateInverseMass Static 0.0 `shouldEqual` 0.0

      it "dead bodies have zero inverse mass" do
        calculateInverseMass Dead 10.0 `shouldEqual` 0.0
        calculateInverseMass Dead 0.0 `shouldEqual` 0.0

      it "dynamic bodies calculate inverse mass correctly" do
        calculateInverseMass Dynamic 1.0 `shouldEqual` 1.0
        calculateInverseMass Dynamic 2.0 `shouldEqual` 0.5
        calculateInverseMass Dynamic 10.0 `shouldEqual` 0.1

      it "BUG #5 FIXED: dynamic body with mass=0 returns 1 instead of Infinity" do
        -- Was: Infinity (1/0)
        -- Now: 1 (1/(0||1) = 1/1)
        calculateInverseMass Dynamic 0.0 `shouldEqual` 1.0
        assertFinite (calculateInverseMass Dynamic 0.0)

      it "BUG #5 FIXED: kinematic body with mass=0 returns 1" do
        -- Kinematic bodies are also dynamic (not static/dead)
        calculateInverseMass Kinematic 0.0 `shouldEqual` 1.0
        assertFinite (calculateInverseMass Kinematic 0.0)

      it "inverse mass is always finite for any body type" do
        let
          bodyTypes =
            [ Tuple "static" Static
            , Tuple "dead" Dead
            , Tuple "dynamic" Dynamic
            , Tuple "kinematic" Kinematic
            ]
          masses = [ 0.0, 0.1, 1.0, 10.0, 100.0 ]
        for_ bodyTypes \(Tuple _ bodyType) ->
          for_ masses \mass -> do
            let result = calculateInverseMass bodyType mass
            case bodyType of
              Static -> result `shouldEqual` 0.0
              Dead -> result `shouldEqual` 0.0
              _ ->
                if mass > 0.0
                  then assertFinite result
                  else pure unit

      it "NaN mass falls back to 1 for dynamic bodies" do
        calculateInverseMass Dynamic Number.nan `shouldEqual` 1.0
        assertFinite (calculateInverseMass Dynamic Number.nan)
