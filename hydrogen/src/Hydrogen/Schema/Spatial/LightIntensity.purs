-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // spatial // light intensity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LightIntensity Atom — Luminous intensity of a light source.
-- |
-- | Units depend on light type (candela, lumens, or arbitrary scalar).
-- | PBR workflows often use physical units.
-- |
-- | Bounds: >= 0.0

module Hydrogen.Schema.Spatial.LightIntensity
  ( LightIntensity
  , lightIntensity
  , unsafeLightIntensity
  , unwrapLightIntensity
  , lightIntensityBounds
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Light intensity
newtype LightIntensity = LightIntensity Number

derive instance eqLightIntensity :: Eq LightIntensity
derive instance ordLightIntensity :: Ord LightIntensity

instance showLightIntensity :: Show LightIntensity where
  show (LightIntensity i) = "(LightIntensity " <> show i <> ")"

-- | Create LightIntensity (non-negative)
lightIntensity :: Number -> LightIntensity
lightIntensity n
  | n < 0.0 = LightIntensity 0.0
  | otherwise = LightIntensity n

unsafeLightIntensity :: Number -> LightIntensity
unsafeLightIntensity = LightIntensity

unwrapLightIntensity :: LightIntensity -> Number
unwrapLightIntensity (LightIntensity n) = n

lightIntensityBounds :: Bounded.NumberBounds
lightIntensityBounds = Bounded.numberBounds 0.0 1000000.0 "LightIntensity"
  "Light intensity value (non-negative)"
