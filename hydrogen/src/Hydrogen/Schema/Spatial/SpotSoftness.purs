-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // spatial // spot softness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SpotSoftness Atom — Penumbra of a spotlight.
-- |
-- | 0.0 = Sharp edge (Hard light)
-- | 1.0 = Maximum softness (Soft light)
-- |
-- | Controls the transition between full intensity and zero intensity.

module Hydrogen.Schema.Spatial.SpotSoftness
  ( SpotSoftness
  , spotSoftness
  , unsafeSpotSoftness
  , unwrapSpotSoftness
  , spotSoftnessBounds
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Spot penumbra factor (0.0 to 1.0)
newtype SpotSoftness = SpotSoftness Number

derive instance eqSpotSoftness :: Eq SpotSoftness
derive instance ordSpotSoftness :: Ord SpotSoftness

instance showSpotSoftness :: Show SpotSoftness where
  show (SpotSoftness s) = "(SpotSoftness " <> show s <> ")"

-- | Create SpotSoftness, clamped to [0, 1]
spotSoftness :: Number -> SpotSoftness
spotSoftness n
  | n < 0.0 = SpotSoftness 0.0
  | n > 1.0 = SpotSoftness 1.0
  | otherwise = SpotSoftness n

unsafeSpotSoftness :: Number -> SpotSoftness
unsafeSpotSoftness = SpotSoftness

unwrapSpotSoftness :: SpotSoftness -> Number
unwrapSpotSoftness (SpotSoftness n) = n

spotSoftnessBounds :: Bounded.NumberBounds
spotSoftnessBounds = Bounded.numberBounds 0.0 1.0 "SpotSoftness"
  "Spotlight penumbra softness (0.0 hard to 1.0 soft)"
