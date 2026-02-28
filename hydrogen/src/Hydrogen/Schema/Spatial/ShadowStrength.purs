-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // spatial // shadow strength
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ShadowStrength Atom — Opacity/Darkness of the shadow.
-- |
-- | 0.0 = Invisible shadow
-- | 1.0 = Fully opaque shadow
-- |
-- | Allows for artistic control over shadow density.

module Hydrogen.Schema.Spatial.ShadowStrength
  ( ShadowStrength
  , shadowStrength
  , unsafeShadowStrength
  , unwrapShadowStrength
  , shadowStrengthBounds
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Shadow opacity (0.0 to 1.0)
newtype ShadowStrength = ShadowStrength Number

derive instance eqShadowStrength :: Eq ShadowStrength
derive instance ordShadowStrength :: Ord ShadowStrength

instance showShadowStrength :: Show ShadowStrength where
  show (ShadowStrength s) = "(ShadowStrength " <> show s <> ")"

-- | Create ShadowStrength, clamped to [0, 1]
shadowStrength :: Number -> ShadowStrength
shadowStrength n
  | n < 0.0 = ShadowStrength 0.0
  | n > 1.0 = ShadowStrength 1.0
  | otherwise = ShadowStrength n

unsafeShadowStrength :: Number -> ShadowStrength
unsafeShadowStrength = ShadowStrength

unwrapShadowStrength :: ShadowStrength -> Number
unwrapShadowStrength (ShadowStrength n) = n

shadowStrengthBounds :: Bounded.NumberBounds
shadowStrengthBounds = Bounded.numberBounds 0.0 1.0 "ShadowStrength"
  "Shadow opacity (0.0 to 1.0)"
