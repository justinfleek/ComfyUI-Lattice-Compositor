-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // spatial // shadow bias
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ShadowBias Atom — Offset for shadow map depth comparison.
-- |
-- | Used to prevent "shadow acne" (self-shadowing artifacts).
-- |
-- | Typical values:
-- | - 0.0 (no bias)
-- | - 0.0001 (small bias)
-- | - -0.0001 (negative bias)

module Hydrogen.Schema.Spatial.ShadowBias
  ( ShadowBias
  , shadowBias
  , unsafeShadowBias
  , unwrapShadowBias
  ) where

import Prelude

-- | Shadow map bias
newtype ShadowBias = ShadowBias Number

derive instance eqShadowBias :: Eq ShadowBias
derive instance ordShadowBias :: Ord ShadowBias

instance showShadowBias :: Show ShadowBias where
  show (ShadowBias b) = "(ShadowBias " <> show b <> ")"

-- | Create ShadowBias
shadowBias :: Number -> ShadowBias
shadowBias = ShadowBias

unsafeShadowBias :: Number -> ShadowBias
unsafeShadowBias = ShadowBias

unwrapShadowBias :: ShadowBias -> Number
unwrapShadowBias (ShadowBias n) = n
