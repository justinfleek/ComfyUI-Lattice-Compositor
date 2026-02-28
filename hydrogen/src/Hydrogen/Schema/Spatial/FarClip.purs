-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // far clip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FarClip Atom — Camera far clipping plane distance.
-- |
-- | Geometry further than this distance is clipped.
-- | Must be > NearClip.
-- |
-- | Typical values:
-- | - 1000.0 (standard)
-- | - 100.0 (foggy/close)
-- | - 10000.0 (large scenes)

module Hydrogen.Schema.Spatial.FarClip
  ( FarClip
  , farClip
  , unsafeFarClip
  , unwrapFarClip
  , farClipBounds
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Far clipping plane distance
newtype FarClip = FarClip Number

derive instance eqFarClip :: Eq FarClip
derive instance ordFarClip :: Ord FarClip

instance showFarClip :: Show FarClip where
  show (FarClip n) = "(FarClip " <> show n <> ")"

-- | Create FarClip, clamped to minimum 0.1
farClip :: Number -> FarClip
farClip n
  | n < 0.1 = FarClip 0.1
  | otherwise = FarClip n

unsafeFarClip :: Number -> FarClip
unsafeFarClip = FarClip

unwrapFarClip :: FarClip -> Number
unwrapFarClip (FarClip n) = n

farClipBounds :: Bounded.NumberBounds
farClipBounds = Bounded.numberBounds 0.1 1000000.0 "FarClip"
  "Far clipping plane distance (> 0.1)"
