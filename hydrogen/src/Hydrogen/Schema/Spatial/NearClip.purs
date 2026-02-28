-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // spatial // near clip
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NearClip Atom — Camera near clipping plane distance.
-- |
-- | Geometry closer than this distance is clipped (not rendered).
-- | Must be > 0.
-- |
-- | Typical values:
-- | - 0.1 (standard)
-- | - 0.01 (close-up)

module Hydrogen.Schema.Spatial.NearClip
  ( NearClip
  , nearClip
  , unsafeNearClip
  , unwrapNearClip
  , nearClipBounds
  ) where

import Prelude
import Hydrogen.Schema.Bounded as Bounded

-- | Near clipping plane distance
newtype NearClip = NearClip Number

derive instance eqNearClip :: Eq NearClip
derive instance ordNearClip :: Ord NearClip

instance showNearClip :: Show NearClip where
  show (NearClip n) = "(NearClip " <> show n <> ")"

-- | Create NearClip, clamped to minimum 0.001
nearClip :: Number -> NearClip
nearClip n
  | n < 0.001 = NearClip 0.001
  | otherwise = NearClip n

unsafeNearClip :: Number -> NearClip
unsafeNearClip = NearClip

unwrapNearClip :: NearClip -> Number
unwrapNearClip (NearClip n) = n

nearClipBounds :: Bounded.NumberBounds
nearClipBounds = Bounded.numberBounds 0.001 100000.0 "NearClip"
  "Near clipping plane distance (> 0.001)"
