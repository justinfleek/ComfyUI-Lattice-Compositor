-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // spatial // focal length
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FocalLength Atom — Camera lens focal length in millimeters.
-- |
-- | Used for physical camera simulation.
-- |
-- | ## Common Values
-- | - 16mm: Ultra wide
-- | - 24mm: Wide
-- | - 35mm: Standard wide
-- | - 50mm: Standard ("Nifty Fifty")
-- | - 85mm: Portrait
-- | - 100mm+: Telephoto

module Hydrogen.Schema.Spatial.FocalLength
  ( FocalLength
  , focalLength
  , unsafeFocalLength
  , unwrapFocalLength
  , focalLengthBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // focal length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focal length in millimeters (> 0)
newtype FocalLength = FocalLength Number

derive instance eqFocalLength :: Eq FocalLength
derive instance ordFocalLength :: Ord FocalLength

instance showFocalLength :: Show FocalLength where
  show (FocalLength f) = "(FocalLength " <> show f <> "mm)"

-- | Create FocalLength, clamping to minimum 1mm
focalLength :: Number -> FocalLength
focalLength f
  | f < 1.0 = FocalLength 1.0
  | otherwise = FocalLength f

-- | Create FocalLength without bounds checking
unsafeFocalLength :: Number -> FocalLength
unsafeFocalLength = FocalLength

-- | Extract raw Number
unwrapFocalLength :: FocalLength -> Number
unwrapFocalLength (FocalLength f) = f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for FocalLength
focalLengthBounds :: Bounded.NumberBounds
focalLengthBounds = Bounded.numberBounds 1.0 5000.0 "focalLength"
  "Lens focal length in millimeters"
