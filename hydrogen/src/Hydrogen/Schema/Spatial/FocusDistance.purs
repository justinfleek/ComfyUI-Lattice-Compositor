-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // spatial // focus distance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FocusDistance Atom — Camera focus plane distance.
-- |
-- | Range: 0 to infinity (finite)
-- | - **0.3m**: Macro photography minimum
-- | - **1-3m**: Portrait range
-- | - **5-10m**: Group shots
-- | - **∞**: Hyperfocal/landscape
-- |
-- | Distance from camera sensor to the plane of sharpest focus.
-- | Combined with aperture, determines depth of field.

module Hydrogen.Schema.Spatial.FocusDistance
  ( FocusDistance
  , focusDistance
  , unwrapFocusDistance
  
  -- * Common Values
  , macro
  , portrait
  , medium
  , far
  , infinity
  
  -- * Operations
  , hyperfocalDistance
  , depthOfFieldNear
  , depthOfFieldFar
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // focus distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus distance in meters
-- |
-- | Non-negative. 0 means focused at sensor (not physically possible).
-- | Very large values approximate infinity focus.
newtype FocusDistance = FocusDistance Number

derive instance eqFocusDistance :: Eq FocusDistance
derive instance ordFocusDistance :: Ord FocusDistance

instance showFocusDistance :: Show FocusDistance where
  show (FocusDistance d) = show d <> "m"

-- | Create a focus distance (clamped to non-negative)
focusDistance :: Number -> FocusDistance
focusDistance n = FocusDistance (if n < 0.0 then 0.0 else n)

-- | Extract distance value (meters)
unwrapFocusDistance :: FocusDistance -> Number
unwrapFocusDistance (FocusDistance d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Macro distance (0.3m)
macro :: FocusDistance
macro = FocusDistance 0.3

-- | Portrait distance (2m)
portrait :: FocusDistance
portrait = FocusDistance 2.0

-- | Medium distance (5m)
medium :: FocusDistance
medium = FocusDistance 5.0

-- | Far distance (15m)
far :: FocusDistance
far = FocusDistance 15.0

-- | Infinity focus (very large distance)
infinity :: FocusDistance
infinity = FocusDistance 1.0e10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate hyperfocal distance
-- |
-- | The focus distance where everything from half that distance to infinity
-- | is acceptably sharp.
-- |
-- | H = f² / (N * c)
-- | where f = focal length (mm), N = f-number, c = circle of confusion (mm)
hyperfocalDistance :: Number -> Number -> Number -> FocusDistance
hyperfocalDistance focalLengthMM fNumber circleOfConfusionMM =
  let h = (focalLengthMM * focalLengthMM) / (fNumber * circleOfConfusionMM)
  in FocusDistance (h / 1000.0)  -- Convert mm to meters

-- | Calculate near limit of depth of field
-- |
-- | Dn = (H * s) / (H + (s - f))
-- | Simplified: Dn ≈ (H * s) / (H + s) for s << H
depthOfFieldNear :: FocusDistance -> FocusDistance -> FocusDistance
depthOfFieldNear (FocusDistance hyperfocal) (FocusDistance subject) =
  if hyperfocal <= 0.0 || subject <= 0.0
    then FocusDistance 0.0
    else FocusDistance ((hyperfocal * subject) / (hyperfocal + subject))

-- | Calculate far limit of depth of field
-- |
-- | Df = (H * s) / (H - s) for s < H
-- | Returns infinity if s >= H
depthOfFieldFar :: FocusDistance -> FocusDistance -> FocusDistance
depthOfFieldFar (FocusDistance hyperfocal) (FocusDistance subject) =
  if subject >= hyperfocal
    then infinity
    else if hyperfocal <= 0.0 || subject <= 0.0
      then FocusDistance 0.0
      else FocusDistance ((hyperfocal * subject) / (hyperfocal - subject))
