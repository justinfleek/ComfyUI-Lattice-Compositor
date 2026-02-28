-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // color // color-wheels
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorWheels - Lift/Gamma/Gain color grading (shadows/midtones/highlights).
-- |
-- | **PROFESSIONAL COLOR GRADING:**
-- | The three-wheel color grading system used in DaVinci Resolve, Premiere Pro,
-- | and professional color grading applications.
-- |
-- | **Three tonal ranges:**
-- | - **Lift** (Blacks/Shadows): Affects darkest areas, minimal impact on highlights
-- | - **Gamma** (Midtones): Affects middle tones, preserves blacks and whites
-- | - **Gain** (Whites/Highlights): Affects brightest areas, minimal impact on shadows
-- |
-- | **Each wheel controls:**
-- | - Color shift (hue rotation on color picker wheel)
-- | - Intensity (distance from center = amount of color added)
-- | - Luminance (master brightness control for that tonal range)
-- |
-- | **Common use cases:**
-- | - Warm shadows, cool highlights (cinematic look)
-- | - Teal shadows, orange midtones (blockbuster style)
-- | - Correct color cast in specific tonal ranges
-- | - Create mood through selective color
-- |
-- | **Integration:**
-- | Part of ColorGrading compound - applied after WhiteBalance, before Curves.

module Hydrogen.Schema.Color.ColorWheels
  ( ColorWheels
  , WheelAdjustment
  , colorWheels
  , neutralWheels
  , wheelAdjustment
  , neutralAdjustment
  , lift
  , gamma
  , gain
  , applyToRgb
  , withLift
  , withGamma
  , withGain
  ) where

import Prelude
  ( negate
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  )

import Data.Int as Int
import Data.Number (cos, sin, pi)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Ch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // wheel adjustment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color wheel adjustment for one tonal range
-- |
-- | **Color picker coordinates:**
-- | - Angle (0-360°): Hue direction (0=red, 120=green, 240=blue)
-- | - Distance (0.0-1.0): Intensity of color shift
-- | - Luminance (-1.0 to 1.0): Master brightness for this tonal range
type WheelAdjustment =
  { angle :: Number        -- ^ Hue angle (0-360°)
  , intensity :: Number    -- ^ Color intensity (0.0-1.0)
  , luminance :: Number    -- ^ Brightness shift (-1.0 to 1.0)
  }

-- | Create wheel adjustment
-- |
-- | ```purescript
-- | wheelAdjustment 30.0 0.3 0.1  -- Orange tint, moderate intensity, slightly brighter
-- | wheelAdjustment 200.0 0.5 0.0 -- Cyan tint, strong intensity, neutral brightness
-- | ```
wheelAdjustment :: Number -> Number -> Number -> WheelAdjustment
wheelAdjustment angle intensity lum =
  { angle: normalizeAngle angle
  , intensity: clamp 0.0 1.0 intensity
  , luminance: clamp (-1.0) 1.0 lum
  }
  where
    normalizeAngle a = a - (Int.toNumber (Int.floor (a / 360.0))) * 360.0
    clamp min' max' val
      | val < min' = min'
      | val > max' = max'
      | otherwise = val

-- | Neutral adjustment (no color shift)
neutralAdjustment :: WheelAdjustment
neutralAdjustment = wheelAdjustment 0.0 0.0 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // color wheels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete color wheels grading system
type ColorWheels =
  { lift :: WheelAdjustment   -- ^ Shadows/blacks
  , gamma :: WheelAdjustment  -- ^ Midtones
  , gain :: WheelAdjustment   -- ^ Highlights/whites
  }

-- | Create color wheels grading
-- |
-- | ```purescript
-- | colorWheels liftAdj gammaAdj gainAdj
-- | ```
colorWheels :: WheelAdjustment -> WheelAdjustment -> WheelAdjustment -> ColorWheels
colorWheels liftAdj gammaAdj gainAdj =
  { lift: liftAdj
  , gamma: gammaAdj
  , gain: gainAdj
  }

-- | Neutral color wheels (no grading applied)
neutralWheels :: ColorWheels
neutralWheels = colorWheels neutralAdjustment neutralAdjustment neutralAdjustment

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get lift (shadows) adjustment
lift :: ColorWheels -> WheelAdjustment
lift wheels = wheels.lift

-- | Get gamma (midtones) adjustment
gamma :: ColorWheels -> WheelAdjustment
gamma wheels = wheels.gamma

-- | Get gain (highlights) adjustment
gain :: ColorWheels -> WheelAdjustment
gain wheels = wheels.gain

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply color wheels grading to RGB color
-- |
-- | **Algorithm:**
-- | 1. Calculate luminance to determine tonal range weights
-- | 2. Apply lift, gamma, gain based on luminance
-- | 3. Blend color shifts proportionally to tonal range
-- |
-- | ```purescript
-- | applyToRgb wheels rgbColor
-- | ```
applyToRgb :: ColorWheels -> RGB.RGB -> RGB.RGB
applyToRgb wheels rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    -- Calculate relative luminance
    luma = 0.2126 * r + 0.7152 * g + 0.0722 * b
    
    -- Calculate tonal range weights (sum to 1.0)
    -- Lift affects shadows (low luma)
    -- Gamma affects midtones (mid luma)
    -- Gain affects highlights (high luma)
    liftWeight = (1.0 - luma) * (1.0 - luma)  -- Strongest in shadows
    gainWeight = luma * luma                   -- Strongest in highlights
    gammaWeight = 1.0 - liftWeight - gainWeight -- Strongest in midtones
    
    -- Apply each wheel with its weight
    rLift = applyWheel wheels.lift r liftWeight
    gLift = applyWheel wheels.lift g liftWeight
    bLift = applyWheel wheels.lift b liftWeight
    
    rGamma = applyWheel wheels.gamma rLift gammaWeight
    gGamma = applyWheel wheels.gamma gLift gammaWeight
    bGamma = applyWheel wheels.gamma bLift gammaWeight
    
    rGain = applyWheel wheels.gain rGamma gainWeight
    gGain = applyWheel wheels.gain gGamma gainWeight
    bGain = applyWheel wheels.gain bGamma gainWeight
    
    -- Clamp and convert to 0-255
    rFinal = Int.round (clamp 0.0 1.0 rGain * 255.0)
    gFinal = Int.round (clamp 0.0 1.0 gGain * 255.0)
    bFinal = Int.round (clamp 0.0 1.0 bGain * 255.0)
  in
    RGB.rgb rFinal gFinal bFinal
  where
    -- Apply single wheel adjustment to a channel value
    applyWheel :: WheelAdjustment -> Number -> Number -> Number
    applyWheel adj val weight =
      let
        -- Convert angle to RGB shift
        angleRad = adj.angle * pi / 180.0
        redShift = cos angleRad * adj.intensity * weight
        blueShift = sin angleRad * adj.intensity * weight
        
        -- Apply luminance shift
        lumShift = adj.luminance * weight
        
        -- Combined adjustment (blend both color axes with luminance)
        result = val + lumShift + (redShift * 0.5) + (blueShift * 0.5)
      in result
    
    clamp min' max' val
      | val < min' = min'
      | val > max' = max'
      | otherwise = val

-- | Update lift (shadows) adjustment
withLift :: WheelAdjustment -> ColorWheels -> ColorWheels
withLift newLift wheels = wheels { lift = newLift }

-- | Update gamma (midtones) adjustment
withGamma :: WheelAdjustment -> ColorWheels -> ColorWheels
withGamma newGamma wheels = wheels { gamma = newGamma }

-- | Update gain (highlights) adjustment
withGain :: WheelAdjustment -> ColorWheels -> ColorWheels
withGain newGain wheels = wheels { gain = newGain }
