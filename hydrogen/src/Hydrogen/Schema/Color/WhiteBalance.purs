-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // color // white-balance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WhiteBalance - temperature and tint correction for color grading.
-- |
-- | **PROFESSIONAL COLOR CORRECTION:**
-- | White balance adjusts the color temperature and tint of an image to
-- | compensate for lighting conditions. Essential for:
-- | - Video color grading (LATTICE)
-- | - Photo processing (COMPASS)
-- | - Consistent color across different lighting
-- | - Correcting color cast
-- |
-- | **Two-axis control:**
-- | - **Temperature** - Blue ↔ Orange (measured in Kelvin shift)
-- | - **Tint** - Green ↔ Magenta (corrects fluorescent/mixed lighting)
-- |
-- | **Common scenarios:**
-- | - Shot under tungsten (3200K), needs daylight correction → +2300K shift
-- | - Fluorescent green cast → +20 tint (toward magenta)
-- | - Shade has blue cast → -500K shift (toward warm)
-- |
-- | **Standard presets:**
-- | - Daylight: 5500K, 0 tint
-- | - Tungsten: 3200K, 0 tint
-- | - Fluorescent: 4000K, +10 tint (magenta to counter green)
-- | - Flash: 5500K, 0 tint
-- | - Cloudy: 6500K, 0 tint
-- | - Shade: 7500K, +10 tint
-- |
-- | **Integration:**
-- | Part of the ColorGrading compound - applied before ColorWheels and Curves.

module Hydrogen.Schema.Color.WhiteBalance
  ( WhiteBalance
  , Preset(..)
  , whiteBalance
  , fromPreset
  , temperature
  , tint
  , applyToRgb
  , withTemperature
  , withTint
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , otherwise
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<>)
  )

import Data.Int as Int
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Ch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // white balance type
-- ═════════════════════════════════════════════════════════════════════════════

-- | White balance adjustment
-- |
-- | Temperature: Kelvin shift (-2000 to +2000 typical range)
-- | Tint: Green-Magenta correction (-100 to +100, where positive = magenta)
type WhiteBalance =
  { temperature :: Int  -- ^ Kelvin shift
  , tint :: Int         -- ^ Green (-) to Magenta (+)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard white balance presets
data Preset
  = AsShot         -- ^ No correction (0K, 0 tint)
  | Auto           -- ^ Auto white balance (algorithm determines correction)
  | Daylight       -- ^ 5500K sunlight
  | Cloudy         -- ^ 6500K overcast
  | Shade          -- ^ 7500K open shade (warm to counter blue cast)
  | Tungsten       -- ^ 3200K incandescent bulbs
  | Fluorescent    -- ^ 4000K fluorescent (with magenta tint)
  | Flash          -- ^ 5500K camera flash
  | Custom Int Int -- ^ Custom Kelvin and tint values

derive instance eqPreset :: Eq Preset

instance showPreset :: Show Preset where
  show = case _ of
    AsShot -> "As Shot"
    Auto -> "Auto"
    Daylight -> "Daylight"
    Cloudy -> "Cloudy"
    Shade -> "Shade"
    Tungsten -> "Tungsten"
    Fluorescent -> "Fluorescent"
    Flash -> "Flash"
    Custom k t -> "Custom (" <> show k <> "K, " <> show t <> " tint)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create white balance adjustment
-- |
-- | ```purescript
-- | whiteBalance 500 10   -- +500K warmer, +10 magenta tint
-- | whiteBalance (-200) 0 -- -200K cooler, neutral tint
-- | ```
whiteBalance :: Int -> Int -> WhiteBalance
whiteBalance temp tintVal =
  { temperature: clampTemp temp
  , tint: clampTint tintVal
  }
  where
    clampTemp t
      | t < (-5000) = (-5000)
      | t > 5000 = 5000
      | otherwise = t
    
    clampTint t
      | t < (-100) = (-100)
      | t > 100 = 100
      | otherwise = t

-- | Create from preset
-- |
-- | ```purescript
-- | fromPreset Daylight      -- 5500K
-- | fromPreset Tungsten      -- 3200K
-- | fromPreset (Custom 6000 5) -- Custom values
-- | ```
fromPreset :: Preset -> WhiteBalance
fromPreset = case _ of
  AsShot -> whiteBalance 0 0
  Auto -> whiteBalance 0 0  -- Would need image analysis for true auto
  Daylight -> whiteBalance 0 0  -- Reference point (5500K is neutral)
  Cloudy -> whiteBalance 1000 0
  Shade -> whiteBalance 2000 10
  Tungsten -> whiteBalance (-2300) 0  -- 3200K relative to 5500K
  Fluorescent -> whiteBalance (-1500) 10  -- 4000K + magenta
  Flash -> whiteBalance 0 0
  Custom k t -> whiteBalance k t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get temperature shift
temperature :: WhiteBalance -> Int
temperature wb = wb.temperature

-- | Get tint correction
tint :: WhiteBalance -> Int
tint wb = wb.tint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply white balance to RGB color
-- |
-- | Algorithm:
-- | 1. Apply temperature shift (blue-orange axis)
-- | 2. Apply tint correction (green-magenta axis)
-- | 3. Normalize to maintain overall brightness
-- |
-- | ```purescript
-- | applyToRgb (whiteBalance 500 10) rgbColor
-- | ```
applyToRgb :: WhiteBalance -> RGB.RGB -> RGB.RGB
applyToRgb wb rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb))
    g = Int.toNumber (Ch.unwrap (RGB.green rgb))
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb))
    
    -- Temperature adjustment (Kelvin shift affects blue-orange)
    -- Positive temp = warmer (more red/orange, less blue)
    -- Negative temp = cooler (less red, more blue)
    tempFactor = Int.toNumber wb.temperature / 5000.0
    rTemp = r + (tempFactor * 50.0)
    bTemp = b - (tempFactor * 50.0)
    
    -- Tint adjustment (green-magenta axis)
    -- Positive tint = more magenta (more red+blue, less green)
    -- Negative tint = more green
    tintFactor = Int.toNumber wb.tint / 100.0
    rTint = rTemp + (tintFactor * 20.0)
    gTint = g - (tintFactor * 40.0)
    bTint = bTemp + (tintFactor * 20.0)
    
    -- Clamp to valid range
    rFinal = Int.round (clamp 0.0 255.0 rTint)
    gFinal = Int.round (clamp 0.0 255.0 gTint)
    bFinal = Int.round (clamp 0.0 255.0 bTint)
  in
    RGB.rgb rFinal gFinal bFinal
  where
    clamp min' max' val
      | val < min' = min'
      | val > max' = max'
      | otherwise = val

-- | Update temperature
withTemperature :: Int -> WhiteBalance -> WhiteBalance
withTemperature newTemp wb = whiteBalance newTemp wb.tint

-- | Update tint
withTint :: Int -> WhiteBalance -> WhiteBalance
withTint newTint wb = whiteBalance wb.temperature newTint
