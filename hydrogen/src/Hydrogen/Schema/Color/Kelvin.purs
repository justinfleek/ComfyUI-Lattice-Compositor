-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // color // kelvin
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kelvin - color temperature of light sources.
-- |
-- | Measured in degrees Kelvin from 1000 to 40000:
-- | - **1,800K**: Candlelight (warm orange)
-- | - **2,700K**: Tungsten/incandescent bulbs (warm white)
-- | - **3,000K**: Warm white LED
-- | - **4,000K**: Neutral white
-- | - **5,500K**: Daylight (reference white, "D55")
-- | - **6,500K**: Cool white (standard daylight, "D65")
-- | - **7,000K**: Overcast sky
-- | - **10,000K+**: Blue sky, deep shade
-- |
-- | ## Physical Basis
-- |
-- | Color temperature describes the spectrum of light emitted by a blackbody
-- | radiator at that temperature. Lower temperatures produce warmer (redder)
-- | light, higher temperatures produce cooler (bluer) light.
-- |
-- | ## Use Cases
-- |
-- | - Light source definitions for glows, buttons, ambient lighting
-- | - White balance for photo/video rendering in LATTICE
-- | - Accurate color preview ("how will this look under tungsten vs daylight?")
-- | - Color grading (film look = warmer temps, clinical = cooler temps)

module Hydrogen.Schema.Color.Kelvin
  ( Kelvin
  , kelvin
  , unsafeKelvin
  , unwrap
  , scale
  , shift
  , bounds
  , toNumber
  , isWarm
  , isNeutral
  , isCool
  , isCandlelight
  , isTungsten
  , isDaylight
  , kelvinToRgb
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (<>)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // kelvin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color temperature in Kelvin (1000-40000)
-- |
-- | Represents the color of light emitted by a blackbody radiator at this
-- | temperature. Used for lighting design, white balance, and color grading.
newtype Kelvin = Kelvin Int

derive instance eqKelvin :: Eq Kelvin
derive instance ordKelvin :: Ord Kelvin

instance showKelvin :: Show Kelvin where
  show (Kelvin k) = show k <> "K"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a kelvin value, clamping to 1000-40000
-- |
-- | Values below 1000K (infrared) or above 40000K (UV) are clamped to valid range.
kelvin :: Int -> Kelvin
kelvin n = Kelvin (Bounded.clampInt 1000 40000 n)

-- | Create a kelvin value without clamping
-- |
-- | Use only when you know the value is valid (1000-40000).
unsafeKelvin :: Int -> Kelvin
unsafeKelvin = Kelvin

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale kelvin by a factor
-- |
-- | Useful for relative adjustments:
-- | ```purescript
-- | scale 1.2 (kelvin 5000)  -- Slightly cooler
-- | scale 0.8 (kelvin 5000)  -- Slightly warmer
-- | ```
scale :: Number -> Kelvin -> Kelvin
scale factor (Kelvin k) = 
  kelvin (Int.round (Int.toNumber k * factor))

-- | Shift kelvin by an amount
-- |
-- | ```purescript
-- | shift 500 (kelvin 5000)   -- 5500K (cooler)
-- | shift (-500) (kelvin 5000) -- 4500K (warmer)
-- | ```
shift :: Int -> Kelvin -> Kelvin
shift amount (Kelvin k) = kelvin (k + amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if warm temperature (< 3500K)
-- |
-- | Warm temperatures: candlelight, tungsten, warm white LEDs
isWarm :: Kelvin -> Boolean
isWarm (Kelvin k) = k < 3500

-- | Check if neutral temperature (3500K - 5000K)
-- |
-- | Neutral temperatures: neutral white LEDs, early morning/late afternoon sun
isNeutral :: Kelvin -> Boolean
isNeutral (Kelvin k) = k >= 3500 && k <= 5000

-- | Check if cool temperature (> 5000K)
-- |
-- | Cool temperatures: daylight, overcast sky, blue sky
isCool :: Kelvin -> Boolean
isCool (Kelvin k) = k > 5000

-- | Check if candlelight range (< 2000K)
isCandlelight :: Kelvin -> Boolean
isCandlelight (Kelvin k) = k < 2000

-- | Check if tungsten/incandescent range (2500K - 3000K)
isTungsten :: Kelvin -> Boolean
isTungsten (Kelvin k) = k >= 2500 && k <= 3000

-- | Check if daylight range (5000K - 6500K)
isDaylight :: Kelvin -> Boolean
isDaylight (Kelvin k) = k >= 5000 && k <= 6500

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Kelvin -> Int
unwrap (Kelvin k) = k

-- | Convert to Number for calculations
toNumber :: Kelvin -> Number
toNumber (Kelvin k) = Int.toNumber k

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 1000 40000 "kelvin" "Color temperature in degrees Kelvin"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert color temperature to approximate RGB value.
-- |
-- | This uses Tanner Helland's approximation algorithm, which is reasonably
-- | accurate for typical lighting ranges (1000K - 40000K).
-- |
-- | Note: This is an approximation of blackbody radiation. For precise color
-- | rendering, use CIE illuminants and chromatic adaptation transforms.
-- |
-- | ```purescript
-- | kelvinToRgb (kelvin 2700)  -- Warm tungsten white
-- | kelvinToRgb (kelvin 6500)  -- Cool daylight white
-- | ```
kelvinToRgb :: Kelvin -> RGB.RGB
kelvinToRgb (Kelvin temp) =
  let
    -- Normalize to 0-100 scale (divide by 100)
    t = Int.toNumber temp / 100.0
    
    -- Calculate red
    r = if t <= 66.0
      then 255.0
      else Math.clamp 0.0 255.0 (329.698727446 * Math.pow (t - 60.0) (-0.1332047592))
    
    -- Calculate green
    g = if t <= 66.0
      then Math.clamp 0.0 255.0 (99.4708025861 * Math.log t - 161.1195681661)
      else Math.clamp 0.0 255.0 (288.1221695283 * Math.pow (t - 60.0) (-0.0755148492))
    
    -- Calculate blue
    b = if t >= 66.0
      then 255.0
      else if t <= 19.0
        then 0.0
        else Math.clamp 0.0 255.0 (138.5177312231 * Math.log (t - 10.0) - 305.0447927307)
  in
    RGB.rgb (Int.round r) (Int.round g) (Int.round b)
