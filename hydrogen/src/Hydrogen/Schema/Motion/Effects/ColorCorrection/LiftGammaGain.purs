-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--           // hydrogen // schema // motion // effects // color // liftgammagain
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lift/Gamma/Gain — Professional 3-way color corrector.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors the Lumetri Color panel's 3-way color wheels:
-- |
-- | - **Lift**: Adjusts shadows/blacks (adds color to dark regions)
-- | - **Gamma**: Adjusts midtones (adds color to mid-brightness regions)
-- | - **Gain**: Adjusts highlights/whites (adds color to bright regions)
-- |
-- | Each wheel has:
-- | - Color offset (x,y position on color wheel, or RGB values)
-- | - Luminance adjustment (-1.0 to 2.0)
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | lift.r | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | lift.g | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | lift.b | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | lift.luminance | Number | -1.0 | 2.0 | clamps | 0.0 |
-- | | gamma.r | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | gamma.g | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | gamma.b | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | gamma.luminance | Number | -1.0 | 2.0 | clamps | 0.0 |
-- | | gain.r | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | gain.g | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | gain.b | Number | -2.0 | 2.0 | clamps | 0.0 |
-- | | gain.luminance | Number | -1.0 | 2.0 | clamps | 0.0 |
-- |
-- | ## Mathematical Model
-- |
-- | For each color channel:
-- | 1. Apply gain: `color * (1.0 + gain)`
-- | 2. Add lift: `+ lift`
-- | 3. Apply gamma: `pow(result, 1.0 / gamma)`
-- |
-- | Lift affects shadows (dark values) most strongly.
-- | Gain affects highlights (bright values) most strongly.
-- | Gamma affects midtones with smooth rolloff to shadows/highlights.

module Hydrogen.Schema.Motion.Effects.ColorCorrection.LiftGammaGain
  ( -- * Color Wheel
    ColorWheel(..)
  , defaultColorWheel
  , mkColorWheel
  , colorWheelFromRGB
  , colorWheelFromAngleMagnitude
  
  -- * Lift/Gamma/Gain Effect
  , LiftGammaGainEffect(..)
  , defaultLiftGammaGainEffect
  , mkLiftGammaGainEffect
  
  -- * Accessors
  , liftWheel
  , gammaWheel
  , gainWheel
  , wheelRed
  , wheelGreen
  , wheelBlue
  , wheelLuminance
  
  -- * Operations
  , setLift
  , setGamma
  , setGain
  , setWheelRGB
  , setWheelLuminance
  , resetWheel
  , resetEffect
  
  -- * Presets
  , lggWarmShadows
  , lggCoolHighlights
  , lggOrangeTeal
  , lggCinematic
  , lggBleachBypass
  , lggCrossPro
  
  -- * Queries
  , isWheelNeutral
  , isEffectNeutral
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , show
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , compare
  , map
  , pure
  , bind
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color // wheel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color wheel adjustment for shadows, midtones, or highlights.
-- |
-- | Represents a position on a color wheel plus luminance adjustment.
-- | RGB values represent the color offset (-2.0 to 2.0 range).
-- | Luminance adjusts overall brightness (-1.0 to 2.0 range).
type ColorWheel =
  { red :: Number        -- ^ Red offset (-2.0 to 2.0)
  , green :: Number      -- ^ Green offset (-2.0 to 2.0)
  , blue :: Number       -- ^ Blue offset (-2.0 to 2.0)
  , luminance :: Number  -- ^ Luminance adjustment (-1.0 to 2.0)
  }

-- | Default neutral color wheel (no adjustment).
defaultColorWheel :: ColorWheel
defaultColorWheel =
  { red: 0.0
  , green: 0.0
  , blue: 0.0
  , luminance: 0.0
  }

-- | Create a color wheel with clamped values.
mkColorWheel :: Number -> Number -> Number -> Number -> ColorWheel
mkColorWheel r g b lum =
  { red: clampNumber (negate 2.0) 2.0 r
  , green: clampNumber (negate 2.0) 2.0 g
  , blue: clampNumber (negate 2.0) 2.0 b
  , luminance: clampNumber (negate 1.0) 2.0 lum
  }

-- | Create color wheel from RGB values (luminance = 0).
colorWheelFromRGB :: Number -> Number -> Number -> ColorWheel
colorWheelFromRGB r g b = mkColorWheel r g b 0.0

-- | Create color wheel from angle (degrees) and magnitude.
-- |
-- | Angle: 0° = red, 120° = green, 240° = blue
-- | Magnitude: 0.0 = neutral, 1.0 = full saturation
colorWheelFromAngleMagnitude :: Number -> Number -> ColorWheel
colorWheelFromAngleMagnitude angleDeg magnitude =
  let angleRad = Math.degreesToRadians angleDeg
      mag = clampNumber 0.0 2.0 magnitude
      r = mag * Math.cos angleRad
      g = mag * Math.cos (angleRad - Math.degreesToRadians 120.0)
      b = mag * Math.cos (angleRad - Math.degreesToRadians 240.0)
  in mkColorWheel r g b 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // lift gamma gain effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Lift/Gamma/Gain effect with three color wheels.
type LiftGammaGainEffect =
  { lift :: ColorWheel   -- ^ Shadow/black adjustment
  , gamma :: ColorWheel  -- ^ Midtone adjustment
  , gain :: ColorWheel   -- ^ Highlight/white adjustment
  }

-- | Default neutral effect (no color grading).
defaultLiftGammaGainEffect :: LiftGammaGainEffect
defaultLiftGammaGainEffect =
  { lift: defaultColorWheel
  , gamma: defaultColorWheel
  , gain: defaultColorWheel
  }

-- | Create effect from three color wheels.
mkLiftGammaGainEffect :: ColorWheel -> ColorWheel -> ColorWheel -> LiftGammaGainEffect
mkLiftGammaGainEffect liftW gammaW gainW =
  { lift: liftW
  , gamma: gammaW
  , gain: gainW
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get lift (shadows) wheel.
liftWheel :: LiftGammaGainEffect -> ColorWheel
liftWheel effect = effect.lift

-- | Get gamma (midtones) wheel.
gammaWheel :: LiftGammaGainEffect -> ColorWheel
gammaWheel effect = effect.gamma

-- | Get gain (highlights) wheel.
gainWheel :: LiftGammaGainEffect -> ColorWheel
gainWheel effect = effect.gain

-- | Get red component of a color wheel.
wheelRed :: ColorWheel -> Number
wheelRed wheel = wheel.red

-- | Get green component of a color wheel.
wheelGreen :: ColorWheel -> Number
wheelGreen wheel = wheel.green

-- | Get blue component of a color wheel.
wheelBlue :: ColorWheel -> Number
wheelBlue wheel = wheel.blue

-- | Get luminance component of a color wheel.
wheelLuminance :: ColorWheel -> Number
wheelLuminance wheel = wheel.luminance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the lift (shadows) wheel.
setLift :: ColorWheel -> LiftGammaGainEffect -> LiftGammaGainEffect
setLift wheel effect = effect { lift = wheel }

-- | Set the gamma (midtones) wheel.
setGamma :: ColorWheel -> LiftGammaGainEffect -> LiftGammaGainEffect
setGamma wheel effect = effect { gamma = wheel }

-- | Set the gain (highlights) wheel.
setGain :: ColorWheel -> LiftGammaGainEffect -> LiftGammaGainEffect
setGain wheel effect = effect { gain = wheel }

-- | Set RGB values on a color wheel.
setWheelRGB :: Number -> Number -> Number -> ColorWheel -> ColorWheel
setWheelRGB r g b wheel =
  { red: clampNumber (negate 2.0) 2.0 r
  , green: clampNumber (negate 2.0) 2.0 g
  , blue: clampNumber (negate 2.0) 2.0 b
  , luminance: wheel.luminance
  }

-- | Set luminance on a color wheel.
setWheelLuminance :: Number -> ColorWheel -> ColorWheel
setWheelLuminance lum wheel = wheel { luminance = clampNumber (negate 1.0) 2.0 lum }

-- | Reset a color wheel to neutral.
resetWheel :: ColorWheel -> ColorWheel
resetWheel _ = defaultColorWheel

-- | Reset entire effect to neutral.
resetEffect :: LiftGammaGainEffect -> LiftGammaGainEffect
resetEffect _ = defaultLiftGammaGainEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warm shadows preset — adds warmth to dark areas.
lggWarmShadows :: LiftGammaGainEffect
lggWarmShadows =
  { lift: mkColorWheel 0.05 0.02 (negate 0.03) 0.0
  , gamma: defaultColorWheel
  , gain: defaultColorWheel
  }

-- | Cool highlights preset — adds cool tones to bright areas.
lggCoolHighlights :: LiftGammaGainEffect
lggCoolHighlights =
  { lift: defaultColorWheel
  , gamma: defaultColorWheel
  , gain: mkColorWheel (negate 0.03) 0.0 0.05 0.0
  }

-- | Orange and teal look — popular cinematic grade.
lggOrangeTeal :: LiftGammaGainEffect
lggOrangeTeal =
  { lift: mkColorWheel (negate 0.05) 0.02 0.08 0.0      -- Teal shadows
  , gamma: mkColorWheel 0.02 0.01 (negate 0.02) 0.0    -- Slight warmth in mids
  , gain: mkColorWheel 0.08 0.04 (negate 0.05) 0.0     -- Orange highlights
  }

-- | Cinematic preset — crushed blacks, warm highlights.
lggCinematic :: LiftGammaGainEffect
lggCinematic =
  { lift: mkColorWheel 0.02 0.01 0.03 0.05             -- Lifted blacks with slight blue
  , gamma: mkColorWheel 0.01 0.0 (negate 0.01) 0.0     -- Neutral mids
  , gain: mkColorWheel 0.05 0.03 (negate 0.02) (negate 0.05)  -- Warm, slightly reduced highlights
  }

-- | Bleach bypass look — desaturated, high contrast.
lggBleachBypass :: LiftGammaGainEffect
lggBleachBypass =
  { lift: mkColorWheel 0.0 0.0 0.0 0.1                 -- Lifted blacks
  , gamma: mkColorWheel 0.0 0.0 0.0 (negate 0.1)       -- Darker mids
  , gain: mkColorWheel 0.0 0.0 0.0 0.15                -- Pushed highlights
  }

-- | Cross-processing look — shifted colors.
lggCrossPro :: LiftGammaGainEffect
lggCrossPro =
  { lift: mkColorWheel (negate 0.08) 0.04 0.1 0.0      -- Cyan/green shadows
  , gamma: mkColorWheel 0.05 0.02 (negate 0.03) 0.0    -- Warm mids
  , gain: mkColorWheel 0.1 0.05 (negate 0.08) 0.0      -- Yellow/orange highlights
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a color wheel is neutral (no adjustment).
isWheelNeutral :: ColorWheel -> Boolean
isWheelNeutral wheel =
  wheel.red == 0.0 &&
  wheel.green == 0.0 &&
  wheel.blue == 0.0 &&
  wheel.luminance == 0.0

-- | Check if entire effect is neutral.
isEffectNeutral :: LiftGammaGainEffect -> Boolean
isEffectNeutral effect =
  isWheelNeutral effect.lift &&
  isWheelNeutral effect.gamma &&
  isWheelNeutral effect.gain
