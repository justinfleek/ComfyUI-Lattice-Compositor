-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // color // lift-gamma-gain
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Three-Way Color Correction (Lift/Gamma/Gain).
-- |
-- | **PROFESSIONAL COLOR GRADING STANDARD:**
-- | The three-way color corrector is the primary tool in every colorist's
-- | arsenal. It separates tonal control into three zones:
-- |
-- | **Lift (Shadows):**
-- | Affects the darkest parts of the image. Lifting blacks makes shadows
-- | milky/washed out. Lowering crushes detail in shadows.
-- |
-- | **Gamma (Midtones):**
-- | Affects the middle tonal range without touching blacks or whites.
-- | Most powerful for overall image brightness and color shifts.
-- |
-- | **Gain (Highlights):**
-- | Affects the brightest parts of the image. Adjusting gain changes
-- | the "ceiling" of your image - where whites live.
-- |
-- | **Why Three-Way?**
-- | - Intuitive mapping to visual perception
-- | - Non-destructive with clear zone separation
-- | - Industry standard (DaVinci, Baselight, Premiere, FCP)

module Hydrogen.Schema.Color.LiftGammaGain
  ( -- * Types
    LiftGammaGain
  , Lift
  , Gamma
  , Gain
  , ColorWheel
  
  -- * Atom Constructors
  , lift
  , gamma
  , gain
  , colorWheel
  
  -- * Atom Unwrappers
  , unwrapLift
  , unwrapGamma
  , unwrapGain
  , colorWheelToRecord
  
  -- * Three-Way Operations
  , liftGammaGain
  , lggIdentity
  , lggFromWheels
  , applyLGG
  
  -- * Accessors
  , getLift
  , getGamma
  , getGain
  , lggToRecord
  
  -- * Manipulation
  , combineLGG
  , scaleLGG
  , resetLift
  , resetGamma
  , resetGain
  
  -- * Presets
  , lggFilmLook
  , lggBleachBypass
  , lggTeal
  , lggOrange
  , lggCrossPro
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // atoms - lgg values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lift value - affects shadows (-1.0 to 1.0)
-- |
-- | - Negative: Crushes blacks (adds density)
-- | - Zero: Neutral
-- | - Positive: Lifts blacks (adds milkiness)
newtype Lift = Lift Number

derive instance eqLift :: Eq Lift

instance showLift :: Show Lift where
  show (Lift n) = "Lift " <> show n

-- | Create lift value (clamped -1.0 to 1.0)
lift :: Number -> Lift
lift n = Lift (Bounded.clampNumber (-1.0) 1.0 n)

-- | Extract raw value
unwrapLift :: Lift -> Number
unwrapLift (Lift n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Gamma value - affects midtones (0.1 to 4.0)
-- |
-- | - < 1.0: Darkens midtones
-- | - 1.0: Neutral
-- | - > 1.0: Brightens midtones
newtype Gamma = Gamma Number

derive instance eqGamma :: Eq Gamma

instance showGamma :: Show Gamma where
  show (Gamma n) = "Gamma " <> show n

-- | Create gamma value (clamped 0.1 to 4.0)
gamma :: Number -> Gamma
gamma n = Gamma (Bounded.clampNumber 0.1 4.0 n)

-- | Extract raw value
unwrapGamma :: Gamma -> Number
unwrapGamma (Gamma n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Gain value - affects highlights (0.0 to 4.0)
-- |
-- | - < 1.0: Reduces highlight intensity
-- | - 1.0: Neutral
-- | - > 1.0: Boosts highlights
newtype Gain = Gain Number

derive instance eqGain :: Eq Gain

instance showGain :: Show Gain where
  show (Gain n) = "Gain " <> show n

-- | Create gain value (clamped 0.0 to 4.0)
gain :: Number -> Gain
gain n = Gain (Bounded.clampNumber 0.0 4.0 n)

-- | Extract raw value
unwrapGain :: Gain -> Number
unwrapGain (Gain n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // molecule - color wheel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color Wheel - RGB adjustment for a tonal zone
-- |
-- | Each zone (lift/gamma/gain) can have independent RGB adjustments.
-- | The wheel represents the color bias applied to that zone.
newtype ColorWheel = ColorWheel
  { r :: Number  -- ^ Red adjustment (-1.0 to 1.0)
  , g :: Number  -- ^ Green adjustment (-1.0 to 1.0)
  , b :: Number  -- ^ Blue adjustment (-1.0 to 1.0)
  , master :: Number  -- ^ Master adjustment (zone-specific range)
  }

derive instance eqColorWheel :: Eq ColorWheel

instance showColorWheel :: Show ColorWheel where
  show (ColorWheel w) = "Wheel(" <> show w.r <> ", " <> show w.g <> ", " <> show w.b <> " @" <> show w.master <> ")"

-- | Create color wheel (RGB clamped -1 to 1, master clamped appropriately)
colorWheel :: Number -> Number -> Number -> Number -> ColorWheel
colorWheel r g b master = ColorWheel
  { r: Bounded.clampNumber (-1.0) 1.0 r
  , g: Bounded.clampNumber (-1.0) 1.0 g
  , b: Bounded.clampNumber (-1.0) 1.0 b
  , master
  }

-- | Convert color wheel to record
colorWheelToRecord :: ColorWheel -> { r :: Number, g :: Number, b :: Number, master :: Number }
colorWheelToRecord (ColorWheel w) = w

-- | Neutral color wheel (no adjustment)
neutralWheel :: Number -> ColorWheel
neutralWheel master = ColorWheel { r: 0.0, g: 0.0, b: 0.0, master }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // compound - lift gamma gain
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Three-Way Color Corrector
-- |
-- | Combines Lift (shadows), Gamma (midtones), and Gain (highlights)
-- | each with their own color wheel and master adjustment.
newtype LiftGammaGain = LiftGammaGain
  { liftWheel :: ColorWheel     -- ^ Shadow color adjustment
  , gammaWheel :: ColorWheel    -- ^ Midtone color adjustment
  , gainWheel :: ColorWheel     -- ^ Highlight color adjustment
  }

derive instance eqLiftGammaGain :: Eq LiftGammaGain

instance showLiftGammaGain :: Show LiftGammaGain where
  show (LiftGammaGain lgg) = "LiftGammaGain[L:" <> show lgg.liftWheel 
    <> " G:" <> show lgg.gammaWheel 
    <> " G:" <> show lgg.gainWheel <> "]"

-- | Create LiftGammaGain with explicit values
-- |
-- | Parameters: lift RGB + master, gamma RGB + master, gain RGB + master
liftGammaGain 
  :: Number -> Number -> Number -> Number  -- ^ Lift R, G, B, master
  -> Number -> Number -> Number -> Number  -- ^ Gamma R, G, B, master
  -> Number -> Number -> Number -> Number  -- ^ Gain R, G, B, master
  -> LiftGammaGain
liftGammaGain lr lg lb lm gr gg gb gm hr hg hb hm = LiftGammaGain
  { liftWheel: colorWheel lr lg lb (Bounded.clampNumber (-1.0) 1.0 lm)
  , gammaWheel: colorWheel gr gg gb (Bounded.clampNumber 0.1 4.0 gm)
  , gainWheel: colorWheel hr hg hb (Bounded.clampNumber 0.0 4.0 hm)
  }

-- | Identity LiftGammaGain (no change)
lggIdentity :: LiftGammaGain
lggIdentity = LiftGammaGain
  { liftWheel: neutralWheel 0.0   -- Lift master: 0 = no lift
  , gammaWheel: neutralWheel 1.0  -- Gamma master: 1 = linear
  , gainWheel: neutralWheel 1.0   -- Gain master: 1 = unity gain
  }

-- | Create LiftGammaGain from color wheels
lggFromWheels :: ColorWheel -> ColorWheel -> ColorWheel -> LiftGammaGain
lggFromWheels liftW gammaW gainW = LiftGammaGain
  { liftWheel: liftW
  , gammaWheel: gammaW
  , gainWheel: gainW
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lgg application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply LiftGammaGain to RGB values
-- |
-- | The formula applies each zone with appropriate weighting:
-- | 1. Gain is applied first (multiplier)
-- | 2. Gamma is applied (power function)
-- | 3. Lift is applied last (offset)
-- |
-- | Color wheels shift the RGB balance within each zone.
applyLGG :: LiftGammaGain -> { r :: Number, g :: Number, b :: Number } -> { r :: Number, g :: Number, b :: Number }
applyLGG (LiftGammaGain lgg) color =
  let 
    -- Extract wheel values
    ColorWheel lw = lgg.liftWheel
    ColorWheel gw = lgg.gammaWheel
    ColorWheel hw = lgg.gainWheel
    
    -- Calculate per-channel adjustments
    -- Gain (multiply)
    gainR = hw.master + hw.r
    gainG = hw.master + hw.g
    gainB = hw.master + hw.b
    
    -- Gamma (power) - convert from visual gamma to power
    -- Visual gamma: > 1 brightens, < 1 darkens
    -- Power: < 1 brightens, > 1 darkens
    -- So we use 1/gamma for the power function
    gammaR = 1.0 / (gw.master + gw.r * 0.5)
    gammaG = 1.0 / (gw.master + gw.g * 0.5)
    gammaB = 1.0 / (gw.master + gw.b * 0.5)
    
    -- Lift (add to shadows)
    liftR = lw.master + lw.r
    liftG = lw.master + lw.g
    liftB = lw.master + lw.b
    
    -- Apply gain
    r1 = color.r * gainR
    g1 = color.g * gainG
    b1 = color.b * gainB
    
    -- Apply gamma (ensure non-negative before power)
    r2 = if r1 < 0.0 then 0.0 else Math.pow r1 gammaR
    g2 = if g1 < 0.0 then 0.0 else Math.pow g1 gammaG
    b2 = if b1 < 0.0 then 0.0 else Math.pow b1 gammaB
    
    -- Apply lift
    r3 = r2 + liftR
    g3 = g2 + liftG
    b3 = b2 + liftB
    
  in { r: clamp01 r3
     , g: clamp01 g3
     , b: clamp01 b3
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get lift wheel
getLift :: LiftGammaGain -> ColorWheel
getLift (LiftGammaGain lgg) = lgg.liftWheel

-- | Get gamma wheel
getGamma :: LiftGammaGain -> ColorWheel
getGamma (LiftGammaGain lgg) = lgg.gammaWheel

-- | Get gain wheel
getGain :: LiftGammaGain -> ColorWheel
getGain (LiftGammaGain lgg) = lgg.gainWheel

-- | Convert to record representation
lggToRecord :: LiftGammaGain -> { lift :: { r :: Number, g :: Number, b :: Number, master :: Number }, gamma :: { r :: Number, g :: Number, b :: Number, master :: Number }, gain :: { r :: Number, g :: Number, b :: Number, master :: Number } }
lggToRecord (LiftGammaGain lgg) =
  { lift: colorWheelToRecord lgg.liftWheel
  , gamma: colorWheelToRecord lgg.gammaWheel
  , gain: colorWheelToRecord lgg.gainWheel
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two LiftGammaGain corrections
combineLGG :: LiftGammaGain -> LiftGammaGain -> LiftGammaGain
combineLGG (LiftGammaGain a) (LiftGammaGain b) = LiftGammaGain
  { liftWheel: combineWheels a.liftWheel b.liftWheel
  , gammaWheel: combineWheelsMultiply a.gammaWheel b.gammaWheel
  , gainWheel: combineWheelsMultiply a.gainWheel b.gainWheel
  }
  where
  combineWheels (ColorWheel w1) (ColorWheel w2) = ColorWheel
    { r: Bounded.clampNumber (-1.0) 1.0 (w1.r + w2.r)
    , g: Bounded.clampNumber (-1.0) 1.0 (w1.g + w2.g)
    , b: Bounded.clampNumber (-1.0) 1.0 (w1.b + w2.b)
    , master: w1.master + w2.master
    }
  combineWheelsMultiply (ColorWheel w1) (ColorWheel w2) = ColorWheel
    { r: Bounded.clampNumber (-1.0) 1.0 (w1.r + w2.r)
    , g: Bounded.clampNumber (-1.0) 1.0 (w1.g + w2.g)
    , b: Bounded.clampNumber (-1.0) 1.0 (w1.b + w2.b)
    , master: w1.master * w2.master
    }

-- | Scale LiftGammaGain toward identity
-- |
-- | factor = 0.0: identity (no effect)
-- | factor = 1.0: full effect
scaleLGG :: Number -> LiftGammaGain -> LiftGammaGain
scaleLGG factor (LiftGammaGain lgg) =
  let f = Bounded.clampNumber 0.0 1.0 factor
      scaleWheel neutralMaster (ColorWheel w) = ColorWheel
        { r: w.r * f
        , g: w.g * f
        , b: w.b * f
        , master: neutralMaster + f * (w.master - neutralMaster)
        }
  in LiftGammaGain
    { liftWheel: scaleWheel 0.0 lgg.liftWheel   -- Lift neutral = 0
    , gammaWheel: scaleWheel 1.0 lgg.gammaWheel -- Gamma neutral = 1
    , gainWheel: scaleWheel 1.0 lgg.gainWheel   -- Gain neutral = 1
    }

-- | Reset lift to neutral
resetLift :: LiftGammaGain -> LiftGammaGain
resetLift (LiftGammaGain lgg) = LiftGammaGain lgg
  { liftWheel = neutralWheel 0.0 }

-- | Reset gamma to neutral
resetGamma :: LiftGammaGain -> LiftGammaGain
resetGamma (LiftGammaGain lgg) = LiftGammaGain lgg
  { gammaWheel = neutralWheel 1.0 }

-- | Reset gain to neutral
resetGain :: LiftGammaGain -> LiftGammaGain
resetGain (LiftGammaGain lgg) = LiftGammaGain lgg
  { gainWheel = neutralWheel 1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classic film look - warm shadows, neutral mids, slightly cooled highlights
lggFilmLook :: LiftGammaGain
lggFilmLook = liftGammaGain
  0.05 (-0.02) (-0.03) 0.02    -- Lift: warm shadows
  0.0 0.0 0.0 1.0              -- Gamma: neutral
  (-0.02) 0.0 0.03 1.0         -- Gain: slightly cool highlights

-- | Bleach bypass look - desaturated, high contrast
lggBleachBypass :: LiftGammaGain
lggBleachBypass = liftGammaGain
  0.0 0.0 0.0 (-0.05)          -- Lift: crush blacks
  0.0 0.0 0.0 0.9              -- Gamma: darker mids
  0.0 0.0 0.0 1.2              -- Gain: boost highlights

-- | Teal shadows preset
lggTeal :: LiftGammaGain
lggTeal = liftGammaGain
  (-0.1) 0.05 0.1 0.0          -- Lift: teal shadows
  0.0 0.0 0.0 1.0              -- Gamma: neutral
  0.0 0.0 0.0 1.0              -- Gain: neutral

-- | Orange/warm highlights preset
lggOrange :: LiftGammaGain
lggOrange = liftGammaGain
  0.0 0.0 0.0 0.0              -- Lift: neutral
  0.0 0.0 0.0 1.0              -- Gamma: neutral
  0.1 0.02 (-0.08) 1.0         -- Gain: orange highlights

-- | Cross-processed look
lggCrossPro :: LiftGammaGain
lggCrossPro = liftGammaGain
  0.0 0.1 0.0 0.02             -- Lift: green-tinted shadows
  0.05 (-0.02) 0.0 1.0         -- Gamma: warm mids
  0.0 0.0 0.1 1.1              -- Gain: blue highlights, boosted

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 = Bounded.clampNumber 0.0 1.0
