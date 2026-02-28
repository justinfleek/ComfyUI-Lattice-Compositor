-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // cdl
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ASC Color Decision List (CDL) for Professional Color Grading.
-- |
-- | **INDUSTRY STANDARD COLOR CORRECTION:**
-- | CDL is the American Society of Cinematographers' standard for
-- | communicating color correction information between software.
-- |
-- | **The CDL Formula:**
-- | ```
-- | out = (in × slope + offset) ^ power
-- | ```
-- |
-- | **Components:**
-- | - `Slope` - Multiplier (gain/contrast) per channel
-- | - `Offset` - Addition (lift/brightness) per channel
-- | - `Power` - Exponent (gamma) per channel
-- | - `Saturation` - Global saturation multiplier
-- |
-- | **Why CDL?**
-- | - Universal exchange between DaVinci, Baselight, Mistika, etc.
-- | - Mathematically invertible
-- | - Non-destructive metadata
-- | - Shot-by-shot corrections in EDL/XML workflows

module Hydrogen.Schema.Color.CDL
  ( -- * CDL Types
    CDL
  , Slope
  , Offset
  , Power
  , Saturation
  , SOP
  , SOPSat
  
  -- * Atom Constructors
  , slope
  , offset
  , power
  , saturation
  
  -- * Atom Unwrappers
  , unwrapSlope
  , unwrapOffset
  , unwrapPower
  , unwrapSaturation
  
  -- * CDL Operations
  , cdl
  , cdlIdentity
  , cdlFromSOP
  , cdlFromSOPSat
  , applyCDL
  , applyCDLLinear
  
  -- * SOP Accessors
  , getSlope
  , getOffset
  , getPower
  , getSaturation
  , sopToRecord
  , cdlToRecord
  
  -- * CDL Manipulation
  , combineCDL
  , invertCDL
  , scaleCDL
  , resetSlope
  , resetOffset
  , resetPower
  , resetSaturation
  
  -- * Presets
  , cdlWarmUp
  , cdlCoolDown
  , cdlLowContrast
  , cdlHighContrast
  , cdlDesaturate
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
  , (==)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // atoms - cdl parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slope (multiplier) - 0.0 to 4.0
-- |
-- | The slope multiplies the input value. A slope of 1.0 is neutral.
-- | - < 1.0: Reduces intensity
-- | - > 1.0: Increases intensity (contrast)
-- | Range is 0.0-4.0 per ASC CDL specification.
newtype Slope = Slope Number

derive instance eqSlope :: Eq Slope

instance showSlope :: Show Slope where
  show (Slope n) = "Slope " <> show n

-- | Create slope value (clamped 0.0-4.0)
slope :: Number -> Slope
slope n = Slope (Bounded.clampNumber 0.0 4.0 n)

-- | Extract raw value
unwrapSlope :: Slope -> Number
unwrapSlope (Slope n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Offset (addition) - -1.0 to 1.0
-- |
-- | The offset is added after slope multiplication. An offset of 0.0 is neutral.
-- | - < 0.0: Darkens image (lifts blacks)
-- | - > 0.0: Brightens image (lifts blacks)
newtype Offset = Offset Number

derive instance eqOffset :: Eq Offset

instance showOffset :: Show Offset where
  show (Offset n) = "Offset " <> show n

-- | Create offset value (clamped -1.0 to 1.0)
offset :: Number -> Offset
offset n = Offset (Bounded.clampNumber (-1.0) 1.0 n)

-- | Extract raw value
unwrapOffset :: Offset -> Number
unwrapOffset (Offset n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Power (exponent) - 0.1 to 4.0
-- |
-- | The power raises the result to this exponent. A power of 1.0 is neutral.
-- | - < 1.0: Lifts midtones (gamma up)
-- | - > 1.0: Darkens midtones (gamma down)
newtype Power = Power Number

derive instance eqPower :: Eq Power

instance showPower :: Show Power where
  show (Power n) = "Power " <> show n

-- | Create power value (clamped 0.1-4.0)
power :: Number -> Power
power n = Power (Bounded.clampNumber 0.1 4.0 n)

-- | Extract raw value
unwrapPower :: Power -> Number
unwrapPower (Power n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Saturation (global multiplier) - 0.0 to 4.0
-- |
-- | Applied after SOP, multiplies color saturation. 1.0 is neutral.
-- | - 0.0: Monochrome
-- | - 1.0: Normal saturation
-- | - > 1.0: Increased saturation
newtype Saturation = Saturation Number

derive instance eqSaturation :: Eq Saturation

instance showSaturation :: Show Saturation where
  show (Saturation n) = "Saturation " <> show n

-- | Create saturation value (clamped 0.0-4.0)
saturation :: Number -> Saturation
saturation n = Saturation (Bounded.clampNumber 0.0 4.0 n)

-- | Extract raw value
unwrapSaturation :: Saturation -> Number
unwrapSaturation (Saturation n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // molecules - sop and sopsat
-- ═════════════════════════════════════════════════════════════════════════════

-- | SOP - Slope, Offset, Power per RGB channel
-- |
-- | The core CDL correction without saturation.
type SOP =
  { slopeR :: Slope
  , slopeG :: Slope
  , slopeB :: Slope
  , offsetR :: Offset
  , offsetG :: Offset
  , offsetB :: Offset
  , powerR :: Power
  , powerG :: Power
  , powerB :: Power
  }

-- | SOPSat - SOP with Saturation
-- |
-- | Complete CDL specification including saturation.
type SOPSat =
  { sop :: SOP
  , saturation :: Saturation
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // compound - color decision list
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete ASC CDL specification
-- |
-- | Contains:
-- | - Per-channel Slope, Offset, Power (SOP)
-- | - Global Saturation
-- | - Metadata for workflow integration
newtype CDL = CDL
  { sopSat :: SOPSat
  , id :: String           -- ^ Unique identifier for shot matching
  , description :: String  -- ^ Human-readable description
  }

derive instance eqCDL :: Eq CDL

instance showCDL :: Show CDL where
  show (CDL c) = "CDL[" <> c.id <> "]"

-- | Create CDL with explicit values
cdl 
  :: Number -> Number -> Number  -- ^ Slope RGB
  -> Number -> Number -> Number  -- ^ Offset RGB
  -> Number -> Number -> Number  -- ^ Power RGB
  -> Number                      -- ^ Saturation
  -> String                      -- ^ ID
  -> CDL
cdl sr sg sb or_ og ob pr pg pb sat id_ = CDL
  { sopSat:
      { sop:
          { slopeR: slope sr
          , slopeG: slope sg
          , slopeB: slope sb
          , offsetR: offset or_
          , offsetG: offset og
          , offsetB: offset ob
          , powerR: power pr
          , powerG: power pg
          , powerB: power pb
          }
      , saturation: saturation sat
      }
  , id: id_
  , description: ""
  }

-- | Identity CDL (no change)
cdlIdentity :: CDL
cdlIdentity = cdl 1.0 1.0 1.0  0.0 0.0 0.0  1.0 1.0 1.0  1.0 "identity"

-- | Create CDL from SOP record
cdlFromSOP :: SOP -> CDL
cdlFromSOP sop = CDL
  { sopSat: { sop, saturation: saturation 1.0 }
  , id: "from-sop"
  , description: ""
  }

-- | Create CDL from SOPSat record
cdlFromSOPSat :: SOPSat -> CDL
cdlFromSOPSat sopSat = CDL
  { sopSat
  , id: "from-sopsat"
  , description: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cdl application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply CDL to linear RGB values (0.0-1.0)
-- |
-- | Formula: out = (in × slope + offset) ^ power
-- | Then saturation is applied.
applyCDL :: CDL -> { r :: Number, g :: Number, b :: Number } -> { r :: Number, g :: Number, b :: Number }
applyCDL (CDL c) color =
  let sop = c.sopSat.sop
      sat = unwrapSaturation c.sopSat.saturation
      
      -- Apply SOP to each channel
      r' = applySOPChannel (unwrapSlope sop.slopeR) (unwrapOffset sop.offsetR) (unwrapPower sop.powerR) color.r
      g' = applySOPChannel (unwrapSlope sop.slopeG) (unwrapOffset sop.offsetG) (unwrapPower sop.powerG) color.g
      b' = applySOPChannel (unwrapSlope sop.slopeB) (unwrapOffset sop.offsetB) (unwrapPower sop.powerB) color.b
      
      -- Calculate luma for saturation adjustment (Rec.709 weights)
      luma = 0.2126 * r' + 0.7152 * g' + 0.0722 * b'
      
      -- Apply saturation
      rFinal = luma + sat * (r' - luma)
      gFinal = luma + sat * (g' - luma)
      bFinal = luma + sat * (b' - luma)
      
  in { r: clamp01 rFinal
     , g: clamp01 gFinal
     , b: clamp01 bFinal
     }

-- | Apply CDL to linear values, returning linear (no clamping for HDR)
applyCDLLinear :: CDL -> { r :: Number, g :: Number, b :: Number } -> { r :: Number, g :: Number, b :: Number }
applyCDLLinear (CDL c) color =
  let sop = c.sopSat.sop
      sat = unwrapSaturation c.sopSat.saturation
      
      r' = applySOPChannel (unwrapSlope sop.slopeR) (unwrapOffset sop.offsetR) (unwrapPower sop.powerR) color.r
      g' = applySOPChannel (unwrapSlope sop.slopeG) (unwrapOffset sop.offsetG) (unwrapPower sop.powerG) color.g
      b' = applySOPChannel (unwrapSlope sop.slopeB) (unwrapOffset sop.offsetB) (unwrapPower sop.powerB) color.b
      
      luma = 0.2126 * r' + 0.7152 * g' + 0.0722 * b'
      
  in { r: luma + sat * (r' - luma)
     , g: luma + sat * (g' - luma)
     , b: luma + sat * (b' - luma)
     }

-- | Apply SOP to single channel
applySOPChannel :: Number -> Number -> Number -> Number -> Number
applySOPChannel s o p input =
  let linear = input * s + o
      -- Ensure non-negative before power (negative ^ fractional = NaN)
      safeLinear = if linear < 0.0 then 0.0 else linear
  in Math.pow safeLinear p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get slope values as record
getSlope :: CDL -> { r :: Number, g :: Number, b :: Number }
getSlope (CDL c) =
  { r: unwrapSlope c.sopSat.sop.slopeR
  , g: unwrapSlope c.sopSat.sop.slopeG
  , b: unwrapSlope c.sopSat.sop.slopeB
  }

-- | Get offset values as record
getOffset :: CDL -> { r :: Number, g :: Number, b :: Number }
getOffset (CDL c) =
  { r: unwrapOffset c.sopSat.sop.offsetR
  , g: unwrapOffset c.sopSat.sop.offsetG
  , b: unwrapOffset c.sopSat.sop.offsetB
  }

-- | Get power values as record
getPower :: CDL -> { r :: Number, g :: Number, b :: Number }
getPower (CDL c) =
  { r: unwrapPower c.sopSat.sop.powerR
  , g: unwrapPower c.sopSat.sop.powerG
  , b: unwrapPower c.sopSat.sop.powerB
  }

-- | Get saturation value
getSaturation :: CDL -> Number
getSaturation (CDL c) = unwrapSaturation c.sopSat.saturation

-- | Convert SOP to record
sopToRecord :: SOP -> { slope :: { r :: Number, g :: Number, b :: Number }, offset :: { r :: Number, g :: Number, b :: Number }, power :: { r :: Number, g :: Number, b :: Number } }
sopToRecord sop =
  { slope: { r: unwrapSlope sop.slopeR, g: unwrapSlope sop.slopeG, b: unwrapSlope sop.slopeB }
  , offset: { r: unwrapOffset sop.offsetR, g: unwrapOffset sop.offsetG, b: unwrapOffset sop.offsetB }
  , power: { r: unwrapPower sop.powerR, g: unwrapPower sop.powerG, b: unwrapPower sop.powerB }
  }

-- | Convert CDL to full record
cdlToRecord :: CDL -> { slope :: { r :: Number, g :: Number, b :: Number }, offset :: { r :: Number, g :: Number, b :: Number }, power :: { r :: Number, g :: Number, b :: Number }, saturation :: Number, id :: String }
cdlToRecord (CDL c) =
  { slope: { r: unwrapSlope c.sopSat.sop.slopeR, g: unwrapSlope c.sopSat.sop.slopeG, b: unwrapSlope c.sopSat.sop.slopeB }
  , offset: { r: unwrapOffset c.sopSat.sop.offsetR, g: unwrapOffset c.sopSat.sop.offsetG, b: unwrapOffset c.sopSat.sop.offsetB }
  , power: { r: unwrapPower c.sopSat.sop.powerR, g: unwrapPower c.sopSat.sop.powerG, b: unwrapPower c.sopSat.sop.powerB }
  , saturation: unwrapSaturation c.sopSat.saturation
  , id: c.id
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cdl manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two CDLs (apply first, then second)
-- |
-- | Note: This is an approximation. True CDL composition is complex
-- | because power operations don't distribute.
combineCDL :: CDL -> CDL -> CDL
combineCDL (CDL a) (CDL b) = CDL
  { sopSat:
      { sop:
          { slopeR: slope (unwrapSlope a.sopSat.sop.slopeR * unwrapSlope b.sopSat.sop.slopeR)
          , slopeG: slope (unwrapSlope a.sopSat.sop.slopeG * unwrapSlope b.sopSat.sop.slopeG)
          , slopeB: slope (unwrapSlope a.sopSat.sop.slopeB * unwrapSlope b.sopSat.sop.slopeB)
          , offsetR: offset (unwrapOffset a.sopSat.sop.offsetR + unwrapOffset b.sopSat.sop.offsetR)
          , offsetG: offset (unwrapOffset a.sopSat.sop.offsetG + unwrapOffset b.sopSat.sop.offsetG)
          , offsetB: offset (unwrapOffset a.sopSat.sop.offsetB + unwrapOffset b.sopSat.sop.offsetB)
          , powerR: power (unwrapPower a.sopSat.sop.powerR * unwrapPower b.sopSat.sop.powerR)
          , powerG: power (unwrapPower a.sopSat.sop.powerG * unwrapPower b.sopSat.sop.powerG)
          , powerB: power (unwrapPower a.sopSat.sop.powerB * unwrapPower b.sopSat.sop.powerB)
          }
      , saturation: saturation (unwrapSaturation a.sopSat.saturation * unwrapSaturation b.sopSat.saturation)
      }
  , id: a.id <> "+" <> b.id
  , description: "Combined"
  }

-- | Invert a CDL (approximately)
-- |
-- | Mathematical inverse: slope' = 1/slope, offset' = -offset/slope, power' = 1/power
invertCDL :: CDL -> CDL
invertCDL (CDL c) = 
  let sop = c.sopSat.sop
      invSlope s = if s == 0.0 then 4.0 else 1.0 / s  -- Clamp to max if divide by zero
  in CDL
    { sopSat:
        { sop:
            { slopeR: slope (invSlope (unwrapSlope sop.slopeR))
            , slopeG: slope (invSlope (unwrapSlope sop.slopeG))
            , slopeB: slope (invSlope (unwrapSlope sop.slopeB))
            , offsetR: offset (negate (unwrapOffset sop.offsetR) / unwrapSlope sop.slopeR)
            , offsetG: offset (negate (unwrapOffset sop.offsetG) / unwrapSlope sop.slopeG)
            , offsetB: offset (negate (unwrapOffset sop.offsetB) / unwrapSlope sop.slopeB)
            , powerR: power (1.0 / unwrapPower sop.powerR)
            , powerG: power (1.0 / unwrapPower sop.powerG)
            , powerB: power (1.0 / unwrapPower sop.powerB)
            }
        , saturation: saturation (1.0 / unwrapSaturation c.sopSat.saturation)
        }
    , id: c.id <> "-inv"
    , description: "Inverted"
    }

-- | Scale CDL values by a factor (blend toward identity)
-- |
-- | factor = 0.0: identity (no change)
-- | factor = 1.0: full CDL effect
scaleCDL :: Number -> CDL -> CDL
scaleCDL factor (CDL c) =
  let f = Bounded.clampNumber 0.0 1.0 factor
      blendSlope s = 1.0 + f * (unwrapSlope s - 1.0)
      blendOffset o = f * unwrapOffset o
      blendPower p = 1.0 + f * (unwrapPower p - 1.0)
      blendSat s = 1.0 + f * (unwrapSaturation s - 1.0)
      sop = c.sopSat.sop
  in CDL
    { sopSat:
        { sop:
            { slopeR: slope (blendSlope sop.slopeR)
            , slopeG: slope (blendSlope sop.slopeG)
            , slopeB: slope (blendSlope sop.slopeB)
            , offsetR: offset (blendOffset sop.offsetR)
            , offsetG: offset (blendOffset sop.offsetG)
            , offsetB: offset (blendOffset sop.offsetB)
            , powerR: power (blendPower sop.powerR)
            , powerG: power (blendPower sop.powerG)
            , powerB: power (blendPower sop.powerB)
            }
        , saturation: saturation (blendSat c.sopSat.saturation)
        }
    , id: c.id
    , description: c.description <> " @" <> show (factor * 100.0) <> "%"
    }

-- | Reset slope to identity (1,1,1)
resetSlope :: CDL -> CDL
resetSlope (CDL c) = CDL c
  { sopSat = c.sopSat
      { sop = c.sopSat.sop
          { slopeR = slope 1.0
          , slopeG = slope 1.0
          , slopeB = slope 1.0
          }
      }
  }

-- | Reset offset to identity (0,0,0)
resetOffset :: CDL -> CDL
resetOffset (CDL c) = CDL c
  { sopSat = c.sopSat
      { sop = c.sopSat.sop
          { offsetR = offset 0.0
          , offsetG = offset 0.0
          , offsetB = offset 0.0
          }
      }
  }

-- | Reset power to identity (1,1,1)
resetPower :: CDL -> CDL
resetPower (CDL c) = CDL c
  { sopSat = c.sopSat
      { sop = c.sopSat.sop
          { powerR = power 1.0
          , powerG = power 1.0
          , powerB = power 1.0
          }
      }
  }

-- | Reset saturation to identity (1.0)
resetSaturation :: CDL -> CDL
resetSaturation (CDL c) = CDL c
  { sopSat = c.sopSat { saturation = saturation 1.0 }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warm up preset (increase red, decrease blue)
cdlWarmUp :: CDL
cdlWarmUp = cdl 1.1 1.0 0.9  0.02 0.0 (-0.02)  1.0 1.0 1.0  1.0 "warm-up"

-- | Cool down preset (decrease red, increase blue)
cdlCoolDown :: CDL
cdlCoolDown = cdl 0.9 1.0 1.1  (-0.02) 0.0 0.02  1.0 1.0 1.0  1.0 "cool-down"

-- | Low contrast preset (lift blacks, lower highlights)
cdlLowContrast :: CDL
cdlLowContrast = cdl 0.9 0.9 0.9  0.05 0.05 0.05  1.1 1.1 1.1  1.0 "low-contrast"

-- | High contrast preset (crush blacks, boost highlights)
cdlHighContrast :: CDL
cdlHighContrast = cdl 1.2 1.2 1.2  (-0.05) (-0.05) (-0.05)  0.9 0.9 0.9  1.1 "high-contrast"

-- | Desaturate preset (reduce saturation to 50%)
cdlDesaturate :: CDL
cdlDesaturate = cdl 1.0 1.0 1.0  0.0 0.0 0.0  1.0 1.0 1.0  0.5 "desaturate"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 = Bounded.clampNumber 0.0 1.0
