-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // color // log // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera Log Curve Atoms and Color Spaces.
-- |
-- | **PROFESSIONAL CINEMA COLOR SCIENCE:**
-- | Camera log encodings compress high dynamic range scenes into recordable
-- | ranges. Each manufacturer has their own encoding curve optimized for
-- | their sensor characteristics.
-- |
-- | **Atoms (encoded single channel values):**
-- | - `LogC` - ARRI LogC (AWG3/AWG4 cameras)
-- | - `SLog3` - Sony S-Log3 (Venice, FX series)
-- | - `VLog` - Panasonic V-Log (Varicam, S1H)
-- | - `RedLog3G10` - RED Log3G10 (RED cameras)
-- | - `CanonLog3` - Canon Log3 (Cinema EOS)
-- | - `BMDFilm` - Blackmagic Film (Pocket/URSA)
-- |
-- | **Molecules (full RGB in log space):**
-- | - `ArriLogC3` - ARRI LogC3 + AWG3 gamut
-- | - `ArriLogC4` - ARRI LogC4 + AWG4 gamut
-- | - `SLog3_SGamut3` - Sony S-Log3 + S-Gamut3
-- | - `VLog_VGamut` - Panasonic V-Log + V-Gamut
-- | - `RedLog3G10_RWG` - RED Log3G10 + REDWideGamutRGB
-- | - `CanonLog3_CG` - Canon Log3 + Cinema Gamut
-- | - `BMDFilm_BWG` - Blackmagic Film + Wide Gamut
-- |
-- | **Why log encoding?**
-- | Human vision is roughly logarithmic. Log encoding matches this perceptual
-- | response, allowing more efficient use of bit depth for high dynamic range.
-- | A linear 16-stop scene would need 16+ bits linear; log fits in 10-12 bits.

module Hydrogen.Schema.Color.Log.Types
  ( -- * Atoms (Single Channel Encoded Values)
    LogC
  , SLog3
  , VLog
  , RedLog3G10
  , CanonLog3
  , BMDFilm
  
  -- * Atom Constructors
  , logC
  , sLog3
  , vLog
  , redLog3G10
  , canonLog3
  , bmdFilm
  
  -- * Atom Unwrappers
  , unwrapLogC
  , unwrapSLog3
  , unwrapVLog
  , unwrapRedLog3G10
  , unwrapCanonLog3
  , unwrapBMDFilm
  
  -- * Molecules (Full RGB Log Spaces)
  , ArriLogC3
  , ArriLogC4
  , SLog3_SGamut3
  , VLog_VGamut
  , RedLog3G10_RWG
  , CanonLog3_CG
  , BMDFilm_BWG
  
  -- * Molecule Constructors
  , arriLogC3
  , arriLogC4
  , sLog3_SGamut3
  , vLog_VGamut
  , redLog3G10_RWG
  , canonLog3_CG
  , bmdFilm_BWG
  
  -- * Molecule Accessors
  , class LogSpaceRGB
  , getR
  , getG
  , getB
  , toRecord
  
  -- * Conversions (Log to Linear)
  , logCToLinear
  , linearToLogC
  , sLog3ToLinear
  , linearToSLog3
  , vLogToLinear
  , linearToVLog
  , redLog3G10ToLinear
  , linearToRedLog3G10
  , canonLog3ToLinear
  , linearToCanonLog3
  , bmdFilmToLinear
  , linearToBMDFilm
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // atoms - log encoded values
-- ═════════════════════════════════════════════════════════════════════════════

-- | ARRI LogC encoded value (0.0-1.0)
-- |
-- | LogC is ARRI's proprietary log encoding, designed for their ALEXA sensors.
-- | The curve is mathematically defined to preserve maximum dynamic range.
newtype LogC = LogC Number

derive instance eqLogC :: Eq LogC
derive instance ordLogC :: Ord LogC

instance showLogC :: Show LogC where
  show (LogC n) = "LogC " <> show n

-- | Create LogC value (clamped 0.0-1.0)
logC :: Number -> LogC
logC n = LogC (Bounded.clampNumber 0.0 1.0 n)

-- | Extract raw value
unwrapLogC :: LogC -> Number
unwrapLogC (LogC n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Sony S-Log3 encoded value (0.0-1.0)
-- |
-- | S-Log3 is Sony's third-generation log curve, used in Venice, FX6, FX9,
-- | and other professional cameras. Wider dynamic range than S-Log2.
newtype SLog3 = SLog3 Number

derive instance eqSLog3 :: Eq SLog3
derive instance ordSLog3 :: Ord SLog3

instance showSLog3 :: Show SLog3 where
  show (SLog3 n) = "SLog3 " <> show n

-- | Create SLog3 value (clamped 0.0-1.0)
sLog3 :: Number -> SLog3
sLog3 n = SLog3 (Bounded.clampNumber 0.0 1.0 n)

-- | Extract raw value
unwrapSLog3 :: SLog3 -> Number
unwrapSLog3 (SLog3 n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Panasonic V-Log encoded value (0.0-1.0)
-- |
-- | V-Log is Panasonic's log curve, similar to Cineon log. Used in Varicam
-- | and S1H cameras. Provides ~14 stops of dynamic range.
newtype VLog = VLog Number

derive instance eqVLog :: Eq VLog
derive instance ordVLog :: Ord VLog

instance showVLog :: Show VLog where
  show (VLog n) = "VLog " <> show n

-- | Create VLog value (clamped 0.0-1.0)
vLog :: Number -> VLog
vLog n = VLog (Bounded.clampNumber 0.0 1.0 n)

-- | Extract raw value
unwrapVLog :: VLog -> Number
unwrapVLog (VLog n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | RED Log3G10 encoded value (0.0-1.0)
-- |
-- | RED's log encoding with 10 stops below 18% gray. Used with REDWideGamutRGB.
-- | Provides very high dynamic range for RED cameras.
newtype RedLog3G10 = RedLog3G10 Number

derive instance eqRedLog3G10 :: Eq RedLog3G10
derive instance ordRedLog3G10 :: Ord RedLog3G10

instance showRedLog3G10 :: Show RedLog3G10 where
  show (RedLog3G10 n) = "RedLog3G10 " <> show n

-- | Create RedLog3G10 value (clamped 0.0-1.0)
redLog3G10 :: Number -> RedLog3G10
redLog3G10 n = RedLog3G10 (Bounded.clampNumber 0.0 1.0 n)

-- | Extract raw value
unwrapRedLog3G10 :: RedLog3G10 -> Number
unwrapRedLog3G10 (RedLog3G10 n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Canon Log3 encoded value (0.0-1.0)
-- |
-- | Canon's log curve for Cinema EOS cameras (C300, C500, C700).
-- | Optimized for highlight handling and skin tones.
newtype CanonLog3 = CanonLog3 Number

derive instance eqCanonLog3 :: Eq CanonLog3
derive instance ordCanonLog3 :: Ord CanonLog3

instance showCanonLog3 :: Show CanonLog3 where
  show (CanonLog3 n) = "CanonLog3 " <> show n

-- | Create CanonLog3 value (clamped 0.0-1.0)
canonLog3 :: Number -> CanonLog3
canonLog3 n = CanonLog3 (Bounded.clampNumber 0.0 1.0 n)

-- | Extract raw value
unwrapCanonLog3 :: CanonLog3 -> Number
unwrapCanonLog3 (CanonLog3 n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Blackmagic Film encoded value (0.0-1.0)
-- |
-- | Blackmagic's log curve for Pocket Cinema and URSA cameras.
-- | Part of Blackmagic's Gen 5 color science.
newtype BMDFilm = BMDFilm Number

derive instance eqBMDFilm :: Eq BMDFilm
derive instance ordBMDFilm :: Ord BMDFilm

instance showBMDFilm :: Show BMDFilm where
  show (BMDFilm n) = "BMDFilm " <> show n

-- | Create BMDFilm value (clamped 0.0-1.0)
bmdFilm :: Number -> BMDFilm
bmdFilm n = BMDFilm (Bounded.clampNumber 0.0 1.0 n)

-- | Extract raw value
unwrapBMDFilm :: BMDFilm -> Number
unwrapBMDFilm (BMDFilm n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // molecules - log color spaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | ARRI LogC3 + AWG3 (ALEXA Wide Gamut 3)
-- |
-- | The standard ARRI camera log space before LogC4. Used in ALEXA Mini, etc.
newtype ArriLogC3 = ArriLogC3
  { r :: LogC
  , g :: LogC
  , b :: LogC
  }

derive instance eqArriLogC3 :: Eq ArriLogC3

instance showArriLogC3 :: Show ArriLogC3 where
  show (ArriLogC3 c) = "ArriLogC3(" <> show (unwrapLogC c.r) <> ", " 
    <> show (unwrapLogC c.g) <> ", " <> show (unwrapLogC c.b) <> ")"

-- | Create ARRI LogC3 color
arriLogC3 :: Number -> Number -> Number -> ArriLogC3
arriLogC3 r g b = ArriLogC3
  { r: logC r
  , g: logC g
  , b: logC b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | ARRI LogC4 + AWG4 (ALEXA Wide Gamut 4)
-- |
-- | The newer ARRI log space for ALEXA 35 and later cameras. Extended range.
newtype ArriLogC4 = ArriLogC4
  { r :: LogC
  , g :: LogC
  , b :: LogC
  }

derive instance eqArriLogC4 :: Eq ArriLogC4

instance showArriLogC4 :: Show ArriLogC4 where
  show (ArriLogC4 c) = "ArriLogC4(" <> show (unwrapLogC c.r) <> ", " 
    <> show (unwrapLogC c.g) <> ", " <> show (unwrapLogC c.b) <> ")"

-- | Create ARRI LogC4 color
arriLogC4 :: Number -> Number -> Number -> ArriLogC4
arriLogC4 r g b = ArriLogC4
  { r: logC r
  , g: logC g
  , b: logC b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | Sony S-Log3 + S-Gamut3
-- |
-- | Sony's professional log space, pairs S-Log3 curve with S-Gamut3 primaries.
newtype SLog3_SGamut3 = SLog3_SGamut3
  { r :: SLog3
  , g :: SLog3
  , b :: SLog3
  }

derive instance eqSLog3_SGamut3 :: Eq SLog3_SGamut3

instance showSLog3_SGamut3 :: Show SLog3_SGamut3 where
  show (SLog3_SGamut3 c) = "SLog3_SGamut3(" <> show (unwrapSLog3 c.r) <> ", " 
    <> show (unwrapSLog3 c.g) <> ", " <> show (unwrapSLog3 c.b) <> ")"

-- | Create Sony S-Log3/S-Gamut3 color
sLog3_SGamut3 :: Number -> Number -> Number -> SLog3_SGamut3
sLog3_SGamut3 r g b = SLog3_SGamut3
  { r: sLog3 r
  , g: sLog3 g
  , b: sLog3 b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | Panasonic V-Log + V-Gamut
-- |
-- | Panasonic's professional log space for Varicam and S1H.
newtype VLog_VGamut = VLog_VGamut
  { r :: VLog
  , g :: VLog
  , b :: VLog
  }

derive instance eqVLog_VGamut :: Eq VLog_VGamut

instance showVLog_VGamut :: Show VLog_VGamut where
  show (VLog_VGamut c) = "VLog_VGamut(" <> show (unwrapVLog c.r) <> ", " 
    <> show (unwrapVLog c.g) <> ", " <> show (unwrapVLog c.b) <> ")"

-- | Create Panasonic V-Log/V-Gamut color
vLog_VGamut :: Number -> Number -> Number -> VLog_VGamut
vLog_VGamut r g b = VLog_VGamut
  { r: vLog r
  , g: vLog g
  , b: vLog b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | RED Log3G10 + REDWideGamutRGB
-- |
-- | RED's professional log space, combining Log3G10 with wide gamut primaries.
newtype RedLog3G10_RWG = RedLog3G10_RWG
  { r :: RedLog3G10
  , g :: RedLog3G10
  , b :: RedLog3G10
  }

derive instance eqRedLog3G10_RWG :: Eq RedLog3G10_RWG

instance showRedLog3G10_RWG :: Show RedLog3G10_RWG where
  show (RedLog3G10_RWG c) = "RedLog3G10_RWG(" <> show (unwrapRedLog3G10 c.r) <> ", " 
    <> show (unwrapRedLog3G10 c.g) <> ", " <> show (unwrapRedLog3G10 c.b) <> ")"

-- | Create RED Log3G10/RWG color
redLog3G10_RWG :: Number -> Number -> Number -> RedLog3G10_RWG
redLog3G10_RWG r g b = RedLog3G10_RWG
  { r: redLog3G10 r
  , g: redLog3G10 g
  , b: redLog3G10 b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | Canon Log3 + Cinema Gamut
-- |
-- | Canon's professional log space for Cinema EOS line.
newtype CanonLog3_CG = CanonLog3_CG
  { r :: CanonLog3
  , g :: CanonLog3
  , b :: CanonLog3
  }

derive instance eqCanonLog3_CG :: Eq CanonLog3_CG

instance showCanonLog3_CG :: Show CanonLog3_CG where
  show (CanonLog3_CG c) = "CanonLog3_CG(" <> show (unwrapCanonLog3 c.r) <> ", " 
    <> show (unwrapCanonLog3 c.g) <> ", " <> show (unwrapCanonLog3 c.b) <> ")"

-- | Create Canon Log3/Cinema Gamut color
canonLog3_CG :: Number -> Number -> Number -> CanonLog3_CG
canonLog3_CG r g b = CanonLog3_CG
  { r: canonLog3 r
  , g: canonLog3 g
  , b: canonLog3 b
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | Blackmagic Film + Wide Gamut
-- |
-- | Blackmagic's professional log space for cinema cameras.
newtype BMDFilm_BWG = BMDFilm_BWG
  { r :: BMDFilm
  , g :: BMDFilm
  , b :: BMDFilm
  }

derive instance eqBMDFilm_BWG :: Eq BMDFilm_BWG

instance showBMDFilm_BWG :: Show BMDFilm_BWG where
  show (BMDFilm_BWG c) = "BMDFilm_BWG(" <> show (unwrapBMDFilm c.r) <> ", " 
    <> show (unwrapBMDFilm c.g) <> ", " <> show (unwrapBMDFilm c.b) <> ")"

-- | Create Blackmagic Film/Wide Gamut color
bmdFilm_BWG :: Number -> Number -> Number -> BMDFilm_BWG
bmdFilm_BWG r g b = BMDFilm_BWG
  { r: bmdFilm r
  , g: bmdFilm g
  , b: bmdFilm b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // generic accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for accessing RGB components from log spaces
class LogSpaceRGB a where
  getR :: a -> Number
  getG :: a -> Number
  getB :: a -> Number

instance logSpaceRGB_ArriLogC3 :: LogSpaceRGB ArriLogC3 where
  getR (ArriLogC3 c) = unwrapLogC c.r
  getG (ArriLogC3 c) = unwrapLogC c.g
  getB (ArriLogC3 c) = unwrapLogC c.b

instance logSpaceRGB_ArriLogC4 :: LogSpaceRGB ArriLogC4 where
  getR (ArriLogC4 c) = unwrapLogC c.r
  getG (ArriLogC4 c) = unwrapLogC c.g
  getB (ArriLogC4 c) = unwrapLogC c.b

instance logSpaceRGB_SLog3_SGamut3 :: LogSpaceRGB SLog3_SGamut3 where
  getR (SLog3_SGamut3 c) = unwrapSLog3 c.r
  getG (SLog3_SGamut3 c) = unwrapSLog3 c.g
  getB (SLog3_SGamut3 c) = unwrapSLog3 c.b

instance logSpaceRGB_VLog_VGamut :: LogSpaceRGB VLog_VGamut where
  getR (VLog_VGamut c) = unwrapVLog c.r
  getG (VLog_VGamut c) = unwrapVLog c.g
  getB (VLog_VGamut c) = unwrapVLog c.b

instance logSpaceRGB_RedLog3G10_RWG :: LogSpaceRGB RedLog3G10_RWG where
  getR (RedLog3G10_RWG c) = unwrapRedLog3G10 c.r
  getG (RedLog3G10_RWG c) = unwrapRedLog3G10 c.g
  getB (RedLog3G10_RWG c) = unwrapRedLog3G10 c.b

instance logSpaceRGB_CanonLog3_CG :: LogSpaceRGB CanonLog3_CG where
  getR (CanonLog3_CG c) = unwrapCanonLog3 c.r
  getG (CanonLog3_CG c) = unwrapCanonLog3 c.g
  getB (CanonLog3_CG c) = unwrapCanonLog3 c.b

instance logSpaceRGB_BMDFilm_BWG :: LogSpaceRGB BMDFilm_BWG where
  getR (BMDFilm_BWG c) = unwrapBMDFilm c.r
  getG (BMDFilm_BWG c) = unwrapBMDFilm c.g
  getB (BMDFilm_BWG c) = unwrapBMDFilm c.b

-- | Convert to record representation
toRecord :: forall a. LogSpaceRGB a => a -> { r :: Number, g :: Number, b :: Number }
toRecord a = { r: getR a, g: getG a, b: getB a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // log-to-linear conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert ARRI LogC to linear
-- |
-- | LogC3 formula (simplified for standard encoding):
-- | linear = (10^((logC - 0.391007) / 0.247190) - 0.052272) / 5.555556
logCToLinear :: LogC -> Number
logCToLinear (LogC logVal)
  | logVal < 0.1496582 = (logVal - 0.092809) / 5.367655
  | otherwise = 
      let expArg = (logVal - 0.391007) / 0.247190
      in (Math.pow 10.0 expArg - 0.052272) / 5.555556

-- | Convert linear to ARRI LogC
linearToLogC :: Number -> LogC
linearToLogC lin
  | lin < 0.010591 = logC (lin * 5.367655 + 0.092809)
  | otherwise = 
      let logArg = lin * 5.555556 + 0.052272
          safeArg = if logArg <= 0.0 then 0.000001 else logArg
      in logC (0.247190 * Math.log10 safeArg + 0.391007)

-- | Convert Sony S-Log3 to linear
-- |
-- | S-Log3 formula per Sony specification.
sLog3ToLinear :: SLog3 -> Number
sLog3ToLinear (SLog3 slog)
  | slog < 0.171875 = (slog - 0.092864) / 5.0
  | otherwise =
      let expArg = (slog - 0.410435) / 0.255620
      in Math.pow 10.0 expArg - 0.014

-- | Convert linear to Sony S-Log3
linearToSLog3 :: Number -> SLog3
linearToSLog3 lin
  | lin < 0.01125 = sLog3 (lin * 5.0 + 0.092864)
  | otherwise =
      let logArg = lin + 0.014
          safeArg = if logArg <= 0.0 then 0.000001 else logArg
      in sLog3 (0.255620 * Math.log10 safeArg + 0.410435)

-- | Convert Panasonic V-Log to linear
-- |
-- | V-Log formula per Panasonic specification.
vLogToLinear :: VLog -> Number
vLogToLinear (VLog vl)
  | vl < 0.181 = (vl - 0.125) / 5.6
  | otherwise =
      let expArg = (vl - 0.598206) / 0.241514
      in Math.pow 10.0 expArg - 0.00873

-- | Convert linear to Panasonic V-Log
linearToVLog :: Number -> VLog
linearToVLog lin
  | lin < 0.01 = vLog (lin * 5.6 + 0.125)
  | otherwise =
      let logArg = lin + 0.00873
          safeArg = if logArg <= 0.0 then 0.000001 else logArg
      in vLog (0.241514 * Math.log10 safeArg + 0.598206)

-- | Convert RED Log3G10 to linear
-- |
-- | RED Log3G10 formula: designed for 10 stops below 18% gray.
-- | Reference: RED Technical Guide
redLog3G10ToLinear :: RedLog3G10 -> Number
redLog3G10ToLinear (RedLog3G10 logVal)
  | logVal < 0.0 = 0.0
  | otherwise =
      let a = 0.224282
          b = 155.975327
          c = 0.01
          g = 15.1927
          -- Log3G10 formula: linear = (10^((logVal - a) / g) - c) / b
          expArg = (logVal - a) / g
      in (Math.pow 10.0 expArg - c) / b

-- | Convert linear to RED Log3G10
linearToRedLog3G10 :: Number -> RedLog3G10
linearToRedLog3G10 lin =
  let a = 0.224282
      b = 155.975327
      c = 0.01
      g = 15.1927
      logArg = lin * b + c
      safeArg = if logArg <= 0.0 then 0.000001 else logArg
  in redLog3G10 (g * Math.log10 safeArg + a)

-- | Convert Canon Log3 to linear
-- |
-- | Canon Log3 formula per Canon specification.
-- | Optimized for C300/C500/C700 cameras.
canonLog3ToLinear :: CanonLog3 -> Number
canonLog3ToLinear (CanonLog3 logVal)
  | logVal < 0.097465 = (logVal - 0.069886) / 14.98325
  | otherwise =
      let expArg = (logVal - 0.358051) / 0.268695
      in Math.pow 10.0 expArg - 0.014

-- | Convert linear to Canon Log3
linearToCanonLog3 :: Number -> CanonLog3
linearToCanonLog3 lin
  | lin < 0.0014 = canonLog3 (lin * 14.98325 + 0.069886)
  | otherwise =
      let logArg = lin + 0.014
          safeArg = if logArg <= 0.0 then 0.000001 else logArg
      in canonLog3 (0.268695 * Math.log10 safeArg + 0.358051)

-- | Convert Blackmagic Film to linear
-- |
-- | BMD Film (Gen 5) log curve per Blackmagic specification.
bmdFilmToLinear :: BMDFilm -> Number
bmdFilmToLinear (BMDFilm logVal)
  | logVal < 0.09 = (logVal - 0.0045) / 8.283
  | otherwise =
      let a = 0.09246575342
          b = 0.5300133392
          c = 0.08692876065
          -- Blackmagic Film formula (approximation)
          expArg = (logVal - b) / c
      in Math.pow 10.0 expArg - a

-- | Convert linear to Blackmagic Film
linearToBMDFilm :: Number -> BMDFilm
linearToBMDFilm lin
  | lin < 0.005 = bmdFilm (lin * 8.283 + 0.0045)
  | otherwise =
      let a = 0.09246575342
          b = 0.5300133392
          c = 0.08692876065
          logArg = lin + a
          safeArg = if logArg <= 0.0 then 0.000001 else logArg
      in bmdFilm (c * Math.log10 safeArg + b)
