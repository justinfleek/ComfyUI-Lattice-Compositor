-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // video
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Video Broadcast Color Atoms and Molecules.
-- |
-- | **VIDEO COLOR ENCODING STANDARDS:**
-- | Video color spaces separate luminance (Y) from chrominance for
-- | efficient transmission and backward compatibility with B&W systems.
-- |
-- | **Atoms:**
-- | - `Luma` - Y luminance component (0.0-1.0), already in YUV.purs
-- | - `Cb` - Blue-difference chroma (-0.5 to +0.5)
-- | - `Cr` - Red-difference chroma (-0.5 to +0.5)
-- | - `I` - In-phase NTSC chroma (-0.5 to +0.5)
-- | - `Q` - Quadrature NTSC chroma (-0.5 to +0.5)
-- |
-- | **Molecules:**
-- | - `YCbCr` - Digital video (ITU-R BT.601/709)
-- | - `YIQ` - NTSC analog (North America)
-- | - `YPbPr` - Component analog video
-- |
-- | **Why multiple standards?**
-- | - YUV/YPbPr: Analog component video (PAL, SECAM)
-- | - YCbCr: Digital video (JPEG, MPEG, H.264, web video)
-- | - YIQ: NTSC broadcast (legacy North America)

module Hydrogen.Schema.Color.Video
  ( -- * Atoms (Chroma Components)
    Cb
  , Cr
  , I
  , Q
  
  -- * Atom Constructors
  , cb
  , cr
  , inPhase
  , quadrature
  
  -- * Atom Unwrappers
  , unwrapCb
  , unwrapCr
  , unwrapI
  , unwrapQ
  
  -- * Re-exports from YUV
  , module YUV
  
  -- * Molecules
  , YCbCr
  , YIQ
  , YPbPr
  
  -- * Molecule Constructors
  , yCbCr
  , yIQ
  , yPbPr
  , yCbCrFromRecord
  , yIQFromRecord
  , yPbPrFromRecord
  
  -- * Molecule Accessors
  , getYCbCr_Y
  , getYCbCr_Cb
  , getYCbCr_Cr
  , getYIQ_Y
  , getYIQ_I
  , getYIQ_Q
  , getYPbPr_Y
  , getYPbPr_Pb
  , getYPbPr_Pr
  , yCbCrToRecord
  , yIQToRecord
  , yPbPrToRecord
  
  -- * Conversions
  , rgbToYCbCr
  , yCbCrToRgb
  , rgbToYIQ
  , yIQToRgb
  , rgbToYPbPr
  , yPbPrToRgb
  
  -- * Inter-format conversions
  , yCbCrToYPbPr
  , yPbPrToYCbCr
  , yuvToYCbCr
  , yCbCrToYuv
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Data.Int (round, toNumber)
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.YUV (Luma, luma, unwrapLuma, YUV, yuv, yuvToRecord, ChromaU, chromaU, unwrapU, ChromaV, chromaV, unwrapV) as YUV
import Hydrogen.Schema.Color.Channel (unwrap) as Chan
import Hydrogen.Schema.Color.RGB (RGB, rgb, red, green, blue) as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // atoms - chroma components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cb - Blue-difference chroma (-0.5 to +0.5)
-- |
-- | Component of YCbCr digital video. Represents the difference between
-- | blue and luminance: Cb = (B - Y) / 1.772
newtype Cb = Cb Number

derive instance eqCb :: Eq Cb
derive instance ordCb :: Ord Cb

instance showCb :: Show Cb where
  show (Cb n) = "Cb " <> show n

-- | Create Cb value (clamped -0.5 to +0.5)
cb :: Number -> Cb
cb n = Cb (Bounded.clampNumber (-0.5) 0.5 n)

-- | Extract raw value
unwrapCb :: Cb -> Number
unwrapCb (Cb n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Cr - Red-difference chroma (-0.5 to +0.5)
-- |
-- | Component of YCbCr digital video. Represents the difference between
-- | red and luminance: Cr = (R - Y) / 1.402
newtype Cr = Cr Number

derive instance eqCr :: Eq Cr
derive instance ordCr :: Ord Cr

instance showCr :: Show Cr where
  show (Cr n) = "Cr " <> show n

-- | Create Cr value (clamped -0.5 to +0.5)
cr :: Number -> Cr
cr n = Cr (Bounded.clampNumber (-0.5) 0.5 n)

-- | Extract raw value
unwrapCr :: Cr -> Number
unwrapCr (Cr n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | I - In-phase NTSC chroma (-0.5 to +0.5)
-- |
-- | Component of YIQ NTSC color. Carries orange-cyan axis, which human
-- | vision is most sensitive to - hence it gets more bandwidth.
newtype I = I Number

derive instance eqI :: Eq I
derive instance ordI :: Ord I

instance showI :: Show I where
  show (I n) = "I " <> show n

-- | Create I value (clamped -0.5 to +0.5)
inPhase :: Number -> I
inPhase n = I (Bounded.clampNumber (-0.5) 0.5 n)

-- | Extract raw value
unwrapI :: I -> Number
unwrapI (I n) = n

-- ─────────────────────────────────────────────────────────────────────────────

-- | Q - Quadrature NTSC chroma (-0.5 to +0.5)
-- |
-- | Component of YIQ NTSC color. Carries green-magenta axis, which human
-- | vision is less sensitive to - gets less bandwidth.
newtype Q = Q Number

derive instance eqQ :: Eq Q
derive instance ordQ :: Ord Q

instance showQ :: Show Q where
  show (Q n) = "Q " <> show n

-- | Create Q value (clamped -0.5 to +0.5)
quadrature :: Number -> Q
quadrature n = Q (Bounded.clampNumber (-0.5) 0.5 n)

-- | Extract raw value
unwrapQ :: Q -> Number
unwrapQ (Q n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // molecules - video color spaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | YCbCr - Digital video color space (ITU-R BT.601/709)
-- |
-- | The standard color space for digital video (JPEG, MPEG, H.264, web).
-- | Composed of luma Y and chroma components Cb and Cr.
newtype YCbCr = YCbCr
  { y :: YUV.Luma
  , cb :: Cb
  , cr :: Cr
  }

derive instance eqYCbCr :: Eq YCbCr

instance showYCbCr :: Show YCbCr where
  show (YCbCr c) = "YCbCr(" <> show (YUV.unwrapLuma c.y) <> ", " 
    <> show (unwrapCb c.cb) <> ", " <> show (unwrapCr c.cr) <> ")"

-- | Create YCbCr color
yCbCr :: Number -> Number -> Number -> YCbCr
yCbCr y' cb' cr' = YCbCr
  { y: YUV.luma y'
  , cb: cb cb'
  , cr: cr cr'
  }

-- | Create from record
yCbCrFromRecord :: { y :: Number, cb :: Number, cr :: Number } -> YCbCr
yCbCrFromRecord r = yCbCr r.y r.cb r.cr

-- | Get Y component
getYCbCr_Y :: YCbCr -> YUV.Luma
getYCbCr_Y (YCbCr c) = c.y

-- | Get Cb component
getYCbCr_Cb :: YCbCr -> Cb
getYCbCr_Cb (YCbCr c) = c.cb

-- | Get Cr component
getYCbCr_Cr :: YCbCr -> Cr
getYCbCr_Cr (YCbCr c) = c.cr

-- | Convert to record
yCbCrToRecord :: YCbCr -> { y :: Number, cb :: Number, cr :: Number }
yCbCrToRecord (YCbCr c) =
  { y: YUV.unwrapLuma c.y
  , cb: unwrapCb c.cb
  , cr: unwrapCr c.cr
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | YIQ - NTSC analog color space (North America)
-- |
-- | Legacy NTSC broadcast standard. I (in-phase) carries orange-cyan,
-- | Q (quadrature) carries green-magenta. Still used in some image processing.
newtype YIQ = YIQ
  { y :: YUV.Luma
  , i :: I
  , q :: Q
  }

derive instance eqYIQ :: Eq YIQ

instance showYIQ :: Show YIQ where
  show (YIQ c) = "YIQ(" <> show (YUV.unwrapLuma c.y) <> ", " 
    <> show (unwrapI c.i) <> ", " <> show (unwrapQ c.q) <> ")"

-- | Create YIQ color
yIQ :: Number -> Number -> Number -> YIQ
yIQ y' i' q' = YIQ
  { y: YUV.luma y'
  , i: inPhase i'
  , q: quadrature q'
  }

-- | Create from record
yIQFromRecord :: { y :: Number, i :: Number, q :: Number } -> YIQ
yIQFromRecord r = yIQ r.y r.i r.q

-- | Get Y component
getYIQ_Y :: YIQ -> YUV.Luma
getYIQ_Y (YIQ c) = c.y

-- | Get I component
getYIQ_I :: YIQ -> I
getYIQ_I (YIQ c) = c.i

-- | Get Q component
getYIQ_Q :: YIQ -> Q
getYIQ_Q (YIQ c) = c.q

-- | Convert to record
yIQToRecord :: YIQ -> { y :: Number, i :: Number, q :: Number }
yIQToRecord (YIQ c) =
  { y: YUV.unwrapLuma c.y
  , i: unwrapI c.i
  , q: unwrapQ c.q
  }

-- ─────────────────────────────────────────────────────────────────────────────

-- | YPbPr - Component analog video
-- |
-- | Analog component video using Y (luma) and Pb/Pr (scaled Cb/Cr).
-- | Used for component video cables (green/blue/red jacks on older TVs).
newtype YPbPr = YPbPr
  { y :: YUV.Luma
  , pb :: Cb  -- Pb is essentially Cb (blue-difference)
  , pr :: Cr  -- Pr is essentially Cr (red-difference)
  }

derive instance eqYPbPr :: Eq YPbPr

instance showYPbPr :: Show YPbPr where
  show (YPbPr c) = "YPbPr(" <> show (YUV.unwrapLuma c.y) <> ", " 
    <> show (unwrapCb c.pb) <> ", " <> show (unwrapCr c.pr) <> ")"

-- | Create YPbPr color
yPbPr :: Number -> Number -> Number -> YPbPr
yPbPr y' pb' pr' = YPbPr
  { y: YUV.luma y'
  , pb: cb pb'
  , pr: cr pr'
  }

-- | Create from record
yPbPrFromRecord :: { y :: Number, pb :: Number, pr :: Number } -> YPbPr
yPbPrFromRecord r = yPbPr r.y r.pb r.pr

-- | Get Y component
getYPbPr_Y :: YPbPr -> YUV.Luma
getYPbPr_Y (YPbPr c) = c.y

-- | Get Pb component
getYPbPr_Pb :: YPbPr -> Cb
getYPbPr_Pb (YPbPr c) = c.pb

-- | Get Pr component
getYPbPr_Pr :: YPbPr -> Cr
getYPbPr_Pr (YPbPr c) = c.pr

-- | Convert to record
yPbPrToRecord :: YPbPr -> { y :: Number, pb :: Number, pr :: Number }
yPbPrToRecord (YPbPr c) =
  { y: YUV.unwrapLuma c.y
  , pb: unwrapCb c.pb
  , pr: unwrapCr c.pr
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to YCbCr (ITU-R BT.601)
-- |
-- | Standard conversion matrix for SD video:
-- | Y  =  0.299 R + 0.587 G + 0.114 B
-- | Cb = -0.169 R - 0.331 G + 0.500 B
-- | Cr =  0.500 R - 0.419 G - 0.081 B
rgbToYCbCr :: RGB.RGB -> YCbCr
rgbToYCbCr rgbColor =
  let r = toNumber (Chan.unwrap (RGB.red rgbColor)) / 255.0
      g = toNumber (Chan.unwrap (RGB.green rgbColor)) / 255.0
      b = toNumber (Chan.unwrap (RGB.blue rgbColor)) / 255.0
      y' = 0.299 * r + 0.587 * g + 0.114 * b
      cb' = (-0.169) * r + (-0.331) * g + 0.500 * b
      cr' = 0.500 * r + (-0.419) * g + (-0.081) * b
  in yCbCr y' cb' cr'

-- | Convert YCbCr to RGB (ITU-R BT.601)
-- |
-- | Inverse conversion:
-- | R = Y + 1.402 Cr
-- | G = Y - 0.344 Cb - 0.714 Cr
-- | B = Y + 1.772 Cb
yCbCrToRgb :: YCbCr -> RGB.RGB
yCbCrToRgb (YCbCr c) =
  let y' = YUV.unwrapLuma c.y
      cb' = unwrapCb c.cb
      cr' = unwrapCr c.cr
      r = y' + 1.402 * cr'
      g = y' - 0.344 * cb' - 0.714 * cr'
      b = y' + 1.772 * cb'
      clamp01 n = Bounded.clampNumber 0.0 1.0 n
  in RGB.rgb 
       (round (clamp01 r * 255.0)) 
       (round (clamp01 g * 255.0)) 
       (round (clamp01 b * 255.0))

-- | Convert RGB to YIQ (NTSC)
-- |
-- | Y = 0.299 R + 0.587 G + 0.114 B
-- | I = 0.596 R - 0.274 G - 0.322 B
-- | Q = 0.211 R - 0.523 G + 0.312 B
rgbToYIQ :: RGB.RGB -> YIQ
rgbToYIQ rgbColor =
  let r = toNumber (Chan.unwrap (RGB.red rgbColor)) / 255.0
      g = toNumber (Chan.unwrap (RGB.green rgbColor)) / 255.0
      b = toNumber (Chan.unwrap (RGB.blue rgbColor)) / 255.0
      y' = 0.299 * r + 0.587 * g + 0.114 * b
      i' = 0.596 * r + (-0.274) * g + (-0.322) * b
      q' = 0.211 * r + (-0.523) * g + 0.312 * b
  in yIQ y' i' q'

-- | Convert YIQ to RGB (NTSC)
-- |
-- | R = Y + 0.956 I + 0.621 Q
-- | G = Y - 0.272 I - 0.647 Q
-- | B = Y - 1.105 I + 1.702 Q
yIQToRgb :: YIQ -> RGB.RGB
yIQToRgb (YIQ c) =
  let y' = YUV.unwrapLuma c.y
      i' = unwrapI c.i
      q' = unwrapQ c.q
      r = y' + 0.956 * i' + 0.621 * q'
      g = y' - 0.272 * i' - 0.647 * q'
      b = y' - 1.105 * i' + 1.702 * q'
      clamp01 n = Bounded.clampNumber 0.0 1.0 n
  in RGB.rgb 
       (round (clamp01 r * 255.0)) 
       (round (clamp01 g * 255.0)) 
       (round (clamp01 b * 255.0))

-- | Convert RGB to YPbPr (Component Analog Video)
-- |
-- | YPbPr uses the same matrix as YCbCr for ITU-R BT.601.
-- | The difference is in signal levels for analog transmission.
-- | Y  =  0.299 R + 0.587 G + 0.114 B
-- | Pb = -0.169 R - 0.331 G + 0.500 B
-- | Pr =  0.500 R - 0.419 G - 0.081 B
rgbToYPbPr :: RGB.RGB -> YPbPr
rgbToYPbPr rgbColor =
  let r = toNumber (Chan.unwrap (RGB.red rgbColor)) / 255.0
      g = toNumber (Chan.unwrap (RGB.green rgbColor)) / 255.0
      b = toNumber (Chan.unwrap (RGB.blue rgbColor)) / 255.0
      y' = 0.299 * r + 0.587 * g + 0.114 * b
      pb' = (-0.169) * r + (-0.331) * g + 0.500 * b
      pr' = 0.500 * r + (-0.419) * g + (-0.081) * b
  in yPbPr y' pb' pr'

-- | Convert YPbPr to RGB (Component Analog Video)
-- |
-- | R = Y + 1.402 Pr
-- | G = Y - 0.344 Pb - 0.714 Pr
-- | B = Y + 1.772 Pb
yPbPrToRgb :: YPbPr -> RGB.RGB
yPbPrToRgb (YPbPr c) =
  let y' = YUV.unwrapLuma c.y
      pb' = unwrapCb c.pb
      pr' = unwrapCr c.pr
      r = y' + 1.402 * pr'
      g = y' - 0.344 * pb' - 0.714 * pr'
      b = y' + 1.772 * pb'
      clamp01 n = Bounded.clampNumber 0.0 1.0 n
  in RGB.rgb 
       (round (clamp01 r * 255.0)) 
       (round (clamp01 g * 255.0)) 
       (round (clamp01 b * 255.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // inter-format conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert YCbCr to YPbPr
-- |
-- | These are mathematically equivalent, just different naming conventions.
-- | YCbCr is digital (scaled 16-235), YPbPr is analog (0.0-1.0).
-- | This conversion assumes normalized values (0.0-1.0 for Y, -0.5 to 0.5 for chroma).
yCbCrToYPbPr :: YCbCr -> YPbPr
yCbCrToYPbPr (YCbCr c) = YPbPr
  { y: c.y
  , pb: c.cb
  , pr: c.cr
  }

-- | Convert YPbPr to YCbCr
-- |
-- | These are mathematically equivalent, just different naming conventions.
yPbPrToYCbCr :: YPbPr -> YCbCr
yPbPrToYCbCr (YPbPr c) = YCbCr
  { y: c.y
  , cb: c.pb
  , cr: c.pr
  }

-- | Convert YUV to YCbCr
-- |
-- | YUV (analog PAL) and YCbCr (digital) use different scaling factors.
-- | YUV: U and V are in range -0.5 to 0.5
-- | YCbCr: Cb and Cr are also in range -0.5 to 0.5 (for normalized values)
-- | The main difference is in how they're encoded for transmission.
yuvToYCbCr :: YUV.YUV -> YCbCr
yuvToYCbCr yuvColor =
  let rec = YUV.yuvToRecord yuvColor
  in yCbCr rec.y rec.u rec.v

-- | Convert YCbCr to YUV
-- |
-- | Direct mapping between normalized YCbCr and YUV.
yCbCrToYuv :: YCbCr -> YUV.YUV
yCbCrToYuv (YCbCr c) = 
  YUV.yuv (YUV.unwrapLuma c.y) (unwrapCb c.cb) (unwrapCr c.cr)
