-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // lut
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lookup Tables for Color Grading.
-- |
-- | **PROFESSIONAL COLOR GRADING INFRASTRUCTURE:**
-- | LUTs (Look-Up Tables) are the backbone of professional color workflows.
-- | They map input colors to output colors, enabling:
-- | - Camera log to display transforms
-- | - Creative color grading looks
-- | - Color space conversions
-- | - HDR tonemapping
-- |
-- | **LUT Types:**
-- | - `LUT1D` - Per-channel curves (1024-65536 entries per channel)
-- | - `LUT3D` - Full color cube (17x17x17 to 65x65x65 entries)
-- |
-- | **Industry Formats:**
-- | - .cube (Adobe/Blackmagic - most common)
-- | - .3dl (Lustre)
-- | - .look (ACES)
-- | - .clf (Common LUT Format - ACES standard)

module Hydrogen.Schema.Color.LUT
  ( -- * LUT Types
    LUT1D
  , LUT3D
  , LUTSize(..)
  , LUT3DSize(..)
  , LUTMetadata
  
  -- * LUT1D Operations
  , lut1D
  , lut1DIdentity
  , lut1DFromCurves
  , lut1DSize
  , sample1D
  , sample1DChannel
  
  -- * LUT3D Operations
  , lut3D
  , lut3DIdentity
  , lut3DSize
  , sample3D
  
  -- * Metadata
  , lutMetadata
  , defaultMetadata
  
  -- * LUT Manipulation
  , invertLUT1D
  , composeLUT1D
  , resizeLUT1D
  
  -- * Format Detection
  , LUTFormat(..)
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , (<>)
  , (-)
  , (+)
  , (*)
  , (/)
  , (>=)
  )

import Data.Array (length, index, replicate, mapWithIndex, reverse)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // lut sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard 1D LUT sizes (entries per channel)
data LUTSize
  = Size1K        -- ^ 1024 entries (10-bit)
  | Size4K        -- ^ 4096 entries (12-bit)
  | Size16K       -- ^ 16384 entries (14-bit)
  | Size65K       -- ^ 65536 entries (16-bit)

derive instance eqLUTSize :: Eq LUTSize

instance showLUTSize :: Show LUTSize where
  show Size1K = "1024"
  show Size4K = "4096"
  show Size16K = "16384"
  show Size65K = "65536"

-- | Convert LUTSize to Int
lutSizeToInt :: LUTSize -> Int
lutSizeToInt Size1K = 1024
lutSizeToInt Size4K = 4096
lutSizeToInt Size16K = 16384
lutSizeToInt Size65K = 65536

-- | Standard 3D LUT sizes (cube edge length)
data LUT3DSize
  = Cube17        -- ^ 17x17x17 (4913 entries) - minimum quality
  | Cube33        -- ^ 33x33x33 (35937 entries) - standard
  | Cube65        -- ^ 65x65x65 (274625 entries) - high quality

derive instance eqLUT3DSize :: Eq LUT3DSize

instance showLUT3DSize :: Show LUT3DSize where
  show Cube17 = "17x17x17"
  show Cube33 = "33x33x33"
  show Cube65 = "65x65x65"

-- | Convert LUT3DSize to Int
lut3DSizeToInt :: LUT3DSize -> Int
lut3DSizeToInt Cube17 = 17
lut3DSizeToInt Cube33 = 33
lut3DSizeToInt Cube65 = 65

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | LUT Metadata for professional workflows
type LUTMetadata =
  { title :: String                    -- ^ Display name
  , comments :: Array String           -- ^ Description, credits, etc.
  , inputColorSpace :: String          -- ^ Source color space (e.g., "ARRI LogC3")
  , outputColorSpace :: String         -- ^ Target color space (e.g., "Rec.709")
  , inputMin :: Number                 -- ^ Input domain minimum
  , inputMax :: Number                 -- ^ Input domain maximum
  , outputMin :: Number                -- ^ Output range minimum
  , outputMax :: Number                -- ^ Output range maximum
  }

-- | Create LUT metadata
lutMetadata 
  :: String 
  -> String 
  -> String 
  -> LUTMetadata
lutMetadata title inputCS outputCS =
  { title
  , comments: []
  , inputColorSpace: inputCS
  , outputColorSpace: outputCS
  , inputMin: 0.0
  , inputMax: 1.0
  , outputMin: 0.0
  , outputMax: 1.0
  }

-- | Default metadata for unspecified LUTs
defaultMetadata :: LUTMetadata
defaultMetadata =
  { title: "Untitled LUT"
  , comments: []
  , inputColorSpace: "Linear"
  , outputColorSpace: "Linear"
  , inputMin: 0.0
  , inputMax: 1.0
  , outputMin: 0.0
  , outputMax: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // 1d lookup table
-- ═════════════════════════════════════════════════════════════════════════════

-- | 1D Lookup Table (per-channel curves)
-- |
-- | A 1D LUT applies the same curve to each RGB channel independently.
-- | Used for gamma curves, log-to-linear, contrast adjustments.
-- |
-- | Each entry is a Number in 0.0-1.0 range representing the output
-- | value for that input index.
newtype LUT1D = LUT1D
  { red :: Array Number      -- ^ Red channel curve
  , green :: Array Number    -- ^ Green channel curve
  , blue :: Array Number     -- ^ Blue channel curve
  , metadata :: LUTMetadata  -- ^ LUT metadata
  }

derive instance eqLUT1D :: Eq LUT1D

instance showLUT1D :: Show LUT1D where
  show (LUT1D lut) = "LUT1D[" <> lut.metadata.title <> ", " 
    <> show (length lut.red) <> " entries]"

-- | Create a 1D LUT from channel arrays
lut1D :: Array Number -> Array Number -> Array Number -> LUTMetadata -> LUT1D
lut1D r g b meta = LUT1D
  { red: map clamp01 r
  , green: map clamp01 g
  , blue: map clamp01 b
  , metadata: meta
  }

-- | Create identity 1D LUT (no change)
lut1DIdentity :: LUTSize -> LUT1D
lut1DIdentity size =
  let n = lutSizeToInt size
      entries = generateRamp n
  in LUT1D
    { red: entries
    , green: entries
    , blue: entries
    , metadata: defaultMetadata { title = "Identity" }
    }

-- | Create 1D LUT from separate curve functions
lut1DFromCurves 
  :: LUTSize 
  -> (Number -> Number)  -- ^ Red curve function
  -> (Number -> Number)  -- ^ Green curve function
  -> (Number -> Number)  -- ^ Blue curve function
  -> LUT1D
lut1DFromCurves size redFn greenFn blueFn =
  let n = lutSizeToInt size
      inputs = generateRamp n
      redOut = map (\x -> clamp01 (redFn x)) inputs
      greenOut = map (\x -> clamp01 (greenFn x)) inputs
      blueOut = map (\x -> clamp01 (blueFn x)) inputs
  in LUT1D
    { red: redOut
    , green: greenOut
    , blue: blueOut
    , metadata: defaultMetadata { title = "Generated Curves" }
    }

-- | Get LUT1D size (number of entries per channel)
lut1DSize :: LUT1D -> Int
lut1DSize (LUT1D lut) = length lut.red

-- | Sample 1D LUT at position (0.0-1.0)
sample1D :: LUT1D -> Number -> Number -> Number -> { r :: Number, g :: Number, b :: Number }
sample1D lut@(LUT1D lutRec) r g b =
  { r: sample1DChannel lutRec.red r lut
  , g: sample1DChannel lutRec.green g lut
  , b: sample1DChannel lutRec.blue b lut
  }

-- | Sample a single channel from 1D LUT with linear interpolation
sample1DChannel :: Array Number -> Number -> LUT1D -> Number
sample1DChannel channelData inputVal _ =
  let clamped = clamp01 inputVal
      n = length channelData
      maxIdx = n - 1
      scaledPos = clamped * toNumber maxIdx
      lowIdx = floor scaledPos
      highIdx = if lowIdx >= maxIdx then maxIdx else lowIdx + 1
      frac = scaledPos - toNumber lowIdx
      lowVal = fromMaybe 0.0 (index channelData lowIdx)
      highVal = fromMaybe 0.0 (index channelData highIdx)
  in lerp lowVal highVal frac

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // 3d lookup table
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Lookup Table (color cube)
-- |
-- | A 3D LUT maps any input RGB to any output RGB, allowing full color
-- | manipulation. The cube is stored as a flat array in RGB order
-- | (R varies fastest, then G, then B).
-- |
-- | Total entries = size^3 * 3 (RGB triplets)
newtype LUT3D = LUT3D
  { data :: Array Number     -- ^ Flat array: [R,G,B, R,G,B, ...] 
  , size :: Int              -- ^ Cube edge size (17, 33, or 65)
  , metadata :: LUTMetadata  -- ^ LUT metadata
  }

derive instance eqLUT3D :: Eq LUT3D

instance showLUT3D :: Show LUT3D where
  show (LUT3D lut) = "LUT3D[" <> lut.metadata.title <> ", " 
    <> show lut.size <> "x" <> show lut.size <> "x" <> show lut.size <> "]"

-- | Create a 3D LUT from flat data array
lut3D :: Int -> Array Number -> LUTMetadata -> LUT3D
lut3D size lutData meta = LUT3D
  { data: map clamp01 lutData
  , size
  , metadata: meta
  }

-- | Create identity 3D LUT (no change)
lut3DIdentity :: LUT3DSize -> LUT3D
lut3DIdentity size =
  let n = lut3DSizeToInt size
      -- Generate identity cube: output RGB = input RGB (n^3 * 3 entries total)
      lutData = generateIdentityCube n
  in LUT3D
    { data: lutData
    , size: n
    , metadata: defaultMetadata { title = "Identity 3D" }
    }

-- | Get LUT3D size (cube edge length)
lut3DSize :: LUT3D -> Int
lut3DSize (LUT3D lut) = lut.size

-- | Sample 3D LUT at position with trilinear interpolation
-- |
-- | Input RGB values should be 0.0-1.0
sample3D :: LUT3D -> Number -> Number -> Number -> { r :: Number, g :: Number, b :: Number }
sample3D (LUT3D lut) inR inG inB =
  let n = lut.size
      maxIdx = n - 1
      
      -- Scale inputs to LUT indices
      rScaled = clamp01 inR * toNumber maxIdx
      gScaled = clamp01 inG * toNumber maxIdx
      bScaled = clamp01 inB * toNumber maxIdx
      
      -- Get integer indices
      r0 = floor rScaled
      g0 = floor gScaled
      b0 = floor bScaled
      r1 = if r0 >= maxIdx then maxIdx else r0 + 1
      g1 = if g0 >= maxIdx then maxIdx else g0 + 1
      b1 = if b0 >= maxIdx then maxIdx else b0 + 1
      
      -- Fractional parts for interpolation
      rFrac = rScaled - toNumber r0
      gFrac = gScaled - toNumber g0
      bFrac = bScaled - toNumber b0
      
      -- Get 8 corner values
      c000 = getVoxel n lut.data r0 g0 b0
      c100 = getVoxel n lut.data r1 g0 b0
      c010 = getVoxel n lut.data r0 g1 b0
      c110 = getVoxel n lut.data r1 g1 b0
      c001 = getVoxel n lut.data r0 g0 b1
      c101 = getVoxel n lut.data r1 g0 b1
      c011 = getVoxel n lut.data r0 g1 b1
      c111 = getVoxel n lut.data r1 g1 b1
      
      -- Trilinear interpolation
      c00 = lerpRGB c000 c100 rFrac
      c01 = lerpRGB c001 c101 rFrac
      c10 = lerpRGB c010 c110 rFrac
      c11 = lerpRGB c011 c111 rFrac
      c0 = lerpRGB c00 c10 gFrac
      c1 = lerpRGB c01 c11 gFrac
  in lerpRGB c0 c1 bFrac

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // lut manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Invert a 1D LUT (approximate - requires monotonic curves)
invertLUT1D :: LUT1D -> LUT1D
invertLUT1D (LUT1D lut) = LUT1D
  { red: invertChannel lut.red
  , green: invertChannel lut.green
  , blue: invertChannel lut.blue
  , metadata: lut.metadata { title = lut.metadata.title <> " (Inverted)" }
  }
  where
  invertChannel arr = reverse arr

-- | Compose two 1D LUTs (apply first, then second)
composeLUT1D :: LUT1D -> LUT1D -> LUT1D
composeLUT1D (LUT1D lut1) lut2 = 
  let composeChannel arr = map (\v -> sample1DChannel arr v lut2) (generateRamp (length arr))
  in LUT1D
    { red: composeChannel lut1.red
    , green: composeChannel lut1.green
    , blue: composeChannel lut1.blue
    , metadata: defaultMetadata 
        { title = lut1.metadata.title <> " + " <> let LUT1D l2 = lut2 in l2.metadata.title }
    }

-- | Resize a 1D LUT to different resolution
resizeLUT1D :: LUTSize -> LUT1D -> LUT1D
resizeLUT1D newSize lut@(LUT1D lutData) =
  let n = lutSizeToInt newSize
      inputs = generateRamp n
      resizeChannel oldArr = map (\v -> sample1DChannel oldArr v lut) inputs
  in LUT1D
    { red: resizeChannel lutData.red
    , green: resizeChannel lutData.green
    , blue: resizeChannel lutData.blue
    , metadata: lutData.metadata
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // format detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Known LUT file formats
data LUTFormat
  = CubeFormat      -- ^ .cube (Adobe/Blackmagic)
  | ThreeDLFormat   -- ^ .3dl (Lustre)
  | CLFFormat       -- ^ .clf (Common LUT Format, ACES)
  | LOOKFormat      -- ^ .look (ACES)
  | CTLFormat       -- ^ .ctl (Color Transform Language)
  | UnknownFormat

derive instance eqLUTFormat :: Eq LUTFormat

instance showLUTFormat :: Show LUTFormat where
  show CubeFormat = ".cube"
  show ThreeDLFormat = ".3dl"
  show CLFFormat = ".clf"
  show LOOKFormat = ".look"
  show CTLFormat = ".ctl"
  show UnknownFormat = "unknown"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to 0.0-1.0
clamp01 :: Number -> Number
clamp01 = Bounded.clampNumber 0.0 1.0

-- | Linear interpolation between two values
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Linear interpolation between two RGB values
lerpRGB 
  :: { r :: Number, g :: Number, b :: Number } 
  -> { r :: Number, g :: Number, b :: Number } 
  -> Number 
  -> { r :: Number, g :: Number, b :: Number }
lerpRGB a b t =
  { r: lerp a.r b.r t
  , g: lerp a.g b.g t
  , b: lerp a.b b.b t
  }

-- | Generate linear ramp from 0.0 to 1.0
generateRamp :: Int -> Array Number
generateRamp n = mapWithIndex (\i _ -> toNumber i / toNumber (n - 1)) (replicate n 0.0)

-- | Generate identity 3D LUT cube data
generateIdentityCube :: Int -> Array Number
generateIdentityCube n =
  let maxIdx = toNumber (n - 1)
      -- Generate all RGB triplets where output = input
      generateEntry idx =
        let b = idx / (n * n)
            g = (idx / n) `mod` n
            r = idx `mod` n
        in [ toNumber r / maxIdx
           , toNumber g / maxIdx
           , toNumber b / maxIdx
           ]
      -- Flatten the array
      indices = mapWithIndex (\i _ -> i) (replicate (n * n * n) 0)
  in join (map generateEntry indices)
  where
  mod a b = a - (a / b) * b
  join arrs = foldlArray (\acc arr -> acc <> arr) [] arrs
  foldlArray f init arr = case index arr 0 of
    Nothing -> init
    Just first -> foldlArrayGo f (f init first) arr 1
  foldlArrayGo f acc arr idx = case index arr idx of
    Nothing -> acc
    Just val -> foldlArrayGo f (f acc val) arr (idx + 1)

-- | Get RGB triplet from voxel position
getVoxel :: Int -> Array Number -> Int -> Int -> Int -> { r :: Number, g :: Number, b :: Number }
getVoxel n lutData ri gi bi =
  let idx = (bi * n * n + gi * n + ri) * 3
  in { r: fromMaybe 0.0 (index lutData idx)
     , g: fromMaybe 0.0 (index lutData (idx + 1))
     , b: fromMaybe 0.0 (index lutData (idx + 2))
     }
