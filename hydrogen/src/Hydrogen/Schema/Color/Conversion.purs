-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // color // conversion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color space conversions for picker/wheel synchronization.
-- |
-- | **BIDIRECTIONAL SYNC REQUIREMENT:**
-- | When a user adjusts any color property (hue slider, RGB input, hex code),
-- | ALL representations must update synchronously. This module provides the
-- | mathematical conversions to maintain consistency across color spaces.
-- |
-- | **Use case: Playground color picker**
-- | 1. User adjusts Hue slider (0-359)
-- | 2. HSL updates → rgbToHsl converts → RGB updates
-- | 3. RGB updates → rgbToHex converts → Hex display updates
-- | 4. All views show the same color, zero drift
-- |
-- | **Color space conversions:**
-- | - HSL ↔ RGB (color wheel ↔ display values)
-- | - RGB ↔ CMYK (screen ↔ print)
-- | - RGB ↔ Hex (code ↔ human-readable)
-- | - Kelvin → RGB (temperature ↔ display)
-- |
-- | **Billion-agent scale requirement:**
-- | All conversions use industry-standard algorithms. Two agents converting
-- | the same color will get identical results (within floating point precision).

module Hydrogen.Schema.Color.Conversion
  ( -- * HSL ↔ RGB
    hslToRgb
  , rgbToHsl
  
  -- * RGB ↔ CMYK
  , rgbToCmyk
  , cmykToRgb
  
  -- * RGB ↔ Hex
  , rgbToHex
  , hexToRgb
  
  -- * RGB ↔ XYZ (device-dependent ↔ device-independent)
  , rgbToXyz
  , xyzToRgb
  
  -- * XYZ ↔ LAB (device-independent ↔ perceptual)
  , xyzToLab
  , labToXyz
  
  -- * RGB ↔ LAB (convenience, goes through XYZ)
  , rgbToLab
  , labToRgb
  
  -- * RGB ↔ LCH (convenience, goes through XYZ → LAB)
  , rgbToLch
  , lchToRgb
  
  -- * Kelvin → RGB
  , kelvinToRgb
  
  -- * RGB ↔ OKLAB (modern perceptual)
  , rgbToOklab
  , oklabToRgb
  
  -- * OKLAB ↔ OKLCH (rectangular ↔ cylindrical)
  , oklabToOklch
  , oklchToOklab
  
  -- * RGB ↔ OKLCH (convenience)
  , rgbToOklch
  , oklchToRgb
  
  -- * RGB ↔ HWB (CSS4)
  , rgbToHwb
  , hwbToRgb
  
  -- * RGB ↔ YUV (video)
  , rgbToYuv
  , yuvToRgb
  
  -- * Record Serialization (for backend persistence)
  , rgbToRecord
  , rgbFromRecord
  , hslToRecord
  , hslFromRecord
  , cmykToRecord
  , cmykFromRecord
  , labToRecord
  , labFromRecord
  , lchToRecord
  , lchFromRecord
  , xyzToRecord
  , xyzFromRecord
  ) where

import Prelude
  ( max
  , min
  , mod
  , negate
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  , (>>>)
  , (<<<)
  )

import Data.Int as Int
import Data.Number (abs, pow)
import Data.String (take, drop)
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.CMYK as CMYK
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Cyan as Cyan
import Hydrogen.Schema.Color.Magenta as Magenta
import Hydrogen.Schema.Color.Yellow as Yellow
import Hydrogen.Schema.Color.Key as Key
import Hydrogen.Schema.Color.Kelvin as K
import Hydrogen.Schema.Color.XYZ as XYZ
import Hydrogen.Schema.Color.LAB as LAB
import Hydrogen.Schema.Color.LCH as LCH
import Hydrogen.Schema.Color.OKLAB as OKLAB
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.HWB as HWB
import Hydrogen.Schema.Color.YUV as YUV

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // hsl ↔ rgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert HSL to RGB
-- |
-- | Uses standard HSL → RGB algorithm:
-- | 1. Convert HSL percentages to 0-1 range
-- | 2. Calculate chroma and intermediate values
-- | 3. Map to RGB cube
-- |
-- | ```purescript
-- | hslToRgb (HSL.hsl 0 100 50)     -- Pure red: RGB(255, 0, 0)
-- | hslToRgb (HSL.hsl 120 100 50)   -- Pure green: RGB(0, 255, 0)
-- | hslToRgb (HSL.hsl 240 100 50)   -- Pure blue: RGB(0, 0, 255)
-- | ```
hslToRgb :: HSL.HSL -> RGB.RGB
hslToRgb hsl =
  let
    h = Int.toNumber (Hue.unwrap (HSL.hue hsl)) / 360.0
    s = Int.toNumber (Sat.unwrap (HSL.saturation hsl)) / 100.0
    l = Int.toNumber (Light.unwrap (HSL.lightness hsl)) / 100.0
    
    -- Calculate chroma
    c = (1.0 - abs (2.0 * l - 1.0)) * s
    x = c * (1.0 - abs (mod' (h * 6.0) 2.0 - 1.0))
    m = l - c / 2.0
    
    -- Map to RGB based on hue sector
    { r: r', g: g', b: b' } = 
      if h < (1.0 / 6.0) then { r: c, g: x, b: 0.0 }
      else if h < (2.0 / 6.0) then { r: x, g: c, b: 0.0 }
      else if h < (3.0 / 6.0) then { r: 0.0, g: c, b: x }
      else if h < (4.0 / 6.0) then { r: 0.0, g: x, b: c }
      else if h < (5.0 / 6.0) then { r: x, g: 0.0, b: c }
      else { r: c, g: 0.0, b: x }
    
    -- Convert to 0-255 range
    r = Int.round ((r' + m) * 255.0)
    g = Int.round ((g' + m) * 255.0)
    b = Int.round ((b' + m) * 255.0)
  in
    RGB.rgb r g b

-- | Convert RGB to HSL
-- |
-- | Uses standard RGB → HSL algorithm:
-- | 1. Normalize RGB to 0-1 range
-- | 2. Find min, max, delta
-- | 3. Calculate hue, saturation, lightness
-- |
-- | ```purescript
-- | rgbToHsl (RGB.rgb 255 0 0)   -- HSL(0°, 100%, 50%) - red
-- | rgbToHsl (RGB.rgb 128 128 128) -- HSL(0°, 0%, 50%) - gray
-- | ```
rgbToHsl :: RGB.RGB -> HSL.HSL
rgbToHsl rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    cmax = max r (max g b)
    cmin = min r (min g b)
    delta = cmax - cmin
    
    -- Calculate lightness
    l = (cmax + cmin) / 2.0
    
    -- Calculate saturation
    s = if delta == 0.0
          then 0.0
          else delta / (1.0 - abs (2.0 * l - 1.0))
    
    -- Calculate hue
    h' = if delta == 0.0
          then 0.0
          else if cmax == r
            then mod' ((g - b) / delta) 6.0
            else if cmax == g
              then ((b - r) / delta) + 2.0
              else ((r - g) / delta) + 4.0
    
    h = h' * 60.0
    
    -- Convert to integer percentages
    hInt = Int.round (if h < 0.0 then h + 360.0 else h)
    sInt = Int.round (s * 100.0)
    lInt = Int.round (l * 100.0)
  in
    HSL.hsl hInt sInt lInt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // rgb ↔ cmyk
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to CMYK (screen to print)
-- |
-- | Uses standard RGB → CMYK algorithm:
-- | 1. Normalize RGB to 0-1 range
-- | 2. Calculate K (black key) = 1 - max(R, G, B)
-- | 3. If K = 1 (pure black), C=M=Y=0
-- | 4. Otherwise: C = (1-R-K)/(1-K), same for M and Y
-- |
-- | ```purescript
-- | rgbToCmyk (RGB.rgb 255 0 0)    -- CMYK(0, 100, 100, 0) - red
-- | rgbToCmyk (RGB.rgb 0 0 0)      -- CMYK(0, 0, 0, 100) - black
-- | ```
rgbToCmyk :: RGB.RGB -> CMYK.CMYK
rgbToCmyk rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    k = 1.0 - max r (max g b)
    
    -- If pure black, CMY are 0
    { c, m, y } = 
      if k >= 1.0 
        then { c: 0.0, m: 0.0, y: 0.0 }
        else 
          { c: (1.0 - r - k) / (1.0 - k)
          , m: (1.0 - g - k) / (1.0 - k)
          , y: (1.0 - b - k) / (1.0 - k)
          }
    
    -- Convert to percentages
    cInt = Int.round (c * 100.0)
    mInt = Int.round (m * 100.0)
    yInt = Int.round (y * 100.0)
    kInt = Int.round (k * 100.0)
  in
    CMYK.cmyk cInt mInt yInt kInt

-- | Convert CMYK to RGB (print to screen)
-- |
-- | Uses standard CMYK → RGB algorithm:
-- | 1. R = 255 * (1 - C) * (1 - K)
-- | 2. G = 255 * (1 - M) * (1 - K)
-- | 3. B = 255 * (1 - Y) * (1 - K)
-- |
-- | ```purescript
-- | cmykToRgb (CMYK.cmyk 0 100 100 0)  -- RGB(255, 0, 0) - red
-- | cmykToRgb (CMYK.cmyk 0 0 0 100)    -- RGB(0, 0, 0) - black
-- | ```
cmykToRgb :: CMYK.CMYK -> RGB.RGB
cmykToRgb cmyk =
  let
    c = Int.toNumber (Cyan.unwrap (CMYK.cyan cmyk)) / 100.0
    m = Int.toNumber (Magenta.unwrap (CMYK.magenta cmyk)) / 100.0
    y = Int.toNumber (Yellow.unwrap (CMYK.yellow cmyk)) / 100.0
    k = Int.toNumber (Key.unwrap (CMYK.key cmyk)) / 100.0
    
    r = Int.round (255.0 * (1.0 - c) * (1.0 - k))
    g = Int.round (255.0 * (1.0 - m) * (1.0 - k))
    b = Int.round (255.0 * (1.0 - y) * (1.0 - k))
  in
    RGB.rgb r g b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ hex
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to hex string
-- |
-- | Returns 6-character hex string (no # prefix).
-- | Agents can prepend # if needed for CSS/HTML contexts.
-- |
-- | ```purescript
-- | rgbToHex (RGB.rgb 255 0 0)     -- "FF0000"
-- | rgbToHex (RGB.rgb 128 128 128) -- "808080"
-- | ```
rgbToHex :: RGB.RGB -> String
rgbToHex rgb =
  let
    r = Ch.unwrap (RGB.red rgb)
    g = Ch.unwrap (RGB.green rgb)
    b = Ch.unwrap (RGB.blue rgb)
  in
    toHex r <> toHex g <> toHex b

-- | Convert hex string to RGB
-- |
-- | Accepts formats:
-- | - "FF0000" (6 chars)
-- | - "#FF0000" (7 chars with #)
-- | - "F00" (3 chars, expands to FF0000)
-- | - "#F00" (4 chars with #)
-- |
-- | Invalid hex returns black RGB(0, 0, 0).
-- |
-- | ```purescript
-- | hexToRgb "FF0000"   -- RGB(255, 0, 0)
-- | hexToRgb "#FF0000"  -- RGB(255, 0, 0)
-- | hexToRgb "F00"      -- RGB(255, 0, 0)
-- | hexToRgb "invalid"  -- RGB(0, 0, 0) - fallback
-- | ```
hexToRgb :: String -> RGB.RGB
hexToRgb hex =
  let
    -- Strip # if present
    cleaned = if take 1 hex == "#" then drop 1 hex else hex
    
    -- Expand 3-char format to 6-char
    expanded = case toCharArray cleaned of
      [ch1, ch2, ch3] -> fromCharArray [ch1, ch1, ch2, ch2, ch3, ch3]
      _ -> cleaned
    
    -- Parse hex components
    r = fromHex (take 2 expanded)
    g = fromHex (take 2 (drop 2 expanded))
    b = fromHex (take 2 (drop 4 expanded))
  in
    RGB.rgb r g b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ xyz
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to XYZ (device-dependent to device-independent)
-- |
-- | Assumes sRGB color space with D65 white point.
-- | Steps:
-- | 1. Convert RGB 0-255 to 0-1
-- | 2. Apply inverse sRGB companding (gamma correction)
-- | 3. Apply sRGB → XYZ matrix transformation
-- |
-- | ```purescript
-- | rgbToXyz (RGB.rgb 255 255 255)  -- D65 white point
-- | rgbToXyz (RGB.rgb 0 0 0)        -- Black
-- | ```
rgbToXyz :: RGB.RGB -> XYZ.XYZ
rgbToXyz rgb =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red rgb)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green rgb)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue rgb)) / 255.0
    
    -- Apply inverse sRGB companding (gamma correction)
    r' = if r <= 0.04045 then r / 12.92 else pow ((r + 0.055) / 1.055) 2.4
    g' = if g <= 0.04045 then g / 12.92 else pow ((g + 0.055) / 1.055) 2.4
    b' = if b <= 0.04045 then b / 12.92 else pow ((b + 0.055) / 1.055) 2.4
    
    -- Apply sRGB → XYZ matrix (D65)
    x = r' * 0.4124564 + g' * 0.3575761 + b' * 0.1804375
    y = r' * 0.2126729 + g' * 0.7151522 + b' * 0.0721750
    z = r' * 0.0193339 + g' * 0.1191920 + b' * 0.9503041
  in
    XYZ.xyz x y z

-- | Convert XYZ to RGB (device-independent to device-dependent)
-- |
-- | Assumes sRGB color space with D65 white point.
-- | Steps:
-- | 1. Apply XYZ → sRGB matrix transformation
-- | 2. Apply sRGB companding (gamma correction)
-- | 3. Convert 0-1 to RGB 0-255
-- |
-- | ```purescript
-- | xyzToRgb XYZ.d65White  -- RGB(255, 255, 255)
-- | ```
xyzToRgb :: XYZ.XYZ -> RGB.RGB
xyzToRgb xyzColor =
  let
    rec = XYZ.toRecord xyzColor
    x = rec.x
    y = rec.y
    z = rec.z
    
    -- Apply XYZ → sRGB matrix (D65)
    r' = x * 3.2404542 + y * (-1.5371385) + z * (-0.4985314)
    g' = x * (-0.9692660) + y * 1.8760108 + z * 0.0415560
    b' = x * 0.0556434 + y * (-0.2040259) + z * 1.0572252
    
    -- Apply sRGB companding (gamma correction)
    r = if r' <= 0.0031308 then r' * 12.92 else 1.055 * pow r' (1.0 / 2.4) - 0.055
    g = if g' <= 0.0031308 then g' * 12.92 else 1.055 * pow g' (1.0 / 2.4) - 0.055
    b = if b' <= 0.0031308 then b' * 12.92 else 1.055 * pow b' (1.0 / 2.4) - 0.055
    
    -- Clamp and convert to 0-255
    rInt = Int.round (clamp01 r * 255.0)
    gInt = Int.round (clamp01 g * 255.0)
    bInt = Int.round (clamp01 b * 255.0)
  in
    RGB.rgb rInt gInt bInt
  where
    clamp01 n
      | n < 0.0 = 0.0
      | n > 1.0 = 1.0
      | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // xyz ↔ lab
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert XYZ to LAB (device-independent to perceptual)
-- |
-- | Uses D65 white point and CIE standard formulas.
-- | This is where the perceptual uniformity is created.
-- |
-- | ```purescript
-- | xyzToLab XYZ.d65White  -- LAB(100, 0, 0) - white
-- | ```
xyzToLab :: XYZ.XYZ -> LAB.LAB
xyzToLab xyzColor =
  let
    rec = XYZ.toRecord xyzColor
    
    -- Normalize by D65 white point
    xr = rec.x / 0.95047
    yr = rec.y / 1.00000
    zr = rec.z / 1.08883
    
    -- Apply CIE LAB function
    fx = labF xr
    fy = labF yr
    fz = labF zr
    
    -- Calculate L*, a*, b*
    l = 116.0 * fy - 16.0
    a = 500.0 * (fx - fy)
    b = 200.0 * (fy - fz)
  in
    LAB.lab l a b
  where
    -- CIE LAB function (piecewise)
    labF t = if t > 0.008856
               then pow t (1.0 / 3.0)
               else (7.787 * t) + (16.0 / 116.0)

-- | Convert LAB to XYZ (perceptual to device-independent)
-- |
-- | Inverse of xyzToLab.
-- |
-- | ```purescript
-- | labToXyz (LAB.lab 100.0 0.0 0.0)  -- D65 white point
-- | ```
labToXyz :: LAB.LAB -> XYZ.XYZ
labToXyz labColor =
  let
    rec = LAB.toRecord labColor
    l = rec.l
    a = rec.a
    b = rec.b
    
    -- Calculate intermediate values
    fy = (l + 16.0) / 116.0
    fx = a / 500.0 + fy
    fz = fy - b / 200.0
    
    -- Apply inverse CIE LAB function
    xr = labFInv fx
    yr = labFInv fy
    zr = labFInv fz
    
    -- Denormalize by D65 white point
    x = xr * 0.95047
    y = yr * 1.00000
    z = zr * 1.08883
  in
    XYZ.xyz x y z
  where
    -- Inverse CIE LAB function (piecewise)
    labFInv t = 
      let t3 = t * t * t
      in if t3 > 0.008856
           then t3
           else (t - 16.0 / 116.0) / 7.787

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // rgb ↔ lab (convenience)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to LAB (convenience function)
-- |
-- | Goes through XYZ: RGB → XYZ → LAB
-- |
-- | ```purescript
-- | rgbToLab (RGB.rgb 255 0 0)  -- Red in perceptual space
-- | ```
rgbToLab :: RGB.RGB -> LAB.LAB
rgbToLab = rgbToXyz >>> xyzToLab

-- | Convert LAB to RGB (convenience function)
-- |
-- | Goes through XYZ: LAB → XYZ → RGB
-- |
-- | ```purescript
-- | labToRgb (LAB.lab 50.0 80.0 67.0)  -- Perceptual red to display RGB
-- | ```
labToRgb :: LAB.LAB -> RGB.RGB
labToRgb = labToXyz >>> xyzToRgb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // rgb ↔ lch (convenience)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to LCH (convenience function)
-- |
-- | Goes through XYZ and LAB: RGB → XYZ → LAB → LCH
-- |
-- | ```purescript
-- | rgbToLch (RGB.rgb 255 0 0)  -- Red in cylindrical perceptual space
-- | ```
rgbToLch :: RGB.RGB -> LCH.LCH
rgbToLch = rgbToLab >>> LCH.labToLch

-- | Convert LCH to RGB (convenience function)
-- |
-- | Goes through LAB and XYZ: LCH → LAB → XYZ → RGB
-- |
-- | ```purescript
-- | lchToRgb (LCH.lch 50.0 100.0 0.0)  -- Perceptual cylindrical to display RGB
-- | ```
lchToRgb :: LCH.LCH -> RGB.RGB
lchToRgb = LCH.lchToLab >>> labToRgb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // kelvin → rgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Kelvin color temperature to RGB
-- |
-- | Re-export from Kelvin module for convenience.
-- | Uses Tanner Helland's algorithm for accurate temperature conversion.
-- |
-- | ```purescript
-- | kelvinToRgb (K.kelvin 2700)  -- Warm tungsten light
-- | kelvinToRgb (K.kelvin 6500)  -- Cool daylight
-- | ```
kelvinToRgb :: K.Kelvin -> RGB.RGB
kelvinToRgb = K.kelvinToRgb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Floating point modulo
mod' :: Number -> Number -> Number
mod' a b = a - b * Int.toNumber (Int.floor (a / b))

-- | Convert int to 2-character hex string
toHex :: Int -> String
toHex n =
  let
    hi = n / 16
    lo = n `mod` 16
  in
    hexDigit hi <> hexDigit lo

-- | Convert digit to hex character
hexDigit :: Int -> String
hexDigit n = case n of
  0 -> "0"
  1 -> "1"
  2 -> "2"
  3 -> "3"
  4 -> "4"
  5 -> "5"
  6 -> "6"
  7 -> "7"
  8 -> "8"
  9 -> "9"
  10 -> "A"
  11 -> "B"
  12 -> "C"
  13 -> "D"
  14 -> "E"
  15 -> "F"
  _ -> "0"

-- | Parse 2-character hex string to int
fromHex :: String -> Int
fromHex str = case toCharArray str of
  [hi, lo] -> hexValue hi * 16 + hexValue lo
  [c] -> hexValue c
  _ -> 0

-- | Get numeric value of hex character
hexValue :: Char -> Int
hexValue c = case c of
  '0' -> 0
  '1' -> 1
  '2' -> 2
  '3' -> 3
  '4' -> 4
  '5' -> 5
  '6' -> 6
  '7' -> 7
  '8' -> 8
  '9' -> 9
  'A' -> 10
  'B' -> 11
  'C' -> 12
  'D' -> 13
  'E' -> 14
  'F' -> 15
  'a' -> 10
  'b' -> 11
  'c' -> 12
  'd' -> 13
  'e' -> 14
  'f' -> 15
  _ -> 0
-- ═════════════════════════════════════════════════════════════════════════════
--                                     // record // serialization // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → Record (for JSON serialization / backend persistence)
rgbToRecord :: RGB.RGB -> { r :: Int, g :: Int, b :: Int }
rgbToRecord = RGB.rgbToRecord

-- | Record → RGB (from JSON deserialization / backend)
rgbFromRecord :: { r :: Int, g :: Int, b :: Int } -> RGB.RGB
rgbFromRecord = RGB.rgbFromRecord

-- | HSL → Record (for JSON serialization / backend persistence)
hslToRecord :: HSL.HSL -> { h :: Int, s :: Int, l :: Int }
hslToRecord = HSL.hslToRecord

-- | Record → HSL (from JSON deserialization / backend)
hslFromRecord :: { h :: Int, s :: Int, l :: Int } -> HSL.HSL
hslFromRecord = HSL.hslFromRecord

-- | CMYK → Record (for JSON serialization / backend persistence)
cmykToRecord :: CMYK.CMYK -> { c :: Int, m :: Int, y :: Int, k :: Int }
cmykToRecord = CMYK.cmykToRecord

-- | Record → CMYK (from JSON deserialization / backend)
cmykFromRecord :: { c :: Int, m :: Int, y :: Int, k :: Int } -> CMYK.CMYK
cmykFromRecord = CMYK.cmykFromRecord

-- | LAB → Record (for JSON serialization / backend persistence)
labToRecord :: LAB.LAB -> { l :: Number, a :: Number, b :: Number }
labToRecord = LAB.labToRecord

-- | Record → LAB (from JSON deserialization / backend)
labFromRecord :: { l :: Number, a :: Number, b :: Number } -> LAB.LAB
labFromRecord = LAB.labFromRecord

-- | LCH → Record (for JSON serialization / backend persistence)
lchToRecord :: LCH.LCH -> { l :: Number, c :: Number, h :: Number }
lchToRecord = LCH.lchToRecord

-- | Record → LCH (from JSON deserialization / backend)
lchFromRecord :: { l :: Number, c :: Number, h :: Number } -> LCH.LCH
lchFromRecord = LCH.lchFromRecord

-- | XYZ → Record (for JSON serialization / backend persistence)
xyzToRecord :: XYZ.XYZ -> { x :: Number, y :: Number, z :: Number }
xyzToRecord = XYZ.xyzToRecord

-- | Record → XYZ (from JSON deserialization / backend)
xyzFromRecord :: { x :: Number, y :: Number, z :: Number } -> XYZ.XYZ
xyzFromRecord = XYZ.xyzFromRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // rgb ↔ oklab
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → OKLAB (modern perceptual uniform space)
-- | Uses linear RGB → LMS → OKLAB transformation
rgbToOklab :: RGB.RGB -> OKLAB.OKLAB
rgbToOklab rgb =
  let
    -- Convert to linear RGB (remove sRGB gamma)
    r = toLinear (Ch.toNumber (RGB.red rgb) / 255.0)
    g = toLinear (Ch.toNumber (RGB.green rgb) / 255.0)
    b = toLinear (Ch.toNumber (RGB.blue rgb) / 255.0)
    
    -- Linear RGB → LMS (cone response)
    l = 0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b
    m = 0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b
    s = 0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b
    
    -- LMS → OKLAB (cube root for perceptual uniformity)
    l' = cbrt l
    m' = cbrt m
    s' = cbrt s
    
    okL = 0.2104542553 * l' + 0.7936177850 * m' - 0.0040720468 * s'
    okA = 1.9779984951 * l' - 2.4285922050 * m' + 0.4505937099 * s'
    okB = 0.0259040371 * l' + 0.7827717662 * m' - 0.8086757660 * s'
  in
    OKLAB.oklab okL okA okB
  where
  -- sRGB to linear RGB
  toLinear c
    | c <= 0.04045 = c / 12.92
    | otherwise = pow ((c + 0.055) / 1.055) 2.4
  
  -- Cube root (∛x)
  cbrt x = pow x (1.0 / 3.0)

-- | OKLAB → RGB
oklabToRgb :: OKLAB.OKLAB -> RGB.RGB
oklabToRgb oklab =
  let
    okL = OKLAB.unwrapOkL (OKLAB.okL oklab)
    okA = OKLAB.unwrapOkA (OKLAB.okA oklab)
    okB = OKLAB.unwrapOkB (OKLAB.okB oklab)
    
    -- OKLAB → LMS (inverse)
    l' = okL + 0.3963377774 * okA + 0.2158037573 * okB
    m' = okL - 0.1055613458 * okA - 0.0638541728 * okB
    s' = okL - 0.0894841775 * okA - 1.2914855480 * okB
    
    -- LMS → Linear RGB (cube and inverse matrix)
    l = l' * l' * l'
    m = m' * m' * m'
    s = s' * s' * s'
    
    r = 4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s
    g = (-1.2684380046) * l + 2.6097574011 * m - 0.3413193965 * s
    b = (-0.0041960863) * l - 0.7034186147 * m + 1.7076147010 * s
    
    -- Linear RGB → sRGB (apply gamma)
    rGamma = toGamma r
    gGamma = toGamma g
    bGamma = toGamma b
  in
    RGB.rgb (Int.round (rGamma * 255.0)) (Int.round (gGamma * 255.0)) (Int.round (bGamma * 255.0))
  where
  -- Linear to sRGB gamma
  toGamma c
    | c <= 0.0031308 = 12.92 * c
    | otherwise = 1.055 * pow c (1.0 / 2.4) - 0.055

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // oklab ↔ oklch
-- ═════════════════════════════════════════════════════════════════════════════

-- | OKLAB → OKLCH (rectangular → cylindrical)
oklabToOklch :: OKLAB.OKLAB -> OKLCH.OKLCH
oklabToOklch oklab =
  let
    okL = OKLAB.unwrapOkL (OKLAB.okL oklab)
    okA = OKLAB.unwrapOkA (OKLAB.okA oklab)
    okB = OKLAB.unwrapOkB (OKLAB.okB oklab)
    
    -- Chroma (distance from neutral)
    c = sqrt (okA * okA + okB * okB)
    
    -- Hue (angle in degrees)
    h = atan2 okB okA * 180.0 / pi
    hNormalized = if h < 0.0 then h + 360.0 else h
  in
    OKLCH.oklch okL c (Int.round hNormalized)
  where
  atan2 y x = Math.atan2 y x
  sqrt x = Math.sqrt x
  pi = Math.pi

-- | OKLCH → OKLAB (cylindrical → rectangular)
oklchToOklab :: OKLCH.OKLCH -> OKLAB.OKLAB
oklchToOklab oklch =
  let
    okL = OKLAB.unwrapOkL (OKLCH.oklchL oklch)
    c = OKLCH.unwrapChroma (OKLCH.chroma oklch)
    h = Int.toNumber (Hue.unwrap (OKLCH.hue oklch))
    
    -- Convert hue to radians
    hRad = h * pi / 180.0
    
    -- Chroma and hue → a,b
    okA = c * cos hRad
    okB = c * sin hRad
  in
    OKLAB.oklab okL okA okB
  where
  cos x = Math.cos x
  sin x = Math.sin x
  pi = Math.pi

-- | RGB → OKLCH (convenience)
rgbToOklch :: RGB.RGB -> OKLCH.OKLCH
rgbToOklch = oklabToOklch <<< rgbToOklab

-- | OKLCH → RGB (convenience)
oklchToRgb :: OKLCH.OKLCH -> RGB.RGB
oklchToRgb = oklabToRgb <<< oklchToOklab

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ hwb
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → HWB (direct conversion)
-- |
-- | **Algorithm:**
-- | - Hue: same as HSL hue (derived from RGB)
-- | - Whiteness: min(R, G, B) / 255 as percentage
-- | - Blackness: 1 - max(R, G, B) / 255 as percentage
-- |
-- | This is a direct calculation, not via HSL intermediate.
rgbToHwb :: RGB.RGB -> HWB.HWB
rgbToHwb rgb =
  let
    r = Ch.unwrap (RGB.red rgb)
    g = Ch.unwrap (RGB.green rgb)
    b = Ch.unwrap (RGB.blue rgb)
    
    -- Get hue from HSL (hue calculation is independent)
    hsl = rgbToHsl rgb
    h = Hue.unwrap (HSL.hue hsl)
    
    -- Direct whiteness/blackness calculation
    minVal = min3 r g b
    maxVal = max3 r g b
    
    -- Whiteness = min / 255 * 100
    wNum = Int.toNumber minVal / 255.0 * 100.0
    -- Blackness = (1 - max / 255) * 100
    bNum = (1.0 - Int.toNumber maxVal / 255.0) * 100.0
  in
    HWB.hwb h (Int.round wNum) (Int.round bNum)
  where
  min3 a b c = if a <= b && a <= c then a else if b <= c then b else c
  max3 a b c = if a >= b && a >= c then a else if b >= c then b else c

-- | HWB → RGB (direct conversion)
-- |
-- | **Algorithm:**
-- | 1. If W + B >= 100: achromatic gray = W / (W + B)
-- | 2. Otherwise: calculate pure hue RGB, then:
-- |    RGB' = RGB * (1 - W/100 - B/100) + W/100
-- |
-- | This avoids HSL intermediate for better precision.
hwbToRgb :: HWB.HWB -> RGB.RGB
hwbToRgb hwb =
  let
    h = Hue.unwrap (HWB.hue hwb)
    wInt = HWB.unwrapWhiteness (HWB.getWhiteness hwb)
    bInt = HWB.unwrapBlackness (HWB.getBlackness hwb)
    w = Int.toNumber wInt / 100.0
    b = Int.toNumber bInt / 100.0
    
    -- Normalize if w + b > 1
    total = w + b
    w' = if total > 1.0 then w / total else w
    b' = if total > 1.0 then b / total else b
  in
    if w' + b' >= 1.0
      then
        -- Achromatic case: gray
        let gray = Int.round (w' / (w' + b') * 255.0)
        in RGB.rgb gray gray gray
      else
        -- Chromatic case: get pure hue, then apply whiteness/blackness
        let
          -- Get pure hue RGB (saturation=100, lightness=50)
          pureHueRgb = hslToRgb (HSL.hsl h 100 50)
          pr = Int.toNumber (Ch.unwrap (RGB.red pureHueRgb)) / 255.0
          pg = Int.toNumber (Ch.unwrap (RGB.green pureHueRgb)) / 255.0
          pb = Int.toNumber (Ch.unwrap (RGB.blue pureHueRgb)) / 255.0
          
          -- Apply formula: RGB' = RGB * (1 - W - B) + W
          factor = 1.0 - w' - b'
          r = Int.round ((pr * factor + w') * 255.0)
          g = Int.round ((pg * factor + w') * 255.0)
          bb = Int.round ((pb * factor + w') * 255.0)
        in
          RGB.rgb r g bb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rgb ↔ yuv
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB → YUV (video color space)
rgbToYuv :: RGB.RGB -> YUV.YUV
rgbToYuv rgb =
  let
    r = Ch.toNumber (RGB.red rgb) / 255.0
    g = Ch.toNumber (RGB.green rgb) / 255.0
    b = Ch.toNumber (RGB.blue rgb) / 255.0
    
    -- ITU-R BT.601 coefficients (standard definition)
    y = 0.299 * r + 0.587 * g + 0.114 * b
    u = 0.492 * (b - y)
    v = 0.877 * (r - y)
  in
    YUV.yuv y u v

-- | YUV → RGB
yuvToRgb :: YUV.YUV -> RGB.RGB
yuvToRgb yuv =
  let
    y = YUV.unwrapLuma (YUV.getLuma yuv)
    u = YUV.unwrapU (YUV.getU yuv)
    v = YUV.unwrapV (YUV.getV yuv)
    
    -- ITU-R BT.601 inverse
    r = y + 1.140 * v
    g = y - 0.395 * u - 0.581 * v
    b = y + 2.032 * u
  in
    RGB.rgb (Int.round (r * 255.0)) (Int.round (g * 255.0)) (Int.round (b * 255.0))
