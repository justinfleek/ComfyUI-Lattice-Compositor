-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // hsv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HSV — Hue, Saturation, Value color molecule.
-- |
-- | **DESIGN TOOL COLOR MODEL:**
-- | HSV (also called HSB - Hue, Saturation, Brightness) is the color model
-- | preferred by design tools like Photoshop, Figma, and color pickers.
-- |
-- | **HSV vs HSL:**
-- | - HSV Value = brightness (V=0 is black, V=100 with S=0 is white)
-- | - HSL Lightness = luminosity (L=0 is black, L=100 is white)
-- | - HSV is more intuitive for picking "paint colors"
-- | - HSL is more intuitive for tints/shades
-- |
-- | **Components:**
-- | - **Hue**: Color wheel position (0-359°, wrapping)
-- | - **Saturation**: Color intensity (0-100%, where 0 = gray)
-- | - **Value/Brightness**: Lightness (0-100%, where 0 = black)
-- |
-- | **Use cases:**
-- | - Color picker UIs
-- | - Design tool integration
-- | - Adjusting color brightness without affecting hue
-- | - Adobe-style color workflows

module Hydrogen.Schema.Color.HSV
  ( -- * Types
    HSV
  , HSVA
  , Value
  
  -- * Value Atom
  , value
  , valueSafe
  , unwrapValue
  
  -- * HSV Constructors
  , hsv
  , hsvFromRecord
  
  -- * HSV Accessors
  , hue
  , saturation
  , valueComponent
  , hsvToRecord
  
  -- * HSVA Constructors
  , hsva
  , hsvaFromRecord
  
  -- * HSVA Accessors
  , hsvaAlpha
  , hsvaToRecord
  
  -- * RGB Conversions
  , fromRGB
  , toRGB
  , fromRGBA
  , toRGBA
  
  -- * HSL Conversions
  , fromHSL
  , toHSL
  
  -- * Operations
  , adjustValue
  , adjustSaturation
  , rotateHue
  , rotateHueOpposite
  , setBrightness
  , desaturate
  , invertBrightness
  
  -- * Comparison
  , isGray
  , isBlack
  , isFullySaturated
  , isEqual
  , isNotEqual
  , isBrighterThan
  , isDarkerThan
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , min
  , max
  , negate
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (||)
  , (<>)
  )

import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.Hue (Hue, unwrap) as Hue
import Hydrogen.Schema.Color.Hue (hue, rotate) as HueC
import Hydrogen.Schema.Color.Saturation (Saturation, saturation, unwrap) as Sat
import Hydrogen.Schema.Color.RGB (RGB, rgb, rgbToRecord) as RGB
import Hydrogen.Schema.Color.RGB (RGBA, rgba, rgbaToRecord) as RGBA
import Hydrogen.Schema.Color.HSL (HSL, hsl, hslToRecord) as HSL
import Hydrogen.Schema.Color.Opacity (Opacity, opacity, toUnitInterval, unwrap) as Op

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // value atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Value (Brightness) - 0 to 100%
-- |
-- | The V in HSV. Represents how bright/dark the color is.
-- | - 0: Black (no brightness)
-- | - 100: Maximum brightness for the hue
newtype Value = Value Int

derive instance eqValue :: Eq Value
derive instance ordValue :: Ord Value

instance showValue :: Show Value where
  show (Value n) = "Value " <> show n

-- | Create a Value (clamped to 0-100)
value :: Int -> Value
value n = Value (Bounded.clampInt 0 100 n)

-- | Create a Value with validation
valueSafe :: Int -> Maybe Value
valueSafe n
  | n >= 0 && n <= 100 = Just (Value n)
  | otherwise = Nothing

-- | Extract raw value
unwrapValue :: Value -> Int
unwrapValue (Value n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // hsv
-- ═════════════════════════════════════════════════════════════════════════════

-- | HSV color (Hue, Saturation, Value/Brightness)
newtype HSV = HSV
  { h :: Hue.Hue
  , s :: Sat.Saturation
  , v :: Value
  }

derive instance eqHSV :: Eq HSV
derive instance ordHSV :: Ord HSV

instance showHSV :: Show HSV where
  show (HSV c) = "hsv(" <> show (Hue.unwrap c.h) <> ", " 
    <> show (Sat.unwrap c.s) <> "%, " 
    <> show (unwrapValue c.v) <> "%)"

-- | Create HSV color
hsv :: Int -> Int -> Int -> HSV
hsv h s v = HSV
  { h: HueC.hue h
  , s: Sat.saturation s
  , v: value v
  }

-- | Create from record
hsvFromRecord :: { h :: Int, s :: Int, v :: Int } -> HSV
hsvFromRecord rec = hsv rec.h rec.s rec.v

-- | Get hue component
hue :: HSV -> Hue.Hue
hue (HSV c) = c.h

-- | Get saturation component
saturation :: HSV -> Sat.Saturation
saturation (HSV c) = c.s

-- | Get value component
valueComponent :: HSV -> Value
valueComponent (HSV c) = c.v

-- | Convert to record
hsvToRecord :: HSV -> { h :: Int, s :: Int, v :: Int }
hsvToRecord (HSV c) =
  { h: Hue.unwrap c.h
  , s: Sat.unwrap c.s
  , v: unwrapValue c.v
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // hsva
-- ═════════════════════════════════════════════════════════════════════════════

-- | HSVA color (HSV with alpha)
newtype HSVA = HSVA
  { h :: Hue.Hue
  , s :: Sat.Saturation
  , v :: Value
  , a :: Op.Opacity
  }

derive instance eqHSVA :: Eq HSVA
derive instance ordHSVA :: Ord HSVA

instance showHSVA :: Show HSVA where
  show (HSVA c) = "hsva(" <> show (Hue.unwrap c.h) <> ", " 
    <> show (Sat.unwrap c.s) <> "%, " 
    <> show (unwrapValue c.v) <> "%, "
    <> show (Op.toUnitInterval c.a) <> ")"

-- | Create HSVA color
hsva :: Int -> Int -> Int -> Int -> HSVA
hsva h s v a = HSVA
  { h: HueC.hue h
  , s: Sat.saturation s
  , v: value v
  , a: Op.opacity a
  }

-- | Create from record
hsvaFromRecord :: { h :: Int, s :: Int, v :: Int, a :: Int } -> HSVA
hsvaFromRecord rec = hsva rec.h rec.s rec.v rec.a

-- | Get alpha
hsvaAlpha :: HSVA -> Op.Opacity
hsvaAlpha (HSVA c) = c.a

-- | Convert to record
hsvaToRecord :: HSVA -> { h :: Int, s :: Int, v :: Int, a :: Int }
hsvaToRecord (HSVA c) =
  { h: Hue.unwrap c.h
  , s: Sat.unwrap c.s
  , v: unwrapValue c.v
  , a: Op.unwrap c.a
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rgb conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to HSV
-- |
-- | Algorithm: standard RGB to HSV conversion
fromRGB :: RGB.RGB -> HSV
fromRGB rgbColor =
  let rec = RGB.rgbToRecord rgbColor
      r = toNumber rec.r / 255.0
      g = toNumber rec.g / 255.0
      b = toNumber rec.b / 255.0
      
      cMax = max r (max g b)
      cMin = min r (min g b)
      delta = cMax - cMin
      
      -- Hue calculation
      h' = if delta == 0.0 then 0.0
           else if cMax == r then 60.0 * modFloat ((g - b) / delta) 6.0
           else if cMax == g then 60.0 * ((b - r) / delta + 2.0)
           else 60.0 * ((r - g) / delta + 4.0)
      
      hNorm = if h' < 0.0 then h' + 360.0 else h'
      
      -- Saturation calculation
      s' = if cMax == 0.0 then 0.0 else delta / cMax
      
      -- Value is just the max component
      v' = cMax
      
  in hsv (round hNorm) (round (s' * 100.0)) (round (v' * 100.0))

-- | Convert HSV to RGB
-- |
-- | Algorithm: standard HSV to RGB conversion
toRGB :: HSV -> RGB.RGB
toRGB (HSV c) =
  let h' = toNumber (Hue.unwrap c.h) / 60.0
      s' = toNumber (Sat.unwrap c.s) / 100.0
      v' = toNumber (unwrapValue c.v) / 100.0
      
      i = floor h'
      f = h' - toNumber i
      p = v' * (1.0 - s')
      q = v' * (1.0 - s' * f)
      t = v' * (1.0 - s' * (1.0 - f))
      
      rgb' = case i `mod` 6 of
        0 -> { r: v', g: t, b: p }
        1 -> { r: q, g: v', b: p }
        2 -> { r: p, g: v', b: t }
        3 -> { r: p, g: q, b: v' }
        4 -> { r: t, g: p, b: v' }
        _ -> { r: v', g: p, b: q }
        
  in RGB.rgb 
    (round (rgb'.r * 255.0))
    (round (rgb'.g * 255.0))
    (round (rgb'.b * 255.0))

-- | Convert RGBA to HSVA
fromRGBA :: RGBA.RGBA -> HSVA
fromRGBA rgbaColor =
  let rec = RGBA.rgbaToRecord rgbaColor
      hsvPart = fromRGB (RGB.rgb rec.r rec.g rec.b)
      hsvRec = hsvToRecord hsvPart
  in hsva hsvRec.h hsvRec.s hsvRec.v rec.a

-- | Convert HSVA to RGBA
toRGBA :: HSVA -> RGBA.RGBA
toRGBA (HSVA c) =
  let rgbPart = toRGB (HSV { h: c.h, s: c.s, v: c.v })
      rec = RGB.rgbToRecord rgbPart
  in RGBA.rgba rec.r rec.g rec.b (Op.unwrap c.a)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hsl conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert HSL to HSV
-- |
-- | HSL and HSV share Hue, but Saturation and Lightness/Value differ.
fromHSL :: HSL.HSL -> HSV
fromHSL hslColor =
  let rec = HSL.hslToRecord hslColor
      h' = rec.h
      sHsl = toNumber rec.s / 100.0
      l = toNumber rec.l / 100.0
      
      -- Convert HSL to HSV
      v = l + sHsl * min l (1.0 - l)
      sHsv = if v == 0.0 then 0.0 else 2.0 * (1.0 - l / v)
      
  in hsv h' (round (sHsv * 100.0)) (round (v * 100.0))

-- | Convert HSV to HSL
toHSL :: HSV -> HSL.HSL
toHSL (HSV c) =
  let h' = Hue.unwrap c.h
      sHsv = toNumber (Sat.unwrap c.s) / 100.0
      v = toNumber (unwrapValue c.v) / 100.0
      
      -- Convert HSV to HSL
      l = v * (1.0 - sHsv / 2.0)
      sHsl = if l == 0.0 || l == 1.0 then 0.0 
             else (v - l) / min l (1.0 - l)
      
  in HSL.hsl h' (round (sHsl * 100.0)) (round (l * 100.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Adjust value/brightness by delta
adjustValue :: Int -> HSV -> HSV
adjustValue delta (HSV c) = HSV c
  { v = value (unwrapValue c.v + delta) }

-- | Adjust saturation by delta
adjustSaturation :: Int -> HSV -> HSV
adjustSaturation delta (HSV c) = HSV c
  { s = Sat.saturation (Sat.unwrap c.s + delta) }

-- | Rotate hue by degrees
rotateHue :: Int -> HSV -> HSV
rotateHue degrees (HSV c) = HSV c
  { h = HueC.rotate degrees c.h }

-- | Set brightness to specific value
setBrightness :: Int -> HSV -> HSV
setBrightness v (HSV c) = HSV c
  { v = value v }

-- | Remove all saturation (convert to grayscale)
desaturate :: HSV -> HSV
desaturate (HSV c) = HSV c
  { s = Sat.saturation 0 }

-- | Invert the brightness (complement value)
invertBrightness :: HSV -> HSV
invertBrightness (HSV c) = HSV c
  { v = value (100 - unwrapValue c.v) }

-- | Shift hue by opposite direction (negate)
rotateHueOpposite :: Int -> HSV -> HSV
rotateHueOpposite degrees (HSV c) = HSV c
  { h = HueC.rotate (negate degrees) c.h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if color is gray (saturation = 0)
isGray :: HSV -> Boolean
isGray (HSV c) = Sat.unwrap c.s == 0

-- | Check if color is black (value = 0)
isBlack :: HSV -> Boolean
isBlack (HSV c) = unwrapValue c.v == 0

-- | Check if color is fully saturated (saturation = 100)
isFullySaturated :: HSV -> Boolean
isFullySaturated (HSV c) = Sat.unwrap c.s == 100

-- | Check if two colors are equal
isEqual :: HSV -> HSV -> Boolean
isEqual (HSV a) (HSV b) =
  Hue.unwrap a.h == Hue.unwrap b.h &&
  Sat.unwrap a.s == Sat.unwrap b.s &&
  unwrapValue a.v == unwrapValue b.v

-- | Check if two colors are NOT equal
isNotEqual :: HSV -> HSV -> Boolean
isNotEqual a b =
  let recA = hsvToRecord a
      recB = hsvToRecord b
  in recA.h /= recB.h || recA.s /= recB.s || recA.v /= recB.v

-- | Check if first color is brighter than second
isBrighterThan :: HSV -> HSV -> Boolean
isBrighterThan (HSV a) (HSV b) = unwrapValue a.v > unwrapValue b.v

-- | Check if first color is darker than second
isDarkerThan :: HSV -> HSV -> Boolean
isDarkerThan (HSV a) (HSV b) = unwrapValue a.v < unwrapValue b.v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Float modulo (for hue calculation)
modFloat :: Number -> Number -> Number
modFloat a b = a - toNumber (floor (a / b)) * b

-- | Floor function
floor :: Number -> Int
floor n = round (n - 0.5)

-- | Integer modulo
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b
