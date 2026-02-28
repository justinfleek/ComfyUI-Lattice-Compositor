-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // color // widegamut
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wide Gamut RGB Color Spaces.
-- |
-- | **DISPLAY AND VIDEO COLOR SPACES:**
-- | Different displays and video standards use different RGB primaries.
-- | These "wide gamut" spaces can represent colors outside sRGB.
-- |
-- | **Color Spaces Defined:**
-- | - `DisplayP3` - Apple's wide gamut (Mac, iPhone, iPad)
-- | - `AdobeRGB` - Wide gamut for print workflows
-- | - `ProPhotoRGB` - Very wide gamut for photography
-- | - `Rec709` - HD video standard (same primaries as sRGB)
-- | - `Rec2020` - UHD/HDR video standard
-- |
-- | **Key Differences:**
-- | - Primaries: Where red, green, blue points are on the CIE diagram
-- | - White point: D65 for most, D50 for ProPhoto
-- | - Transfer function: sRGB-like gamma, Rec.709, or linear
-- |
-- | **Why separate from Gamut.purs?**
-- | Gamut.purs handles camera-native gamuts (ARRI, RED, Sony, etc.).
-- | This module handles display/delivery color spaces that end users see.

module Hydrogen.Schema.Color.WideGamut
  ( -- * Display P3
    DisplayP3
  , displayP3
  , displayP3FromRecord
  , displayP3ToRecord
  
  -- * Adobe RGB
  , AdobeRGB
  , adobeRGB
  , adobeRGBFromRecord
  , adobeRGBToRecord
  
  -- * ProPhoto RGB
  , ProPhotoRGB
  , proPhotoRGB
  , proPhotoRGBFromRecord
  , proPhotoRGBToRecord
  
  -- * Rec.709 (HD Video)
  , Rec709
  , rec709
  , rec709FromRecord
  , rec709ToRecord
  
  -- * Rec.2020 (UHD/HDR Video)
  , Rec2020
  , rec2020
  , rec2020FromRecord
  , rec2020ToRecord
  
  -- * Common Accessors
  , class RGBColorSpace
  , getRed
  , getGreen
  , getBlue
  , toRecord
  
  -- * Gamut Info
  , GamutCoverage(..)
  , gamutCoverage
  , isWiderThan
  , isNarrowerThan
  
  -- * Range Checking
  , isInGamut
  , isOutOfGamut
  , clampToGamut
  
  -- * Comparison
  , isBlack
  , isWhite
  , isGray
  , isEqual
  , isNotEqual
  
  -- * Operations
  , blendP3
  , scaleP3
  , addP3
  , subtractP3
  , luminanceP3
  , averageP3
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
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

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // display p3
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display P3 - Apple's wide gamut color space
-- |
-- | Used by modern Apple devices (Mac, iPhone, iPad).
-- | Wider gamut than sRGB, especially in greens and reds.
-- | Uses D65 white point and sRGB-like transfer function.
newtype DisplayP3 = DisplayP3
  { r :: Number
  , g :: Number
  , b :: Number
  }

derive instance eqDisplayP3 :: Eq DisplayP3
derive instance ordDisplayP3 :: Ord DisplayP3

instance showDisplayP3 :: Show DisplayP3 where
  show (DisplayP3 c) = "color(display-p3 " <> show c.r <> " " 
    <> show c.g <> " " <> show c.b <> ")"

-- | Create Display P3 color (values 0.0-1.0)
displayP3 :: Number -> Number -> Number -> DisplayP3
displayP3 r g b = DisplayP3
  { r: Bounded.clampNumber 0.0 1.0 r
  , g: Bounded.clampNumber 0.0 1.0 g
  , b: Bounded.clampNumber 0.0 1.0 b
  }

-- | Create from record
displayP3FromRecord :: { r :: Number, g :: Number, b :: Number } -> DisplayP3
displayP3FromRecord rec = displayP3 rec.r rec.g rec.b

-- | Convert to record
displayP3ToRecord :: DisplayP3 -> { r :: Number, g :: Number, b :: Number }
displayP3ToRecord (DisplayP3 c) = { r: c.r, g: c.g, b: c.b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // adobe rgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | Adobe RGB (1998) - Wide gamut for print workflows
-- |
-- | Developed by Adobe for photographers.
-- | Wider than sRGB, especially in cyan-green region.
-- | Uses D65 white point and gamma 2.2 transfer function.
newtype AdobeRGB = AdobeRGB
  { r :: Number
  , g :: Number
  , b :: Number
  }

derive instance eqAdobeRGB :: Eq AdobeRGB
derive instance ordAdobeRGB :: Ord AdobeRGB

instance showAdobeRGB :: Show AdobeRGB where
  show (AdobeRGB c) = "color(a98-rgb " <> show c.r <> " " 
    <> show c.g <> " " <> show c.b <> ")"

-- | Create Adobe RGB color (values 0.0-1.0)
adobeRGB :: Number -> Number -> Number -> AdobeRGB
adobeRGB r g b = AdobeRGB
  { r: Bounded.clampNumber 0.0 1.0 r
  , g: Bounded.clampNumber 0.0 1.0 g
  , b: Bounded.clampNumber 0.0 1.0 b
  }

-- | Create from record
adobeRGBFromRecord :: { r :: Number, g :: Number, b :: Number } -> AdobeRGB
adobeRGBFromRecord rec = adobeRGB rec.r rec.g rec.b

-- | Convert to record
adobeRGBToRecord :: AdobeRGB -> { r :: Number, g :: Number, b :: Number }
adobeRGBToRecord (AdobeRGB c) = { r: c.r, g: c.g, b: c.b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // prophoto rgb
-- ═════════════════════════════════════════════════════════════════════════════

-- | ProPhoto RGB (ROMM RGB) - Very wide gamut for photography
-- |
-- | The widest commonly-used RGB working space.
-- | Can represent almost all visible colors.
-- | Uses D50 white point (different from others!).
-- | WARNING: Many ProPhoto colors cannot be displayed on any monitor.
newtype ProPhotoRGB = ProPhotoRGB
  { r :: Number
  , g :: Number
  , b :: Number
  }

derive instance eqProPhotoRGB :: Eq ProPhotoRGB
derive instance ordProPhotoRGB :: Ord ProPhotoRGB

instance showProPhotoRGB :: Show ProPhotoRGB where
  show (ProPhotoRGB c) = "color(prophoto-rgb " <> show c.r <> " " 
    <> show c.g <> " " <> show c.b <> ")"

-- | Create ProPhoto RGB color (values 0.0-1.0)
proPhotoRGB :: Number -> Number -> Number -> ProPhotoRGB
proPhotoRGB r g b = ProPhotoRGB
  { r: Bounded.clampNumber 0.0 1.0 r
  , g: Bounded.clampNumber 0.0 1.0 g
  , b: Bounded.clampNumber 0.0 1.0 b
  }

-- | Create from record
proPhotoRGBFromRecord :: { r :: Number, g :: Number, b :: Number } -> ProPhotoRGB
proPhotoRGBFromRecord rec = proPhotoRGB rec.r rec.g rec.b

-- | Convert to record
proPhotoRGBToRecord :: ProPhotoRGB -> { r :: Number, g :: Number, b :: Number }
proPhotoRGBToRecord (ProPhotoRGB c) = { r: c.r, g: c.g, b: c.b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // rec.709
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rec.709 (ITU-R BT.709) - HD Video standard
-- |
-- | The standard for HD television (1080p, etc.).
-- | Same primaries as sRGB but different transfer function (Rec.709 OETF).
-- | Uses D65 white point.
newtype Rec709 = Rec709
  { r :: Number
  , g :: Number
  , b :: Number
  }

derive instance eqRec709 :: Eq Rec709
derive instance ordRec709 :: Ord Rec709

instance showRec709 :: Show Rec709 where
  show (Rec709 c) = "color(rec2020 " <> show c.r <> " " 
    <> show c.g <> " " <> show c.b <> ")"

-- | Create Rec.709 color (values 0.0-1.0)
rec709 :: Number -> Number -> Number -> Rec709
rec709 r g b = Rec709
  { r: Bounded.clampNumber 0.0 1.0 r
  , g: Bounded.clampNumber 0.0 1.0 g
  , b: Bounded.clampNumber 0.0 1.0 b
  }

-- | Create from record
rec709FromRecord :: { r :: Number, g :: Number, b :: Number } -> Rec709
rec709FromRecord rec = rec709 rec.r rec.g rec.b

-- | Convert to record
rec709ToRecord :: Rec709 -> { r :: Number, g :: Number, b :: Number }
rec709ToRecord (Rec709 c) = { r: c.r, g: c.g, b: c.b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // rec.2020
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rec.2020 (ITU-R BT.2020) - UHD/HDR Video standard
-- |
-- | The standard for 4K/8K television and HDR content.
-- | Very wide gamut, close to laser projector primaries.
-- | Uses D65 white point and can use PQ or HLG for HDR.
newtype Rec2020 = Rec2020
  { r :: Number
  , g :: Number
  , b :: Number
  }

derive instance eqRec2020 :: Eq Rec2020
derive instance ordRec2020 :: Ord Rec2020

instance showRec2020 :: Show Rec2020 where
  show (Rec2020 c) = "color(rec2020 " <> show c.r <> " " 
    <> show c.g <> " " <> show c.b <> ")"

-- | Create Rec.2020 color (values 0.0-1.0)
rec2020 :: Number -> Number -> Number -> Rec2020
rec2020 r g b = Rec2020
  { r: Bounded.clampNumber 0.0 1.0 r
  , g: Bounded.clampNumber 0.0 1.0 g
  , b: Bounded.clampNumber 0.0 1.0 b
  }

-- | Create from record
rec2020FromRecord :: { r :: Number, g :: Number, b :: Number } -> Rec2020
rec2020FromRecord rec = rec2020 rec.r rec.g rec.b

-- | Convert to record
rec2020ToRecord :: Rec2020 -> { r :: Number, g :: Number, b :: Number }
rec2020ToRecord (Rec2020 c) = { r: c.r, g: c.g, b: c.b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for accessing RGB from wide gamut spaces
class RGBColorSpace a where
  getRed :: a -> Number
  getGreen :: a -> Number
  getBlue :: a -> Number

instance rgbColorSpace_DisplayP3 :: RGBColorSpace DisplayP3 where
  getRed (DisplayP3 c) = c.r
  getGreen (DisplayP3 c) = c.g
  getBlue (DisplayP3 c) = c.b

instance rgbColorSpace_AdobeRGB :: RGBColorSpace AdobeRGB where
  getRed (AdobeRGB c) = c.r
  getGreen (AdobeRGB c) = c.g
  getBlue (AdobeRGB c) = c.b

instance rgbColorSpace_ProPhotoRGB :: RGBColorSpace ProPhotoRGB where
  getRed (ProPhotoRGB c) = c.r
  getGreen (ProPhotoRGB c) = c.g
  getBlue (ProPhotoRGB c) = c.b

instance rgbColorSpace_Rec709 :: RGBColorSpace Rec709 where
  getRed (Rec709 c) = c.r
  getGreen (Rec709 c) = c.g
  getBlue (Rec709 c) = c.b

instance rgbColorSpace_Rec2020 :: RGBColorSpace Rec2020 where
  getRed (Rec2020 c) = c.r
  getGreen (Rec2020 c) = c.g
  getBlue (Rec2020 c) = c.b

-- | Convert to record (generic)
toRecord :: forall a. RGBColorSpace a => a -> { r :: Number, g :: Number, b :: Number }
toRecord a = { r: getRed a, g: getGreen a, b: getBlue a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // gamut info
-- ═════════════════════════════════════════════════════════════════════════════

-- | Relative gamut coverage (approximate percentage of visible spectrum)
data GamutCoverage
  = SRGBCoverage       -- ^ ~35% of visible colors
  | Rec709Coverage     -- ^ ~35% (same as sRGB)
  | AdobeRGBCoverage   -- ^ ~50% of visible colors
  | DisplayP3Coverage  -- ^ ~45% of visible colors
  | Rec2020Coverage    -- ^ ~75% of visible colors
  | ProPhotoCoverage   -- ^ ~90% of visible colors (includes imaginary)

derive instance eqGamutCoverage :: Eq GamutCoverage
derive instance ordGamutCoverage :: Ord GamutCoverage

instance showGamutCoverage :: Show GamutCoverage where
  show = case _ of
    SRGBCoverage -> "sRGB (~35%)"
    Rec709Coverage -> "Rec.709 (~35%)"
    AdobeRGBCoverage -> "Adobe RGB (~50%)"
    DisplayP3Coverage -> "Display P3 (~45%)"
    Rec2020Coverage -> "Rec.2020 (~75%)"
    ProPhotoCoverage -> "ProPhoto (~90%)"

-- | Get gamut coverage for a color space
gamutCoverage :: forall a. RGBColorSpace a => a -> GamutCoverage
gamutCoverage _ = SRGBCoverage  -- Default, would need type-level info for correct answer

-- | Check if one gamut is wider than another
isWiderThan :: GamutCoverage -> GamutCoverage -> Boolean
isWiderThan a b = coverageToInt a > coverageToInt b

-- | Check if one gamut is narrower than another
isNarrowerThan :: GamutCoverage -> GamutCoverage -> Boolean
isNarrowerThan a b = coverageToInt a < coverageToInt b

-- | Convert coverage to comparable int
coverageToInt :: GamutCoverage -> Int
coverageToInt = case _ of
  SRGBCoverage -> 35
  Rec709Coverage -> 35
  AdobeRGBCoverage -> 50
  DisplayP3Coverage -> 45
  Rec2020Coverage -> 75
  ProPhotoCoverage -> 90

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // range checking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if color values are in valid range (0.0-1.0)
isInGamut :: forall a. RGBColorSpace a => a -> Boolean
isInGamut c =
  getRed c >= 0.0 && getRed c <= 1.0 &&
  getGreen c >= 0.0 && getGreen c <= 1.0 &&
  getBlue c >= 0.0 && getBlue c <= 1.0

-- | Check if any channel is out of range
isOutOfGamut :: forall a. RGBColorSpace a => a -> Boolean
isOutOfGamut c =
  getRed c < 0.0 || getRed c > 1.0 ||
  getGreen c < 0.0 || getGreen c > 1.0 ||
  getBlue c < 0.0 || getBlue c > 1.0

-- | Clamp values to valid range
clampToGamut :: DisplayP3 -> DisplayP3
clampToGamut (DisplayP3 c) = DisplayP3
  { r: Bounded.clampNumber 0.0 1.0 c.r
  , g: Bounded.clampNumber 0.0 1.0 c.g
  , b: Bounded.clampNumber 0.0 1.0 c.b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if color is black
isBlack :: forall a. RGBColorSpace a => a -> Boolean
isBlack c = getRed c == 0.0 && getGreen c == 0.0 && getBlue c == 0.0

-- | Check if color is white
isWhite :: forall a. RGBColorSpace a => a -> Boolean
isWhite c = getRed c == 1.0 && getGreen c == 1.0 && getBlue c == 1.0

-- | Check if color is gray
isGray :: forall a. RGBColorSpace a => a -> Boolean
isGray c = getRed c == getGreen c && getGreen c == getBlue c

-- | Check if two colors are equal
isEqual :: forall a. RGBColorSpace a => a -> a -> Boolean
isEqual a b =
  getRed a == getRed b &&
  getGreen a == getGreen b &&
  getBlue a == getBlue b

-- | Check if two colors are not equal
isNotEqual :: forall a. RGBColorSpace a => a -> a -> Boolean
isNotEqual a b =
  getRed a /= getRed b ||
  getGreen a /= getGreen b ||
  getBlue a /= getBlue b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two Display P3 colors
blendP3 :: Number -> DisplayP3 -> DisplayP3 -> DisplayP3
blendP3 weight (DisplayP3 a) (DisplayP3 b) =
  let w = clampWeight weight
  in DisplayP3
    { r: a.r * (1.0 - w) + b.r * w
    , g: a.g * (1.0 - w) + b.g * w
    , b: a.b * (1.0 - w) + b.b * w
    }

-- | Scale Display P3 brightness
scaleP3 :: Number -> DisplayP3 -> DisplayP3
scaleP3 factor (DisplayP3 c) = displayP3 (c.r * factor) (c.g * factor) (c.b * factor)

-- | Add two Display P3 colors (for light mixing)
addP3 :: DisplayP3 -> DisplayP3 -> DisplayP3
addP3 (DisplayP3 a) (DisplayP3 b) = displayP3 (a.r + b.r) (a.g + b.g) (a.b + b.b)

-- | Subtract two Display P3 colors
subtractP3 :: DisplayP3 -> DisplayP3 -> DisplayP3
subtractP3 (DisplayP3 a) (DisplayP3 b) = displayP3 (a.r - b.r) (a.g - b.g) (a.b - b.b)

-- | Calculate relative luminance for Display P3
luminanceP3 :: DisplayP3 -> Number
luminanceP3 (DisplayP3 c) = 0.2126 * c.r + 0.7152 * c.g + 0.0722 * c.b

-- | Average two Display P3 colors
averageP3 :: DisplayP3 -> DisplayP3 -> DisplayP3
averageP3 (DisplayP3 a) (DisplayP3 b) = DisplayP3
  { r: (a.r + b.r) / 2.0
  , g: (a.g + b.g) / 2.0
  , b: (a.b + b.b) / 2.0
  }

-- | Clamp weight to 0.0-1.0
clampWeight :: Number -> Number
clampWeight w
  | w < 0.0 = 0.0
  | w > 1.0 = 1.0
  | otherwise = w
