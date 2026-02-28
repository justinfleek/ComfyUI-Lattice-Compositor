-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // space
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color spaces for professional color management.
-- |
-- | This module provides types for various color spaces used in:
-- | - **Web**: sRGB (standard), Display P3 (wide gamut)
-- | - **Print**: CMYK, Pantone references
-- | - **Film/Video**: ACES, Rec.709, Rec.2020, DCI-P3
-- | - **Perceptual**: LAB, OKLAB, LCH, OKLCH
-- | - **3D/PBR**: Linear RGB for physically-based rendering

module Hydrogen.Schema.Color.Space
  ( -- * Color Space Identifiers
    ColorSpace(..)
  , Gamut(..)
  , TransferFunction(..)
  , WhitePoint(..)
  , Illuminant(..)
  
  -- * Space-Aware Color
  , ColorInSpace(..)
  , LinearRGB
  , LAB
  , OKLAB
  , LCH
  , OKLCH
  , CMYK
  , XYZ
  
  -- * Constructors
  , srgb
  , linearRgb
  , displayP3
  , lab
  , oklab
  , lch
  , oklch
  , cmyk
  , xyz
  
  -- * Conversions (placeholder signatures)
  , toLinear
  , fromLinear
  , toXYZ
  , fromXYZ
  
  -- * Working Space
  , WorkingSpace(..)
  , acesAP0
  , acesAP1
  , rec709
  , rec2020
  , dciP3
  
  -- * Gamut Mapping
  , GamutMapping(..)
  , isInGamut
  ) where

import Prelude
  ( class Eq
  , class Show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<=)
  , (>=)
  , (&&)
  )

import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // color space types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identifies a color space by its characteristics
data ColorSpace
  = SRGB                -- ^ Standard RGB (web default)
  | LinearSRGB          -- ^ Linear sRGB (no gamma)
  | DisplayP3           -- ^ Apple Display P3 (wide gamut)
  | AdobeRGB            -- ^ Adobe RGB (1998)
  | ProPhotoRGB         -- ^ ProPhoto RGB (very wide gamut)
  | Rec709              -- ^ ITU-R BT.709 (HDTV)
  | Rec2020             -- ^ ITU-R BT.2020 (UHDTV, wide gamut)
  | DCIP3               -- ^ DCI-P3 (digital cinema)
  | ACES_AP0            -- ^ ACES Primaries 0 (archival)
  | ACES_AP1            -- ^ ACES Primaries 1 (working)
  | CIE_XYZ             -- ^ CIE 1931 XYZ (reference)
  | CIE_LAB             -- ^ CIE L*a*b* (perceptually uniform)
  | CIE_LCH             -- ^ CIE LCH (cylindrical LAB)
  | OKLab               -- ^ Oklab (improved perceptual uniformity)
  | OKLCH               -- ^ OKLCH (cylindrical Oklab)
  | CMYK_FOGRA39        -- ^ CMYK with FOGRA39 profile
  | CMYK_GRACoL         -- ^ CMYK with GRACoL profile

derive instance eqColorSpace :: Eq ColorSpace

instance showColorSpace :: Show ColorSpace where
  show = case _ of
    SRGB -> "sRGB"
    LinearSRGB -> "Linear sRGB"
    DisplayP3 -> "Display P3"
    AdobeRGB -> "Adobe RGB"
    ProPhotoRGB -> "ProPhoto RGB"
    Rec709 -> "Rec.709"
    Rec2020 -> "Rec.2020"
    DCIP3 -> "DCI-P3"
    ACES_AP0 -> "ACES AP0"
    ACES_AP1 -> "ACES AP1"
    CIE_XYZ -> "CIE XYZ"
    CIE_LAB -> "CIE L*a*b*"
    CIE_LCH -> "CIE LCH"
    OKLab -> "Oklab"
    OKLCH -> "OKLCH"
    CMYK_FOGRA39 -> "CMYK (FOGRA39)"
    CMYK_GRACoL -> "CMYK (GRACoL)"

-- | Gamut describes the range of colors a space can represent
data Gamut
  = GamutSRGB           -- ^ ~35% of visible spectrum
  | GamutP3             -- ^ ~45% of visible spectrum
  | GamutRec2020        -- ^ ~76% of visible spectrum
  | GamutAP0            -- ^ Encompasses all visible colors
  | GamutProPhoto       -- ^ Includes some imaginary colors

derive instance eqGamut :: Eq Gamut

-- | Transfer function (gamma curve)
data TransferFunction
  = Linear              -- ^ No gamma (1.0)
  | Gamma22             -- ^ Simple 2.2 gamma
  | Gamma24             -- ^ Simple 2.4 gamma
  | Gamma26             -- ^ Simple 2.6 gamma (DCI-P3)
  | SRGBTransfer        -- ^ sRGB piecewise curve
  | PQTransfer          -- ^ Perceptual Quantizer (HDR)
  | HLGTransfer         -- ^ Hybrid Log-Gamma (HDR)
  | ACEScct             -- ^ ACES CCT (log encoding)
  | ACEScc              -- ^ ACES CC (log encoding)

derive instance eqTransferFunction :: Eq TransferFunction

-- | Standard illuminants (white points)
data Illuminant
  = D50                 -- ^ 5003K (print, ProPhoto)
  | D55                 -- ^ 5503K (daylight)
  | D65                 -- ^ 6504K (sRGB, Rec.709, web standard)
  | D75                 -- ^ 7504K (north sky daylight)
  | DCI                 -- ^ DCI white (digital cinema)
  | ACES                -- ^ ACES white (~6000K)

derive instance eqIlluminant :: Eq Illuminant

-- | White point as chromaticity coordinates
type WhitePoint =
  { x :: Number
  , y :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // color value in space
-- ═════════════════════════════════════════════════════════════════════════════

-- | A color value tagged with its color space
data ColorInSpace
  = InSRGB { r :: Number, g :: Number, b :: Number }
  | InLinearRGB LinearRGB
  | InDisplayP3 { r :: Number, g :: Number, b :: Number }
  | InXYZ XYZ
  | InLAB LAB
  | InOKLAB OKLAB
  | InLCH LCH
  | InOKLCH OKLCH
  | InCMYK CMYK

derive instance eqColorInSpace :: Eq ColorInSpace

-- | Linear RGB (no gamma, for compositing and PBR)
type LinearRGB =
  { r :: Number  -- ^ 0.0 to 1.0 (can exceed for HDR)
  , g :: Number
  , b :: Number
  }

-- | CIE XYZ (device-independent reference space)
type XYZ =
  { x :: Number
  , y :: Number  -- ^ Luminance
  , z :: Number
  }

-- | CIE L*a*b* (perceptually uniform)
type LAB =
  { l :: Number  -- ^ Lightness: 0 (black) to 100 (white)
  , a :: Number  -- ^ Green-red axis: negative = green, positive = red
  , b :: Number  -- ^ Blue-yellow axis: negative = blue, positive = yellow
  }

-- | Oklab (improved perceptual uniformity over LAB)
type OKLAB =
  { l :: Number  -- ^ Lightness: 0.0 to 1.0
  , a :: Number  -- ^ Green-red axis
  , b :: Number  -- ^ Blue-yellow axis
  }

-- | CIE LCH (cylindrical form of LAB)
type LCH =
  { l :: Number  -- ^ Lightness: 0 to 100
  , c :: Number  -- ^ Chroma (saturation): 0 to ~150
  , h :: Number  -- ^ Hue: 0 to 360 degrees
  }

-- | OKLCH (cylindrical form of Oklab)
type OKLCH =
  { l :: Number  -- ^ Lightness: 0.0 to 1.0
  , c :: Number  -- ^ Chroma: 0.0 to ~0.4
  , h :: Number  -- ^ Hue: 0 to 360 degrees
  }

-- | CMYK for print production
type CMYK =
  { c :: Number  -- ^ Cyan: 0-100%
  , m :: Number  -- ^ Magenta: 0-100%
  , y :: Number  -- ^ Yellow: 0-100%
  , k :: Number  -- ^ Key (Black): 0-100%
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an sRGB color (values 0.0-1.0)
srgb :: Number -> Number -> Number -> ColorInSpace
srgb r g b = InSRGB { r, g, b }

-- | Create a linear RGB color (values 0.0-1.0, can exceed for HDR)
linearRgb :: Number -> Number -> Number -> ColorInSpace
linearRgb r g b = InLinearRGB { r, g, b }

-- | Create a Display P3 color
displayP3 :: Number -> Number -> Number -> ColorInSpace
displayP3 r g b = InDisplayP3 { r, g, b }

-- | Create a CIE L*a*b* color
lab :: Number -> Number -> Number -> ColorInSpace
lab l a b = InLAB { l, a, b }

-- | Create an Oklab color
oklab :: Number -> Number -> Number -> ColorInSpace
oklab l a b = InOKLAB { l, a, b }

-- | Create a CIE LCH color
lch :: Number -> Number -> Number -> ColorInSpace
lch l c h = InLCH { l, c, h }

-- | Create an OKLCH color
oklch :: Number -> Number -> Number -> ColorInSpace
oklch l c h = InOKLCH { l, c, h }

-- | Create a CMYK color
cmyk :: Number -> Number -> Number -> Number -> ColorInSpace
cmyk c m y k = InCMYK { c, m, y, k }

-- | Create a CIE XYZ color
xyz :: Number -> Number -> Number -> ColorInSpace
xyz x y z = InXYZ { x, y, z }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert sRGB to Linear RGB (remove gamma)
toLinear :: ColorInSpace -> ColorInSpace
toLinear = case _ of
  InSRGB { r, g, b } -> InLinearRGB 
    { r: srgbToLinearChannel r
    , g: srgbToLinearChannel g
    , b: srgbToLinearChannel b
    }
  other -> other

-- | Convert Linear RGB to sRGB (apply gamma)
fromLinear :: ColorInSpace -> ColorInSpace
fromLinear = case _ of
  InLinearRGB { r, g, b } -> InSRGB
    { r: linearToSrgbChannel r
    , g: linearToSrgbChannel g
    , b: linearToSrgbChannel b
    }
  other -> other

-- | Convert to CIE XYZ (reference space)
toXYZ :: ColorInSpace -> ColorInSpace
toXYZ = case _ of
  InLinearRGB { r, g, b } ->
    -- sRGB to XYZ matrix (D65 illuminant)
    let x = 0.4124564 * r + 0.3575761 * g + 0.1804375 * b
        y = 0.2126729 * r + 0.7151522 * g + 0.0721750 * b
        z = 0.0193339 * r + 0.1191920 * g + 0.9503041 * b
    in InXYZ { x, y, z }
  InSRGB _ -> toXYZ (toLinear (InSRGB { r: 0.0, g: 0.0, b: 0.0 }))
  other -> other

-- | Convert from CIE XYZ to Linear RGB
fromXYZ :: ColorInSpace -> ColorInSpace
fromXYZ = case _ of
  InXYZ { x, y, z } ->
    -- XYZ to sRGB matrix (D65 illuminant)
    let r =  3.2404542 * x - 1.5371385 * y - 0.4985314 * z
        g = -0.9692660 * x + 1.8760108 * y + 0.0415560 * z
        b =  0.0556434 * x - 0.2040259 * y + 1.0572252 * z
    in InLinearRGB { r, g, b }
  other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // working spaces
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete working color space definition
type WorkingSpace =
  { name :: String
  , gamut :: Gamut
  , transfer :: TransferFunction
  , whitePoint :: Illuminant
  }

-- | ACES AP0 (Academy Color Encoding System, archival)
acesAP0 :: WorkingSpace
acesAP0 = 
  { name: "ACES AP0"
  , gamut: GamutAP0
  , transfer: Linear
  , whitePoint: ACES
  }

-- | ACES AP1 (working space for ACES pipeline)
acesAP1 :: WorkingSpace
acesAP1 = 
  { name: "ACES AP1"
  , gamut: GamutRec2020
  , transfer: ACEScct
  , whitePoint: ACES
  }

-- | Rec.709 (HDTV standard)
rec709 :: WorkingSpace
rec709 = 
  { name: "Rec.709"
  , gamut: GamutSRGB
  , transfer: Gamma24
  , whitePoint: D65
  }

-- | Rec.2020 (UHDTV standard)
rec2020 :: WorkingSpace
rec2020 = 
  { name: "Rec.2020"
  , gamut: GamutRec2020
  , transfer: PQTransfer
  , whitePoint: D65
  }

-- | DCI-P3 (digital cinema)
dciP3 :: WorkingSpace
dciP3 = 
  { name: "DCI-P3"
  , gamut: GamutP3
  , transfer: Gamma26
  , whitePoint: DCI
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // gamut mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Strategy for handling out-of-gamut colors
data GamutMapping
  = Clip               -- ^ Hard clip to gamut boundary
  | Compress           -- ^ Perceptually compress toward center
  | ProjectToSurface   -- ^ Project to nearest in-gamut color
  | PreserveLightness  -- ^ Reduce chroma while preserving L*

derive instance eqGamutMapping :: Eq GamutMapping

-- | Check if a color is within the sRGB gamut
isInGamut :: ColorInSpace -> Boolean
isInGamut = case _ of
  InSRGB { r, g, b } -> inRange r && inRange g && inRange b
  InLinearRGB { r, g, b } -> inRange r && inRange g && inRange b
  _ -> true  -- Other spaces need full conversion check
  where
    inRange n = n >= 0.0 && n <= 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | sRGB gamma to linear conversion for single channel
srgbToLinearChannel :: Number -> Number
srgbToLinearChannel c =
  if c <= 0.04045
    then c / 12.92
    else Math.pow ((c + 0.055) / 1.055) 2.4

-- | Linear to sRGB gamma conversion for single channel
linearToSrgbChannel :: Number -> Number
linearToSrgbChannel c =
  if c <= 0.0031308
    then c * 12.92
    else 1.055 * Math.pow c (1.0 / 2.4) - 0.055
