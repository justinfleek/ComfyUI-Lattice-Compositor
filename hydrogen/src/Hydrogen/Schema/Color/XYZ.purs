-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // xyz
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | XYZ - CIE 1931 XYZ color space (device-independent).
-- |
-- | **FOUNDATION OF COLOR SCIENCE:**
-- | XYZ is THE fundamental color space in professional color management.
-- | Created by the International Commission on Illumination (CIE) in 1931,
-- | it's based on how human cone cells actually respond to light.
-- |
-- | **Why XYZ exists:**
-- | RGB is device-dependent - same RGB values look different on different screens.
-- | XYZ is device-independent - same XYZ values produce the same perceived color
-- | on any calibrated device. This is why every ICC color profile uses XYZ.
-- |
-- | **Components (Tristimulus values):**
-- | - **X**: Roughly corresponds to red-green (0.0-0.95047 for D65 white)
-- | - **Y**: Luminance/brightness (0.0-1.0, where 1.0 = perfect white)
-- | - **Z**: Roughly corresponds to blue-yellow (0.0-1.08883 for D65 white)
-- |
-- | **White point:**
-- | This module uses D65 illuminant (standard for sRGB displays):
-- | - X = 0.95047
-- | - Y = 1.00000
-- | - Z = 1.08883
-- |
-- | **The conversion bridge:**
-- | You CANNOT convert RGB ↔ LAB directly. The path is:
-- | ```
-- | RGB → XYZ → LAB → LCH
-- | LCH → LAB → XYZ → RGB
-- | ```
-- |
-- | **Use cases:**
-- | - ICC color profile conversions
-- | - Cross-device color matching
-- | - Professional color management
-- | - Scientific color measurements
-- | - Accurate color space transformations

module Hydrogen.Schema.Color.XYZ
  ( -- * Types
    XYZ
  , XComponent
  , YComponent
  , ZComponent
  
  -- * Constructors
  , xyz
  , xyzFromRecord
  
  -- * Accessors
  , xComponent
  , yComponent
  , zComponent
  , xyzToRecord
  , toRecord
  
  -- * White point
  , d65White
  ) where

import Prelude (class Eq, class Ord, class Show, show, (<>), (<), (>), otherwise)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | X component (tristimulus value): 0.0-0.95047 (D65 white)
-- | Roughly corresponds to red-green axis
newtype XComponent = XComponent Number

derive instance eqXComponent :: Eq XComponent
derive instance ordXComponent :: Ord XComponent

instance showXComponent :: Show XComponent where
  show (XComponent n) = "X " <> show n

-- | Create X value (clamped 0.0-1.2 for safety, though D65 white is 0.95047)
xValue :: Number -> XComponent
xValue n
  | n < 0.0 = XComponent 0.0
  | n > 1.2 = XComponent 1.2  -- Safety clamp beyond D65 white
  | otherwise = XComponent n

unwrapX :: XComponent -> Number
unwrapX (XComponent n) = n

-- | Y component (tristimulus value): 0.0-1.0
-- | Represents luminance (brightness). Y=1.0 is perfect white.
newtype YComponent = YComponent Number

derive instance eqYComponent :: Eq YComponent
derive instance ordYComponent :: Ord YComponent

instance showYComponent :: Show YComponent where
  show (YComponent n) = "Y " <> show n

-- | Create Y value (clamped 0.0-1.0)
yValue :: Number -> YComponent
yValue n
  | n < 0.0 = YComponent 0.0
  | n > 1.0 = YComponent 1.0
  | otherwise = YComponent n

unwrapY :: YComponent -> Number
unwrapY (YComponent n) = n

-- | Z component (tristimulus value): 0.0-1.08883 (D65 white)
-- | Roughly corresponds to blue-yellow axis
newtype ZComponent = ZComponent Number

derive instance eqZComponent :: Eq ZComponent
derive instance ordZComponent :: Ord ZComponent

instance showZComponent :: Show ZComponent where
  show (ZComponent n) = "Z " <> show n

-- | Create Z value (clamped 0.0-1.3 for safety, though D65 white is 1.08883)
zValue :: Number -> ZComponent
zValue n
  | n < 0.0 = ZComponent 0.0
  | n > 1.3 = ZComponent 1.3  -- Safety clamp beyond D65 white
  | otherwise = ZComponent n

unwrapZ :: ZComponent -> Number
unwrapZ (ZComponent n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | XYZ color - CIE 1931 device-independent color space
type XYZ =
  { x :: XComponent  -- ^ X tristimulus (0.0-0.95047 for D65)
  , y :: YComponent  -- ^ Y tristimulus / luminance (0.0-1.0)
  , z :: ZComponent  -- ^ Z tristimulus (0.0-1.08883 for D65)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create XYZ color from tristimulus values
-- |
-- | ```purescript
-- | xyz 0.95047 1.0 1.08883  -- D65 white point
-- | xyz 0.0 0.0 0.0          -- Black
-- | xyz 0.41246 0.21267 0.01933  -- Pure sRGB red
-- | ```
xyz :: Number -> Number -> Number -> XYZ
xyz x y z =
  { x: xValue x
  , y: yValue y
  , z: zValue z
  }

-- | Create from record
xyzFromRecord :: { x :: Number, y :: Number, z :: Number } -> XYZ
xyzFromRecord { x, y, z } = xyz x y z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get X component
xComponent :: XYZ -> XComponent
xComponent color = color.x

-- | Get Y component (luminance)
yComponent :: XYZ -> YComponent
yComponent color = color.y

-- | Get Z component
zComponent :: XYZ -> ZComponent
zComponent color = color.z

-- | Convert to record - explicitly named for backend persistence
xyzToRecord :: XYZ -> { x :: Number, y :: Number, z :: Number }
xyzToRecord color =
  { x: unwrapX color.x
  , y: unwrapY color.y
  , z: unwrapZ color.z
  }

-- | Generic alias for xyzToRecord
toRecord :: XYZ -> { x :: Number, y :: Number, z :: Number }
toRecord = xyzToRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // white point
-- ═════════════════════════════════════════════════════════════════════════════

-- | D65 white point (standard daylight illuminant for sRGB)
-- |
-- | Used as reference white for RGB ↔ XYZ ↔ LAB conversions.
-- | These are the XYZ values that correspond to pure white (RGB 255, 255, 255).
-- |
-- | ```purescript
-- | d65White  -- { x: 0.95047, y: 1.0, z: 1.08883 }
-- | ```
d65White :: XYZ
d65White = xyz 0.95047 1.0 1.08883
