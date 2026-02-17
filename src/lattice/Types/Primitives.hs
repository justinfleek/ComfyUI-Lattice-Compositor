-- |
-- Module      : Lattice.Types.Primitives
-- Description : Foundational primitive types for Lattice Compositor
-- 
-- Migrated from ui/src/schemas/layers/primitives-schema.ts
-- All numeric values must be finite (reject NaN/Infinity)
-- This is the BASE SCHEMA - everything else depends on these types
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lattice.Types.Primitives
  ( -- Vector types
    Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  -- Color types
  , RGBAColor(..)
  , RGBA255Color(..)
  , HexColor(..)
  , ColorValue(..)
  -- Geometry types
  , Rect(..)
  -- ID types
  , EntityId(..)
  , NullableEntityId(..)
  -- Enum types
  , BlendMode(..)
  , QualityMode(..)
  -- Validation functions
  , validateFinite
  , validatePositive
  , validateNonNegative
  , validateNormalized01
  , validateNormalizedNeg1To1
  , validatePositiveInt
  , validateNonNegativeInt
  , validateFrameNumber
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  , Value(..)
  )
import Data.Aeson.Types (Parser)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Text.Regex.TDFA ((=~))
import Lattice.Utils.NumericSafety (isFinite)

-- ============================================================================
-- VALIDATION FUNCTIONS
-- ============================================================================
-- These enforce the .finite() constraint from TypeScript
-- In Haskell, we use smart constructors or validation at JSON parse time

-- | Validate that a Double is finite (not NaN, not Infinity)
validateFinite :: Double -> Bool
validateFinite x = isFinite x && not (isNaN x)

-- | Validate that a Double is positive and finite
validatePositive :: Double -> Bool
validatePositive x = validateFinite x && x > 0

-- | Validate that a Double is non-negative and finite
validateNonNegative :: Double -> Bool
validateNonNegative x = validateFinite x && x >= 0

-- | Validate that a Double is in range [0, 1] and finite
validateNormalized01 :: Double -> Bool
validateNormalized01 x = validateFinite x && x >= 0 && x <= 1

-- | Validate that a Double is in range [-1, 1] and finite
validateNormalizedNeg1To1 :: Double -> Bool
validateNormalizedNeg1To1 x = validateFinite x && x >= -1 && x <= 1

-- | Validate that an Int is positive
validatePositiveInt :: Int -> Bool
validatePositiveInt x = x > 0

-- | Validate that an Int is non-negative
validateNonNegativeInt :: Int -> Bool
validateNonNegativeInt x = x >= 0

-- | Validate frame number (non-negative integer)
validateFrameNumber :: Int -> Bool
validateFrameNumber = validateNonNegativeInt

-- ============================================================================
-- VECTOR TYPES
-- ============================================================================

-- | 2D vector with x and y components (finite numbers)
data Vec2 = Vec2
  { vec2X :: Double
  , vec2Y :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Vec2 where
  toJSON (Vec2 x y) = object ["x" .= x, "y" .= y]

instance FromJSON Vec2 where
  parseJSON = withObject "Vec2" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    -- Validate finite
    if validateFinite x && validateFinite y
      then return (Vec2 x y)
      else fail "Vec2 components must be finite numbers"

-- | 3D vector with x, y, and z components (finite numbers)
data Vec3 = Vec3
  { vec3X :: Double
  , vec3Y :: Double
  , vec3Z :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Vec3 where
  toJSON (Vec3 x y z) = object ["x" .= x, "y" .= y, "z" .= z]

instance FromJSON Vec3 where
  parseJSON = withObject "Vec3" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    z <- o .: "z"
    -- Validate finite
    if validateFinite x && validateFinite y && validateFinite z
      then return (Vec3 x y z)
      else fail "Vec3 components must be finite numbers"

-- | 2D or 3D position with optional z component
data Position2DOr3D = Position2DOr3D
  { position2DOr3DX :: Double
  , position2DOr3DY :: Double
  , position2DOr3DZ :: Maybe Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Position2DOr3D where
  toJSON (Position2DOr3D x y mz) =
    let
      baseFields = ["x" .= x, "y" .= y]
      withZ = case mz of Just z -> ("z" .= z) : baseFields; Nothing -> baseFields
    in object withZ

instance FromJSON Position2DOr3D where
  parseJSON = withObject "Position2DOr3D" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    mz <- o .:? "z"
    -- Validate finite
    if validateFinite x && validateFinite y && maybe True validateFinite mz
      then return (Position2DOr3D x y mz)
      else fail "Position2DOr3D components must be finite numbers"

-- ============================================================================
-- COLOR TYPES
-- ============================================================================

-- | RGBA color with values 0-1 (normalized)
data RGBAColor = RGBAColor
  { rgbaR :: Double
  , rgbaG :: Double
  , rgbaB :: Double
  , rgbaA :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON RGBAColor where
  toJSON (RGBAColor r g b a) = object
    [ "r" .= r
    , "g" .= g
    , "b" .= b
    , "a" .= a
    ]

instance FromJSON RGBAColor where
  parseJSON = withObject "RGBAColor" $ \o -> do
    r <- o .: "r"
    g <- o .: "g"
    b <- o .: "b"
    a <- o .: "a"
    -- Validate normalized [0, 1]
    if validateNormalized01 r && validateNormalized01 g &&
       validateNormalized01 b && validateNormalized01 a
      then return (RGBAColor r g b a)
      else fail "RGBAColor components must be in range [0, 1]"

-- | RGBA color with values 0-255 (integer)
data RGBA255Color = RGBA255Color
  { rgba255R :: Int
  , rgba255G :: Int
  , rgba255B :: Int
  , rgba255A :: Int
  }
  deriving (Eq, Show, Generic)

instance ToJSON RGBA255Color where
  toJSON (RGBA255Color r g b a) = object
    [ "r" .= r
    , "g" .= g
    , "b" .= b
    , "a" .= a
    ]

instance FromJSON RGBA255Color where
  parseJSON = withObject "RGBA255Color" $ \o -> do
    r <- o .: "r"
    g <- o .: "g"
    b <- o .: "b"
    a <- o .: "a"
    -- Validate range [0, 255]
    if r >= 0 && r <= 255 && g >= 0 && g <= 255 &&
       b >= 0 && b <= 255 && a >= 0 && a <= 255
      then return (RGBA255Color r g b a)
      else fail "RGBA255Color components must be in range [0, 255]"

-- | Hex color string (with or without #)
newtype HexColor = HexColor { unHexColor :: Text }
  deriving (Eq, Show, Generic)

-- | Validate hex color format: #?[0-9a-fA-F]{3,8}
validateHexColor :: Text -> Bool
validateHexColor t =
  let s = T.unpack t
  in s =~ ("^#?[0-9a-fA-F]{3,8}$" :: String)

instance ToJSON HexColor where
  toJSON (HexColor t) = toJSON t

instance FromJSON HexColor where
  parseJSON v = do
    t <- parseJSON v
    if validateHexColor t
      then return (HexColor t)
      else fail "Invalid hex color format (expected #?[0-9a-fA-F]{3,8})"

-- | Color that can be hex string or RGBA object
data ColorValue
  = ColorValueHex HexColor
  | ColorValueRGBA RGBAColor
  deriving (Eq, Show, Generic)

instance ToJSON ColorValue where
  toJSON (ColorValueHex h) = toJSON h
  toJSON (ColorValueRGBA c) = toJSON c

instance FromJSON ColorValue where
  parseJSON v@(String _) = ColorValueHex <$> parseJSON v
  parseJSON v@(Object _) = ColorValueRGBA <$> parseJSON v
  parseJSON _ = fail "ColorValue must be hex string or RGBA object"

-- ============================================================================
-- GEOMETRY TYPES
-- ============================================================================

-- | Rectangle with x, y, width, height
data Rect = Rect
  { rectX :: Double
  , rectY :: Double
  , rectWidth :: Double
  , rectHeight :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Rect where
  toJSON (Rect x y w h) = object
    [ "x" .= x
    , "y" .= y
    , "width" .= w
    , "height" .= h
    ]

instance FromJSON Rect where
  parseJSON = withObject "Rect" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    w <- o .: "width"
    h <- o .: "height"
    -- Validate: x, y finite; width, height non-negative finite
    if validateFinite x && validateFinite y &&
       validateNonNegative w && validateNonNegative h
      then return (Rect x y w h)
      else fail "Rect: x,y must be finite; width,height must be non-negative finite"

-- ============================================================================
-- ID TYPES
-- ============================================================================

-- | Valid entity ID (non-empty string)
newtype EntityId = EntityId { unEntityId :: Text }
  deriving (Eq, Show, Generic, ToJSON)

instance FromJSON EntityId where
  parseJSON v = do
    t <- parseJSON v
    if T.length t > 0
      then return (EntityId t)
      else fail "EntityId must be non-empty string"

-- | Nullable entity ID (null means no reference)
type NullableEntityId = Maybe EntityId

-- ============================================================================
-- ENUM TYPES
-- ============================================================================

-- | Blend modes (industry standard compatibility)
data BlendMode
  -- Normal
  = BlendNormal
  | BlendDissolve
  -- Darken
  | BlendDarken
  | BlendMultiply
  | BlendColorBurn
  | BlendLinearBurn
  | BlendDarkerColor
  -- Lighten
  | BlendLighten
  | BlendScreen
  | BlendColorDodge
  | BlendLinearDodge
  | BlendLighterColor
  | BlendAdd
  -- Contrast
  | BlendOverlay
  | BlendSoftLight
  | BlendHardLight
  | BlendVividLight
  | BlendLinearLight
  | BlendPinLight
  | BlendHardMix
  -- Inversion
  | BlendDifference
  | BlendExclusion
  | BlendSubtract
  | BlendDivide
  -- Component (HSL)
  | BlendHue
  | BlendSaturation
  | BlendColor
  | BlendLuminosity
  -- Utility/Advanced modes
  | BlendStencilAlpha
  | BlendStencilLuma
  | BlendSilhouetteAlpha
  | BlendSilhouetteLuma
  | BlendBehind
  | BlendAlphaAdd
  | BlendLuminescentPremul
  -- Classic blend modes (legacy compatibility)
  | BlendClassicColorBurn
  | BlendClassicColorDodge
  deriving (Eq, Show, Generic)

instance ToJSON BlendMode where
  toJSON BlendNormal = "normal"
  toJSON BlendDissolve = "dissolve"
  toJSON BlendDarken = "darken"
  toJSON BlendMultiply = "multiply"
  toJSON BlendColorBurn = "color-burn"
  toJSON BlendLinearBurn = "linear-burn"
  toJSON BlendDarkerColor = "darker-color"
  toJSON BlendLighten = "lighten"
  toJSON BlendScreen = "screen"
  toJSON BlendColorDodge = "color-dodge"
  toJSON BlendLinearDodge = "linear-dodge"
  toJSON BlendLighterColor = "lighter-color"
  toJSON BlendAdd = "add"
  toJSON BlendOverlay = "overlay"
  toJSON BlendSoftLight = "soft-light"
  toJSON BlendHardLight = "hard-light"
  toJSON BlendVividLight = "vivid-light"
  toJSON BlendLinearLight = "linear-light"
  toJSON BlendPinLight = "pin-light"
  toJSON BlendHardMix = "hard-mix"
  toJSON BlendDifference = "difference"
  toJSON BlendExclusion = "exclusion"
  toJSON BlendSubtract = "subtract"
  toJSON BlendDivide = "divide"
  toJSON BlendHue = "hue"
  toJSON BlendSaturation = "saturation"
  toJSON BlendColor = "color"
  toJSON BlendLuminosity = "luminosity"
  toJSON BlendStencilAlpha = "stencil-alpha"
  toJSON BlendStencilLuma = "stencil-luma"
  toJSON BlendSilhouetteAlpha = "silhouette-alpha"
  toJSON BlendSilhouetteLuma = "silhouette-luma"
  toJSON BlendBehind = "behind"
  toJSON BlendAlphaAdd = "alpha-add"
  toJSON BlendLuminescentPremul = "luminescent-premul"
  toJSON BlendClassicColorBurn = "classic-color-burn"
  toJSON BlendClassicColorDodge = "classic-color-dodge"

instance FromJSON BlendMode where
  parseJSON (String "normal") = return BlendNormal
  parseJSON (String "dissolve") = return BlendDissolve
  parseJSON (String "darken") = return BlendDarken
  parseJSON (String "multiply") = return BlendMultiply
  parseJSON (String "color-burn") = return BlendColorBurn
  parseJSON (String "linear-burn") = return BlendLinearBurn
  parseJSON (String "darker-color") = return BlendDarkerColor
  parseJSON (String "lighten") = return BlendLighten
  parseJSON (String "screen") = return BlendScreen
  parseJSON (String "color-dodge") = return BlendColorDodge
  parseJSON (String "linear-dodge") = return BlendLinearDodge
  parseJSON (String "lighter-color") = return BlendLighterColor
  parseJSON (String "add") = return BlendAdd
  parseJSON (String "overlay") = return BlendOverlay
  parseJSON (String "soft-light") = return BlendSoftLight
  parseJSON (String "hard-light") = return BlendHardLight
  parseJSON (String "vivid-light") = return BlendVividLight
  parseJSON (String "linear-light") = return BlendLinearLight
  parseJSON (String "pin-light") = return BlendPinLight
  parseJSON (String "hard-mix") = return BlendHardMix
  parseJSON (String "difference") = return BlendDifference
  parseJSON (String "exclusion") = return BlendExclusion
  parseJSON (String "subtract") = return BlendSubtract
  parseJSON (String "divide") = return BlendDivide
  parseJSON (String "hue") = return BlendHue
  parseJSON (String "saturation") = return BlendSaturation
  parseJSON (String "color") = return BlendColor
  parseJSON (String "luminosity") = return BlendLuminosity
  parseJSON (String "stencil-alpha") = return BlendStencilAlpha
  parseJSON (String "stencil-luma") = return BlendStencilLuma
  parseJSON (String "silhouette-alpha") = return BlendSilhouetteAlpha
  parseJSON (String "silhouette-luma") = return BlendSilhouetteLuma
  parseJSON (String "behind") = return BlendBehind
  parseJSON (String "alpha-add") = return BlendAlphaAdd
  parseJSON (String "luminescent-premul") = return BlendLuminescentPremul
  parseJSON (String "classic-color-burn") = return BlendClassicColorBurn
  parseJSON (String "classic-color-dodge") = return BlendClassicColorDodge
  parseJSON _ = fail "Invalid BlendMode"

-- | Quality modes
data QualityMode
  = QualityDraft
  | QualityBest
  deriving (Eq, Show, Generic)

instance ToJSON QualityMode where
  toJSON QualityDraft = "draft"
  toJSON QualityBest = "best"

instance FromJSON QualityMode where
  parseJSON (String "draft") = return QualityDraft
  parseJSON (String "best") = return QualityBest
  parseJSON _ = fail "Invalid QualityMode (expected 'draft' or 'best')"
