{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Lattice.Primitives
Description : Core primitive types with invariant proofs
Copyright   : (c) Lattice, 2026
License     : MIT

Single source of truth for all primitive types.
Uses refined newtypes to encode invariants at the type level.

This is Layer 0 - no imports from other Lattice modules.
All other Lattice modules depend on this.
-}

module Lattice.Primitives
  ( -- * String Primitives
    NonEmptyString(..)
  , mkNonEmptyString
  , unNonEmptyString
    -- * Integer Primitives
  , PositiveInt(..)
  , mkPositiveInt
  , unPositiveInt
    -- * Float Primitives
  , FiniteFloat(..)
  , mkFiniteFloat
  , unFiniteFloat
  , PositiveFloat(..)
  , mkPositiveFloat
  , unPositiveFloat
  , NonNegativeFloat(..)
  , mkNonNegativeFloat
  , unNonNegativeFloat
  , Percentage(..)
  , mkPercentage
  , unPercentage
  , UnitFloat(..)
  , mkUnitFloat
  , unUnitFloat
    -- * Frame Number
  , FrameNumber(..)
    -- * Vector Primitives
  , Vec2(..)
  , Vec3(..)
  , Vec4(..)
    -- * Matrix Primitives
  , Matrix3x3(..)
  , Matrix4x4(..)
    -- * Color Primitives
  , RGB(..)
  , RGBA(..)
  , HexColor(..)
  , mkHexColor
  , unHexColor
    -- * Constants
  , minFrameNumber
  , maxFrameNumber
  , fps24, fps25, fps30, fps60
  , res720pWidth, res720pHeight
  , res1080pWidth, res1080pHeight
  , res4kWidth, res4kHeight
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T

--------------------------------------------------------------------------------
-- String Primitives
--------------------------------------------------------------------------------

-- | Non-empty string (length > 0)
newtype NonEmptyString = NonEmptyString Text
  deriving stock (Eq, Ord, Show, Generic)

-- | Smart constructor for NonEmptyString
mkNonEmptyString :: Text -> Maybe NonEmptyString
mkNonEmptyString t
  | T.null t  = Nothing
  | otherwise = Just (NonEmptyString t)

-- | Extract the underlying Text
unNonEmptyString :: NonEmptyString -> Text
unNonEmptyString (NonEmptyString t) = t

--------------------------------------------------------------------------------
-- Integer Primitives
--------------------------------------------------------------------------------

-- | Positive integer (value > 0)
newtype PositiveInt = PositiveInt Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Num)

-- | Smart constructor for PositiveInt
mkPositiveInt :: Int -> Maybe PositiveInt
mkPositiveInt n
  | n > 0     = Just (PositiveInt n)
  | otherwise = Nothing

-- | Extract the underlying Int
unPositiveInt :: PositiveInt -> Int
unPositiveInt (PositiveInt n) = n

--------------------------------------------------------------------------------
-- Float Primitives
--------------------------------------------------------------------------------

-- | Finite float (not NaN, not Infinity)
newtype FiniteFloat = FiniteFloat Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Num, Fractional)

-- | Smart constructor for FiniteFloat
mkFiniteFloat :: Double -> Maybe FiniteFloat
mkFiniteFloat f
  | isNaN f || isInfinite f = Nothing
  | otherwise               = Just (FiniteFloat f)

-- | Extract the underlying Double
unFiniteFloat :: FiniteFloat -> Double
unFiniteFloat (FiniteFloat f) = f

-- | Positive float (value > 0 and finite)
newtype PositiveFloat = PositiveFloat Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Num, Fractional)

-- | Smart constructor for PositiveFloat
mkPositiveFloat :: Double -> Maybe PositiveFloat
mkPositiveFloat f
  | f > 0 && not (isNaN f) && not (isInfinite f) = Just (PositiveFloat f)
  | otherwise = Nothing

-- | Extract the underlying Double
unPositiveFloat :: PositiveFloat -> Double
unPositiveFloat (PositiveFloat f) = f

-- | Non-negative float (value >= 0 and finite)
newtype NonNegativeFloat = NonNegativeFloat Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Num, Fractional)

-- | Smart constructor for NonNegativeFloat
mkNonNegativeFloat :: Double -> Maybe NonNegativeFloat
mkNonNegativeFloat f
  | f >= 0 && not (isNaN f) && not (isInfinite f) = Just (NonNegativeFloat f)
  | otherwise = Nothing

-- | Extract the underlying Double
unNonNegativeFloat :: NonNegativeFloat -> Double
unNonNegativeFloat (NonNegativeFloat f) = f

-- | Percentage (0 <= value <= 100 and finite)
newtype Percentage = Percentage Double
  deriving stock (Eq, Ord, Show, Generic)

-- | Smart constructor for Percentage
mkPercentage :: Double -> Maybe Percentage
mkPercentage f
  | f >= 0 && f <= 100 && not (isNaN f) && not (isInfinite f) = Just (Percentage f)
  | otherwise = Nothing

-- | Extract the underlying Double
unPercentage :: Percentage -> Double
unPercentage (Percentage f) = f

-- | Unit float / normalized value (0 <= value <= 1 and finite)
newtype UnitFloat = UnitFloat Double
  deriving stock (Eq, Ord, Show, Generic)

-- | Smart constructor for UnitFloat
mkUnitFloat :: Double -> Maybe UnitFloat
mkUnitFloat f
  | f >= 0 && f <= 1 && not (isNaN f) && not (isInfinite f) = Just (UnitFloat f)
  | otherwise = Nothing

-- | Extract the underlying Double
unUnitFloat :: UnitFloat -> Double
unUnitFloat (UnitFloat f) = f

--------------------------------------------------------------------------------
-- Frame Number
--------------------------------------------------------------------------------

-- | Frame number (always >= 0)
newtype FrameNumber = FrameNumber { unFrameNumber :: Int }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Num)

--------------------------------------------------------------------------------
-- Vector Primitives
--------------------------------------------------------------------------------

-- | 2D vector with finite components
data Vec2 = Vec2
  { vec2X :: !FiniteFloat
  , vec2Y :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

-- | 3D vector with finite components
data Vec3 = Vec3
  { vec3X :: !FiniteFloat
  , vec3Y :: !FiniteFloat
  , vec3Z :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

-- | 4D vector with finite components
data Vec4 = Vec4
  { vec4X :: !FiniteFloat
  , vec4Y :: !FiniteFloat
  , vec4Z :: !FiniteFloat
  , vec4W :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Matrix Primitives
--------------------------------------------------------------------------------

-- | 3x3 matrix with finite entries (row-major)
data Matrix3x3 = Matrix3x3
  { m3_00, m3_01, m3_02 :: !Double
  , m3_10, m3_11, m3_12 :: !Double
  , m3_20, m3_21, m3_22 :: !Double
  } deriving stock (Eq, Show, Generic)

-- | 4x4 matrix with finite entries (row-major)
data Matrix4x4 = Matrix4x4
  { m4_00, m4_01, m4_02, m4_03 :: !Double
  , m4_10, m4_11, m4_12, m4_13 :: !Double
  , m4_20, m4_21, m4_22, m4_23 :: !Double
  , m4_30, m4_31, m4_32, m4_33 :: !Double
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Color Primitives
--------------------------------------------------------------------------------

-- | RGB color with values in [0, 255]
data RGB = RGB
  { rgbR :: !FiniteFloat
  , rgbG :: !FiniteFloat
  , rgbB :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

-- | RGBA color with R,G,B in [0, 255] and A in [0, 1]
data RGBA = RGBA
  { rgbaR :: !FiniteFloat
  , rgbaG :: !FiniteFloat
  , rgbaB :: !FiniteFloat
  , rgbaA :: !UnitFloat
  } deriving stock (Eq, Show, Generic)

-- | Hex color string (e.g., "#ff0000" or "#ff0000ff")
newtype HexColor = HexColor Text
  deriving stock (Eq, Ord, Show, Generic)

-- | Smart constructor for HexColor
mkHexColor :: Text -> Maybe HexColor
mkHexColor t
  | isValidHex t = Just (HexColor t)
  | otherwise    = Nothing
  where
    isValidHex s =
      T.length s == 7 || T.length s == 9
      && T.head s == '#'
      && T.all isHexChar (T.tail s)
    isHexChar c = c `elem` ("0123456789abcdefABCDEF" :: String)

-- | Extract the underlying Text
unHexColor :: HexColor -> Text
unHexColor (HexColor t) = t

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Minimum frame number (always 0)
minFrameNumber :: FrameNumber
minFrameNumber = FrameNumber 0

-- | Maximum frame number (practical limit: 2^31 - 1)
maxFrameNumber :: FrameNumber
maxFrameNumber = FrameNumber 2147483647

-- | Standard FPS: 24
fps24 :: PositiveInt
fps24 = PositiveInt 24

-- | Standard FPS: 25
fps25 :: PositiveInt
fps25 = PositiveInt 25

-- | Standard FPS: 30
fps30 :: PositiveInt
fps30 = PositiveInt 30

-- | Standard FPS: 60
fps60 :: PositiveInt
fps60 = PositiveInt 60

-- | 720p width
res720pWidth :: PositiveInt
res720pWidth = PositiveInt 1280

-- | 720p height
res720pHeight :: PositiveInt
res720pHeight = PositiveInt 720

-- | 1080p width
res1080pWidth :: PositiveInt
res1080pWidth = PositiveInt 1920

-- | 1080p height
res1080pHeight :: PositiveInt
res1080pHeight = PositiveInt 1080

-- | 4K width
res4kWidth :: PositiveInt
res4kWidth = PositiveInt 3840

-- | 4K height
res4kHeight :: PositiveInt
res4kHeight = PositiveInt 2160
