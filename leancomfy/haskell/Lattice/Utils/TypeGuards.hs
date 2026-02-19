{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Utils.TypeGuards
Description : Runtime type checks and safe defaults
Copyright   : (c) Lattice, 2026
License     : MIT

Runtime type guards with explicit validation.
These check values and narrow types at runtime.

Source: leancomfy/lean/Lattice/Utils/TypeGuards.lean
-}

module Lattice.Utils.TypeGuards
  ( -- * Primitive Type Guards
    isFiniteDouble
  , isNonEmptyString
  , isNonEmptyList
    -- * Numeric Type Guards
  , isPositive
  , isNonNegative
  , isUnitRange
  , isPercentageRange
  , isColorChannel
    -- * Vector Type Guards
  , isValidVec2
  , isValidVec3
  , isValidVec4
    -- * Bounding Box
  , BoundingBox(..)
  , mkBoundingBox
    -- * Color Type Guards
  , isValidRGB
  , isValidRGBA
    -- * Safe Defaults
  , safeCoordinateDefault
  , safeNonNegativeDefault
  , safePositiveDefault
  , safeUnitDefault
  , safePercentageDefault
  , safeArrayDefault
  , safeStringDefault
    -- * Assertions
  , assertFinite
  , assertPositive
  , assertNonNegative
  , assertNonEmpty
  , assertNonEmptyList
    -- * Checked Constructors
  , mkVec2Checked
  , mkVec3Checked
  , mkRGBChecked
  , mkRGBAChecked
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import qualified Data.Vector as V
import Lattice.Primitives
import Lattice.Utils.Validation

--------------------------------------------------------------------------------
-- Primitive Type Guards
--------------------------------------------------------------------------------

-- | Check if Double is finite (not NaN, not Infinity)
isFiniteDouble :: Double -> Bool
isFiniteDouble x = not (isNaN x) && not (isInfinite x)

-- | Check if Text is non-empty
isNonEmptyString :: Text -> Bool
isNonEmptyString = not . T.null

-- | Check if list is non-empty
isNonEmptyList :: [a] -> Bool
isNonEmptyList = not . null

--------------------------------------------------------------------------------
-- Numeric Type Guards
--------------------------------------------------------------------------------

-- | Check if value is positive
isPositive :: Double -> Bool
isPositive x = isFiniteDouble x && x > 0

-- | Check if value is non-negative
isNonNegative :: Double -> Bool
isNonNegative x = isFiniteDouble x && x >= 0

-- | Check if value is in unit range [0, 1]
isUnitRange :: Double -> Bool
isUnitRange x = isFiniteDouble x && x >= 0 && x <= 1

-- | Check if value is percentage [0, 100]
isPercentageRange :: Double -> Bool
isPercentageRange x = isFiniteDouble x && x >= 0 && x <= 100

-- | Check if value is color channel [0, 255]
isColorChannel :: Double -> Bool
isColorChannel x = isFiniteDouble x && x >= 0 && x <= 255

--------------------------------------------------------------------------------
-- Vector Type Guards
--------------------------------------------------------------------------------

-- | Check if Vec2 has valid coordinates
isValidVec2 :: Vec2 -> Bool
isValidVec2 (Vec2 (FiniteFloat x) (FiniteFloat y)) =
  isFiniteDouble x && isFiniteDouble y

-- | Check if Vec3 has valid coordinates
isValidVec3 :: Vec3 -> Bool
isValidVec3 (Vec3 (FiniteFloat x) (FiniteFloat y) (FiniteFloat z)) =
  isFiniteDouble x && isFiniteDouble y && isFiniteDouble z

-- | Check if Vec4 has valid coordinates
isValidVec4 :: Vec4 -> Bool
isValidVec4 (Vec4 (FiniteFloat x) (FiniteFloat y) (FiniteFloat z) (FiniteFloat w)) =
  isFiniteDouble x && isFiniteDouble y && isFiniteDouble z && isFiniteDouble w

--------------------------------------------------------------------------------
-- Bounding Box
--------------------------------------------------------------------------------

-- | Bounding box with validated dimensions
data BoundingBox = BoundingBox
  { bbX :: !FiniteFloat
  , bbY :: !FiniteFloat
  , bbWidth :: !PositiveFloat
  , bbHeight :: !PositiveFloat
  } deriving (Eq, Show)

-- | Try to create bounding box from raw values
mkBoundingBox :: Double -> Double -> Double -> Double -> Maybe BoundingBox
mkBoundingBox x y width height
  | isFiniteDouble x && isFiniteDouble y && isPositive width && isPositive height =
      Just $ BoundingBox
        (FiniteFloat x)
        (FiniteFloat y)
        (PositiveFloat width)
        (PositiveFloat height)
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Color Type Guards
--------------------------------------------------------------------------------

-- | Check if RGB has valid channel values (all in [0, 255])
isValidRGB :: RGB -> Bool
isValidRGB (RGB (FiniteFloat r) (FiniteFloat g) (FiniteFloat b)) =
  isColorChannel r && isColorChannel g && isColorChannel b

-- | Check if RGBA has valid values (R,G,B in [0, 255], A in [0, 1])
isValidRGBA :: RGBA -> Bool
isValidRGBA (RGBA (FiniteFloat r) (FiniteFloat g) (FiniteFloat b) (UnitFloat a)) =
  isColorChannel r && isColorChannel g && isColorChannel b && isUnitRange a

--------------------------------------------------------------------------------
-- Safe Defaults
--------------------------------------------------------------------------------

-- | Safe coordinate default - allows negative, zero, positive
safeCoordinateDefault :: Maybe Double -> FiniteFloat -> FiniteFloat
safeCoordinateDefault Nothing def = def
safeCoordinateDefault (Just v) def
  | isFiniteDouble v = FiniteFloat v
  | otherwise = def

-- | Safe non-negative default - requires >= 0
safeNonNegativeDefault :: Maybe Double -> NonNegativeFloat -> NonNegativeFloat
safeNonNegativeDefault Nothing def = def
safeNonNegativeDefault (Just v) def
  | isNonNegative v = NonNegativeFloat v
  | otherwise = def

-- | Safe positive default - requires > 0
safePositiveDefault :: Maybe Double -> PositiveFloat -> PositiveFloat
safePositiveDefault Nothing def = def
safePositiveDefault (Just v) def
  | isPositive v = PositiveFloat v
  | otherwise = def

-- | Safe unit default - requires [0, 1]
safeUnitDefault :: Maybe Double -> UnitFloat -> UnitFloat
safeUnitDefault Nothing def = def
safeUnitDefault (Just v) def
  | isUnitRange v = UnitFloat v
  | otherwise = def

-- | Safe percentage default - requires [0, 100]
safePercentageDefault :: Maybe Double -> Percentage -> Percentage
safePercentageDefault Nothing def = def
safePercentageDefault (Just v) def
  | isPercentageRange v = Percentage v
  | otherwise = def

-- | Safe array default
safeArrayDefault :: Maybe (Vector a) -> Vector a -> Vector a
safeArrayDefault Nothing def = def
safeArrayDefault (Just v) _ = v

-- | Safe non-empty string default
safeStringDefault :: Maybe Text -> NonEmptyString -> NonEmptyString
safeStringDefault Nothing def = def
safeStringDefault (Just v) def
  | T.null v = def
  | otherwise = NonEmptyString v

--------------------------------------------------------------------------------
-- Assertions
--------------------------------------------------------------------------------

-- | Assert and extract finite double
assertFinite :: Double -> Text -> Either Text FiniteFloat
assertFinite value name
  | isFiniteDouble value = Right (FiniteFloat value)
  | otherwise = Left (name <> " must be finite, got " <> T.pack (show value))

-- | Assert and extract positive double
assertPositive :: Double -> Text -> Either Text PositiveFloat
assertPositive value name
  | isPositive value = Right (PositiveFloat value)
  | otherwise = Left (name <> " must be positive, got " <> T.pack (show value))

-- | Assert and extract non-negative double
assertNonNegative :: Double -> Text -> Either Text NonNegativeFloat
assertNonNegative value name
  | isNonNegative value = Right (NonNegativeFloat value)
  | otherwise = Left (name <> " must be non-negative, got " <> T.pack (show value))

-- | Assert non-empty string
assertNonEmpty :: Text -> Text -> Either Text NonEmptyString
assertNonEmpty value name
  | T.null value = Left (name <> " cannot be empty")
  | otherwise = Right (NonEmptyString value)

-- | Assert list is non-empty
assertNonEmptyList :: [a] -> Text -> Either Text [a]
assertNonEmptyList [] name = Left (name <> " cannot be empty")
assertNonEmptyList xs _ = Right xs

--------------------------------------------------------------------------------
-- Checked Constructors
--------------------------------------------------------------------------------

-- | Create Vec2 with validation
mkVec2Checked :: Double -> Double -> Text -> ValidationResult Vec2
mkVec2Checked x y name = validateVec2 x y name

-- | Create Vec3 with validation
mkVec3Checked :: Double -> Double -> Double -> Text -> ValidationResult Vec3
mkVec3Checked x y z name = validateVec3 x y z name

-- | Create RGB with validation
mkRGBChecked :: Double -> Double -> Double -> Text -> ValidationResult RGB
mkRGBChecked r g b name = validateRGB r g b name

-- | Create RGBA with validation
mkRGBAChecked :: Double -> Double -> Double -> Double -> Text -> ValidationResult RGBA
mkRGBAChecked r g b a name = validateRGBA r g b a name
