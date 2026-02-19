-- | Lattice.Utils.TypeGuards - Runtime type checks and safe defaults
-- |
-- | Runtime type guards with explicit validation.
-- | These check values and narrow types at runtime.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/TypeGuards.lean

module Lattice.Utils.TypeGuards
  ( isFiniteNumber
  , isNonEmptyString
  , isNonEmptyArray
  , isPositive
  , isNonNegative
  , isUnitRange
  , isPercentageRange
  , isColorChannel
  , isValidVec2
  , isValidVec3
  , isValidVec4
  , BoundingBox
  , mkBoundingBox
  , isValidRGB
  , isValidRGBA
  , safeCoordinateDefault
  , safeNonNegativeDefault
  , safePositiveDefault
  , safeUnitDefault
  , safePercentageDefault
  , safeArrayDefault
  , safeStringDefault
  , assertFinite
  , assertPositive
  , assertNonNegative
  , assertNonEmpty
  , assertNonEmptyArray
  , mkVec2Checked
  , mkVec3Checked
  , mkRGBChecked
  , mkRGBAChecked
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Number (isFinite, isNaN) as Number
import Lattice.Primitives
import Lattice.Utils.Validation (ValidationResult(..), validateVec2, validateVec3, validateRGB, validateRGBA)

-- ────────────────────────────────────────────────────────────────────────────
-- Primitive Type Guards
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if Number is finite (not NaN, not Infinity)
isFiniteNumber :: Number -> Boolean
isFiniteNumber x = Number.isFinite x && not (Number.isNaN x)

-- | Check if String is non-empty
isNonEmptyString :: String -> Boolean
isNonEmptyString = not <<< String.null

-- | Check if array is non-empty
isNonEmptyArray :: forall a. Array a -> Boolean
isNonEmptyArray = not <<< Array.null

-- ────────────────────────────────────────────────────────────────────────────
-- Numeric Type Guards
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if value is positive
isPositive :: Number -> Boolean
isPositive x = isFiniteNumber x && x > 0.0

-- | Check if value is non-negative
isNonNegative :: Number -> Boolean
isNonNegative x = isFiniteNumber x && x >= 0.0

-- | Check if value is in unit range [0, 1]
isUnitRange :: Number -> Boolean
isUnitRange x = isFiniteNumber x && x >= 0.0 && x <= 1.0

-- | Check if value is percentage [0, 100]
isPercentageRange :: Number -> Boolean
isPercentageRange x = isFiniteNumber x && x >= 0.0 && x <= 100.0

-- | Check if value is color channel [0, 255]
isColorChannel :: Number -> Boolean
isColorChannel x = isFiniteNumber x && x >= 0.0 && x <= 255.0

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Type Guards
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if Vec2 has valid coordinates
isValidVec2 :: Vec2 -> Boolean
isValidVec2 v = isFiniteNumber (unFiniteFloat v.x) && isFiniteNumber (unFiniteFloat v.y)

-- | Check if Vec3 has valid coordinates
isValidVec3 :: Vec3 -> Boolean
isValidVec3 v = isFiniteNumber (unFiniteFloat v.x) && isFiniteNumber (unFiniteFloat v.y) && isFiniteNumber (unFiniteFloat v.z)

-- | Check if Vec4 has valid coordinates
isValidVec4 :: Vec4 -> Boolean
isValidVec4 v = isFiniteNumber (unFiniteFloat v.x) && isFiniteNumber (unFiniteFloat v.y) && isFiniteNumber (unFiniteFloat v.z) && isFiniteNumber (unFiniteFloat v.w)

-- ────────────────────────────────────────────────────────────────────────────
-- Bounding Box
-- ────────────────────────────────────────────────────────────────────────────

-- | Bounding box with validated dimensions
type BoundingBox =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , width :: PositiveFloat
  , height :: PositiveFloat
  }

-- | Try to create bounding box from raw values
mkBoundingBox :: Number -> Number -> Number -> Number -> Maybe BoundingBox
mkBoundingBox x y width height
  | isFiniteNumber x && isFiniteNumber y && isPositive width && isPositive height =
      Just { x: FiniteFloat x, y: FiniteFloat y, width: PositiveFloat width, height: PositiveFloat height }
  | otherwise = Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Color Type Guards
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if RGB has valid channel values
isValidRGB :: RGB -> Boolean
isValidRGB c = isColorChannel (unUnitFloat c.r) && isColorChannel (unUnitFloat c.g) && isColorChannel (unUnitFloat c.b)

-- | Check if RGBA has valid values
isValidRGBA :: RGBA -> Boolean
isValidRGBA c = isColorChannel (unUnitFloat c.r) && isColorChannel (unUnitFloat c.g) && isColorChannel (unUnitFloat c.b) && isUnitRange (unUnitFloat c.a)

-- ────────────────────────────────────────────────────────────────────────────
-- Safe Defaults
-- ────────────────────────────────────────────────────────────────────────────

-- | Safe coordinate default - allows negative, zero, positive
safeCoordinateDefault :: Maybe Number -> FiniteFloat -> FiniteFloat
safeCoordinateDefault Nothing def = def
safeCoordinateDefault (Just v) def
  | isFiniteNumber v = FiniteFloat v
  | otherwise = def

-- | Safe non-negative default - requires >= 0
safeNonNegativeDefault :: Maybe Number -> NonNegativeFloat -> NonNegativeFloat
safeNonNegativeDefault Nothing def = def
safeNonNegativeDefault (Just v) def
  | isNonNegative v = NonNegativeFloat v
  | otherwise = def

-- | Safe positive default - requires > 0
safePositiveDefault :: Maybe Number -> PositiveFloat -> PositiveFloat
safePositiveDefault Nothing def = def
safePositiveDefault (Just v) def
  | isPositive v = PositiveFloat v
  | otherwise = def

-- | Safe unit default - requires [0, 1]
safeUnitDefault :: Maybe Number -> UnitFloat -> UnitFloat
safeUnitDefault Nothing def = def
safeUnitDefault (Just v) def
  | isUnitRange v = UnitFloat v
  | otherwise = def

-- | Safe percentage default - requires [0, 100]
safePercentageDefault :: Maybe Number -> Percentage -> Percentage
safePercentageDefault Nothing def = def
safePercentageDefault (Just v) def
  | isPercentageRange v = Percentage v
  | otherwise = def

-- | Safe array default
safeArrayDefault :: forall a. Maybe (Array a) -> Array a -> Array a
safeArrayDefault Nothing def = def
safeArrayDefault (Just v) _ = v

-- | Safe non-empty string default
safeStringDefault :: Maybe String -> NonEmptyString -> NonEmptyString
safeStringDefault Nothing def = def
safeStringDefault (Just v) def
  | String.null v = def
  | otherwise = NonEmptyString v

-- ────────────────────────────────────────────────────────────────────────────
-- Assertions
-- ────────────────────────────────────────────────────────────────────────────

-- | Assert and extract finite number
assertFinite :: Number -> String -> Either String FiniteFloat
assertFinite value name
  | isFiniteNumber value = Right (FiniteFloat value)
  | otherwise = Left (name <> " must be finite, got " <> show value)

-- | Assert and extract positive number
assertPositive :: Number -> String -> Either String PositiveFloat
assertPositive value name
  | isPositive value = Right (PositiveFloat value)
  | otherwise = Left (name <> " must be positive, got " <> show value)

-- | Assert and extract non-negative number
assertNonNegative :: Number -> String -> Either String NonNegativeFloat
assertNonNegative value name
  | isNonNegative value = Right (NonNegativeFloat value)
  | otherwise = Left (name <> " must be non-negative, got " <> show value)

-- | Assert non-empty string
assertNonEmpty :: String -> String -> Either String NonEmptyString
assertNonEmpty value name
  | String.null value = Left (name <> " cannot be empty")
  | otherwise = Right (NonEmptyString value)

-- | Assert array is non-empty
assertNonEmptyArray :: forall a. Array a -> String -> Either String (Array a)
assertNonEmptyArray arr name
  | Array.null arr = Left (name <> " cannot be empty")
  | otherwise = Right arr

-- ────────────────────────────────────────────────────────────────────────────
-- Checked Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Create Vec2 with validation
mkVec2Checked :: Number -> Number -> String -> ValidationResult Vec2
mkVec2Checked x y name = validateVec2 x y name

-- | Create Vec3 with validation
mkVec3Checked :: Number -> Number -> Number -> String -> ValidationResult Vec3
mkVec3Checked x y z name = validateVec3 x y z name

-- | Create RGB with validation
mkRGBChecked :: Number -> Number -> Number -> String -> ValidationResult RGB
mkRGBChecked r g b name = validateRGB r g b name

-- | Create RGBA with validation
mkRGBAChecked :: Number -> Number -> Number -> Number -> String -> ValidationResult RGBA
mkRGBAChecked r g b a name = validateRGBA r g b a name
