{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveFunctor #-}

{-|
Module      : Lattice.Utils.Validation
Description : Runtime input validation with Result types
Copyright   : (c) Lattice, 2026
License     : MIT

Validates input at runtime boundaries (AI commands, file imports, user input).
All validators return explicit success/failure results.

Source: leancomfy/lean/Lattice/Utils/Validation.lean
-}

module Lattice.Utils.Validation
  ( -- * Result Type
    ValidationResult(..)
  , ok
  , fail'
  , isOk
  , getOr
    -- * Primitive Validators
  , StringOptions(..)
  , validateString
  , NumberOptions(..)
  , validateFiniteNumber
  , validateInteger
  , validateBoolean
  , validateEnum
    -- * Numeric Type Validators
  , validatePositive
  , validateNonNegative
  , validateUnit
  , validatePercentage
  , validateFrameNumber
    -- * Array Validators
  , validateArray
  , validateNumberArray
    -- * Vector Validators
  , validateVec2
  , validateVec3
  , validateVec4
    -- * Color Validators
  , validateRGB
  , validateRGBA
    -- * Optional/Default Helpers
  , optional
  , withDefault
    -- * Composition Helpers
  , validateAll
  , andThen
  , both
  ) where

import Prelude hiding (fail)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Result Type
--------------------------------------------------------------------------------

-- | Validation result - either success with typed value, or failure with error
data ValidationResult a
  = Ok !a
  | Fail !Text
  deriving (Eq, Show, Functor)

instance Applicative ValidationResult where
  pure = Ok
  Ok f <*> Ok x = Ok (f x)
  Fail e <*> _ = Fail e
  _ <*> Fail e = Fail e

instance Monad ValidationResult where
  Ok x >>= f = f x
  Fail e >>= _ = Fail e

-- | Create success result
ok :: a -> ValidationResult a
ok = Ok

-- | Create failure result
fail' :: Text -> ValidationResult a
fail' = Fail

-- | Check if result is success
isOk :: ValidationResult a -> Bool
isOk (Ok _) = True
isOk (Fail _) = False

-- | Get value with default fallback
getOr :: a -> ValidationResult a -> a
getOr _ (Ok v) = v
getOr d (Fail _) = d

--------------------------------------------------------------------------------
-- Primitive Validators
--------------------------------------------------------------------------------

-- | Options for string validation
data StringOptions = StringOptions
  { soMinLength :: !(Maybe Int)
  , soMaxLength :: !(Maybe Int)
  , soAllowEmpty :: !Bool
  } deriving (Eq, Show)

defaultStringOptions :: StringOptions
defaultStringOptions = StringOptions Nothing Nothing False

-- | Validate non-empty string
validateString :: Text -> Text -> StringOptions -> ValidationResult NonEmptyString
validateString value name opts
  | not (soAllowEmpty opts) && T.null value =
      Fail (name <> " cannot be empty")
  | Just minLen <- soMinLength opts, T.length value < minLen =
      Fail (name <> " must be at least " <> T.pack (show minLen) <> " characters")
  | Just maxLen <- soMaxLength opts, T.length value > maxLen =
      Fail (name <> " must be at most " <> T.pack (show maxLen) <> " characters")
  | T.null value = Fail (name <> " cannot be empty")
  | otherwise = Ok (NonEmptyString value)

-- | Options for numeric validation
data NumberOptions = NumberOptions
  { noMin :: !(Maybe Double)
  , noMax :: !(Maybe Double)
  } deriving (Eq, Show)

defaultNumberOptions :: NumberOptions
defaultNumberOptions = NumberOptions Nothing Nothing

-- | Check if Double is finite
isFiniteDouble :: Double -> Bool
isFiniteDouble x = not (isNaN x) && not (isInfinite x)

-- | Validate finite number
validateFiniteNumber :: Double -> Text -> NumberOptions -> ValidationResult FiniteFloat
validateFiniteNumber value name opts
  | not (isFiniteDouble value) =
      Fail (name <> " must be a finite number")
  | Just minVal <- noMin opts, value < minVal =
      Fail (name <> " must be >= " <> T.pack (show minVal) <> ", got " <> T.pack (show value))
  | Just maxVal <- noMax opts, value > maxVal =
      Fail (name <> " must be <= " <> T.pack (show maxVal) <> ", got " <> T.pack (show value))
  | otherwise = Ok (FiniteFloat value)

-- | Validate integer
validateInteger :: Double -> Text -> NumberOptions -> ValidationResult Int
validateInteger value name opts = do
  _ <- validateFiniteNumber value name opts
  let intVal = truncate value :: Int
  if fromIntegral intVal == value
    then Ok intVal
    else Fail (name <> " must be an integer, got " <> T.pack (show value))

-- | Validate boolean (always succeeds)
validateBoolean :: Bool -> Text -> ValidationResult Bool
validateBoolean = const . Ok

-- | Validate value is in allowed list
validateEnum :: (Eq a, Show a) => a -> Text -> [a] -> ValidationResult a
validateEnum value name allowed
  | value `elem` allowed = Ok value
  | otherwise = Fail (name <> " must be one of allowed values")

--------------------------------------------------------------------------------
-- Numeric Type Validators
--------------------------------------------------------------------------------

-- | Validate positive number (> 0)
validatePositive :: Double -> Text -> ValidationResult PositiveFloat
validatePositive value name
  | not (isFiniteDouble value) = Fail (name <> " must be a finite number")
  | value <= 0 = Fail (name <> " must be positive, got " <> T.pack (show value))
  | otherwise = Ok (PositiveFloat value)

-- | Validate non-negative number (>= 0)
validateNonNegative :: Double -> Text -> ValidationResult NonNegativeFloat
validateNonNegative value name
  | not (isFiniteDouble value) = Fail (name <> " must be a finite number")
  | value < 0 = Fail (name <> " must be non-negative, got " <> T.pack (show value))
  | otherwise = Ok (NonNegativeFloat value)

-- | Validate unit float (0 to 1)
validateUnit :: Double -> Text -> ValidationResult UnitFloat
validateUnit value name
  | not (isFiniteDouble value) = Fail (name <> " must be a finite number")
  | value < 0 = Fail (name <> " must be >= 0, got " <> T.pack (show value))
  | value > 1 = Fail (name <> " must be <= 1, got " <> T.pack (show value))
  | otherwise = Ok (UnitFloat value)

-- | Validate percentage (0 to 100)
validatePercentage :: Double -> Text -> ValidationResult Percentage
validatePercentage value name
  | not (isFiniteDouble value) = Fail (name <> " must be a finite number")
  | value < 0 = Fail (name <> " must be >= 0, got " <> T.pack (show value))
  | value > 100 = Fail (name <> " must be <= 100, got " <> T.pack (show value))
  | otherwise = Ok (Percentage value)

-- | Validate frame number (non-negative integer)
validateFrameNumber :: Double -> Text -> ValidationResult FrameNumber
validateFrameNumber value name
  | not (isFiniteDouble value) = Fail (name <> " must be a finite number")
  | value < 0 = Fail (name <> " must be non-negative, got " <> T.pack (show value))
  | otherwise =
      let intVal = truncate value :: Int
      in if fromIntegral intVal == value && intVal >= 0
         then Ok (FrameNumber (fromIntegral intVal))
         else Fail (name <> " must be a non-negative integer, got " <> T.pack (show value))

--------------------------------------------------------------------------------
-- Array Validators
--------------------------------------------------------------------------------

-- | Validate array with item validator
validateArray :: [Double] -> Text -> (Double -> Text -> ValidationResult a) -> ValidationResult [a]
validateArray values name itemValidator = go values 0 []
  where
    go [] _ acc = Ok (reverse acc)
    go (x:xs) idx acc =
      case itemValidator x (name <> "[" <> T.pack (show idx) <> "]") of
        Ok v -> go xs (idx + 1) (v : acc)
        Fail e -> Fail e

-- | Validate array of finite numbers
validateNumberArray :: [Double] -> Text -> NumberOptions -> ValidationResult [FiniteFloat]
validateNumberArray values name opts =
  validateArray values name (\v n -> validateFiniteNumber v n opts)

--------------------------------------------------------------------------------
-- Vector Validators
--------------------------------------------------------------------------------

-- | Validate Vec2
validateVec2 :: Double -> Double -> Text -> ValidationResult Vec2
validateVec2 x y name = do
  vx <- validateFiniteNumber x (name <> ".x") defaultNumberOptions
  vy <- validateFiniteNumber y (name <> ".y") defaultNumberOptions
  pure (Vec2 vx vy)

-- | Validate Vec3
validateVec3 :: Double -> Double -> Double -> Text -> ValidationResult Vec3
validateVec3 x y z name = do
  vx <- validateFiniteNumber x (name <> ".x") defaultNumberOptions
  vy <- validateFiniteNumber y (name <> ".y") defaultNumberOptions
  vz <- validateFiniteNumber z (name <> ".z") defaultNumberOptions
  pure (Vec3 vx vy vz)

-- | Validate Vec4
validateVec4 :: Double -> Double -> Double -> Double -> Text -> ValidationResult Vec4
validateVec4 x y z w name = do
  vx <- validateFiniteNumber x (name <> ".x") defaultNumberOptions
  vy <- validateFiniteNumber y (name <> ".y") defaultNumberOptions
  vz <- validateFiniteNumber z (name <> ".z") defaultNumberOptions
  vw <- validateFiniteNumber w (name <> ".w") defaultNumberOptions
  pure (Vec4 vx vy vz vw)

--------------------------------------------------------------------------------
-- Color Validators
--------------------------------------------------------------------------------

-- | Validate RGB color (0-255 each)
validateRGB :: Double -> Double -> Double -> Text -> ValidationResult RGB
validateRGB r g b name = do
  let colorOpts = NumberOptions (Just 0) (Just 255)
  vr <- validateFiniteNumber r (name <> ".r") colorOpts
  vg <- validateFiniteNumber g (name <> ".g") colorOpts
  vb <- validateFiniteNumber b (name <> ".b") colorOpts
  pure (RGB vr vg vb)

-- | Validate RGBA color
validateRGBA :: Double -> Double -> Double -> Double -> Text -> ValidationResult RGBA
validateRGBA r g b a name = do
  let colorOpts = NumberOptions (Just 0) (Just 255)
  vr <- validateFiniteNumber r (name <> ".r") colorOpts
  vg <- validateFiniteNumber g (name <> ".g") colorOpts
  vb <- validateFiniteNumber b (name <> ".b") colorOpts
  va <- validateUnit a (name <> ".a")
  pure (RGBA vr vg vb va)

--------------------------------------------------------------------------------
-- Optional/Default Helpers
--------------------------------------------------------------------------------

-- | Make validation optional
optional :: (Double -> Text -> ValidationResult a) -> Maybe Double -> Text -> ValidationResult (Maybe a)
optional _ Nothing _ = Ok Nothing
optional validator (Just v) name = Just <$> validator v name

-- | Provide default if validation fails
withDefault :: (Double -> Text -> ValidationResult a) -> a -> Double -> Text -> ValidationResult a
withDefault validator def v name =
  case validator v name of
    Ok x -> Ok x
    Fail _ -> Ok def

--------------------------------------------------------------------------------
-- Composition Helpers
--------------------------------------------------------------------------------

-- | Collect all errors from multiple validations
validateAll :: [ValidationResult ()] -> ValidationResult ()
validateAll validations =
  let errors = [e | Fail e <- validations]
  in if null errors
     then Ok ()
     else Fail (T.intercalate "; " errors)

-- | Chain two validations
andThen :: ValidationResult a -> (a -> ValidationResult b) -> ValidationResult b
andThen = (>>=)

-- | Combine two validations into a pair
both :: ValidationResult a -> ValidationResult b -> ValidationResult (a, b)
both (Ok a) (Ok b) = Ok (a, b)
both (Fail e) _ = Fail e
both _ (Fail e) = Fail e
