-- | Lattice.Utils.Validation - Runtime input validation with Result types
-- |
-- | Validates input at runtime boundaries (AI commands, file imports, user input).
-- | All validators return explicit success/failure results.
-- |
-- | Source: leancomfy/lean/Lattice/Utils/Validation.lean

module Lattice.Utils.Validation
  ( ValidationResult(..)
  , ok
  , fail'
  , isOk
  , getOr
  , StringOptions
  , validateString
  , NumberOptions
  , validateFiniteNumber
  , validateInteger
  , validateBoolean
  , validateEnum
  , validatePositive
  , validateNonNegative
  , validateUnit
  , validatePercentage
  , validateFrameNumber
  , validateArray
  , validateNumberArray
  , validateVec2
  , validateVec3
  , validateVec4
  , validateRGB
  , validateRGBA
  , optional
  , withDefault
  , validateAll
  , andThen
  , both
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array (foldl, reverse, (:))
import Data.Array as Array
import Data.Int (floor, toNumber)
import Data.Number (isFinite, isNaN) as Number
import Data.String as String
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Result Type
--------------------------------------------------------------------------------

-- | Validation result - either success with typed value, or failure with error
data ValidationResult a
  = Ok a
  | Fail String

derive instance Eq a => Eq (ValidationResult a)

instance Show a => Show (ValidationResult a) where
  show (Ok a) = "Ok " <> show a
  show (Fail e) = "Fail " <> show e

instance Functor ValidationResult where
  map f (Ok a) = Ok (f a)
  map _ (Fail e) = Fail e

instance Apply ValidationResult where
  apply (Ok f) (Ok x) = Ok (f x)
  apply (Fail e) _ = Fail e
  apply _ (Fail e) = Fail e

instance Applicative ValidationResult where
  pure = Ok

instance Bind ValidationResult where
  bind (Ok x) f = f x
  bind (Fail e) _ = Fail e

instance Monad ValidationResult

-- | Create success result
ok :: forall a. a -> ValidationResult a
ok = Ok

-- | Create failure result
fail' :: forall a. String -> ValidationResult a
fail' = Fail

-- | Check if result is success
isOk :: forall a. ValidationResult a -> Boolean
isOk (Ok _) = true
isOk (Fail _) = false

-- | Get value with default fallback
getOr :: forall a. a -> ValidationResult a -> a
getOr _ (Ok v) = v
getOr d (Fail _) = d

--------------------------------------------------------------------------------
-- Primitive Validators
--------------------------------------------------------------------------------

-- | Options for string validation
type StringOptions =
  { minLength :: Maybe Int
  , maxLength :: Maybe Int
  , allowEmpty :: Boolean
  }

defaultStringOptions :: StringOptions
defaultStringOptions = { minLength: Nothing, maxLength: Nothing, allowEmpty: false }

-- | Check if Number is finite
isFiniteNumber :: Number -> Boolean
isFiniteNumber x = Number.isFinite x && not (Number.isNaN x)

-- | Validate non-empty string
validateString :: String -> String -> StringOptions -> ValidationResult NonEmptyString
validateString value name opts
  | not opts.allowEmpty && String.null value =
      Fail (name <> " cannot be empty")
  | Just minLen <- opts.minLength, String.length value < minLen =
      Fail (name <> " must be at least " <> show minLen <> " characters")
  | Just maxLen <- opts.maxLength, String.length value > maxLen =
      Fail (name <> " must be at most " <> show maxLen <> " characters")
  | String.null value = Fail (name <> " cannot be empty")
  | otherwise = case mkNonEmptyString value of
      Just nes -> Ok nes
      Nothing -> Fail (name <> " cannot be empty")

-- | Options for numeric validation
type NumberOptions =
  { min :: Maybe Number
  , max :: Maybe Number
  }

defaultNumberOptions :: NumberOptions
defaultNumberOptions = { min: Nothing, max: Nothing }

-- | Validate finite number
validateFiniteNumber :: Number -> String -> NumberOptions -> ValidationResult FiniteFloat
validateFiniteNumber value name opts
  | not (isFiniteNumber value) =
      Fail (name <> " must be a finite number")
  | Just minVal <- opts.min, value < minVal =
      Fail (name <> " must be >= " <> show minVal <> ", got " <> show value)
  | Just maxVal <- opts.max, value > maxVal =
      Fail (name <> " must be <= " <> show maxVal <> ", got " <> show value)
  | otherwise = case mkFiniteFloat value of
      Just ff -> Ok ff
      Nothing -> Fail (name <> " must be a finite number")

-- | Validate integer
validateInteger :: Number -> String -> NumberOptions -> ValidationResult Int
validateInteger value name opts = do
  _ <- validateFiniteNumber value name opts
  let intVal = floor value
  if toNumber intVal == value
    then Ok intVal
    else Fail (name <> " must be an integer, got " <> show value)

-- | Validate boolean (always succeeds)
validateBoolean :: Boolean -> String -> ValidationResult Boolean
validateBoolean value _ = Ok value

-- | Validate value is in allowed list
validateEnum :: forall a. Eq a => Show a => a -> String -> Array a -> ValidationResult a
validateEnum value name allowed
  | Array.elem value allowed = Ok value
  | otherwise = Fail (name <> " must be one of allowed values")

--------------------------------------------------------------------------------
-- Numeric Type Validators
--------------------------------------------------------------------------------

-- | Validate positive number (> 0)
validatePositive :: Number -> String -> ValidationResult PositiveFloat
validatePositive value name
  | not (isFiniteNumber value) = Fail (name <> " must be a finite number")
  | value <= 0.0 = Fail (name <> " must be positive, got " <> show value)
  | otherwise = Ok (PositiveFloat value)

-- | Validate non-negative number (>= 0)
validateNonNegative :: Number -> String -> ValidationResult NonNegativeFloat
validateNonNegative value name
  | not (isFiniteNumber value) = Fail (name <> " must be a finite number")
  | value < 0.0 = Fail (name <> " must be non-negative, got " <> show value)
  | otherwise = Ok (NonNegativeFloat value)

-- | Validate unit float (0 to 1)
validateUnit :: Number -> String -> ValidationResult UnitFloat
validateUnit value name
  | not (isFiniteNumber value) = Fail (name <> " must be a finite number")
  | value < 0.0 = Fail (name <> " must be >= 0, got " <> show value)
  | value > 1.0 = Fail (name <> " must be <= 1, got " <> show value)
  | otherwise = Ok (UnitFloat value)

-- | Validate percentage (0 to 100)
validatePercentage :: Number -> String -> ValidationResult Percentage
validatePercentage value name
  | not (isFiniteNumber value) = Fail (name <> " must be a finite number")
  | value < 0.0 = Fail (name <> " must be >= 0, got " <> show value)
  | value > 100.0 = Fail (name <> " must be <= 100, got " <> show value)
  | otherwise = Ok (Percentage value)

-- | Validate frame number (non-negative integer)
validateFrameNumber :: Number -> String -> ValidationResult FrameNumber
validateFrameNumber value name
  | not (isFiniteNumber value) = Fail (name <> " must be a finite number")
  | value < 0.0 = Fail (name <> " must be non-negative, got " <> show value)
  | otherwise =
      let intVal = floor value
      in if toNumber intVal == value && intVal >= 0
         then Ok (FrameNumber intVal)
         else Fail (name <> " must be a non-negative integer, got " <> show value)

--------------------------------------------------------------------------------
-- Array Validators
--------------------------------------------------------------------------------

-- | Validate array with item validator
validateArray :: forall a. Array Number -> String -> (Number -> String -> ValidationResult a) -> ValidationResult (Array a)
validateArray values name itemValidator = go values 0 []
  where
    go :: Array Number -> Int -> Array a -> ValidationResult (Array a)
    go arr idx acc = case Array.uncons arr of
      Nothing -> Ok (reverse acc)
      Just { head: x, tail: xs } ->
        case itemValidator x (name <> "[" <> show idx <> "]") of
          Ok v -> go xs (idx + 1) (v : acc)
          Fail e -> Fail e

-- | Validate array of finite numbers
validateNumberArray :: Array Number -> String -> NumberOptions -> ValidationResult (Array FiniteFloat)
validateNumberArray values name opts =
  validateArray values name (\v n -> validateFiniteNumber v n opts)

--------------------------------------------------------------------------------
-- Vector Validators
--------------------------------------------------------------------------------

-- | Validate Vec2
validateVec2 :: Number -> Number -> String -> ValidationResult Vec2
validateVec2 x y name = do
  vx <- validateFiniteNumber x (name <> ".x") defaultNumberOptions
  vy <- validateFiniteNumber y (name <> ".y") defaultNumberOptions
  pure { x: vx, y: vy }

-- | Validate Vec3
validateVec3 :: Number -> Number -> Number -> String -> ValidationResult Vec3
validateVec3 x y z name = do
  vx <- validateFiniteNumber x (name <> ".x") defaultNumberOptions
  vy <- validateFiniteNumber y (name <> ".y") defaultNumberOptions
  vz <- validateFiniteNumber z (name <> ".z") defaultNumberOptions
  pure { x: vx, y: vy, z: vz }

-- | Validate Vec4
validateVec4 :: Number -> Number -> Number -> Number -> String -> ValidationResult Vec4
validateVec4 x y z w name = do
  vx <- validateFiniteNumber x (name <> ".x") defaultNumberOptions
  vy <- validateFiniteNumber y (name <> ".y") defaultNumberOptions
  vz <- validateFiniteNumber z (name <> ".z") defaultNumberOptions
  vw <- validateFiniteNumber w (name <> ".w") defaultNumberOptions
  pure { x: vx, y: vy, z: vz, w: vw }

--------------------------------------------------------------------------------
-- Color Validators
--------------------------------------------------------------------------------

-- | Validate RGB color (0-1 unit floats)
validateRGB :: Number -> Number -> Number -> String -> ValidationResult RGB
validateRGB r g b name = do
  vr <- validateUnit r (name <> ".r")
  vg <- validateUnit g (name <> ".g")
  vb <- validateUnit b (name <> ".b")
  pure { r: vr, g: vg, b: vb }

-- | Validate RGBA color (0-1 unit floats)
validateRGBA :: Number -> Number -> Number -> Number -> String -> ValidationResult RGBA
validateRGBA r g b a name = do
  vr <- validateUnit r (name <> ".r")
  vg <- validateUnit g (name <> ".g")
  vb <- validateUnit b (name <> ".b")
  va <- validateUnit a (name <> ".a")
  pure { r: vr, g: vg, b: vb, a: va }

--------------------------------------------------------------------------------
-- Optional/Default Helpers
--------------------------------------------------------------------------------

-- | Make validation optional
optional :: forall a. (Number -> String -> ValidationResult a) -> Maybe Number -> String -> ValidationResult (Maybe a)
optional _ Nothing _ = Ok Nothing
optional validator (Just v) name = map Just (validator v name)

-- | Provide default if validation fails
withDefault :: forall a. (Number -> String -> ValidationResult a) -> a -> Number -> String -> ValidationResult a
withDefault validator def v name =
  case validator v name of
    Ok x -> Ok x
    Fail _ -> Ok def

--------------------------------------------------------------------------------
-- Composition Helpers
--------------------------------------------------------------------------------

-- | Collect all errors from multiple validations
validateAll :: Array (ValidationResult Unit) -> ValidationResult Unit
validateAll validations =
  let errors = Array.mapMaybe getError validations
  in if Array.null errors
     then Ok unit
     else Fail (String.joinWith "; " errors)
  where
    getError (Fail e) = Just e
    getError (Ok _) = Nothing

-- | Chain two validations
andThen :: forall a b. ValidationResult a -> (a -> ValidationResult b) -> ValidationResult b
andThen = bind

-- | Combine two validations into a pair
both :: forall a b. ValidationResult a -> ValidationResult b -> ValidationResult { fst :: a, snd :: b }
both (Ok a) (Ok b) = Ok { fst: a, snd: b }
both (Fail e) _ = Fail e
both _ (Fail e) = Fail e
