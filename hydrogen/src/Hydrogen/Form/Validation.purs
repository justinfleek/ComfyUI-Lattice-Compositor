-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // form // validation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Type-safe form validation
-- |
-- | Composable validation rules with error accumulation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Form.Validation as V
-- |
-- | -- Single validators
-- | V.required "Name is required"
-- | V.minLength 3 "Name must be at least 3 characters"
-- | V.email "Invalid email address"
-- |
-- | -- Compose validators
-- | nameValidator = V.required "Required" <> V.minLength 3 "Too short"
-- |
-- | -- Run validation
-- | case V.validate nameValidator "John" of
-- |   V.Valid -> -- success
-- |   V.Invalid errors -> -- show errors
-- | ```
module Hydrogen.Form.Validation
  ( -- * Validation Result
    ValidationResult(Valid, Invalid)
  , isValid
  , isInvalid
  , getErrors
    -- * Validator Type
  , Validator
  , validate
  , validateM
    -- * Common Validators
  , required
  , minLength
  , maxLength
  , pattern
  , email
  , url
  , numeric
  , integer
  , min
  , max
  , range
  , equals
  , notEquals
  , oneOf
  , custom
    -- * Combinators
  , optional
  , when
  , unless
  ) where

import Prelude hiding (min, max, when)

import Data.Array as Array
import Data.Either (Either(Left, Right))
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))
import Data.Number as Number
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags as RegexFlags

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // validation result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of validation
data ValidationResult
  = Valid
  | Invalid (Array String)

derive instance eqValidationResult :: Eq ValidationResult

instance showValidationResult :: Show ValidationResult where
  show Valid = "Valid"
  show (Invalid errs) = "(Invalid " <> show errs <> ")"

instance semigroupValidationResult :: Semigroup ValidationResult where
  append Valid Valid = Valid
  append Valid (Invalid errs) = Invalid errs
  append (Invalid errs) Valid = Invalid errs
  append (Invalid errs1) (Invalid errs2) = Invalid (errs1 <> errs2)

instance monoidValidationResult :: Monoid ValidationResult where
  mempty = Valid

-- | Check if validation passed
isValid :: ValidationResult -> Boolean
isValid Valid = true
isValid _ = false

-- | Check if validation failed
isInvalid :: ValidationResult -> Boolean
isInvalid = not <<< isValid

-- | Extract error messages
getErrors :: ValidationResult -> Array String
getErrors Valid = []
getErrors (Invalid errs) = errs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // validator type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A validator is a function from value to result
newtype Validator a = Validator (a -> ValidationResult)

instance semigroupValidator :: Semigroup (Validator a) where
  append (Validator f) (Validator g) = Validator \a -> f a <> g a

instance monoidValidator :: Monoid (Validator a) where
  mempty = Validator \_ -> Valid

-- | Run a validator
validate :: forall a. Validator a -> a -> ValidationResult
validate (Validator f) = f

-- | Run validation returning Either
validateM :: forall a. Validator a -> a -> Either (Array String) a
validateM v a = case validate v a of
  Valid -> Right a
  Invalid errs -> Left errs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // common validators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Value must not be empty
required :: String -> Validator String
required err = Validator \s ->
  if String.null (String.trim s)
    then Invalid [ err ]
    else Valid

-- | String must have minimum length
minLength :: Int -> String -> Validator String
minLength len err = Validator \s ->
  if String.length s < len
    then Invalid [ err ]
    else Valid

-- | String must not exceed maximum length
maxLength :: Int -> String -> Validator String
maxLength len err = Validator \s ->
  if String.length s > len
    then Invalid [ err ]
    else Valid

-- | String must match regex pattern
pattern :: String -> String -> Validator String
pattern pat err = Validator \s ->
  case Regex.regex pat RegexFlags.noFlags of
    Left _ -> Valid  -- Invalid regex, pass through
    Right re ->
      if Regex.test re s
        then Valid
        else Invalid [ err ]

-- | Must be valid email format
email :: String -> Validator String
email err = pattern "^[^\\s@]+@[^\\s@]+\\.[^\\s@]+$" err

-- | Must be valid URL format
url :: String -> Validator String
url err = pattern "^https?://" err

-- | Must be numeric
numeric :: String -> Validator String
numeric err = Validator \s ->
  case Number.fromString s of
    Just _ -> Valid
    Nothing -> Invalid [ err ]

-- | Must be an integer
integer :: String -> Validator String
integer err = Validator \s ->
  case Int.fromString s of
    Just _ -> Valid
    Nothing -> Invalid [ err ]

-- | Number must be at least minimum
min :: Number -> String -> Validator Number
min minVal err = Validator \n ->
  if n < minVal
    then Invalid [ err ]
    else Valid

-- | Number must not exceed maximum
max :: Number -> String -> Validator Number
max maxVal err = Validator \n ->
  if n > maxVal
    then Invalid [ err ]
    else Valid

-- | Number must be within range
range :: Number -> Number -> String -> Validator Number
range minVal maxVal err = min minVal err <> max maxVal err

-- | Must equal expected value
equals :: forall a. Eq a => a -> String -> Validator a
equals expected err = Validator \a ->
  if a == expected
    then Valid
    else Invalid [ err ]

-- | Must not equal value
notEquals :: forall a. Eq a => a -> String -> Validator a
notEquals forbidden err = Validator \a ->
  if a == forbidden
    then Invalid [ err ]
    else Valid

-- | Must be one of allowed values
oneOf :: forall a. Eq a => Array a -> String -> Validator a
oneOf allowed err = Validator \a ->
  if Array.elem a allowed
    then Valid
    else Invalid [ err ]

-- | Custom validation function
custom :: forall a. (a -> Boolean) -> String -> Validator a
custom pred err = Validator \a ->
  if pred a
    then Valid
    else Invalid [ err ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // combinators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Make a validator optional (empty string passes)
optional :: Validator String -> Validator String
optional (Validator f) = Validator \s ->
  if String.null (String.trim s)
    then Valid
    else f s

-- | Only run validator when condition is true
when :: forall a. Boolean -> Validator a -> Validator a
when true v = v
when false _ = mempty

-- | Only run validator when condition is false
unless :: forall a. Boolean -> Validator a -> Validator a
unless cond = when (not cond)
