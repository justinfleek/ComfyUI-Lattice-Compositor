-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // reactive // validation-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ValidationState - form field validation lifecycle.
-- |
-- | Composes validation flags into molecules and compounds for
-- | form state management. Tracks validity, modification, and
-- | async validation progress.

module Hydrogen.Schema.Reactive.ValidationState
  ( -- * Validation Result
    ValidationResult(..)
  , isValidResult
  , isInvalidResult
  , isPendingResult
  -- * Validation Severity
  , ValidationSeverity(..)
  , isSeverityError
  , isSeverityWarning
  , isSeverityInfo
  -- * Validation Message
  , ValidationMessage
  , validationMessage
  , errorMessage
  , warningMessage
  , infoMessage
  -- * Field Modification State
  , ModificationState(..)
  , isPristine
  , isDirty
  -- * Field Touch State
  , TouchState(..)
  , isTouched
  , isUntouched
  -- * Field Validation State (Molecule)
  , FieldValidation
  , fieldValidation
  , defaultFieldValidation
  , validField
  , invalidField
  , pendingField
  -- * Computed Properties
  , shouldShowError
  , shouldShowWarning
  , hasMessages
  , firstError
  , allErrors
  , allWarnings
  -- * Form Validation State (Compound)
  , FormValidation
  , formValidation
  , defaultFormValidation
  , isFormValid
  , isFormSubmittable
  , touchedFieldCount
  , dirtyFieldCount
  , invalidFieldCount
  ) where

import Prelude

import Data.Array (filter, head, length)
import Data.Maybe (Maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // validation result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of validation check
data ValidationResult
  = ValidationValid       -- ^ Passes all validation rules
  | ValidationInvalid     -- ^ Fails one or more rules
  | ValidationPending     -- ^ Async validation in progress
  | ValidationSkipped     -- ^ Validation not performed (e.g., disabled field)

derive instance eqValidationResult :: Eq ValidationResult
derive instance ordValidationResult :: Ord ValidationResult

instance showValidationResult :: Show ValidationResult where
  show ValidationValid = "valid"
  show ValidationInvalid = "invalid"
  show ValidationPending = "pending"
  show ValidationSkipped = "skipped"

isValidResult :: ValidationResult -> Boolean
isValidResult ValidationValid = true
isValidResult _ = false

isInvalidResult :: ValidationResult -> Boolean
isInvalidResult ValidationInvalid = true
isInvalidResult _ = false

isPendingResult :: ValidationResult -> Boolean
isPendingResult ValidationPending = true
isPendingResult _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // validation severity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Severity level of validation message
data ValidationSeverity
  = SeverityError    -- ^ Blocks submission
  | SeverityWarning  -- ^ Allows submission with caution
  | SeverityInfo     -- ^ Informational only

derive instance eqValidationSeverity :: Eq ValidationSeverity
derive instance ordValidationSeverity :: Ord ValidationSeverity

instance showValidationSeverity :: Show ValidationSeverity where
  show SeverityError = "error"
  show SeverityWarning = "warning"
  show SeverityInfo = "info"

isSeverityError :: ValidationSeverity -> Boolean
isSeverityError SeverityError = true
isSeverityError _ = false

isSeverityWarning :: ValidationSeverity -> Boolean
isSeverityWarning SeverityWarning = true
isSeverityWarning _ = false

isSeverityInfo :: ValidationSeverity -> Boolean
isSeverityInfo SeverityInfo = true
isSeverityInfo _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // validation message
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation message with severity and rule identifier
type ValidationMessage =
  { severity :: ValidationSeverity
  , message :: String
  , rule :: String           -- ^ Rule identifier (e.g., "required", "minLength")
  , params :: Array String   -- ^ Rule parameters (e.g., ["8"] for minLength 8)
  }

-- | Create validation message
validationMessage :: ValidationSeverity -> String -> String -> Array String -> ValidationMessage
validationMessage severity message rule params =
  { severity, message, rule, params }

-- | Create error message
errorMessage :: String -> String -> ValidationMessage
errorMessage rule message = validationMessage SeverityError message rule []

-- | Create warning message
warningMessage :: String -> String -> ValidationMessage
warningMessage rule message = validationMessage SeverityWarning message rule []

-- | Create info message
infoMessage :: String -> String -> ValidationMessage
infoMessage rule message = validationMessage SeverityInfo message rule []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // modification state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Field modification state
data ModificationState
  = Pristine    -- ^ Value equals initial value
  | Modified    -- ^ Value differs from initial value

derive instance eqModificationState :: Eq ModificationState
derive instance ordModificationState :: Ord ModificationState

instance showModificationState :: Show ModificationState where
  show Pristine = "pristine"
  show Modified = "modified"

isPristine :: ModificationState -> Boolean
isPristine Pristine = true
isPristine _ = false

isDirty :: ModificationState -> Boolean
isDirty Modified = true
isDirty _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // touch state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Field interaction state
data TouchState
  = Untouched   -- ^ Field has never received focus
  | Touched     -- ^ Field has been focused and blurred at least once

derive instance eqTouchState :: Eq TouchState
derive instance ordTouchState :: Ord TouchState

instance showTouchState :: Show TouchState where
  show Untouched = "untouched"
  show Touched = "touched"

isTouched :: TouchState -> Boolean
isTouched Touched = true
isTouched _ = false

isUntouched :: TouchState -> Boolean
isUntouched Untouched = true
isUntouched _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // field validation molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete validation state for a single field
type FieldValidation =
  { result :: ValidationResult
  , messages :: Array ValidationMessage
  , modification :: ModificationState
  , touch :: TouchState
  , isValidating :: Boolean    -- ^ Async validation in progress
  , validateOnBlur :: Boolean  -- ^ Trigger validation on blur
  , validateOnChange :: Boolean -- ^ Trigger validation on change
  }

-- | Create field validation state
fieldValidation 
  :: ValidationResult 
  -> Array ValidationMessage 
  -> ModificationState 
  -> TouchState 
  -> FieldValidation
fieldValidation result messages modification touch =
  { result
  , messages
  , modification
  , touch
  , isValidating: false
  , validateOnBlur: true
  , validateOnChange: false
  }

-- | Default field validation (pristine, untouched, valid)
defaultFieldValidation :: FieldValidation
defaultFieldValidation =
  { result: ValidationValid
  , messages: []
  , modification: Pristine
  , touch: Untouched
  , isValidating: false
  , validateOnBlur: true
  , validateOnChange: false
  }

-- | Create valid field state
validField :: FieldValidation
validField = defaultFieldValidation

-- | Create invalid field state with error
invalidField :: String -> String -> FieldValidation
invalidField rule message =
  defaultFieldValidation
    { result = ValidationInvalid
    , messages = [ errorMessage rule message ]
    }

-- | Create pending validation state
pendingField :: FieldValidation
pendingField =
  defaultFieldValidation
    { result = ValidationPending
    , isValidating = true
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Should show error state to user?
-- | Only show errors for touched fields (don't punish before interaction)
shouldShowError :: FieldValidation -> Boolean
shouldShowError fv = 
  isTouched fv.touch && isInvalidResult fv.result

-- | Should show warning state to user?
shouldShowWarning :: FieldValidation -> Boolean
shouldShowWarning fv =
  isTouched fv.touch && hasWarnings fv

-- | Does field have any validation messages?
hasMessages :: FieldValidation -> Boolean
hasMessages fv = length fv.messages > 0

-- | Get first error message
firstError :: FieldValidation -> Maybe ValidationMessage
firstError fv = head (allErrors fv)

-- | Get all error messages
allErrors :: FieldValidation -> Array ValidationMessage
allErrors fv = filter (\m -> isSeverityError m.severity) fv.messages

-- | Get all warning messages
allWarnings :: FieldValidation -> Array ValidationMessage
allWarnings fv = filter (\m -> isSeverityWarning m.severity) fv.messages

-- | Does field have warnings?
hasWarnings :: FieldValidation -> Boolean
hasWarnings fv = length (allWarnings fv) > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // form validation compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aggregate validation state for entire form
type FormValidation =
  { fields :: Array { name :: String, validation :: FieldValidation }
  , isSubmitting :: Boolean    -- ^ Form submission in progress
  , isSubmitted :: Boolean     -- ^ Form has been submitted at least once
  , submitCount :: Int         -- ^ Number of submission attempts
  , isValid :: Boolean         -- ^ All fields valid
  , isDirty :: Boolean         -- ^ Any field modified
  }

-- | Create form validation state
formValidation 
  :: Array { name :: String, validation :: FieldValidation } 
  -> FormValidation
formValidation fields =
  { fields
  , isSubmitting: false
  , isSubmitted: false
  , submitCount: 0
  , isValid: allFieldsValid fields
  , isDirty: anyFieldDirty fields
  }
  where
  allFieldsValid :: Array { name :: String, validation :: FieldValidation } -> Boolean
  allFieldsValid fs = length (filter (\f -> not (isValidResult f.validation.result)) fs) == 0
  
  anyFieldDirty :: Array { name :: String, validation :: FieldValidation } -> Boolean
  anyFieldDirty fs = length (filter (\f -> isDirty f.validation.modification) fs) > 0

-- | Default form validation (no fields)
defaultFormValidation :: FormValidation
defaultFormValidation = formValidation []

-- | Is entire form valid?
isFormValid :: FormValidation -> Boolean
isFormValid fv = fv.isValid

-- | Can form be submitted? (valid and not currently submitting)
isFormSubmittable :: FormValidation -> Boolean
isFormSubmittable fv = fv.isValid && not fv.isSubmitting

-- | Count of touched fields
touchedFieldCount :: FormValidation -> Int
touchedFieldCount fv = 
  length (filter (\f -> isTouched f.validation.touch) fv.fields)

-- | Count of dirty fields
dirtyFieldCount :: FormValidation -> Int
dirtyFieldCount fv = 
  length (filter (\f -> isDirty f.validation.modification) fv.fields)

-- | Count of invalid fields
invalidFieldCount :: FormValidation -> Int
invalidFieldCount fv = 
  length (filter (\f -> isInvalidResult f.validation.result) fv.fields)
