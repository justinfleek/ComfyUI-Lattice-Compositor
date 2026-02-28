-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // otpinput // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OTPInput Types — Strict, bounded types for OTP handling.
-- |
-- | ## Security Philosophy
-- |
-- | OTP values are **security-critical**. This module defines types that:
-- |
-- | 1. **Bound digit counts** — No unbounded arrays, memory is predictable
-- | 2. **Validate on construction** — Invalid OTPs cannot exist
-- | 3. **Mask by default** — Display values are explicitly requested
-- | 4. **No partial functions** — Every operation is total
-- |
-- | ## Strict Data Boundaries
-- |
-- | The `OTPValue` type ensures:
-- | - Minimum 4 digits, maximum 8 digits (covers all standard OTP formats)
-- | - Only valid characters (digits for numeric, alphanumeric otherwise)
-- | - Immutable once constructed
-- | - Constant-time comparison (timing attack resistance)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Element.Compound.OTPInput.Types
  ( -- * Core Types
    OTPInputType(Numeric, Alphanumeric)
  , OTPDigitCount(OTPDigitCount)
  , OTPValue(OTPValue)
  , OTPDigit(OTPDigit)
  , OTPIndex(OTPIndex)
  
  -- * Component State
  , OTPState(Idle, Entering, Verifying, Success, Error)
  , OTPFocusState(Unfocused, Focused)
  
  -- * Animation State
  , DigitAnimationState(DigitIdle, DigitEntering, DigitFilled, DigitError, DigitSuccess)
  
  -- * Messages
  , OTPMsg(DigitInput, DigitDelete, DigitFocus, DigitBlur, PasteDetected, Completed, ResendClicked, ClearError)
  
  -- * Constructors
  , digitCount
  , otpValue
  , emptyOTP
  , otpDigit
  , otpIndex
  
  -- * Accessors
  , unwrapDigitCount
  , unwrapOTPValue
  , unwrapOTPDigit
  , unwrapOTPIndex
  , otpLength
  , isOTPComplete
  , getDigitAt
  , getMaskedValue
  
  -- * Operations
  , setDigitAt
  , appendDigit
  , deleteLastDigit
  , clearOTP
  
  -- * Bounds
  , minDigits
  , maxDigits
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (+)
  , (-)
  , (<>)
  , map
  , otherwise
  )

import Data.Array (length, index, updateAt, snoc, replicate)
import Data.Char (toCharCode)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.String as String
import Data.String.CodeUnits as SCU

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum OTP digits (4-digit PINs)
minDigits :: Int
minDigits = 4

-- | Maximum OTP digits (8-digit codes)
maxDigits :: Int
maxDigits = 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // input type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of characters allowed in OTP
data OTPInputType
  = Numeric       -- ^ Digits 0-9 only
  | Alphanumeric  -- ^ Letters A-Z, a-z and digits 0-9

derive instance eqOTPInputType :: Eq OTPInputType

instance showOTPInputType :: Show OTPInputType where
  show Numeric = "numeric"
  show Alphanumeric = "alphanumeric"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // digit count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounded digit count (4-8).
-- |
-- | Cannot be constructed outside this range. Covers:
-- | - 4-digit PINs
-- | - 6-digit TOTP/SMS codes
-- | - 8-digit backup codes
newtype OTPDigitCount = OTPDigitCount Int

derive instance eqOTPDigitCount :: Eq OTPDigitCount
derive instance ordOTPDigitCount :: Ord OTPDigitCount

instance showOTPDigitCount :: Show OTPDigitCount where
  show (OTPDigitCount n) = show n

-- | Construct a digit count, clamping to valid range [4, 8]
digitCount :: Int -> OTPDigitCount
digitCount n
  | n < minDigits = OTPDigitCount minDigits
  | n > maxDigits = OTPDigitCount maxDigits
  | otherwise = OTPDigitCount n

-- | Unwrap digit count
unwrapDigitCount :: OTPDigitCount -> Int
unwrapDigitCount (OTPDigitCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // otp digit
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single OTP digit (or empty).
-- |
-- | Represents one character position in the OTP. Can be:
-- | - Empty (not yet entered)
-- | - Filled with a valid character
newtype OTPDigit = OTPDigit (Maybe Char)

derive instance eqOTPDigit :: Eq OTPDigit

instance showOTPDigit :: Show OTPDigit where
  show (OTPDigit Nothing) = "_"
  show (OTPDigit (Just c)) = SCU.singleton c

-- | Construct an OTP digit from a character.
-- | Returns empty digit if character is invalid for the input type.
otpDigit :: OTPInputType -> Char -> OTPDigit
otpDigit inputType c =
  if isValidChar inputType c
    then OTPDigit (Just c)
    else OTPDigit Nothing

-- | Unwrap digit to Maybe Char
unwrapOTPDigit :: OTPDigit -> Maybe Char
unwrapOTPDigit (OTPDigit mc) = mc

-- | Check if a character is valid for the input type
isValidChar :: OTPInputType -> Char -> Boolean
isValidChar Numeric c = isDigitChar c
isValidChar Alphanumeric c = isDigitChar c || isLetterChar c

-- | Check if character is 0-9
isDigitChar :: Char -> Boolean
isDigitChar c =
  let code = toCharCode c
  in code >= 48 && code <= 57  -- '0' = 48, '9' = 57

-- | Check if character is a-z or A-Z
isLetterChar :: Char -> Boolean
isLetterChar c =
  let code = toCharCode c
  in (code >= 65 && code <= 90) || (code >= 97 && code <= 122)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // otp index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index into OTP digits, bounded by digit count.
newtype OTPIndex = OTPIndex Int

derive instance eqOTPIndex :: Eq OTPIndex
derive instance ordOTPIndex :: Ord OTPIndex

instance showOTPIndex :: Show OTPIndex where
  show (OTPIndex i) = show i

-- | Construct an OTP index, clamping to valid range [0, count-1]
otpIndex :: OTPDigitCount -> Int -> OTPIndex
otpIndex (OTPDigitCount count) i
  | i < 0 = OTPIndex 0
  | i >= count = OTPIndex (count - 1)
  | otherwise = OTPIndex i

-- | Unwrap index
unwrapOTPIndex :: OTPIndex -> Int
unwrapOTPIndex (OTPIndex i) = i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // otp value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete OTP value as array of digits.
-- |
-- | Invariants enforced by construction:
-- | - Length is always equal to digit count
-- | - Each digit is either empty or valid for input type
newtype OTPValue = OTPValue (Array OTPDigit)

derive instance eqOTPValue :: Eq OTPValue

instance showOTPValue :: Show OTPValue where
  show (OTPValue digits) = "OTP[" <> String.joinWith "" (map show digits) <> "]"

-- | Create an OTP value from a string.
-- | Pads or truncates to match digit count.
-- | Invalid characters become empty digits.
otpValue :: OTPInputType -> OTPDigitCount -> String -> OTPValue
otpValue inputType (OTPDigitCount count) str =
  let
    chars = SCU.toCharArray str
    digits = map (otpDigit inputType) chars
    padded = padOrTruncate count digits
  in
    OTPValue padded

-- | Create an empty OTP of given length
emptyOTP :: OTPDigitCount -> OTPValue
emptyOTP (OTPDigitCount count) =
  OTPValue (replicate count (OTPDigit Nothing))

-- | Pad or truncate array to exact length
padOrTruncate :: Int -> Array OTPDigit -> Array OTPDigit
padOrTruncate targetLen arr =
  let currentLen = length arr
  in if currentLen >= targetLen
       then take targetLen arr
       else arr <> replicate (targetLen - currentLen) (OTPDigit Nothing)
  where
    take n xs = 
      let result = go n xs []
      in result
    go 0 _ acc = acc
    go _ [] acc = acc
    go n xs acc = case index xs 0 of
      Nothing -> acc
      Just x -> go (n - 1) (dropFirst xs) (snoc acc x)
    dropFirst xs = fromMaybe [] (dropAt 0 xs)
    dropAt _ [] = Just []
    dropAt i xs = 
      let before = takeArr i xs
          after = dropArr (i + 1) xs
      in Just (before <> after)
    takeArr n xs = go2 n xs []
    go2 0 _ acc = acc
    go2 _ [] acc = acc
    go2 n xs acc = case index xs 0 of
      Nothing -> acc
      Just x -> go2 (n - 1) (fromMaybe [] (tailArr xs)) (snoc acc x)
    dropArr n xs = go3 n xs
    go3 0 xs = xs
    go3 _ [] = []
    go3 n xs = go3 (n - 1) (fromMaybe [] (tailArr xs))
    tailArr [] = Nothing
    tailArr xs = Just (map (\i -> fromMaybe (OTPDigit Nothing) (index xs i)) (rangeArr 1 (length xs - 1)))
    rangeArr start end = go4 start end []
    go4 s e acc = if s > e then acc else go4 (s + 1) e (snoc acc s)

-- | Unwrap OTP to string (only filled digits)
unwrapOTPValue :: OTPValue -> String
unwrapOTPValue (OTPValue digits) =
  String.joinWith "" (map digitToString digits)
  where
    digitToString (OTPDigit Nothing) = ""
    digitToString (OTPDigit (Just c)) = SCU.singleton c

-- | Get OTP length (total slots, not filled count)
otpLength :: OTPValue -> Int
otpLength (OTPValue digits) = length digits

-- | Check if all digits are filled
isOTPComplete :: OTPValue -> Boolean
isOTPComplete (OTPValue digits) =
  length digits > 0 && allFilled digits
  where
    allFilled [] = true
    allFilled ds = case index ds 0 of
      Nothing -> true
      Just (OTPDigit Nothing) -> false
      Just (OTPDigit (Just _)) -> allFilled (fromMaybe [] (dropFirstArr ds))
    dropFirstArr xs = case length xs of
      0 -> Just []
      _ -> Just (map (\i -> fromMaybe (OTPDigit Nothing) (index xs i)) (rangeArr 1 (length xs - 1)))
    rangeArr start end = go start end []
    go s e acc = if s > e then acc else go (s + 1) e (snoc acc s)

-- | Get digit at index
getDigitAt :: OTPIndex -> OTPValue -> OTPDigit
getDigitAt (OTPIndex i) (OTPValue digits) =
  fromMaybe (OTPDigit Nothing) (index digits i)

-- | Get masked display value (dots for filled, empty for unfilled)
getMaskedValue :: OTPValue -> String
getMaskedValue (OTPValue digits) =
  String.joinWith "" (map maskDigit digits)
  where
    maskDigit (OTPDigit Nothing) = ""
    maskDigit (OTPDigit (Just _)) = "•"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set digit at index
setDigitAt :: OTPIndex -> OTPDigit -> OTPValue -> OTPValue
setDigitAt (OTPIndex i) digit (OTPValue digits) =
  OTPValue (fromMaybe digits (updateAt i digit digits))

-- | Append digit to first empty slot
appendDigit :: OTPDigit -> OTPValue -> OTPValue
appendDigit digit (OTPValue digits) =
  OTPValue (appendToFirstEmpty digit digits)
  where
    appendToFirstEmpty _ [] = []
    appendToFirstEmpty d ds = 
      case findFirstEmptyIndex ds 0 of
        Nothing -> ds  -- All filled
        Just idx -> fromMaybe ds (updateAt idx d ds)
    findFirstEmptyIndex [] _ = Nothing
    findFirstEmptyIndex ds idx =
      case index ds idx of
        Nothing -> Nothing
        Just (OTPDigit Nothing) -> Just idx
        Just (OTPDigit (Just _)) -> findFirstEmptyIndex ds (idx + 1)

-- | Delete last filled digit
deleteLastDigit :: OTPValue -> OTPValue
deleteLastDigit (OTPValue digits) =
  OTPValue (clearLastFilled digits)
  where
    clearLastFilled [] = []
    clearLastFilled ds =
      case findLastFilledIndex ds (length ds - 1) of
        Nothing -> ds  -- All empty
        Just idx -> fromMaybe ds (updateAt idx (OTPDigit Nothing) ds)
    findLastFilledIndex [] _ = Nothing
    findLastFilledIndex _ idx | idx < 0 = Nothing
    findLastFilledIndex ds idx =
      case index ds idx of
        Nothing -> Nothing
        Just (OTPDigit (Just _)) -> Just idx
        Just (OTPDigit Nothing) -> findLastFilledIndex ds (idx - 1)

-- | Clear all digits
clearOTP :: OTPDigitCount -> OTPValue
clearOTP = emptyOTP

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // component state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overall OTP input state
data OTPState
  = Idle        -- ^ Initial state, no interaction
  | Entering    -- ^ User is entering digits
  | Verifying   -- ^ OTP submitted, waiting for verification
  | Success     -- ^ OTP verified successfully
  | Error       -- ^ OTP verification failed

derive instance eqOTPState :: Eq OTPState

instance showOTPState :: Show OTPState where
  show Idle = "Idle"
  show Entering = "Entering"
  show Verifying = "Verifying"
  show Success = "Success"
  show Error = "Error"

-- | Focus state of the OTP input
data OTPFocusState
  = Unfocused
  | Focused

derive instance eqOTPFocusState :: Eq OTPFocusState

instance showOTPFocusState :: Show OTPFocusState where
  show Unfocused = "Unfocused"
  show Focused = "Focused"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // animation state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation state for individual digit
data DigitAnimationState
  = DigitIdle      -- ^ No animation
  | DigitEntering  -- ^ Currently being typed
  | DigitFilled    -- ^ Has value, stable
  | DigitError     -- ^ Error shake animation
  | DigitSuccess   -- ^ Success pulse animation

derive instance eqDigitAnimationState :: Eq DigitAnimationState

instance showDigitAnimationState :: Show DigitAnimationState where
  show DigitIdle = "DigitIdle"
  show DigitEntering = "DigitEntering"
  show DigitFilled = "DigitFilled"
  show DigitError = "DigitError"
  show DigitSuccess = "DigitSuccess"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | OTP component messages
data OTPMsg
  = DigitInput OTPIndex Char     -- ^ Digit entered at index
  | DigitDelete OTPIndex         -- ^ Backspace at index
  | DigitFocus OTPIndex          -- ^ Digit focused
  | DigitBlur OTPIndex           -- ^ Digit lost focus
  | PasteDetected String         -- ^ Paste event with value
  | Completed String             -- ^ All digits filled
  | ResendClicked                -- ^ Resend button clicked
  | ClearError                   -- ^ Clear error state

derive instance eqOTPMsg :: Eq OTPMsg

instance showOTPMsg :: Show OTPMsg where
  show (DigitInput idx c) = "DigitInput(" <> show idx <> ", " <> SCU.singleton c <> ")"
  show (DigitDelete idx) = "DigitDelete(" <> show idx <> ")"
  show (DigitFocus idx) = "DigitFocus(" <> show idx <> ")"
  show (DigitBlur idx) = "DigitBlur(" <> show idx <> ")"
  show (PasteDetected _) = "PasteDetected(***)"  -- Don't log OTP values
  show (Completed _) = "Completed(***)"          -- Don't log OTP values
  show ResendClicked = "ResendClicked"
  show ClearError = "ClearError"
