-- |
-- Module      : Lattice.Utils.Validation
-- Description : Input validation utilities for runtime boundary checking
-- 
-- Migrated from ui/src/utils/validation.ts
-- Pure validation functions that return Either String a (success or error)
-- Used for AI commands, file imports, user input validation
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Validation
  ( -- Validation result type
    ValidationResult(..)
  , ok
  , failValidation
  -- Primitive validators
  , validateString
  , validateFiniteNumber
  , validateInteger
  , validateBoolean
  , validateEnum
  -- Array validators
  , validateArray
  , validateNumberArray
  -- Object validators
  , validateObject
  , validateVec2
  , validateVec3
  , validateColor
  -- Optional validators
  , optional
  , withDefault
  -- Composition helpers
  , validateSchema
  , validateAll
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Scientific (toRealFloat)
import Data.Aeson (Value(..), ToJSON(..))
import Lattice.Utils.ArrayUtils (safeArrayGet)
import Lattice.Utils.NumericSafety (isFinite)

-- ============================================================================
-- VALIDATION RESULT TYPE
-- ============================================================================

-- | Validation result - either success with typed value, or failure with error message
data ValidationResult a
  = Ok a
  | Fail Text
  deriving (Eq, Show)

-- | Make ValidationResult a Monad for do-notation
instance Functor ValidationResult where
  fmap f (Ok x) = Ok (f x)
  fmap _ (Fail err) = Fail err

instance Applicative ValidationResult where
  pure = Ok
  (Ok f) <*> (Ok x) = Ok (f x)
  (Fail err) <*> _ = Fail err
  _ <*> (Fail err) = Fail err

instance Monad ValidationResult where
  (Ok x) >>= f = f x
  (Fail err) >>= _ = Fail err

-- | Helper to create success result
ok :: a -> ValidationResult a
ok = Ok

-- | Helper to create failure result (exported as failValidation to avoid Prelude conflict)
failValidation :: Text -> ValidationResult a
failValidation = Fail

fail :: Text -> ValidationResult a
fail = Fail

-- | Extract value from ValidationResult, using default on failure
fromValidation :: a -> ValidationResult a -> a
fromValidation _ (Ok x) = x
fromValidation def (Fail _) = def

-- | Check if validation succeeded
isOk :: ValidationResult a -> Bool
isOk (Ok _) = True
isOk (Fail _) = False

-- ============================================================================
-- PRIMITIVE VALIDATORS
-- ============================================================================

-- | String validation options
data StringOptions = StringOptions
  { stringOptionsMinLength :: Maybe Int
  , stringOptionsMaxLength :: Maybe Int
  , stringOptionsAllowEmpty :: Bool
  }

defaultStringOptions :: StringOptions
defaultStringOptions = StringOptions Nothing Nothing False

-- | Validate that value is a string
validateString :: Text -> Text -> StringOptions -> ValidationResult Text
validateString value name opts =
  if T.null value && not (stringOptionsAllowEmpty opts)
    then Fail (name <> " cannot be empty")
    else case stringOptionsMinLength opts of
      Just minLen ->
        if T.length value < minLen
          then Fail (name <> " must be at least " <> T.pack (show minLen) <> " characters")
          else case stringOptionsMaxLength opts of
            Just maxLen ->
              if T.length value > maxLen
                then Fail (name <> " must be at most " <> T.pack (show maxLen) <> " characters")
                else Ok value
            Nothing -> Ok value
      Nothing -> case stringOptionsMaxLength opts of
        Just maxLen ->
          if T.length value > maxLen
            then Fail (name <> " must be at most " <> T.pack (show maxLen) <> " characters")
            else Ok value
        Nothing -> Ok value

-- | Number validation options
data NumberOptions = NumberOptions
  { numberOptionsMin :: Maybe Double
  , numberOptionsMax :: Maybe Double
  , numberOptionsAllowNaN :: Bool
  }

defaultNumberOptions :: NumberOptions
defaultNumberOptions = NumberOptions Nothing Nothing False

-- | Validate that value is a finite number (not NaN, not Infinity)
validateFiniteNumber :: Double -> Text -> NumberOptions -> ValidationResult Double
validateFiniteNumber value name opts
  | isNaN value && not (numberOptionsAllowNaN opts) =
      Fail (name <> " must be a valid number, got NaN")
  | not (isFinite value) =
      Fail (name <> " must be a finite number, got " <> T.pack (show value))
  | otherwise = case numberOptionsMin opts of
      Just minVal ->
        if value < minVal
          then Fail (name <> " must be >= " <> T.pack (show minVal) <> ", got " <> T.pack (show value))
          else case numberOptionsMax opts of
            Just maxVal ->
              if value > maxVal
                then Fail (name <> " must be <= " <> T.pack (show maxVal) <> ", got " <> T.pack (show value))
                else Ok value
            Nothing -> Ok value
      Nothing -> case numberOptionsMax opts of
        Just maxVal ->
          if value > maxVal
            then Fail (name <> " must be <= " <> T.pack (show maxVal) <> ", got " <> T.pack (show value))
            else Ok value
        Nothing -> Ok value

-- | Validate that value is an integer
validateInteger :: Double -> Text -> NumberOptions -> ValidationResult Int
validateInteger value name opts = do
  num <- validateFiniteNumber value name opts
  if fromIntegral (round num) == num
    then Ok (round num)
    else Fail (name <> " must be an integer, got " <> T.pack (show num))

-- | Validate that value is a boolean
validateBoolean :: Bool -> Text -> ValidationResult Bool
validateBoolean value _ = Ok value

-- | Validate that value is one of allowed values
validateEnum :: Text -> Text -> [Text] -> ValidationResult Text
validateEnum value name allowed =
  if value `elem` allowed
    then Ok value
    else Fail (name <> " must be one of [" <> T.intercalate ", " allowed <> "], got \"" <> value <> "\"")

-- ============================================================================
-- ARRAY VALIDATORS
-- ============================================================================

-- | Array validation options
data ArrayOptions = ArrayOptions
  { arrayOptionsMinLength :: Maybe Int
  , arrayOptionsMaxLength :: Maybe Int
  }

defaultArrayOptions :: ArrayOptions
defaultArrayOptions = ArrayOptions Nothing Nothing

-- | Validate that value is an array
validateArray :: (Value -> Int -> ValidationResult a) -> [Value] -> Text -> ArrayOptions -> ValidationResult [a]
validateArray itemValidator arr name opts = do
  let len = length arr
  case arrayOptionsMinLength opts of
    Just minLen ->
      if len < minLen
        then Fail (name <> " must have at least " <> T.pack (show minLen) <> " items")
        else validateItems arr 0
    Nothing -> validateItems arr 0
  where
    validateItems [] _ = Ok []
    validateItems (x:xs) idx = do
      item <- itemValidator x idx
      rest <- validateItems xs (idx + 1)
      return (item : rest)

-- | Validate array of finite numbers
validateNumberArray :: [Double] -> Text -> ArrayOptions -> NumberOptions -> ValidationResult [Double]
validateNumberArray arr name arrOpts numOpts =
  let len = length arr
      checkLength = case arrayOptionsMinLength arrOpts of
        Just minLen -> if len < minLen
          then Fail (name <> " must have at least " <> T.pack (show minLen) <> " items")
          else Ok ()
        Nothing -> Ok ()
      checkMaxLength = case arrayOptionsMaxLength arrOpts of
        Just maxLen -> if len > maxLen
          then Fail (name <> " must have at most " <> T.pack (show maxLen) <> " items")
          else Ok ()
        Nothing -> Ok ()
  in do
    checkLength
    checkMaxLength
    mapM (\idx -> validateFiniteNumber (safeArrayGet arr idx 0.0) (name <> "[" <> T.pack (show idx) <> "]") numOpts) [0 .. len - 1]

-- ============================================================================
-- OBJECT VALIDATORS
-- ============================================================================

-- | Validate that value is a non-null object
validateObject :: HashMap Text Value -> Text -> ValidationResult (HashMap Text Value)
validateObject obj _ = Ok obj

-- | Validate a Vec2 (x, y coordinates)
validateVec2 :: HashMap Text Value -> Text -> ValidationResult (Double, Double)
validateVec2 obj name = do
  xVal <- case HM.lookup "x" obj of
    Just (Number x) -> Ok (toRealFloat x)
    _ -> Fail (name <> ".x must be a number")
  yVal <- case HM.lookup "y" obj of
    Just (Number y) -> Ok (toRealFloat y)
    _ -> Fail (name <> ".y must be a number")
  x <- validateFiniteNumber xVal (name <> ".x") defaultNumberOptions
  y <- validateFiniteNumber yVal (name <> ".y") defaultNumberOptions
  return (x, y)

-- | Validate a Vec3 (x, y, z coordinates)
validateVec3 :: HashMap Text Value -> Text -> Bool -> ValidationResult (Double, Double, Double)
validateVec3 obj name allowMissingZ = do
  xVal <- case HM.lookup "x" obj of
    Just (Number x) -> Ok (toRealFloat x)
    _ -> Fail (name <> ".x must be a number")
  yVal <- case HM.lookup "y" obj of
    Just (Number y) -> Ok (toRealFloat y)
    _ -> Fail (name <> ".y must be a number")
  zVal <- case HM.lookup "z" obj of
    Just (Number z) -> Ok (toRealFloat z)
    Nothing -> if allowMissingZ then Ok 0.0 else Fail (name <> ".z must be a number")
    _ -> Fail (name <> ".z must be a number")
  x <- validateFiniteNumber xVal (name <> ".x") defaultNumberOptions
  y <- validateFiniteNumber yVal (name <> ".y") defaultNumberOptions
  z <- validateFiniteNumber zVal (name <> ".z") defaultNumberOptions
  return (x, y, z)

-- | Validate a color object (r, g, b, optional a)
validateColor :: HashMap Text Value -> Text -> ValidationResult (Double, Double, Double, Maybe Double)
validateColor obj name = do
  rVal <- case HM.lookup "r" obj of
    Just (Number r) -> Ok (toRealFloat r)
    _ -> Fail (name <> ".r must be a number")
  gVal <- case HM.lookup "g" obj of
    Just (Number g) -> Ok (toRealFloat g)
    _ -> Fail (name <> ".g must be a number")
  bVal <- case HM.lookup "b" obj of
    Just (Number b) -> Ok (toRealFloat b)
    _ -> Fail (name <> ".b must be a number")
  r <- validateFiniteNumber rVal (name <> ".r") (NumberOptions (Just 0) (Just 255) False)
  g <- validateFiniteNumber gVal (name <> ".g") (NumberOptions (Just 0) (Just 255) False)
  b <- validateFiniteNumber bVal (name <> ".b") (NumberOptions (Just 0) (Just 255) False)
  a <- case HM.lookup "a" obj of
    Just (Number alpha) -> do
      aVal <- validateFiniteNumber (toRealFloat alpha) (name <> ".a") (NumberOptions (Just 0) (Just 1) False)
      return (Just aVal)
    _ -> return Nothing
  return (r, g, b, a)

-- ============================================================================
-- OPTIONAL VALIDATORS
-- ============================================================================

-- | Make a validator optional - returns Nothing if value is Nothing
optional :: (a -> Text -> ValidationResult b) -> Maybe a -> Text -> ValidationResult (Maybe b)
optional validator Nothing _ = Ok Nothing
optional validator (Just val) name = do
  result <- validator val name
  return (Just result)

-- | Provide a default value if Nothing
withDefault :: (a -> Text -> ValidationResult b) -> b -> Maybe a -> Text -> ValidationResult b
withDefault validator def Nothing _ = Ok def
withDefault validator _ (Just val) name = validator val name

-- ============================================================================
-- COMPOSITION HELPERS
-- ============================================================================

-- | Validate all fields of an object schema
validateSchema :: HashMap Text (Value -> Text -> ValidationResult a) -> HashMap Text Value -> Text -> ValidationResult (HashMap Text a)
validateSchema schema obj name =
  let validateField (key, validator) = do
        val <- case HM.lookup key obj of
          Just v -> Ok v
          Nothing -> Fail (name <> "." <> key <> " is required")
        result <- validator val (name <> "." <> key)
        return (key, result)
  in do
    results <- mapM validateField (HM.toList schema)
    return (HM.fromList results)

-- | Collect all validation errors instead of failing on first
validateAll :: [ValidationResult a] -> ValidationResult [a]
validateAll validations =
  let (oks, fails) = partitionResults validations
  in if null fails
    then Ok oks
    else Fail (T.intercalate "; " fails)
  where
    partitionResults [] = ([], [])
    partitionResults (Ok x : xs) = let (oks', fails') = partitionResults xs in (x : oks', fails')
    partitionResults (Fail err : xs) = let (oks', fails') = partitionResults xs in (oks', err : fails')

-- Note: Using `fail` as a function name conflicts with Prelude.fail
-- Using `failValidation` instead to avoid conflict
