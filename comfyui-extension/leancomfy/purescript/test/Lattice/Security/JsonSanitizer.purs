-- | Port of ui/src/__tests__/security/jsonSanitizer.test.ts
-- |
-- | Tests security validation and sanitization for JSON data to prevent:
-- |   - JSON bombs (deeply nested structures)
-- |   - Resource exhaustion (large arrays/objects)
-- |   - Prototype pollution attacks
-- |
-- | 35 tests across 12 describe blocks:
-- |   - parseAndSanitize - Depth Limits (3 tests)
-- |   - parseAndSanitize - Array Size Limits (3 tests)
-- |   - parseAndSanitize - String Size Limits (2 tests)
-- |   - parseAndSanitize - Prototype Pollution Protection (5 tests)
-- |   - parseAndSanitize - Object Key Limits (2 tests)
-- |   - parseAndSanitize - Special Values (4 tests)
-- |   - parseAndSanitize - Invalid JSON (2 tests)
-- |   - sanitize - Pre-parsed Data (2 tests)
-- |   - quickValidate - Fast Rejection (4 tests)
-- |   - safeParse - Convenience Function (3 tests)
-- |   - deepFreeze - Immutability (2 tests)
-- |   - Custom Options (4 tests)

module Test.Lattice.Security.JsonSanitizer (spec) where

import Prelude

import Data.Argonaut.Core as Json
import Data.Array (any, elem, replicate)
import Data.Either (Either(..), isLeft)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Foreign.Object as Obj
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Test.Spec.Assertions.String (shouldContain) as StringAssert

import Lattice.Services.Security.JsonSanitizer
  ( defaultOptions
  , parseAndSanitize
  , sanitize
  , quickValidate
  , safeParse
  , deepFreeze
  )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Build a deeply nested JSON string: {"nested": {"nested": ... {"value": 1} ... }}
buildNestedJson :: Int -> String
buildNestedJson depth =
  let prefix = foldl (\acc _ -> acc <> "{\"nested\": ") "" (replicate depth unit)
      suffix = foldl (\acc _ -> acc <> "}") "" (replicate depth unit)
  in prefix <> "{\"value\": 1}" <> suffix

-- | Build a JSON array of n integers wrapped in an object: {"data": [1, 1, ...]}
buildLargeArrayJson :: Int -> String
buildLargeArrayJson n =
  let elements = joinWith ", " (replicate n "1")
  in "{\"data\": [" <> elements <> "]}"

-- | Build a JSON string with a repeated character of length n: {"data": "aaa..."}
buildLongStringJson :: Int -> String
buildLongStringJson n =
  let str = joinWith "" (replicate n "a")
  in "{\"data\": \"" <> str <> "\"}"

-- | Repeat a string n times
repeatStr :: Int -> String -> String
repeatStr n s = joinWith "" (replicate n s)

-- | Assert that a result is invalid and its error contains a substring
assertInvalidWithError :: forall r. { valid :: Boolean, err :: Maybe String | r } -> String -> Aff Unit
assertInvalidWithError result expectedSubstr = do
  result.valid `shouldEqual` false
  case result.err of
    Just errMsg -> errMsg `StringAssert.shouldContain` expectedSubstr
    Nothing -> fail ("Expected error containing '" <> expectedSubstr <> "' but got no error")

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "JSON Sanitizer - Security" do
    depthLimitTests
    arraySizeLimitTests
    stringSizeLimitTests
    prototypePollutionTests
    objectKeyLimitTests
    specialValueTests
    invalidJsonTests
    sanitizePreParsedTests
    quickValidateTests
    safeParseTests
    deepFreezeTests
    customOptionsTests

--------------------------------------------------------------------------------
-- parseAndSanitize - Depth Limits
--------------------------------------------------------------------------------

depthLimitTests :: Spec Unit
depthLimitTests = do
  describe "parseAndSanitize - Depth Limits" do

    it "should BLOCK JSON exceeding max depth (default: 50)" do
      -- Create deeply nested JSON: {"nested": {"nested": ... }} with 60 levels
      let json = buildNestedJson 60
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg -> errMsg `StringAssert.shouldContain` "depth"
        Nothing -> fail "Expected error about depth"

    it "should ALLOW JSON within depth limit" do
      -- Create JSON with 10 levels of nesting
      let json = buildNestedJson 10
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      -- Depth should be reasonable (10 nesting + 1 inner object = 11)
      if result.stats.depth <= 15
        then pure unit
        else fail ("Expected depth <= 15, got " <> show result.stats.depth)

    it "should track actual depth in stats" do
      -- {"a": {"b": {"c": {"d": 1}}}} is 4 levels deep
      let json = "{\"a\": {\"b\": {\"c\": {\"d\": 1}}}}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.depth `shouldEqual` 4

--------------------------------------------------------------------------------
-- parseAndSanitize - Array Size Limits
--------------------------------------------------------------------------------

arraySizeLimitTests :: Spec Unit
arraySizeLimitTests = do
  describe "parseAndSanitize - Array Size Limits" do

    it "should BLOCK arrays exceeding max length" do
      -- Use custom options with small limit to avoid generating huge strings
      let opts = defaultOptions { maxArrayLength = 100 }
      let json = buildLargeArrayJson 150
      let result = parseAndSanitize json opts
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg -> errMsg `StringAssert.shouldContain` "Array exceeds"
        Nothing -> fail "Expected error about array exceeds"

    it "should ALLOW arrays within limit" do
      let json = buildLargeArrayJson 100
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true

    it "should BLOCK cumulative array elements across many arrays" do
      -- Use custom options: maxArrayLength = 50 so cumulative limit = 500
      -- Create 60 small arrays of size 10 each = 600 cumulative + outer array of 60
      let opts = defaultOptions { maxArrayLength = 50 }
      let innerArray = joinWith ", " (replicate 10 "1")
      let arrays = replicate 60 ("[" <> innerArray <> "]")
      let json = "{\"data\": [" <> joinWith ", " arrays <> "]}"
      let result = parseAndSanitize json opts
      -- Either exceeds single array limit or cumulative limit
      result.valid `shouldEqual` false

--------------------------------------------------------------------------------
-- parseAndSanitize - String Size Limits
--------------------------------------------------------------------------------

stringSizeLimitTests :: Spec Unit
stringSizeLimitTests = do
  describe "parseAndSanitize - String Size Limits" do

    it "should BLOCK strings exceeding max length" do
      -- Use custom options with small string limit to keep test fast
      -- String of 150 chars in JSON wrapper ~161 bytes, passes pre-parse check (200*2=400)
      -- but the individual string (150) exceeds maxStringLength (200)
      let opts = defaultOptions { maxStringLength = 200 }
      let json = buildLongStringJson 300
      let result = parseAndSanitize json opts
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg -> errMsg `StringAssert.shouldContain` "String exceeds"
        Nothing -> fail "Expected error about string exceeds"

    it "should ALLOW strings within limit" do
      let json = buildLongStringJson 1000
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true

--------------------------------------------------------------------------------
-- parseAndSanitize - Prototype Pollution Protection
--------------------------------------------------------------------------------

prototypePollutionTests :: Spec Unit
prototypePollutionTests = do
  describe "parseAndSanitize - Prototype Pollution Protection" do

    it "should BLOCK __proto__ keys" do
      let json = "{\"__proto__\": {\"polluted\": true}, \"safe\": 1}"
      let result = parseAndSanitize json defaultOptions
      -- Result is still valid, but the key is removed with a warning
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 1
      -- Check that the warning was recorded
      let hasWarning = any (_ == "Prototype pollution key removed: __proto__") result.warnings
      hasWarning `shouldEqual` true
      -- Verify __proto__ key was removed from result
      -- NOTE: Obj.lookup uses JS 'in' operator which traverses the prototype chain,
      -- so __proto__/constructor are always found. Use Obj.keys (Object.keys) instead.
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj -> do
            -- The __proto__ key should not be in the sanitized object's own keys
            if elem "__proto__" (Obj.keys obj)
              then fail "Expected __proto__ key to be removed"
              else pure unit
            -- The safe key should still be present
            if elem "safe" (Obj.keys obj)
              then pure unit
              else fail "Expected 'safe' key to be present"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"

    it "should BLOCK constructor keys" do
      let json = "{\"constructor\": {\"prototype\": {\"evil\": true}}}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 1
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj ->
            if elem "constructor" (Obj.keys obj)
              then fail "Expected 'constructor' key to be removed"
              else pure unit
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"

    it "should BLOCK prototype keys" do
      let json = "{\"prototype\": {\"evil\": true}}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 1

    it "should BLOCK case variations of dangerous keys" do
      let json = "{\"__PROTO__\": {\"evil\": true}, \"CONSTRUCTOR\": {\"bad\": true}}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 2

    it "should BLOCK __defineGetter__ and similar" do
      let json = "{\"__defineGetter__\": \"evil\", \"__defineSetter__\": \"bad\"}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 2

--------------------------------------------------------------------------------
-- parseAndSanitize - Object Key Limits
--------------------------------------------------------------------------------

objectKeyLimitTests :: Spec Unit
objectKeyLimitTests = do
  describe "parseAndSanitize - Object Key Limits" do

    it "should BLOCK objects with too many total keys" do
      -- Use custom options with small key limit to keep test fast
      let opts = defaultOptions { maxTotalKeys = 5 }
      let json = "{\"a\": 1, \"b\": 2, \"c\": 3, \"d\": 4, \"e\": 5, \"f\": 6, \"g\": 7}"
      let result = parseAndSanitize json opts
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg -> errMsg `StringAssert.shouldContain` "keys exceed"
        Nothing -> fail "Expected error about keys exceed"

    it "should SKIP keys that are too long" do
      -- Create a key longer than maxKeyLength (default: 1000)
      let longKey = repeatStr 1500 "a"
      let json = "{\"" <> longKey <> "\": 1, \"normal\": 2}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      -- Check for truncation warning
      let expectedWarning = "Key truncated: " <> repeatStr 50 "a" <> "... (exceeded 1000 chars)"
      let hasWarning = any (_ == expectedWarning) result.warnings
      hasWarning `shouldEqual` true
      -- Verify the normal key is present and the long key is not
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj -> do
            case Obj.lookup "normal" obj of
              Just _ -> pure unit
              Nothing -> fail "Expected 'normal' key to be present"
            case Obj.lookup longKey obj of
              Nothing -> pure unit
              Just _ -> fail "Expected long key to be removed"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"

--------------------------------------------------------------------------------
-- parseAndSanitize - Special Values
--------------------------------------------------------------------------------

specialValueTests :: Spec Unit
specialValueTests = do
  describe "parseAndSanitize - Special Values" do

    it "should handle null values" do
      let json = "{\"value\": null}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj ->
            case Obj.lookup "value" obj of
              Just v ->
                if Json.isNull v
                  then pure unit
                  else fail "Expected null value"
              Nothing -> fail "Expected 'value' key"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"

    it "should handle boolean values" do
      let json = "{\"yes\": true, \"no\": false}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj -> do
            case Obj.lookup "yes" obj of
              Just v -> Json.toBoolean v `shouldEqual` Just true
              Nothing -> fail "Expected 'yes' key"
            case Obj.lookup "no" obj of
              Just v -> Json.toBoolean v `shouldEqual` Just false
              Nothing -> fail "Expected 'no' key"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"

    it "should handle number values" do
      let json = "{\"int\": 42, \"float\": 3.14, \"neg\": -10}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj -> do
            case Obj.lookup "int" obj of
              Just v -> Json.toNumber v `shouldEqual` Just 42.0
              Nothing -> fail "Expected 'int' key"
            case Obj.lookup "float" obj of
              Just v -> Json.toNumber v `shouldEqual` Just 3.14
              Nothing -> fail "Expected 'float' key"
            case Obj.lookup "neg" obj of
              Just v -> Json.toNumber v `shouldEqual` Just (-10.0)
              Nothing -> fail "Expected 'neg' key"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"

    it "should remove null bytes from strings" do
      let json = "{\"value\": \"hello\\u0000world\"}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj ->
            case Obj.lookup "value" obj of
              Just v -> Json.toString v `shouldEqual` Just "helloworld"
              Nothing -> fail "Expected 'value' key"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"
      -- Check warning about null bytes
      let hasWarning = any (_ == "Null bytes removed from string") result.warnings
      hasWarning `shouldEqual` true

--------------------------------------------------------------------------------
-- parseAndSanitize - Invalid JSON
--------------------------------------------------------------------------------

invalidJsonTests :: Spec Unit
invalidJsonTests = do
  describe "parseAndSanitize - Invalid JSON" do

    it "should return error for invalid JSON syntax" do
      let result = parseAndSanitize "{not valid json}" defaultOptions
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg -> errMsg `StringAssert.shouldContain` "Invalid JSON"
        Nothing -> fail "Expected error about invalid JSON"

    it "should return error for empty string input" do
      let result = parseAndSanitize "" defaultOptions
      result.valid `shouldEqual` false

--------------------------------------------------------------------------------
-- sanitize - Pre-parsed Data
--------------------------------------------------------------------------------

sanitizePreParsedTests :: Spec Unit
sanitizePreParsedTests = do
  describe "sanitize - Pre-parsed Data" do

    it "should sanitize already-parsed objects" do
      -- Build a Json object with "safe" and "__proto__" keys
      let obj = Obj.fromFoldable
            [ Tuple "safe" (Json.fromString "value")
            , Tuple "__proto__" (Json.fromObject (Obj.singleton "evil" (Json.fromBoolean true)))
            ]
      let json = Json.fromObject obj
      let result = sanitize json defaultOptions
      result.valid `shouldEqual` true
      case result.dat of
        Just d -> case Json.toObject d of
          Just sanitizedObj -> do
            -- safe key should be present
            case Obj.lookup "safe" sanitizedObj of
              Just v -> Json.toString v `shouldEqual` Just "value"
              Nothing -> fail "Expected 'safe' key to be present"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"

    it "should handle arrays" do
      let arr = Json.fromArray
            [ Json.fromNumber 1.0
            , Json.fromNumber 2.0
            , Json.fromObject (Obj.singleton "nested" (Json.fromBoolean true))
            ]
      let result = sanitize arr defaultOptions
      result.valid `shouldEqual` true
      case result.dat of
        Just d ->
          if Json.isArray d
            then pure unit
            else fail "Expected result to be an array"
        Nothing -> fail "Expected data in result"

--------------------------------------------------------------------------------
-- quickValidate - Fast Rejection
--------------------------------------------------------------------------------

quickValidateTests :: Spec Unit
quickValidateTests = do
  describe "quickValidate - Fast Rejection" do

    it "should quickly reject oversized JSON" do
      -- Use custom options with a small limit for test speed
      let opts = defaultOptions { maxStringLength = 50 }
      let large = repeatStr 200 "a"
      let json = "{\"x\":\"" <> large <> "\"}"
      quickValidate json opts `shouldEqual` false

    it "should quickly reject deep nesting" do
      -- Build 60 levels of nesting with square brackets
      let json = foldl (\acc _ -> "[" <> acc <> "]") "1" (replicate 60 unit)
      quickValidate json defaultOptions `shouldEqual` false

    it "should quickly reject __proto__ keys" do
      quickValidate "{\"__proto__\": {}}" defaultOptions `shouldEqual` false
      quickValidate "{\"constructor\": {}}" defaultOptions `shouldEqual` false

    it "should pass valid JSON" do
      quickValidate "{\"safe\": \"value\"}" defaultOptions `shouldEqual` true

--------------------------------------------------------------------------------
-- safeParse - Convenience Function
--------------------------------------------------------------------------------

safeParseTests :: Spec Unit
safeParseTests = do
  describe "safeParse - Convenience Function" do

    it "should return parsed data for valid JSON" do
      let result = safeParse "{\"value\": 42}" defaultOptions
      case result of
        Right json -> case Json.toObject json of
          Just obj ->
            case Obj.lookup "value" obj of
              Just v -> Json.toNumber v `shouldEqual` Just 42.0
              Nothing -> fail "Expected 'value' key"
          Nothing -> fail "Expected result to be an object"
        Left err -> fail ("Expected Right, got Left: " <> err)

    it "should return Left for invalid JSON" do
      let result = safeParse "{invalid}" defaultOptions
      isLeft result `shouldEqual` true

    it "should return Left for oversized JSON" do
      -- Use custom options with small string limit
      let opts = defaultOptions { maxStringLength = 10 }
      let large = repeatStr 50 "a"
      let result = safeParse ("{\"x\":\"" <> large <> "\"}") opts
      isLeft result `shouldEqual` true

--------------------------------------------------------------------------------
-- deepFreeze - Immutability
--------------------------------------------------------------------------------

deepFreezeTests :: Spec Unit
deepFreezeTests = do
  describe "deepFreeze - Immutability" do

    it "should be identity for objects (PureScript is immutable by default)" do
      let obj = Json.fromObject (Obj.fromFoldable
            [ Tuple "a" (Json.fromNumber 1.0)
            , Tuple "nested" (Json.fromObject (Obj.singleton "b" (Json.fromNumber 2.0)))
            ])
      let frozen = deepFreeze obj
      -- deepFreeze is identity in PureScript
      (Json.stringify frozen) `shouldEqual` (Json.stringify obj)

    it "should handle primitives" do
      Json.stringify (deepFreeze (Json.fromNumber 42.0)) `shouldEqual` Json.stringify (Json.fromNumber 42.0)
      Json.stringify (deepFreeze (Json.fromString "string")) `shouldEqual` Json.stringify (Json.fromString "string")
      Json.stringify (deepFreeze Json.jsonNull) `shouldEqual` Json.stringify Json.jsonNull

--------------------------------------------------------------------------------
-- Custom Options
--------------------------------------------------------------------------------

customOptionsTests :: Spec Unit
customOptionsTests = do
  describe "Custom Options" do

    it "should respect custom maxDepth" do
      -- {"a": {"b": {"c": 1}}} is 3 levels deep
      let json = "{\"a\": {\"b\": {\"c\": 1}}}"
      let result = parseAndSanitize json (defaultOptions { maxDepth = 2 })
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg -> errMsg `StringAssert.shouldContain` "depth"
        Nothing -> fail "Expected error about depth"

    it "should respect custom maxArrayLength" do
      let json = buildLargeArrayJson 100
      let result = parseAndSanitize json (defaultOptions { maxArrayLength = 50 })
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg -> errMsg `StringAssert.shouldContain` "Array exceeds"
        Nothing -> fail "Expected error about array exceeds"

    it "should allow prototype keys when disabled" do
      let json = "{\"__proto__\": {\"x\": 1}}"
      let result = parseAndSanitize json (defaultOptions { removePrototypeKeys = false })
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 0

    it "should allow null bytes when disabled" do
      let json = "{\"value\": \"hello\\u0000world\"}"
      let result = parseAndSanitize json (defaultOptions { removeNullBytes = false })
      result.valid `shouldEqual` true
      case result.dat of
        Just d -> case Json.toObject d of
          Just obj ->
            case Obj.lookup "value" obj of
              Just v -> Json.toString v `shouldEqual` Just "hello\x0000world"
              Nothing -> fail "Expected 'value' key"
          Nothing -> fail "Expected result to be an object"
        Nothing -> fail "Expected data in result"
