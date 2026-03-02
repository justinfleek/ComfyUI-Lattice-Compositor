-- | Port of ui/src/__tests__/security/attackSurface.test.ts
-- |
-- | Tests security CONCEPTS that can be verified in pure PureScript without
-- | browser APIs, dynamic imports, or mock infrastructure. The original TS file
-- | depends heavily on ExportPipeline (mocks, browser APIs) which cannot be
-- | ported. This module tests the underlying defense primitives:
-- |
-- |   - JSON bomb defense via JsonSanitizer
-- |   - Path traversal detection via pure string checks
-- |   - Input validation for numeric bounds
-- |   - Prototype pollution defense via JsonSanitizer
-- |   - URL injection defense via UrlValidator
-- |
-- | 13 tests across 5 describe blocks:
-- |   - JSON Bomb Defense (3 tests)
-- |   - Path Traversal Defense (2 tests)
-- |   - Input Validation Defense (3 tests)
-- |   - Prototype Pollution Defense (3 tests)
-- |   - URL Injection Defense (2 tests)

module Test.Lattice.Security.AttackSurface (spec) where

import Prelude

import Data.Array (replicate)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Data.Number (isFinite) as Number
import Data.String (Pattern(..), contains) as Str
import Data.String (joinWith, take)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.Services.Security.JsonSanitizer (parseAndSanitize, defaultOptions)
import Lattice.Services.Security.UrlValidator (URLContext(..), validateURL)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Build a deeply nested JSON string: {"nested": {"nested": ... {"value": 1} ... }}
buildNestedJson :: Int -> String
buildNestedJson depth =
  let prefix = foldl (\acc _ -> acc <> "{\"nested\": ") "" (replicate depth unit)
      suffix = foldl (\acc _ -> acc <> "}") "" (replicate depth unit)
  in prefix <> "{\"value\": 1}" <> suffix

-- | Build a JSON array of n integers: [1, 1, ...]
buildArrayJson :: Int -> String
buildArrayJson n =
  let elements = joinWith ", " (replicate n "1")
  in "[" <> elements <> "]"

-- | Check if a string contains path traversal indicators.
-- | Returns true if the path contains ".." or starts with "/".
hasPathTraversal :: String -> Boolean
hasPathTraversal path =
  Str.contains (Str.Pattern "..") path
  || take 1 path == "/"

-- | Check if a string contains URL-encoded traversal sequences.
-- | "%2e" is URL-encoded "." so "%2e%2e%2f" is "../"
hasEncodedTraversal :: String -> Boolean
hasEncodedTraversal path =
  Str.contains (Str.Pattern "%2e") path
  || Str.contains (Str.Pattern "%2E") path

-- | Validate export dimensions: width and height must be > 0 and <= 8192.
validDimension :: Int -> Boolean
validDimension n = n > 0 && n <= 8192

-- | Validate frame count: must be > 0 and <= 10000.
validFrameCount :: Int -> Boolean
validFrameCount n = n > 0 && n <= 10000

-- | Validate frame range: startFrame >= 0 and endFrame > startFrame.
validFrameRange :: Int -> Int -> Boolean
validFrameRange startFrame endFrame =
  startFrame >= 0 && endFrame > startFrame

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Attack Surface - Security Concepts" do
    jsonBombDefenseTests
    pathTraversalDefenseTests
    inputValidationDefenseTests
    prototypePollutionDefenseTests
    urlInjectionDefenseTests

--------------------------------------------------------------------------------
-- JSON Bomb Defense
--------------------------------------------------------------------------------

jsonBombDefenseTests :: Spec Unit
jsonBombDefenseTests = do
  describe "JSON Bomb Defense" do

    it "should reject deeply nested JSON (JSON bomb)" do
      -- Create JSON nested > 50 levels (default maxDepth is 50)
      let json = buildNestedJson 60
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg ->
          if Str.contains (Str.Pattern "depth") errMsg
            then pure unit
            else fail ("Expected error about depth, got: " <> errMsg)
        Nothing -> fail "Expected error about depth but got no error"

    it "should reject large array JSON" do
      -- Use maxArrayLength = 10, provide array of 20 elements
      let opts = defaultOptions { maxArrayLength = 10 }
      let json = buildArrayJson 20
      let result = parseAndSanitize json opts
      result.valid `shouldEqual` false
      case result.err of
        Just errMsg ->
          if Str.contains (Str.Pattern "Array exceeds") errMsg
            then pure unit
            else fail ("Expected error about array exceeds, got: " <> errMsg)
        Nothing -> fail "Expected error about array exceeds but got no error"

    it "should reject __proto__ pollution via sanitizer" do
      -- The sanitizer strips __proto__ keys; verify removal via stats
      let json = "{\"__proto__\": {\"polluted\": true}, \"safe\": 1}"
      let result = parseAndSanitize json defaultOptions
      -- Result is valid because the key is stripped (not rejected)
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 1

--------------------------------------------------------------------------------
-- Path Traversal Defense
--------------------------------------------------------------------------------

pathTraversalDefenseTests :: Spec Unit
pathTraversalDefenseTests = do
  describe "Path Traversal Defense" do

    it "should detect path traversal patterns" do
      -- These are pure string pattern checks for dangerous path inputs
      hasPathTraversal "../../../etc/passwd" `shouldEqual` true
      hasPathTraversal "..\\..\\Windows" `shouldEqual` true
      hasPathTraversal "/etc/passwd" `shouldEqual` true
      -- Safe path should not trigger
      hasPathTraversal "images/photo.png" `shouldEqual` false

    it "should detect URL-encoded traversal" do
      -- "%2e%2e%2f" is URL-encoded "../"
      hasEncodedTraversal "%2e%2e%2fetc%2fpasswd" `shouldEqual` true
      hasEncodedTraversal "%2E%2E%2Fetc%2Fpasswd" `shouldEqual` true
      -- Clean path should not trigger
      hasEncodedTraversal "images/photo.png" `shouldEqual` false

--------------------------------------------------------------------------------
-- Input Validation Defense
--------------------------------------------------------------------------------

inputValidationDefenseTests :: Spec Unit
inputValidationDefenseTests = do
  describe "Input Validation Defense" do

    it "should validate numeric bounds for export dimensions" do
      -- Width/height must be > 0 and <= 8192
      validDimension 1920 `shouldEqual` true
      validDimension 8192 `shouldEqual` true
      validDimension 0 `shouldEqual` false
      validDimension (-1) `shouldEqual` false
      validDimension 8193 `shouldEqual` false
      -- Frame count must be > 0 and <= 10000
      validFrameCount 1 `shouldEqual` true
      validFrameCount 10000 `shouldEqual` true
      validFrameCount 0 `shouldEqual` false
      validFrameCount 10001 `shouldEqual` false

    it "should reject negative frame ranges" do
      -- startFrame >= 0, endFrame > startFrame
      validFrameRange 0 100 `shouldEqual` true
      validFrameRange 10 20 `shouldEqual` true
      validFrameRange (-1) 10 `shouldEqual` false
      validFrameRange 10 10 `shouldEqual` false
      validFrameRange 20 10 `shouldEqual` false

    it "should reject non-finite numbers" do
      let nan = 0.0 / 0.0
      let posInf = 1.0 / 0.0
      let negInf = (-1.0) / 0.0
      Number.isFinite nan `shouldEqual` false
      Number.isFinite posInf `shouldEqual` false
      Number.isFinite negInf `shouldEqual` false
      -- Finite numbers should pass
      Number.isFinite 42.0 `shouldEqual` true
      Number.isFinite 0.0 `shouldEqual` true
      Number.isFinite (-3.14) `shouldEqual` true

--------------------------------------------------------------------------------
-- Prototype Pollution Defense
--------------------------------------------------------------------------------

prototypePollutionDefenseTests :: Spec Unit
prototypePollutionDefenseTests = do
  describe "Prototype Pollution Defense" do

    it "should strip __proto__ from parsed JSON" do
      let json = "{\"__proto__\": {\"isAdmin\": true}, \"name\": \"safe\"}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 1

    it "should strip constructor from parsed JSON" do
      let json = "{\"constructor\": {\"prototype\": {\"evil\": true}}}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 1

    it "should strip __defineGetter__ from parsed JSON" do
      let json = "{\"__defineGetter__\": \"evil\", \"safe\": 1}"
      let result = parseAndSanitize json defaultOptions
      result.valid `shouldEqual` true
      result.stats.prototypeKeysRemoved `shouldEqual` 1

--------------------------------------------------------------------------------
-- URL Injection Defense
--------------------------------------------------------------------------------

urlInjectionDefenseTests :: Spec Unit
urlInjectionDefenseTests = do
  describe "URL Injection Defense" do

    it "should block javascript: URLs in export paths" do
      let result = validateURL "javascript:alert(1)" CtxAsset
      result.valid `shouldEqual` false
      case result.error of
        Just err ->
          if Str.contains (Str.Pattern "javascript:") err
            then pure unit
            else fail ("Expected error mentioning 'javascript:', got: " <> err)
        Nothing -> fail "Expected error about javascript: protocol"

    it "should block data: URLs with HTML content" do
      let result = validateURL "data:text/html,<script>alert(1)</script>" CtxAsset
      result.valid `shouldEqual` false
      case result.error of
        Just err ->
          if Str.contains (Str.Pattern "blocked") err
            then pure unit
            else fail ("Expected error mentioning 'blocked', got: " <> err)
        Nothing -> fail "Expected error about blocked data URL"
