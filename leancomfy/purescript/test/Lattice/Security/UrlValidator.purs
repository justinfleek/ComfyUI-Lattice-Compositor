-- | Port of ui/src/__tests__/security/urlValidator.test.ts
-- |
-- | Tests security validation for URLs to prevent XSS, code execution,
-- | and other URL-based attacks.
-- |
-- | 30 tests across 8 describe blocks:
-- |   - validateURL - Blocked Protocols (7 tests)
-- |   - validateURL - Data URLs (10 tests)
-- |   - validateURL - Safe Protocols (6 tests)
-- |   - validateURL - Edge Cases (5 tests)
-- |   - sanitizeURLForHTML (2 tests)
-- |   - validateURLs - Batch Validation (1 test)
-- |   - isTrustedDomain (4 tests)
-- |   - extractAndValidateURLs (2 tests)

module Test.Lattice.Security.UrlValidator (spec) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..), isLeft)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Test.Spec.Assertions.String (shouldContain, shouldNotContain) as StringAssert

import Lattice.Services.Security.UrlValidator
  ( URLContext(..)
  , URLRiskLevel(..)
  , validateURL
  , validateURLs
  , sanitizeURLForHTML
  , isTrustedDomain
  , extractAndValidateURLs
  )

spec :: Spec Unit
spec = do
  describe "URL Validator - Security" do

    ---------------------------------------------------------------------------
    -- validateURL - Blocked Protocols
    ---------------------------------------------------------------------------
    describe "validateURL - Blocked Protocols" do
      it "should BLOCK javascript: URLs" do
        let result = validateURL "javascript:alert(1)" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked
        case result.error of
          Just err -> err `StringAssert.shouldContain` "javascript:"
          Nothing -> fail "Expected error message containing 'javascript:'"

      it "should BLOCK vbscript: URLs" do
        let result = validateURL "vbscript:msgbox(\"test\")" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

      it "should BLOCK file: URLs" do
        let result = validateURL "file:///etc/passwd" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

      it "should BLOCK ftp: URLs" do
        let result = validateURL "ftp://ftp.example.com/file.txt" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

      it "should BLOCK chrome: URLs" do
        let result = validateURL "chrome://settings" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

      it "should BLOCK about: URLs" do
        let result = validateURL "about:blank" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

      it "should BLOCK ws: WebSocket URLs for assets" do
        let result = validateURL "ws://example.com/socket" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

    ---------------------------------------------------------------------------
    -- validateURL - Data URLs
    ---------------------------------------------------------------------------
    describe "validateURL - Data URLs" do
      it "should BLOCK data:text/html (XSS vector)" do
        let result = validateURL "data:text/html,<script>alert(1)</script>" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked
        case result.error of
          Just err -> err `StringAssert.shouldContain` "blocked content type"
          Nothing -> fail "Expected error about blocked content type"

      it "should BLOCK data:application/javascript" do
        let result = validateURL "data:application/javascript,alert(1)" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

      it "should BLOCK data:image/svg+xml with script tags" do
        let result = validateURL "data:image/svg+xml,<svg><script>alert(1)</script></svg>" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

      it "should ALLOW data:image/png" do
        let result = validateURL "data:image/png;base64,iVBORw0KGgo=" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should ALLOW data:image/jpeg" do
        let result = validateURL "data:image/jpeg;base64,/9j/4AAQ" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should ALLOW data:image/svg+xml without script" do
        let result = validateURL "data:image/svg+xml,<svg><rect width=\"100\" height=\"100\"/></svg>" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should ALLOW data:audio/mp3" do
        let result = validateURL "data:audio/mp3;base64,//uQ" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should ALLOW data:video/mp4" do
        let result = validateURL "data:video/mp4;base64,AAAA" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should ALLOW data:application/json" do
        let result = validateURL "data:application/json,{\"test\":true}" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should BLOCK unknown data MIME types" do
        let result = validateURL "data:application/x-unknown,test" CtxAsset
        result.valid `shouldEqual` false
        result.riskLevel `shouldEqual` RiskBlocked

    ---------------------------------------------------------------------------
    -- validateURL - Safe Protocols
    ---------------------------------------------------------------------------
    describe "validateURL - Safe Protocols" do
      it "should ALLOW https: URLs" do
        let result = validateURL "https://example.com/image.png" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe
        result.protocol `shouldEqual` "https:"

      it "should ALLOW http: URLs with warning" do
        let result = validateURL "http://example.com/image.png" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskWarning
        case result.warning of
          Just warn -> warn `StringAssert.shouldContain` "Unencrypted"
          Nothing -> fail "Expected warning about unencrypted connection"

      it "should ALLOW blob: URLs" do
        let result = validateURL "blob:https://example.com/abc-123" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should ALLOW relative URLs starting with /" do
        let result = validateURL "/images/photo.png" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe
        result.protocol `shouldEqual` "relative"

      it "should ALLOW relative URLs starting with ./" do
        let result = validateURL "./assets/image.png" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

      it "should ALLOW relative URLs starting with ../" do
        let result = validateURL "../images/photo.png" CtxAsset
        result.valid `shouldEqual` true
        result.riskLevel `shouldEqual` RiskSafe

    ---------------------------------------------------------------------------
    -- validateURL - Edge Cases
    ---------------------------------------------------------------------------
    describe "validateURL - Edge Cases" do
      it "should BLOCK empty string and whitespace" do
        (validateURL "" CtxAsset).valid `shouldEqual` false
        (validateURL "   " CtxAsset).valid `shouldEqual` false

      it "should BLOCK empty string" do
        (validateURL "" CtxAsset).valid `shouldEqual` false
        (validateURL "   " CtxAsset).valid `shouldEqual` false

      it "should BLOCK extremely long URLs (DoS prevention)" do
        -- Build a URL exceeding maxURLLength (2MB = 2_000_000 chars)
        -- Construct by repeated concatenation: 10^6 then triple it
        let a1 = "aaaaaaaaaa" -- 10 chars
        let a2 = a1 <> a1 <> a1 <> a1 <> a1 <> a1 <> a1 <> a1 <> a1 <> a1 -- 100
        let a3 = a2 <> a2 <> a2 <> a2 <> a2 <> a2 <> a2 <> a2 <> a2 <> a2 -- 1_000
        let a4 = a3 <> a3 <> a3 <> a3 <> a3 <> a3 <> a3 <> a3 <> a3 <> a3 -- 10_000
        let a5 = a4 <> a4 <> a4 <> a4 <> a4 <> a4 <> a4 <> a4 <> a4 <> a4 -- 100_000
        let a6 = a5 <> a5 <> a5 <> a5 <> a5 <> a5 <> a5 <> a5 <> a5 <> a5 -- 1_000_000
        let longUrl = "https://example.com/" <> a6 <> a6 <> a6 -- ~3_000_020
        (validateURL longUrl CtxAsset).valid `shouldEqual` false

      it "should BLOCK unknown protocols" do
        let result = validateURL "custom://something" CtxAsset
        result.valid `shouldEqual` false
        case result.error of
          Just err -> err `StringAssert.shouldContain` "Unknown protocol"
          Nothing -> fail "Expected error about unknown protocol"

      it "should handle case-insensitive protocol check" do
        (validateURL "JAVASCRIPT:alert(1)" CtxAsset).valid `shouldEqual` false
        (validateURL "JavaScript:alert(1)" CtxAsset).valid `shouldEqual` false
        (validateURL "HTTPS://example.com" CtxAsset).valid `shouldEqual` true

    ---------------------------------------------------------------------------
    -- sanitizeURLForHTML
    ---------------------------------------------------------------------------
    describe "sanitizeURLForHTML" do
      it "should return Left for blocked URLs" do
        let result = sanitizeURLForHTML "javascript:alert(1)"
        isLeft result `shouldEqual` true

      it "should escape HTML special characters" do
        let result = sanitizeURLForHTML "https://example.com?foo=<bar>&x=\"test\""
        case result of
          Left err -> fail ("Expected Right but got Left: " <> err)
          Right sanitized -> do
            sanitized `StringAssert.shouldNotContain` "<"
            sanitized `StringAssert.shouldNotContain` ">"
            sanitized `StringAssert.shouldNotContain` "\""
            sanitized `StringAssert.shouldContain` "&lt;"
            sanitized `StringAssert.shouldContain` "&gt;"
            sanitized `StringAssert.shouldContain` "&quot;"

    ---------------------------------------------------------------------------
    -- validateURLs - Batch Validation
    ---------------------------------------------------------------------------
    describe "validateURLs - Batch Validation" do
      it "should validate multiple URLs and return map" do
        let urls =
              [ "https://safe.com/image.png"
              , "javascript:alert(1)"
              , "data:image/png;base64,ABC"
              ]
        let results = validateURLs urls
        -- Check https URL is valid
        case Map.lookup "https://safe.com/image.png" results of
          Just r -> r.valid `shouldEqual` true
          Nothing -> fail "Expected result for https://safe.com/image.png"
        -- Check javascript URL is blocked
        case Map.lookup "javascript:alert(1)" results of
          Just r -> r.valid `shouldEqual` false
          Nothing -> fail "Expected result for javascript:alert(1)"
        -- Check data:image/png is allowed
        case Map.lookup "data:image/png;base64,ABC" results of
          Just r -> r.valid `shouldEqual` true
          Nothing -> fail "Expected result for data:image/png;base64,ABC"

    ---------------------------------------------------------------------------
    -- isTrustedDomain
    ---------------------------------------------------------------------------
    describe "isTrustedDomain" do
      let trustedDomains = ["example.com", "cdn.trusted.org"]

      it "should match exact domain" do
        isTrustedDomain "https://example.com/path" trustedDomains
          `shouldEqual` true

      it "should match subdomain" do
        isTrustedDomain "https://api.example.com/path" trustedDomains
          `shouldEqual` true
        isTrustedDomain "https://static.cdn.trusted.org/file" trustedDomains
          `shouldEqual` true

      it "should NOT match partial domain name" do
        isTrustedDomain "https://fakeexample.com/path" trustedDomains
          `shouldEqual` false

      it "should return false for invalid URLs" do
        isTrustedDomain "not-a-url" trustedDomains
          `shouldEqual` false

    ---------------------------------------------------------------------------
    -- extractAndValidateURLs
    ---------------------------------------------------------------------------
    describe "extractAndValidateURLs" do
      it "should extract and validate URLs from text" do
        let text = "Check out https://safe.com/image.png and also http://another.com/video.mp4 Also here is data:image/png;base64,ABC"
        let results = extractAndValidateURLs text
        -- Extracts https, http, and data URLs
        Array.length results `shouldEqual` 3
        case results of
          [r0, r1, r2] -> do
            r0.valid `shouldEqual` true   -- https
            r1.valid `shouldEqual` true   -- http (with warning)
            r2.valid `shouldEqual` true   -- data:image/png is safe
          _ -> fail ("Expected 3 results, got " <> show (Array.length results))

      it "should identify dangerous data URLs when extracted" do
        let text = "data:text/html,<script>alert(1)</script>"
        let results = extractAndValidateURLs text
        Array.length results `shouldEqual` 1
        case results of
          [r0] -> do
            r0.valid `shouldEqual` false
            r0.riskLevel `shouldEqual` RiskBlocked
          _ -> fail ("Expected 1 result, got " <> show (Array.length results))
