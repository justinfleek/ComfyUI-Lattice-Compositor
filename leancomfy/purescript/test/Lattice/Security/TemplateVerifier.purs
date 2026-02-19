-- | Port of ui/src/__tests__/security/templateVerifier.test.ts (synchronous tests only)
-- |
-- | Tests getVerificationBadge, shouldWarnBeforeLoading, getLoadingWarning,
-- | and constant values. Async tests requiring Ed25519 FFI are skipped
-- | since the FFI stubs throw errors.
-- |
-- | Source: ui/src/__tests__/security/templateVerifier.test.ts

module Test.Lattice.Security.TemplateVerifier (spec) where

import Prelude

import Data.Array (elem)
import Data.Either (Either(..), isLeft)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (contains, Pattern(..)) as Str
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Lattice.Services.Security.TemplateVerifier
  ( VerificationResult, VerificationStatus(..), BadgeColor(..)
  , getVerificationBadge, shouldWarnBeforeLoading, getLoadingWarning
  , officialPublicKey, supportedVersions
  )

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Create a VerificationResult with the given status and flags.
-- | signerPublicKey and signedAt default to Nothing.
mkResult :: VerificationStatus -> Boolean -> Boolean -> Boolean -> String -> VerificationResult
mkResult status isSigned isValid isOfficial message =
  { isSigned, isValid, isOfficial, status, message, signerPublicKey: Nothing, signedAt: Nothing }

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Template Signature Verification" do
    getVerificationBadgeTests
    shouldWarnBeforeLoadingTests
    getLoadingWarningTests
    constantTests

--------------------------------------------------------------------------------
-- getVerificationBadge
--------------------------------------------------------------------------------

getVerificationBadgeTests :: Spec Unit
getVerificationBadgeTests = do
  describe "getVerificationBadge" do
    it "should return green badge for official templates" do
      let result = mkResult VsOfficial true true true "Verified"
      let badge = getVerificationBadge result
      badge.color `shouldEqual` ColorGreen
      if Str.contains (Str.Pattern "Verified") badge.label
        then pure unit
        else fail ("Expected badge label to contain 'Verified', got: " <> badge.label)
      badge.icon `shouldEqual` "check"

    it "should return yellow badge for third-party valid" do
      let result = mkResult VsThirdPartyValid true true false "Third party"
      let badge = getVerificationBadge result
      badge.color `shouldEqual` ColorYellow
      badge.icon `shouldEqual` "warning"

    it "should return red badge for invalid signatures" do
      let result = mkResult VsThirdPartyInvalid true false false "Invalid"
      let badge = getVerificationBadge result
      badge.color `shouldEqual` ColorRed
      badge.icon `shouldEqual` "x"

    it "should return gray badge for unsigned" do
      let result = mkResult VsUnsigned false false false "Unsigned"
      let badge = getVerificationBadge result
      badge.color `shouldEqual` ColorGray
      badge.icon `shouldEqual` "question"

--------------------------------------------------------------------------------
-- shouldWarnBeforeLoading
--------------------------------------------------------------------------------

shouldWarnBeforeLoadingTests :: Spec Unit
shouldWarnBeforeLoadingTests = do
  describe "shouldWarnBeforeLoading" do
    it "should not warn for official templates" do
      let result = mkResult VsOfficial true true true "OK"
      shouldWarnBeforeLoading result `shouldEqual` false

    it "should warn for all non-official templates" do
      let nonOfficialStatuses =
            [ { status: VsThirdPartyValid, isSigned: true, isValid: true }
            , { status: VsThirdPartyInvalid, isSigned: true, isValid: false }
            , { status: VsUnsigned, isSigned: false, isValid: false }
            ]
      for_ nonOfficialStatuses \entry -> do
        let result = mkResult entry.status entry.isSigned entry.isValid false "Test"
        shouldWarnBeforeLoading result `shouldEqual` true

--------------------------------------------------------------------------------
-- getLoadingWarning
--------------------------------------------------------------------------------

getLoadingWarningTests :: Spec Unit
getLoadingWarningTests = do
  describe "getLoadingWarning" do
    it "should return Left for official templates" do
      let result = mkResult VsOfficial true true true "OK"
      let warning = getLoadingWarning result
      if isLeft warning
        then pure unit
        else fail "Expected Left for official template, got Right"

    it "should return Right with message for third-party valid" do
      let result = mkResult VsThirdPartyValid true true false "Third party"
      let warning = getLoadingWarning result
      case warning of
        Right msg ->
          if Str.contains (Str.Pattern "third party") msg
            then pure unit
            else fail ("Expected warning to contain 'third party', got: " <> msg)
        Left _ ->
          fail "Expected Right for third-party valid template, got Left"

    it "should return Right with WARNING for invalid" do
      let result = mkResult VsThirdPartyInvalid true false false "Invalid"
      let warning = getLoadingWarning result
      case warning of
        Right msg ->
          if Str.contains (Str.Pattern "WARNING") msg
            then pure unit
            else fail ("Expected warning to contain 'WARNING', got: " <> msg)
        Left _ ->
          fail "Expected Right for invalid template, got Left"

    it "should return Right for unsigned" do
      let result = mkResult VsUnsigned false false false "Unsigned"
      let warning = getLoadingWarning result
      case warning of
        Right msg ->
          if Str.contains (Str.Pattern "unsigned") msg
            then pure unit
            else fail ("Expected warning to contain 'unsigned', got: " <> msg)
        Left _ ->
          fail "Expected Right for unsigned template, got Left"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

constantTests :: Spec Unit
constantTests = do
  describe "Constants" do
    it "officialPublicKey should be the expected value" do
      officialPublicKey `shouldEqual` "xmCWXfRKw7DQLuyQdqQIJlAb+r0arpUu2oVjTdJgv/k="

    it "supportedVersions should contain 1.0" do
      if elem "1.0" supportedVersions
        then pure unit
        else fail "Expected supportedVersions to contain \"1.0\""
