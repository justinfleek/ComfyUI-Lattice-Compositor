-- |
-- Module      : Lattice.State.ToastSpec
-- Description : Test suite for toast state management
--

module Lattice.State.ToastSpec (spec) where

import Data.Text (Text)
import Lattice.State.Toast
  ( createToast
  , getToasts
  , findToastById
  , filterToastsByType
  , ToastType(..)
  , Toast(..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ============================================================================
-- TEST HELPERS
-- ============================================================================

createTestToast :: Text -> ToastType -> Toast
createTestToast id_ type_ = createToast id_ "Test message" type_ 3000.0

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Toast"
    [ testGroup
        "createToast"
        [ testCase "createToast - creates success toast" $ do
            let toast = createToast "toast1" "Success!" ToastTypeSuccess 3000.0
            assertEqual "Should have correct ID" "toast1" (toastId toast)
            assertEqual "Should have correct message" "Success!" (toastMessage toast)
            assertEqual "Should have correct type" ToastTypeSuccess (toastType toast)
            assertEqual "Should have correct duration" 3000.0 (toastDuration toast)
        , testCase "createToast - creates error toast" $ do
            let toast = createToast "toast2" "Error!" ToastTypeError 5000.0
            assertEqual "Should have correct type" ToastTypeError (toastType toast)
            assertEqual "Should have correct duration" 5000.0 (toastDuration toast)
        , testCase "createToast - creates warning toast" $ do
            let toast = createToast "toast3" "Warning!" ToastTypeWarning 4000.0
            assertEqual "Should have correct type" ToastTypeWarning (toastType toast)
        , testCase "createToast - creates info toast" $ do
            let toast = createToast "toast4" "Info!" ToastTypeInfo 3000.0
            assertEqual "Should have correct type" ToastTypeInfo (toastType toast)
        ]
    , testGroup
        "getToasts"
        [ testCase "getToasts - returns empty list" $ do
            let result = getToasts []
            assertEqual "Should return empty list" [] result
        , testCase "getToasts - returns all toasts" $ do
            let toast1 = createTestToast "toast1" ToastTypeSuccess
            let toast2 = createTestToast "toast2" ToastTypeError
            let toasts = [toast1, toast2]
            let result = getToasts toasts
            assertEqual "Should return all toasts" 2 (length result)
        ]
    , testGroup
        "findToastById"
        [ testCase "findToastById - returns Nothing for non-existent ID" $ do
            let toast1 = createTestToast "toast1" ToastTypeSuccess
            let toasts = [toast1]
            let result = findToastById "nonexistent" toasts
            assertBool "Should return Nothing" (result == Nothing)
        , testCase "findToastById - returns toast when exists" $ do
            let toast1 = createTestToast "toast1" ToastTypeSuccess
            let toast2 = createTestToast "toast2" ToastTypeError
            let toasts = [toast1, toast2]
            let result = findToastById "toast1" toasts
            assertBool "Should return toast" (result == Just toast1)
        , testCase "findToastById - returns correct toast from multiple" $ do
            let toast1 = createTestToast "toast1" ToastTypeSuccess
            let toast2 = createTestToast "toast2" ToastTypeError
            let toast3 = createTestToast "toast3" ToastTypeWarning
            let toasts = [toast1, toast2, toast3]
            let result = findToastById "toast2" toasts
            assertBool "Should return correct toast" (result == Just toast2)
        ]
    , testGroup
        "filterToastsByType"
        [ testCase "filterToastsByType - returns empty list for non-existent type" $ do
            let toast1 = createTestToast "toast1" ToastTypeSuccess
            let toast2 = createTestToast "toast2" ToastTypeSuccess
            let toasts = [toast1, toast2]
            let result = filterToastsByType ToastTypeError toasts
            assertEqual "Should return empty list" [] result
        , testCase "filterToastsByType - filters by success type" $ do
            let toast1 = createTestToast "toast1" ToastTypeSuccess
            let toast2 = createTestToast "toast2" ToastTypeError
            let toast3 = createTestToast "toast3" ToastTypeSuccess
            let toasts = [toast1, toast2, toast3]
            let result = filterToastsByType ToastTypeSuccess toasts
            assertEqual "Should return 2 success toasts" 2 (length result)
            case result of
              [] -> assertBool "Should not be empty" False
              (firstToast : _) -> assertBool "Should contain toast1 or toast3" (toastId firstToast == "toast1" || toastId firstToast == "toast3")
        , testCase "filterToastsByType - filters by error type" $ do
            let toast1 = createTestToast "toast1" ToastTypeSuccess
            let toast2 = createTestToast "toast2" ToastTypeError
            let toast3 = createTestToast "toast3" ToastTypeWarning
            let toasts = [toast1, toast2, toast3]
            let result = filterToastsByType ToastTypeError toasts
            assertEqual "Should return 1 error toast" 1 (length result)
            case result of
              [] -> assertBool "Should not be empty" False
              (toast : _) -> assertEqual "Should be toast2" "toast2" (toastId toast)
        , testCase "filterToastsByType - filters by warning type" $ do
            let toast1 = createTestToast "toast1" ToastTypeWarning
            let toast2 = createTestToast "toast2" ToastTypeInfo
            let toast3 = createTestToast "toast3" ToastTypeWarning
            let toasts = [toast1, toast2, toast3]
            let result = filterToastsByType ToastTypeWarning toasts
            assertEqual "Should return 2 warning toasts" 2 (length result)
        , testCase "filterToastsByType - filters by info type" $ do
            let toast1 = createTestToast "toast1" ToastTypeInfo
            let toast2 = createTestToast "toast2" ToastTypeInfo
            let toast3 = createTestToast "toast3" ToastTypeSuccess
            let toasts = [toast1, toast2, toast3]
            let result = filterToastsByType ToastTypeInfo toasts
            assertEqual "Should return 2 info toasts" 2 (length result)
        ]
    ]
