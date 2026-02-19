-- |
-- Module      : Lattice.State.ExpressionSpec
-- Description : Test suite for expression state management
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.ExpressionSpec (spec) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Expression
  ( getDriversForLayer
  , getDriversForProperty
  , checkCircularDependency
  , PropertyDriver(..)
  , AudioFeatureType(..)
  )
import Lattice.Services.PropertyDriver
  ( DriverSourceType(..)
  , DriverTransform(..)
  , BlendMode(..)
  )
import Lattice.Utils.Defaults (defaultText, defaultDouble, defaultBool)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual, assertBool)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // test // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a test property driver with minimal required fields
-- All values have explicit defaults - no Maybe/Nothing
createTestDriver ::
  Text ->  -- ID
  Text ->  -- Name
  Text ->  -- Target layer ID
  Text ->  -- Target property
  Bool ->  -- Enabled
  PropertyDriver
createTestDriver id_ name targetLayerId targetProperty enabled =
  PropertyDriver
    { propertyDriverId = id_
    , propertyDriverName = name
    , propertyDriverEnabled = enabled
    , propertyDriverTargetLayerId = targetLayerId
    , propertyDriverTargetProperty = targetProperty
    , propertyDriverSourceType = SourceProperty
    , propertyDriverSourceLayerId = defaultText
    , propertyDriverSourceLayerIdSet = False
    , propertyDriverSourceProperty = defaultText
    , propertyDriverSourcePropertySet = False
    , propertyDriverAudioFeature = AudioAmplitude
    , propertyDriverAudioFeatureSet = False
    , propertyDriverAudioThreshold = defaultDouble
    , propertyDriverAudioThresholdSet = False
    , propertyDriverAudioAboveThreshold = defaultBool
    , propertyDriverAudioAboveThresholdSet = False
    , propertyDriverTransforms = []
    , propertyDriverBlendMode = BlendAdd
    , propertyDriverBlendAmount = 1.0
    }

-- | Create a property-to-property driver
-- All values have explicit defaults - no Maybe/Nothing
createPropertyDriver ::
  Text ->  -- ID
  Text ->  -- Target layer ID
  Text ->  -- Target property
  Text ->  -- Source layer ID
  Text ->  -- Source property
  PropertyDriver
createPropertyDriver id_ targetLayerId targetProperty sourceLayerId sourceProperty =
  PropertyDriver
    { propertyDriverId = id_
    , propertyDriverName = "Property Link"
    , propertyDriverEnabled = True
    , propertyDriverTargetLayerId = targetLayerId
    , propertyDriverTargetProperty = targetProperty
    , propertyDriverSourceType = SourceProperty
    , propertyDriverSourceLayerId = sourceLayerId
    , propertyDriverSourceLayerIdSet = True
    , propertyDriverSourceProperty = sourceProperty
    , propertyDriverSourcePropertySet = True
    , propertyDriverAudioFeature = AudioAmplitude
    , propertyDriverAudioFeatureSet = False
    , propertyDriverAudioThreshold = defaultDouble
    , propertyDriverAudioThresholdSet = False
    , propertyDriverAudioAboveThreshold = defaultBool
    , propertyDriverAudioAboveThresholdSet = False
    , propertyDriverTransforms = []
    , propertyDriverBlendMode = BlendAdd
    , propertyDriverBlendAmount = 1.0
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Expression"
    [ testGroup
        "getDriversForLayer"
        [ testCase "getDriversForLayer - filters drivers by layer ID" $ do
            let driver1 = createTestDriver "d1" "Driver 1" "layer1" "transform.position.x" True
            let driver2 = createTestDriver "d2" "Driver 2" "layer2" "transform.position.y" True
            let driver3 = createTestDriver "d3" "Driver 3" "layer1" "transform.rotation" False
            let drivers = [driver1, driver2, driver3]
            let result = getDriversForLayer "layer1" drivers
            assertEqual "Should return 2 drivers" 2 (length result)
        , testCase "getDriversForLayer - returns empty list when no matches" $ do
            let driver1 = createTestDriver "d1" "Driver 1" "layer1" "transform.position.x" True
            let drivers = [driver1]
            let result = getDriversForLayer "nonexistent" drivers
            assertEqual "Should return empty list" [] result
        , testCase "getDriversForLayer - handles empty drivers list" $ do
            let result = getDriversForLayer "layer1" []
            assertEqual "Should return empty list" [] result
        ]
    , testGroup
        "getDriversForProperty"
        [ testCase "getDriversForProperty - filters by layer ID and property path" $ do
            let driver1 = createTestDriver "d1" "Driver 1" "layer1" "transform.position.x" True
            let driver2 = createTestDriver "d2" "Driver 2" "layer1" "transform.position.y" True
            let driver3 = createTestDriver "d3" "Driver 3" "layer1" "transform.position.x" False  -- Disabled
            let drivers = [driver1, driver2, driver3]
            let result = getDriversForProperty "layer1" "transform.position.x" drivers
            assertEqual "Should return 1 enabled driver" 1 (length result)
            assertEqual "Should return driver1" "d1" (propertyDriverId (head result))
        , testCase "getDriversForProperty - returns empty when no enabled drivers" $ do
            let driver1 = createTestDriver "d1" "Driver 1" "layer1" "transform.position.x" False
            let drivers = [driver1]
            let result = getDriversForProperty "layer1" "transform.position.x" drivers
            assertEqual "Should return empty list" [] result
        ]
    , testGroup
        "checkCircularDependency"
        [ testCase "checkCircularDependency - detects direct cycle" $ do
            -- Driver: layer1.position.x -> layer1.position.x (direct cycle)
            let newDriver = createPropertyDriver "d1" "layer1" "transform.position.x" "layer1" "transform.position.x"
            let existing = []
            let result = checkCircularDependency newDriver existing
            assertBool "Should detect direct cycle" result
        , testCase "checkCircularDependency - detects indirect cycle" $ do
            -- Existing: layer1.position.x -> layer2.position.y
            -- New: layer2.position.y -> layer1.position.x (creates cycle)
            let existingDriver = createPropertyDriver "d1" "layer1" "transform.position.x" "layer2" "transform.position.y"
            let newDriver = createPropertyDriver "d2" "layer2" "transform.position.y" "layer1" "transform.position.x"
            let existing = [existingDriver]
            let result = checkCircularDependency newDriver existing
            assertBool "Should detect indirect cycle" result
        , testCase "checkCircularDependency - no cycle for non-property source" $ do
            -- Audio source cannot create cycles
            let newDriver = (createTestDriver "d1" "Driver 1" "layer1" "transform.position.x" True)
              { propertyDriverSourceType = SourceAudio
              , propertyDriverAudioFeature = AudioAmplitude
              , propertyDriverAudioFeatureSet = True
              }
            let existing = []
            let result = checkCircularDependency newDriver existing
            assertBool "Should not detect cycle for audio source" (not result)
        , testCase "checkCircularDependency - no cycle for valid chain" $ do
            -- Existing: layer1.position.x -> layer2.position.y
            -- New: layer3.position.z -> layer1.position.x (no cycle)
            let existingDriver = createPropertyDriver "d1" "layer1" "transform.position.x" "layer2" "transform.position.y"
            let newDriver = createPropertyDriver "d2" "layer3" "transform.position.z" "layer1" "transform.position.x"
            let existing = [existingDriver]
            let result = checkCircularDependency newDriver existing
            assertBool "Should not detect cycle for valid chain" (not result)
        , testCase "checkCircularDependency - no cycle when source incomplete" $ do
            -- Driver with missing source cannot create cycle
            let newDriver = (createTestDriver "d1" "Driver 1" "layer1" "transform.position.x" True)
              { propertyDriverSourceLayerIdSet = False
              , propertyDriverSourcePropertySet = False
              }
            let existing = []
            let result = checkCircularDependency newDriver existing
            assertBool "Should not detect cycle when source incomplete" (not result)
        ]
    ]
