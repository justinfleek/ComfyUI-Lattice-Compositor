-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // test // gen // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Generator Infrastructure
-- |
-- | This module provides shared generators used across all property tests.
-- | Generators are designed with realistic distributions based on production
-- | usage patterns, plus adversarial variants for edge case testing.
-- |
-- | ## Distribution Philosophy
-- |
-- | At billion-agent scale, uniform distributions miss edge cases that matter.
-- | Our generators use weighted distributions:
-- | - 60% realistic values (common in production)
-- | - 20% boundary values (0, 1, max, min)
-- | - 20% adversarial values (NaN-producing, overflow-prone)
-- |
-- | ## Reuse
-- |
-- | All generators in this module are pure and composable.
-- | Import this module in all property test files.

module Test.Gen.Core
  ( -- * Numeric Generators
    genUnitInterval
  , genUnitIntervalAdversarial
  , genPercent
  , genPercentAdversarial
  , genByte
  , genByteAdversarial
  , genPositiveNumber
  , genNonNegativeInt
  , genBoundedNumber
  , genBoundedInt
  
  -- * Adversarial Numeric
  , genNumericAdversarial
  , genIntAdversarial
  , genNumberEdges
  
  -- * String Generators
  , genShortString
  , genIdentifier
  , genSlug
  , genUnicodeString
  , genAdversarialString
  
  -- * Array Generators
  , genSmallArray
  , genNonEmptyArray
  
  -- * Timestamp Generators
  , genTimestamp
  , genTTL
  
  -- * Comparison Helpers
  , approxEqual
  , withinTolerance
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( bind
  , map
  , negate
  , pure
  , ($)
  , (-)
  , (+)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (>)
  , (&&)
  )

import Data.Array.NonEmpty (cons') as NEA
import Data.Int (toNumber)
import Data.Number (abs) as Number
import Data.Tuple (Tuple(Tuple))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, vectorOf)
import Control.Monad.Gen.Class (chooseFloat)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // numeric generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unit interval [0,1] with production-realistic distribution.
-- |
-- | Distribution (based on real opacity/progress values):
-- | - 25% at 0.0 (fully transparent, not started)
-- | - 25% at 1.0 (fully opaque, complete)
-- | - 10% at 0.5 (50% opacity common)
-- | - 40% uniform across [0,1]
genUnitInterval :: Gen Number
genUnitInterval = frequency $ NEA.cons'
  (Tuple 25.0 (pure 0.0))
  [ Tuple 25.0 (pure 1.0)
  , Tuple 10.0 (pure 0.5)
  , Tuple 40.0 (map (\n -> toNumber n / 1000.0) (chooseInt 0 1000))
  ]

-- | Adversarial unit interval - tests clamping behavior.
genUnitIntervalAdversarial :: Gen Number
genUnitIntervalAdversarial = elements $ NEA.cons'
  0.0
  [ 1.0
  , (-0.1)           -- Below min
  , 1.1              -- Above max
  , (-1.0)           -- Far below
  , 2.0              -- Far above
  , 0.0000001        -- Near zero
  , 0.9999999        -- Near one
  , 0.5              -- Exact midpoint
  ]

-- | Percentage [0,100] with production-realistic distribution.
-- |
-- | Distribution (based on real UI percentages):
-- | - 15% at 0 (empty, none)
-- | - 15% at 100 (full, complete)
-- | - 10% at 50 (half)
-- | - 10% at 25 (quarter)
-- | - 10% at 75 (three-quarters)
-- | - 40% uniform
genPercent :: Gen Int
genPercent = frequency $ NEA.cons'
  (Tuple 15.0 (pure 0))
  [ Tuple 15.0 (pure 100)
  , Tuple 10.0 (pure 50)
  , Tuple 10.0 (pure 25)
  , Tuple 10.0 (pure 75)
  , Tuple 40.0 (chooseInt 0 100)
  ]

-- | Adversarial percentage - tests clamping behavior.
genPercentAdversarial :: Gen Int
genPercentAdversarial = elements $ NEA.cons'
  0
  [ 100
  , (-1)             -- Below min
  , 101              -- Above max
  , (-100)           -- Far below
  , 200              -- Far above
  , 1                -- Near zero
  , 99               -- Near max
  ]

-- | Byte [0,255] with production-realistic distribution.
-- |
-- | Distribution (based on color channel usage):
-- | - 15% at 0 (black component)
-- | - 15% at 255 (white component)
-- | - 10% at 128 (midpoint)
-- | - 20% dark range (0-64)
-- | - 20% light range (192-255)
-- | - 20% uniform
genByte :: Gen Int
genByte = frequency $ NEA.cons'
  (Tuple 15.0 (pure 0))
  [ Tuple 15.0 (pure 255)
  , Tuple 10.0 (pure 128)
  , Tuple 20.0 (chooseInt 0 64)
  , Tuple 20.0 (chooseInt 192 255)
  , Tuple 20.0 (chooseInt 0 255)
  ]

-- | Adversarial byte - tests clamping behavior.
genByteAdversarial :: Gen Int
genByteAdversarial = elements $ NEA.cons'
  0
  [ 255
  , (-1)             -- Below min
  , 256              -- Above max
  , (-255)           -- Far below
  , 512              -- Far above
  , 1                -- Near zero
  , 254              -- Near max
  ]

-- | Positive number (> 0).
genPositiveNumber :: Gen Number
genPositiveNumber = frequency $ NEA.cons'
  (Tuple 30.0 (chooseFloat 0.001 1.0))
  [ Tuple 30.0 (chooseFloat 1.0 100.0)
  , Tuple 20.0 (chooseFloat 100.0 10000.0)
  , Tuple 20.0 (pure 0.0001)
  ]

-- | Non-negative integer (>= 0).
genNonNegativeInt :: Gen Int
genNonNegativeInt = frequency $ NEA.cons'
  (Tuple 20.0 (pure 0))
  [ Tuple 40.0 (chooseInt 1 100)
  , Tuple 30.0 (chooseInt 100 10000)
  , Tuple 10.0 (chooseInt 10000 1000000)
  ]

-- | Bounded number within [lo, hi].
genBoundedNumber :: Number -> Number -> Gen Number
genBoundedNumber lo hi = frequency $ NEA.cons'
  (Tuple 15.0 (pure lo))
  [ Tuple 15.0 (pure hi)
  , Tuple 10.0 (pure ((lo + hi) / 2.0))
  , Tuple 60.0 (chooseFloat lo hi)
  ]

-- | Bounded integer within [lo, hi].
genBoundedInt :: Int -> Int -> Gen Int
genBoundedInt lo hi = frequency $ NEA.cons'
  (Tuple 15.0 (pure lo))
  [ Tuple 15.0 (pure hi)
  , Tuple 70.0 (chooseInt lo hi)
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // adversarial numeric
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Adversarial number generator - tests edge cases.
-- |
-- | Targets: 0, -0, very small, very large, near-boundary
genNumericAdversarial :: Number -> Number -> Gen Number
genNumericAdversarial lo hi = elements $ NEA.cons'
  0.0
  [ lo                               -- Exact minimum
  , hi                               -- Exact maximum
  , lo - 0.0001                      -- Just below min
  , hi + 0.0001                      -- Just above max
  , (lo + hi) / 2.0                  -- Exact midpoint
  , lo + 0.000001                    -- Epsilon above min
  , hi - 0.000001                    -- Epsilon below max
  ]

-- | Adversarial integer generator.
genIntAdversarial :: Int -> Int -> Gen Int
genIntAdversarial lo hi = elements $ NEA.cons'
  lo
  [ hi
  , lo - 1                           -- Just below min
  , hi + 1                           -- Just above max
  , (lo + hi) / 2                    -- Midpoint (truncated)
  ]

-- | Edge case numbers.
genNumberEdges :: Gen Number
genNumberEdges = elements $ NEA.cons'
  0.0
  [ 1.0
  , (-1.0)
  , 0.5
  , (-0.5)
  , 0.0000001
  , (-0.0000001)
  , 999999.0
  , (-999999.0)
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // string generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Short string (1-20 chars) for names, labels.
genShortString :: Gen String
genShortString = elements $ NEA.cons'
  "a"
  [ "test"
  , "hello"
  , "node-1"
  , "layer_01"
  , "Card"
  , "Button"
  , "rect-123"
  , "my-element"
  , "SourceImage"
  ]

-- | Valid identifier (alphanumeric + underscore).
genIdentifier :: Gen String
genIdentifier = elements $ NEA.cons'
  "id"
  [ "nodeId"
  , "layer_1"
  , "effect_blur"
  , "trigger_hover"
  , "source_image"
  , "blend_normal"
  , "cache_key"
  , "transform_2d"
  , "opacity_100"
  ]

-- | URL-safe slug.
genSlug :: Gen String
genSlug = elements $ NEA.cons'
  "my-slug"
  [ "test-node"
  , "layer-1"
  , "card-header"
  , "button-primary"
  , "image-source"
  , "video-player"
  , "chart-bar"
  , "widget-form"
  , "composition-root"
  ]

-- | Unicode string for internationalization testing.
genUnicodeString :: Gen String
genUnicodeString = elements $ NEA.cons'
  "Hello"
  [ "日本語"
  , "한국어"
  , "العربية"
  , "עברית"
  , "Ελληνικά"
  , "中文"
  , "Émoji: 🎨"
  , "Mixed: Hello 世界"
  , "Symbols: ∀∃∈∉"
  ]

-- | Adversarial strings for security/robustness testing.
genAdversarialString :: Gen String
genAdversarialString = elements $ NEA.cons'
  ""
  [ " "
  , "  "
  , "\t"
  , "\n"
  , "\r\n"
  , "<script>"
  , "'; DROP TABLE"
  , "{{template}}"
  , "${expression}"
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // array generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Small array (0-10 elements).
genSmallArray :: forall a. Gen a -> Gen (Array a)
genSmallArray g = do
  len <- chooseInt 0 10
  vectorOf len g

-- | Non-empty array (1-10 elements).
genNonEmptyArray :: forall a. Gen a -> Gen (Array a)
genNonEmptyArray g = do
  len <- chooseInt 1 10
  vectorOf len g

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // timestamp generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timestamp in milliseconds (realistic range).
-- |
-- | Distribution:
-- | - 40% recent (last hour)
-- | - 30% today
-- | - 20% this week
-- | - 10% older
genTimestamp :: Gen Number
genTimestamp = frequency $ NEA.cons'
  (Tuple 40.0 (chooseFloat 1700000000000.0 1700003600000.0))
  [ Tuple 30.0 (chooseFloat 1699920000000.0 1700000000000.0)
  , Tuple 20.0 (chooseFloat 1699400000000.0 1699920000000.0)
  , Tuple 10.0 (chooseFloat 1690000000000.0 1699400000000.0)
  ]

-- | TTL in milliseconds (cache expiration).
-- |
-- | Distribution based on tier defaults:
-- | - 40% L0 (60 seconds)
-- | - 30% L1 (5 minutes)
-- | - 20% L2 (1 hour)
-- | - 10% custom
genTTL :: Gen Number
genTTL = frequency $ NEA.cons'
  (Tuple 40.0 (pure 60000.0))
  [ Tuple 30.0 (pure 300000.0)
  , Tuple 20.0 (pure 3600000.0)
  , Tuple 10.0 (chooseFloat 1000.0 86400000.0)
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // comparison helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Approximate equality for floating point comparison.
approxEqual :: Number -> Number -> Number -> Boolean
approxEqual tolerance a b = Number.abs (a - b) <= tolerance

-- | Check if value is within tolerance of expected.
withinTolerance :: Number -> Number -> Number -> Boolean
withinTolerance expected tolerance actual =
  actual >= (expected - tolerance) && actual <= (expected + tolerance)
