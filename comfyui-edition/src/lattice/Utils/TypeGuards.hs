-- |
-- Module      : Lattice.Utils.TypeGuards
-- Description : Runtime type guards for validating data structures
-- 
-- Migrated from ui/src/utils/typeGuards.ts
-- Pure predicate functions that check runtime types and narrow types
-- These are ACTUAL runtime checks, not type assertions
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module Lattice.Utils.TypeGuards
  ( -- Primitive type guards
    isObject
  , isFiniteNumber
  , isNonEmptyString
  , isArray
  , isFunction
  -- Geometry type guards
  , hasXY
  , hasXYZ
  , isBoundingBox
  -- Color type guards
  , isRGBColor
  , isRGBAColor
  -- Array type guards
  , isNumberArray
  , isVec2Array
  -- Transform type guards
  , hasPosition
  , hasScale
  , hasRotation
  -- Layer data type guards
  , hasAssetId
  , hasCompositionId
  , hasSource
  , hasDimensions
  , hasAssetIdProperty
  -- Utility predicates
  , hasProperty
  , isArrayOf
  ) where

import Data.Aeson (Value(..), Object)
import Data.Aeson.Key (Key, fromString, fromText)
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.Scientific (isFloating, toRealFloat)
-- isInfinite, isNaN from Prelude

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // primitive // type // guards
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if value is a non-null object
isObject :: Value -> Bool
isObject (Object _) = True
isObject _ = False

-- | Check if value is a finite number (not NaN, not Infinity)
isFiniteNumber :: Value -> Bool
isFiniteNumber (Number n) =
  if isFloating n
    then let d = toRealFloat n :: Double
         in not (isInfinite d || isNaN d)
    else True  -- Integer numbers are always finite
isFiniteNumber _ = False

-- | Check if value is a non-empty string
isNonEmptyString :: Value -> Bool
isNonEmptyString (String s) = not (T.null s)
isNonEmptyString _ = False

-- | Check if value is an array
isArray :: Value -> Bool
isArray (Array _) = True
isArray _ = False

-- | Check if value is a function
-- Note: In Haskell, functions are not representable in JSON Value
-- This always returns False for JSON values
isFunction :: Value -> Bool
isFunction _ = False

-- ════════════════════════════════════════════════════════════════════════════
--                                                // geometry // type // guards
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if value has numeric x and y properties
hasXY :: Value -> Bool
hasXY (Object obj) =
  case (KeyMap.lookup (fromString "x") obj, KeyMap.lookup (fromString "y") obj) of
    (Just (Number x), Just (Number y)) -> isFiniteNumber (Number x) && isFiniteNumber (Number y)
    _ -> False
hasXY _ = False

-- | Check if value has numeric x, y, and z properties
hasXYZ :: Value -> Bool
hasXYZ (Object obj) =
  case (KeyMap.lookup (fromString "x") obj, KeyMap.lookup (fromString "y") obj, KeyMap.lookup (fromString "z") obj) of
    (Just (Number x), Just (Number y), Just (Number z)) ->
      isFiniteNumber (Number x) && isFiniteNumber (Number y) && isFiniteNumber (Number z)
    _ -> False
hasXYZ _ = False

-- | Check if value is a valid bounding box
isBoundingBox :: Value -> Bool
isBoundingBox (Object obj) =
  case (KeyMap.lookup (fromString "x") obj, KeyMap.lookup (fromString "y") obj, KeyMap.lookup (fromString "width") obj, KeyMap.lookup (fromString "height") obj) of
    (Just (Number x), Just (Number y), Just (Number w), Just (Number h)) ->
      isFiniteNumber (Number x) && isFiniteNumber (Number y) && isFiniteNumber (Number w) && isFiniteNumber (Number h)
    _ -> False
isBoundingBox _ = False

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // color // type // guards
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if value is a valid RGB color
isRGBColor :: Value -> Bool
isRGBColor (Object obj) =
  case (KeyMap.lookup (fromString "r") obj, KeyMap.lookup (fromString "g") obj, KeyMap.lookup (fromString "b") obj) of
    (Just (Number r), Just (Number g), Just (Number b)) ->
      let rVal = toRealFloat r :: Double
          gVal = toRealFloat g :: Double
          bVal = toRealFloat b :: Double
      in isFiniteNumber (Number r) && isFiniteNumber (Number g) && isFiniteNumber (Number b) &&
         rVal >= 0 && rVal <= 255 &&
         gVal >= 0 && gVal <= 255 &&
         bVal >= 0 && bVal <= 255
    _ -> False
isRGBColor _ = False

-- | Check if value is a valid RGBA color
isRGBAColor :: Value -> Bool
isRGBAColor (Object obj) =
  case (KeyMap.lookup (fromString "a") obj, isRGBColor (Object obj)) of
    (Just (Number a), True) ->
      let aVal = toRealFloat a :: Double
      in isFiniteNumber (Number a) && aVal >= 0 && aVal <= 1
    _ -> False
isRGBAColor _ = False

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // array // type // guards
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if all elements of array satisfy a predicate
isArrayOf :: (Value -> Bool) -> Value -> Bool
isArrayOf itemGuard (Array vec) = V.all itemGuard vec
isArrayOf _ _ = False

-- | Check if value is an array of finite numbers
isNumberArray :: Value -> Bool
isNumberArray = isArrayOf isFiniteNumber

-- | Check if value is an array of Vec2
isVec2Array :: Value -> Bool
isVec2Array = isArrayOf hasXY

-- ════════════════════════════════════════════════════════════════════════════
--                                               // transform // type // guards
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if value has position property with x, y coordinates
hasPosition :: Value -> Bool
hasPosition (Object obj) =
  case KeyMap.lookup (fromString "position") obj of
    Just (Object posObj) ->
      case KeyMap.lookup (fromString "value") posObj of
        Just val -> hasXY val
        _ -> False
    _ -> False
hasPosition _ = False

-- | Check if value has scale property with x, y values
hasScale :: Value -> Bool
hasScale (Object obj) =
  case KeyMap.lookup (fromString "scale") obj of
    Just (Object scaleObj) ->
      case KeyMap.lookup (fromString "value") scaleObj of
        Just val -> hasXY val
        _ -> False
    _ -> False
hasScale _ = False

-- | Check if value has rotation property with numeric value
hasRotation :: Value -> Bool
hasRotation (Object obj) =
  case KeyMap.lookup (fromString "rotation") obj of
    Just (Object rotObj) ->
      case KeyMap.lookup (fromString "value") rotObj of
        Just (Number n) -> isFiniteNumber (Number n)
        _ -> False
    _ -> False
hasRotation _ = False

-- ════════════════════════════════════════════════════════════════════════════
--                                           // layer // data // type // guards
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if layer data has asset ID
hasAssetId :: Value -> Bool
hasAssetId (Object obj) =
  case KeyMap.lookup (fromString "assetId") obj of
    Just Null -> True
    Just (String s) -> not (T.null s)
    _ -> False
hasAssetId _ = False

-- | Check if layer data has composition ID (for nested comps)
hasCompositionId :: Value -> Bool
hasCompositionId (Object obj) =
  case KeyMap.lookup (fromString "compositionId") obj of
    Just (String s) -> not (T.null s)
    _ -> False
hasCompositionId _ = False

-- | Check if layer data has source URL/path
hasSource :: Value -> Bool
hasSource (Object obj) =
  case KeyMap.lookup (fromString "source") obj of
    Just (String s) -> not (T.null s)
    _ -> False
hasSource _ = False

-- | Check if layer data has width and height properties directly
-- (e.g., SolidLayerData)
hasDimensions :: Value -> Bool
hasDimensions (Object obj) =
  case (KeyMap.lookup (fromString "width") obj, KeyMap.lookup (fromString "height") obj) of
    (Just (Number w), Just (Number h)) ->
      let wVal = toRealFloat w :: Double
          hVal = toRealFloat h :: Double
      in isFiniteNumber (Number w) && isFiniteNumber (Number h) && wVal > 0 && hVal > 0
    _ -> False
hasDimensions _ = False

-- | Check if layer data has assetId property
-- (e.g., ImageLayerData, VideoData)
hasAssetIdProperty :: Value -> Bool
hasAssetIdProperty (Object obj) =
  case KeyMap.lookup (fromString "assetId") obj of
    Just Null -> True
    Just (String s) -> True
    _ -> False
hasAssetIdProperty _ = False

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // utility // predicates
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if object has a specific property that satisfies a predicate
hasProperty :: T.Text -> (Value -> Bool) -> Value -> Bool
hasProperty key typeCheck (Object obj) =
  case KeyMap.lookup (fromText key) obj of
    Just val -> typeCheck val
    _ -> False
hasProperty _ _ _ = False
