-- |
-- Module      : Lattice.Utils.Defaults
-- Description : Common default value patterns
-- 
--                             // every // value // has // explicit // defaults
-- All values are deterministic with min/max bounds
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Defaults
  ( -- Text defaults
    defaultText
  , defaultTextNonEmpty
  -- Numeric defaults
  , defaultDouble
  , defaultInt
  , defaultDoubleBounded
  -- Collection defaults
  , defaultList
  , defaultHashMap
  -- Boolean defaults
  , defaultBool
  -- Common patterns
  , defaultMaybeToValue
  , defaultMaybeToFlag
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // text // defaults
-- ════════════════════════════════════════════════════════════════════════════

-- | Default text value (empty string)
-- Default: "" (min: 0 chars, max: no upper bound)
defaultText :: Text
defaultText = T.pack ""

-- | Default non-empty text (for required fields)
-- Use when field must have a value
-- Default: "default" (min: 1 char, max: no upper bound)
defaultTextNonEmpty :: Text
defaultTextNonEmpty = T.pack "default"

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // numeric // defaults
-- ════════════════════════════════════════════════════════════════════════════

-- | Default double value
-- Default: 0.0 (min: -Infinity, max: +Infinity, but must be finite)
defaultDouble :: Double
defaultDouble = 0.0

-- | Default int value
-- Default: 0 (min: -Infinity, max: +Infinity, but must be finite)
defaultInt :: Int
defaultInt = 0

-- | Default double with bounds
-- Default: 0.0 (min: minVal, max: maxVal)
defaultDoubleBounded :: Double -> Double -> Double
defaultDoubleBounded minVal maxVal =
  if minVal <= 0.0 && 0.0 <= maxVal
  then 0.0
  else minVal  -- If 0.0 not in range, use minVal

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // collection // defaults
-- ════════════════════════════════════════════════════════════════════════════

-- | Default list (empty list)
-- Default: [] (min: 0 elements, max: no upper bound)
defaultList :: [a]
defaultList = []

-- | Default hash map (empty map)
-- Default: HM.empty (min: 0 entries, max: no upper bound)
defaultHashMap :: HashMap k v
defaultHashMap = HM.empty

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // boolean // defaults
-- ════════════════════════════════════════════════════════════════════════════

-- | Default boolean value
-- Default: False
defaultBool :: Bool
defaultBool = False

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // common // patterns
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert Maybe to explicit value with default
-- Pattern: Maybe a -> (a, Bool)
-- Returns: (defaultValue, False) if Nothing, (value, True) if Just value
defaultMaybeToValue :: a -> Maybe a -> (a, Bool)
defaultMaybeToValue defaultValue mValue =
  case mValue of
    Nothing -> (defaultValue, False)
    Just value -> (value, True)

-- | Convert Maybe to explicit flag
-- Pattern: Maybe a -> Bool
-- Returns: False if Nothing, True if Just _
defaultMaybeToFlag :: Maybe a -> Bool
defaultMaybeToFlag mValue =
  case mValue of
    Nothing -> False
    Just _ -> True
