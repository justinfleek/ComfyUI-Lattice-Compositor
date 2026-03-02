-- |
-- Module      : Lattice.Services.ProjectValidation
-- Description : Pure project validation functions
-- 
-- Migrated from src/lattice/nodes/compositor_node.py
-- Pure validation logic extracted from Python validation functions
-- Note: Logging handled separately (caller can log validation results)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.ProjectValidation
  ( -- Validation functions
    calculateMaxDepth
  , validateExpressions
  , validateSingleExpression
  , validateNumericBounds
  , validatePaths
  , countLayers
  , validateStringLengths
  , validateArrayLengths
  , validateProjectId
  -- Types
  , ValidationError(..)
  , NumericBounds
  -- Constants
  , maxNestingDepth
  , maxExpressionLength
  , maxStringLength
  , maxArrayLength
  , maxLayers
  , defaultNumericBounds
  ) where

import Data.Aeson (Value(..))
import Data.Aeson.Key (Key, toText)
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Char (isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Utils.NumericSafety (isFinite)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Scientific (Scientific, toRealFloat)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // constants
-- ════════════════════════════════════════════════════════════════════════════

maxNestingDepth :: Int
maxNestingDepth = 50

maxExpressionLength :: Int
maxExpressionLength = 10000

maxStringLength :: Int
maxStringLength = 100000

maxArrayLength :: Int
maxArrayLength = 100000

maxLayers :: Int
maxLayers = 1000

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Validation error with path
data ValidationError = ValidationError
  { validationErrorPath :: Text
  , validationErrorMessage :: Text
  } deriving (Eq, Show)

-- | Numeric bounds for validation
type NumericBounds = HashMap Text (Double, Double)

-- Default numeric bounds
defaultNumericBounds :: NumericBounds
defaultNumericBounds = HM.fromList
  [ (T.pack "fps", (1, 240))
  , (T.pack "width", (1, 16384))
  , (T.pack "height", (1, 16384))
  , (T.pack "duration", (0, 86400))
  , (T.pack "frameCount", (1, 100000))
  , (T.pack "opacity", (0, 100))
  , (T.pack "volume", (0, 10))
  , (T.pack "speed", (-100, 100))
  ]

-- Dangerous expression patterns (simplified - full regex in Python)
dangerousPatterns :: [Text]
dangerousPatterns =
  [ T.pack "eval("
  , T.pack "Function("
  , T.pack "require("
  , T.pack "import("
  , T.pack "process."
  , T.pack "child_process"
  , T.pack "fs."
  , T.pack "__proto__"
  , T.pack "constructor["
  , T.pack "fetch("
  , T.pack "XMLHttpRequest"
  , T.pack "WebSocket"
  , T.pack "document."
  , T.pack "window."
  , T.pack "globalThis"
  , T.pack "self."
  , T.pack ".call("
  , T.pack ".apply("
  , T.pack ".bind("
  , T.pack "Reflect."
  , T.pack "Proxy("
  , T.pack "with("
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate maximum nesting depth of a JSON structure
-- Pure function: same inputs → same outputs
calculateMaxDepth :: Value -> Int -> Int
calculateMaxDepth val currentDepth
  | currentDepth > maxNestingDepth = currentDepth  -- Early exit
  | otherwise = case val of
      Object obj ->
        if KeyMap.null obj
          then currentDepth
          else maximum (map (\v -> calculateMaxDepth v (currentDepth + 1)) (KeyMap.elems obj))
      Array arr ->
        if V.null arr
          then currentDepth
          else maximum (map (\v -> calculateMaxDepth v (currentDepth + 1)) (V.toList arr))
      _ -> currentDepth

-- | Find and validate all expression fields
-- Pure function: same inputs → same outputs
validateExpressions :: Value -> Text -> [ValidationError]
validateExpressions val path = case val of
  Object obj ->
    concatMap (\(key, value) ->
      let keyT = toText key
          currentPath = if T.null path then keyT else path <> T.pack "." <> keyT
      in case (keyT, value) of
        (k, String expr) | k == T.pack "expression" ->
          validateSingleExpression expr currentPath
        (k, Object exprs) | k == T.pack "expressions" ->
          concatMap (\(exprKey, exprValue) ->
            case exprValue of
              String exprStr -> validateSingleExpression exprStr (currentPath <> T.pack "." <> toText exprKey)
              _ -> []
            ) (KeyMap.toList exprs)
        _ -> validateExpressions value currentPath
      ) (KeyMap.toList obj)
  Array arr ->
    concatMap (\(i, item) ->
      validateExpressions item (path <> T.pack "[" <> T.pack (show i) <> T.pack "]")
      ) (zip [0 ..] (V.toList arr))
  _ -> []

-- | Validate a single expression string
-- Pure function: same inputs → same outputs
validateSingleExpression :: Text -> Text -> [ValidationError]
validateSingleExpression expr path
  | T.length expr > maxExpressionLength =
      [ValidationError path (T.pack "Expression too long: " <> T.pack (show (T.length expr)) <> T.pack " chars (max " <> T.pack (show maxExpressionLength) <> T.pack ")")]
  | otherwise =
      let exprLower = T.toLower expr
          hasDangerousPattern = any (`T.isInfixOf` exprLower) dangerousPatterns
      in if hasDangerousPattern
           then [ValidationError path (T.pack "Dangerous pattern detected in expression")]
           else []

-- | Validate numeric values are within expected bounds
-- Pure function: same inputs → same outputs
validateNumericBounds :: Value -> Text -> NumericBounds -> [ValidationError]
validateNumericBounds val path bounds = case val of
  Object obj ->
    concatMap (\(key, value) ->
      let keyT = toText key
          currentPath = if T.null path then keyT else path <> T.pack "." <> keyT
      in case value of
        Number n ->
          let d = toRealFloat n :: Double
          in case HM.lookup keyT bounds of
            Just (minVal, maxVal) ->
              if d < minVal || d > maxVal
                then [ValidationError currentPath (T.pack "Value out of range: " <> T.pack (show d) <> T.pack " (expected " <> T.pack (show minVal) <> T.pack " to " <> T.pack (show maxVal) <> T.pack ")")]
                else []
            Nothing -> []
          ++ if isNaN d
               then [ValidationError currentPath (T.pack "NaN value")]
               else []
          ++ if isInfinite d
               then [ValidationError currentPath (T.pack "Infinite value")]
               else []
        _ -> validateNumericBounds value currentPath bounds
      ) (KeyMap.toList obj)
  Array arr ->
    concatMap (\(i, item) ->
      validateNumericBounds item (path <> T.pack "[" <> T.pack (show i) <> T.pack "]") bounds
      ) (zip [0 ..] (V.toList arr))
  _ -> []

-- | Validate file paths don't contain traversal attacks
-- Pure function: same inputs → same outputs
validatePaths :: Value -> Text -> [ValidationError]
validatePaths val path =
  let pathFields = map T.pack ["path", "src", "source", "file", "filename", "url", "href", "assetPath"]
  in case val of
    Object obj ->
      concatMap (\(key, value) ->
        let keyT = toText key
            currentPath = if T.null path then keyT else path <> T.pack "." <> keyT
            keyLower = T.toLower keyT
        in case value of
          String str ->
            if keyLower `elem` pathFields
              then if (T.pack ".." `T.isInfixOf` str || T.isPrefixOf (T.pack "/") str || T.isPrefixOf (T.pack "\\") str)
                     && not (T.isPrefixOf (T.pack "http://") str || T.isPrefixOf (T.pack "https://") str)
                     then [ValidationError currentPath (T.pack "Potential path traversal: " <> T.take 50 str)]
                     else []
              else []
          _ -> validatePaths value currentPath
        ) (KeyMap.toList obj)
    Array arr ->
      concatMap (\(i, item) ->
        validatePaths item (path <> T.pack "[" <> T.pack (show i) <> T.pack "]")
        ) (zip [0 ..] (V.toList arr))
    _ -> []

-- | Count total number of layers in project
-- Pure function: same inputs → same outputs
countLayers :: Value -> Int
countLayers val = case val of
  Object obj ->
    case KeyMap.lookup "layers" obj of
      Just (Array layers) ->
        V.length layers + sum (map countLayers (V.toList layers))
      _ -> sum (map countLayers (KeyMap.elems obj))
  Array arr -> sum (map countLayers (V.toList arr))
  _ -> 0

-- | Validate string fields aren't too long
-- Pure function: same inputs → same outputs
validateStringLengths :: Value -> Text -> [ValidationError]
validateStringLengths val path = case val of
  String str ->
    if T.length str > maxStringLength
      then [ValidationError path (T.pack "String too long: " <> T.pack (show (T.length str)) <> T.pack " chars")]
      else []
  Object obj ->
    concatMap (\(key, value) ->
      let keyT = toText key
          currentPath = if T.null path then keyT else path <> T.pack "." <> keyT
      in validateStringLengths value currentPath
      ) (KeyMap.toList obj)
  Array arr ->
    concatMap (\(i, item) ->
      validateStringLengths item (path <> T.pack "[" <> T.pack (show i) <> T.pack "]")
      ) (zip [0 ..] (V.toList arr))
  _ -> []

-- | Validate arrays aren't too long
-- Pure function: same inputs → same outputs
validateArrayLengths :: Value -> Text -> [ValidationError]
validateArrayLengths val path = case val of
  Array arr ->
    (if V.length arr > maxArrayLength
       then [ValidationError path (T.pack "Array too long: " <> T.pack (show (V.length arr)) <> T.pack " items")]
       else [])
    ++ concatMap (\(i, item) ->
         validateArrayLengths item (path <> T.pack "[" <> T.pack (show i) <> T.pack "]")
         ) (zip [0 ..] (V.toList arr))
  Object obj ->
    concatMap (\(key, value) ->
      let keyT = toText key
          currentPath = if T.null path then keyT else path <> T.pack "." <> keyT
      in validateArrayLengths value currentPath
      ) (KeyMap.toList obj)
  _ -> []

-- | Validate project ID is safe for filesystem use
-- Pure function: same inputs → same outputs
validateProjectId :: Text -> Bool
validateProjectId projectId
  | T.null projectId = False
  | T.length projectId > 255 = False
  | T.pack ".." `T.isInfixOf` projectId = False
  | T.pack "/" `T.isInfixOf` projectId = False
  | T.pack "\\" `T.isInfixOf` projectId = False
  | otherwise = T.all (\c -> isAlphaNum c || c == '_' || c == '-') projectId
