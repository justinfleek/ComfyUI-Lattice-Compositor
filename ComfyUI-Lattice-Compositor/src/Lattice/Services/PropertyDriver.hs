-- |
-- Module      : Lattice.Services.PropertyDriver
-- Description : Pure property driver functions
-- 
-- Migrated from ui/src/services/propertyDriver.ts
-- Pure path parsing, transform, and driver creation functions
-- Note: Stateful class methods deferred
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.PropertyDriver
  ( -- Types
    DriverSourceType(..)
  , BlendMode(..)
  , DriverTransform(..)
  , SplineControlPointProperty(..)
  , ParsedSplinePath(..)
  -- Path parsing functions
  , isSplineControlPointPath
  , isLightPropertyPath
  , parseSplineControlPointPath
  , createSplineControlPointPath
  -- Transform functions
  , applyTransform
  , applyTransforms
  , blendValue
  -- Path utility functions
  , getPropertyPathDisplayName
  , getAllPropertyPaths
  , getLightPropertyPaths
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.NumericSafety (ensureFiniteD, safeSqrtD)
import Text.Regex.TDFA ((=~))

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Driver source type
data DriverSourceType
  = SourceProperty
  | SourceAudio
  | SourceTime
  | SourceExpression
  deriving (Eq, Show)

-- | Blend mode
data BlendMode
  = BlendReplace
  | BlendAdd
  | BlendMultiply
  deriving (Eq, Show)

-- | Spline control point property
data SplineControlPointProperty
  = SplinePropertyX
  | SplinePropertyY
  | SplinePropertyDepth
  deriving (Eq, Show)

-- | Parsed spline control point path
data ParsedSplinePath = ParsedSplinePath
  { parsedIndex :: Int
  , parsedProperty :: SplineControlPointProperty
  }
  deriving (Eq, Show)

-- | Driver transform type
data DriverTransform
  = TransformScale Double
  | TransformOffset Double
  | TransformClamp (Maybe Double) (Maybe Double)  -- min, max (Nothing = no bound)
  | TransformSmooth Double  -- smoothing factor (0-1)
  | TransformInvert
  | TransformRemap Double Double Double Double  -- inMin, inMax, outMin, outMax
  | TransformThreshold Double
  | TransformOscillate Double Double Double  -- frequency, amplitude, phase
  deriving (Eq, Show)

-- ============================================================================
-- PATH PARSING FUNCTIONS
-- ============================================================================

-- | Check if a property path is a spline control point path
-- Pure function: same inputs → same outputs
isSplineControlPointPath :: Text -> Bool
isSplineControlPointPath path = "spline.controlPoint." `T.isPrefixOf` path

-- | Check if a property path is a light property path
-- Pure function: same inputs → same outputs
isLightPropertyPath :: Text -> Bool
isLightPropertyPath path = "light." `T.isPrefixOf` path

-- | Safe list accessor
safeListGet :: [a] -> Int -> Maybe a
safeListGet [] _ = Nothing
safeListGet arr idx
  | idx < 0 = Nothing
  | otherwise = go arr idx
  where
    go [] _ = Nothing
    go (x:xs) 0 = Just x
    go (_:xs) n = go xs (n - 1)

-- | Parse a spline control point path into components
-- Pure function: same inputs → same outputs
-- Returns Left error message or Right parsed path
parseSplineControlPointPath :: Text -> Either Text ParsedSplinePath
parseSplineControlPointPath path =
  if T.null path
  then Left "Cannot parse spline control point path: Invalid path string (empty)"
  else
    let pattern :: Text = T.pack "^spline\\.controlPoint\\.([0-9]+)\\.(x|y|depth)$"
        matches = path =~ pattern :: [[Text]]
    in case matches of
         [] -> Left ("Cannot parse spline control point path: Path doesn't match expected pattern (path: \"" <> path <> "\")")
         (matchGroup:_) ->
           case (safeListGet matchGroup 1, safeListGet matchGroup 2) of
             (Just indexStr, Just propertyStr) ->
               case readMaybe (T.unpack indexStr) :: Maybe Int of
                 Nothing -> Left ("Cannot parse spline control point path: Invalid index in path (parsed index: " <> indexStr <> ")")
                 Just idx ->
                   if idx < 0
                   then Left ("Cannot parse spline control point path: Invalid index in path (index must be non-negative: " <> T.pack (show idx) <> ")")
                   else
                     case propertyStr of
                       "x" -> Right (ParsedSplinePath idx SplinePropertyX)
                       "y" -> Right (ParsedSplinePath idx SplinePropertyY)
                       "depth" -> Right (ParsedSplinePath idx SplinePropertyDepth)
                       _ -> Left ("Cannot parse spline control point path: Invalid property in path (property: \"" <> propertyStr <> "\")")
             _ -> Left ("Cannot parse spline control point path: Path doesn't match expected pattern (path: \"" <> path <> "\")")

-- | Safe integer parsing
readMaybe :: String -> Maybe Int
readMaybe s = case reads s of
  [(n, "")] -> Just n
  _ -> Nothing

-- | Create a spline control point property path
-- Pure function: same inputs → same outputs
createSplineControlPointPath :: Int -> SplineControlPointProperty -> Text
createSplineControlPointPath index property =
  let propStr = case property of
        SplinePropertyX -> "x"
        SplinePropertyY -> "y"
        SplinePropertyDepth -> "depth"
  in "spline.controlPoint." <> T.pack (show index) <> "." <> propStr

-- ============================================================================
-- TRANSFORM FUNCTIONS
-- ============================================================================

-- | Apply a single transform to a value
-- Pure function: same inputs → same outputs
-- Note: For smooth transform, previous smoothed value must be passed as parameter
applyTransform ::
  DriverTransform ->  -- Transform to apply
  Double ->           -- Input value
  Maybe Double ->     -- Previous smoothed value (for smooth transform)
  (Double, Maybe Double)  -- (Output value, new smoothed value)
applyTransform transform value mPrevSmoothed = case transform of
  TransformScale factor ->
    let finiteFactor = ensureFiniteD factor 1.0
    in (ensureFiniteD (value * finiteFactor) value, mPrevSmoothed)
  
  TransformOffset amount ->
    let finiteAmount = ensureFiniteD amount 0.0
    in (ensureFiniteD (value + finiteAmount) value, mPrevSmoothed)
  
  TransformClamp mMin mMax ->
    let minVal = case mMin of
          Just m -> if isFinite m then m else -1.0 / 0.0  -- -Infinity
          Nothing -> -1.0 / 0.0
        maxVal = case mMax of
          Just m -> if isFinite m then m else 1.0 / 0.0  -- Infinity
          Nothing -> 1.0 / 0.0
        clamped = max minVal (min maxVal value)
    in (ensureFiniteD clamped value, mPrevSmoothed)
  
  TransformSmooth smoothing ->
    let finiteSmoothing = ensureFiniteD smoothing 0.5
        clampedSmoothing = max 0.0 (min 1.0 finiteSmoothing)
        prevValue = case mPrevSmoothed of
          Just p -> if isFinite p then p else value
          Nothing -> value
        smoothed = prevValue * clampedSmoothing + value * (1.0 - clampedSmoothing)
    in (ensureFiniteD smoothed value, Just smoothed)
  
  TransformInvert ->
    (ensureFiniteD (1.0 - value) value, mPrevSmoothed)
  
  TransformRemap inMin inMax outMin outMax ->
    let finiteInMin = ensureFiniteD inMin 0.0
        finiteInMax = ensureFiniteD inMax 1.0
        finiteOutMin = ensureFiniteD outMin 0.0
        finiteOutMax = ensureFiniteD outMax 1.0
        inRange = finiteInMax - finiteInMin
    in if inRange == 0.0
       then (ensureFiniteD ((finiteOutMin + finiteOutMax) / 2.0) value, mPrevSmoothed)
       else
         let normalized = (value - finiteInMin) / inRange
             remapped = finiteOutMin + normalized * (finiteOutMax - finiteOutMin)
         in (ensureFiniteD remapped value, mPrevSmoothed)
  
  TransformThreshold threshold ->
    let finiteThreshold = ensureFiniteD threshold 0.5
        result = if value > finiteThreshold then 1.0 else 0.0
    in (ensureFiniteD result value, mPrevSmoothed)
  
  TransformOscillate freq amp phase ->
    let finiteFreq = if isFinite freq && freq > 0 then freq else 1.0
        finiteAmp = if isFinite amp && amp >= 0 then amp else 1.0
        finitePhase = ensureFiniteD phase 0.0
        oscillated = sin ((value * finiteFreq + finitePhase) * pi * 2.0) * finiteAmp
    in (ensureFiniteD oscillated value, mPrevSmoothed)

-- | Apply a chain of transforms to a value
-- Pure function: same inputs → same outputs
-- Returns (final value, final smoothed value map)
applyTransforms ::
  [DriverTransform] ->  -- Transform chain
  Double ->             -- Input value
  Maybe Double ->       -- Previous smoothed value (for smooth transforms)
  (Double, Maybe Double)  -- (Output value, new smoothed value)
applyTransforms transforms value mPrevSmoothed =
  foldl (\(val, mPrev) transform ->
    applyTransform transform val mPrev
  ) (value, mPrevSmoothed) transforms

-- | Blend driven value with base value
-- Pure function: same inputs → same outputs
blendValue ::
  Double ->      -- Base value
  Double ->      -- Driven value
  BlendMode ->   -- Blend mode
  Double ->      -- Blend amount (0-1)
  Double         -- Blended value
blendValue base driven mode amount =
  let finiteAmount = max 0.0 (min 1.0 (ensureFiniteD amount 1.0))
      result = case mode of
        BlendReplace -> driven
        BlendAdd -> base + driven
        BlendMultiply -> base * driven
      -- Mix between base and result based on blend amount
      blended = base * (1.0 - finiteAmount) + result * finiteAmount
  in ensureFiniteD blended base

-- ============================================================================
-- PATH UTILITY FUNCTIONS
-- ============================================================================

-- | Get display name for property path
-- Pure function: same inputs → same outputs
getPropertyPathDisplayName :: Text -> Text
getPropertyPathDisplayName path =
  -- Check for spline control point paths first
  case parseSplineControlPointPath path of
    Right (ParsedSplinePath index property) ->
      let propName = case property of
            SplinePropertyX -> "X"
            SplinePropertyY -> "Y"
            SplinePropertyDepth -> "Depth"
      in "Control Point " <> T.pack (show index) <> " " <> propName
    Left _ ->
      -- Check known paths
      case path of
        "transform.position.x" -> "Position X"
        "transform.position.y" -> "Position Y"
        "transform.position.z" -> "Position Z"
        "transform.anchorPoint.x" -> "Anchor Point X"
        "transform.anchorPoint.y" -> "Anchor Point Y"
        "transform.anchorPoint.z" -> "Anchor Point Z"
        "transform.scale.x" -> "Scale X"
        "transform.scale.y" -> "Scale Y"
        "transform.scale.z" -> "Scale Z"
        "transform.rotation" -> "Rotation"
        "transform.rotationX" -> "X Rotation"
        "transform.rotationY" -> "Y Rotation"
        "transform.rotationZ" -> "Z Rotation"
        "opacity" -> "Opacity"
        "light.intensity" -> "Light Intensity"
        "light.color.r" -> "Light Color Red"
        "light.color.g" -> "Light Color Green"
        "light.color.b" -> "Light Color Blue"
        "light.colorTemperature" -> "Color Temperature (K)"
        "light.coneAngle" -> "Cone Angle"
        "light.penumbra" -> "Penumbra"
        "light.falloff" -> "Falloff"
        "light.shadow.intensity" -> "Shadow Intensity"
        "light.shadow.softness" -> "Shadow Softness"
        "light.shadow.bias" -> "Shadow Bias"
        "light.poi.x" -> "Point of Interest X"
        "light.poi.y" -> "Point of Interest Y"
        "light.poi.z" -> "Point of Interest Z"
        "light.areaSize.width" -> "Area Light Width"
        "light.areaSize.height" -> "Area Light Height"
        "light.physicalIntensity" -> "Physical Intensity (lm)"
        _ -> path

-- | Get all available property paths (common properties)
-- Pure function: same inputs → same outputs
getAllPropertyPaths :: [Text]
getAllPropertyPaths =
  [ "transform.position.x"
  , "transform.position.y"
  , "transform.position.z"
  , "transform.anchorPoint.x"
  , "transform.anchorPoint.y"
  , "transform.anchorPoint.z"
  , "transform.scale.x"
  , "transform.scale.y"
  , "transform.scale.z"
  , "transform.rotation"
  , "transform.rotationX"
  , "transform.rotationY"
  , "transform.rotationZ"
  , "opacity"
  ]

-- | Get all light property paths
-- Pure function: same inputs → same outputs
getLightPropertyPaths :: [Text]
getLightPropertyPaths =
  [ "light.intensity"
  , "light.color.r"
  , "light.color.g"
  , "light.color.b"
  , "light.colorTemperature"
  , "light.coneAngle"
  , "light.penumbra"
  , "light.falloff"
  , "light.shadow.intensity"
  , "light.shadow.softness"
  , "light.shadow.bias"
  , "light.poi.x"
  , "light.poi.y"
  , "light.poi.z"
  , "light.areaSize.width"
  , "light.areaSize.height"
  , "light.physicalIntensity"
  ]
