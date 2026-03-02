-- |
-- Module      : Lattice.State.Keyframe.Expression
-- Description : Property expression operations
--
-- Migrated from ui/src/stores/keyframeStore/expressions.ts
-- Pure functions for setting, enabling, disabling, and managing property expressions
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Expression
  ( setPropertyExpression
  , enablePropertyExpression
  , disablePropertyExpression
  , togglePropertyExpression
  , removePropertyExpression
  , getPropertyExpression
  , hasPropertyExpression
  , updateExpressionParams
  , convertExpressionToKeyframes
  , canBakeExpression
  ) where

import Data.List (find, filter, foldl)
import Data.Maybe (Maybe(..), isJust)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.CRUD (addKeyframeWithPropertyValue)
import Lattice.State.Keyframe.Evaluation (evaluatePropertyAtFrame)
import Lattice.State.Keyframe.Helpers (findPropertyByPath)
import Lattice.State.Keyframe.Interpolation (updatePropertyInLayer)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation (PropertyValue(..))
import Lattice.Types.Primitives
  ( Vec2(..)
  , validateFinite
  )
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , ExpressionParamValue(..)
  , ExpressionType(..)
  , PropertyExpression(..)
  )
import Lattice.Types.Layer (Layer(..))

-- ============================================================================
-- EXPRESSION METHODS
-- ============================================================================

-- | Set an expression on a property
-- Pure function: takes layer ID, property path, expression, and layers list
-- Returns updated layers list or error
setPropertyExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  PropertyExpression -> -- Expression to set
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setPropertyExpression layerId propertyPath expression layers =
  case getLayerById layerId layers of
    Nothing -> Left ("setPropertyExpression: layer not found: " <> T.unpack layerId)
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Left ("setPropertyExpression: property not found: " <> T.unpack propertyPath)
        Just _prop ->
          case updatePropertyInLayer layer propertyPath (\prop -> prop {animatablePropertyExpression = Just expression}) of
            Nothing -> Right layers
            Just updatedLayer ->
              let
                updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
              in
                Right updatedLayers

-- | Enable expression on a property (creates default if not exists)
-- Pure function: takes layer ID, property path, expression name, params, and layers list
-- Returns updated layers list or error
enablePropertyExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Expression name (default: "custom")
  [(Text, ExpressionParamValue)] -> -- Expression parameters
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
enablePropertyExpression layerId propertyPath expressionName params layers =
  let
    -- Determine expression type based on name
    exprType = if expressionName == "custom" then ExpressionCustom else ExpressionPreset
    expression = PropertyExpression
      { propertyExpressionEnabled = True
      , propertyExpressionType = exprType
      , propertyExpressionName = expressionName
      , propertyExpressionParams = params
      }
  in
    setPropertyExpression layerId propertyPath expression layers

-- | Disable expression on a property (keeps expression data for re-enabling)
-- Pure function: takes layer ID, property path, and layers list
-- Returns updated layers list or error
disablePropertyExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
disablePropertyExpression layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> Right layers
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Right layers
        Just _prop ->
          case updatePropertyInLayer layer propertyPath (\prop ->
            case animatablePropertyExpression prop of
              Nothing -> prop
              Just expr -> prop {animatablePropertyExpression = Just (expr {propertyExpressionEnabled = False})}
            ) of
            Nothing -> Right layers
            Just updatedLayer ->
              let
                updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
              in
                Right updatedLayers

-- | Toggle expression enabled state
-- Pure function: takes layer ID, property path, and layers list
-- Returns updated layers list and new enabled state or error
togglePropertyExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Current layers list
  Either Text (Bool, [Layer]) -- (new enabled state, updated layers list) or error
togglePropertyExpression layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> Right (False, layers)
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Right (False, layers)
        Just _prop ->
          case updatePropertyInLayer layer propertyPath (\prop ->
            case animatablePropertyExpression prop of
              Nothing -> prop
              Just expr ->
                let
                  newEnabled = not (propertyExpressionEnabled expr)
                in
                  prop {animatablePropertyExpression = Just (expr {propertyExpressionEnabled = newEnabled})}
            ) of
            Nothing -> Right (False, layers)
            Just updatedLayer ->
              let
                updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
                newEnabled = case findPropertyByPath updatedLayer propertyPath of
                  Nothing -> False  -- Property not found, expression disabled
                  Just p -> case animatablePropertyExpression p of
                    Nothing -> False
                    Just expr -> propertyExpressionEnabled expr
              in
                Right (newEnabled, updatedLayers)

-- | Remove expression from a property
-- Pure function: takes layer ID, property path, and layers list
-- Returns updated layers list or error
removePropertyExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
removePropertyExpression layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> Right layers
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Right layers
        Just _prop ->
          case updatePropertyInLayer layer propertyPath (\prop -> prop {animatablePropertyExpression = Nothing}) of
            Nothing -> Right layers
            Just updatedLayer ->
              let
                updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
              in
                Right updatedLayers

-- | Get expression on a property
-- Pure function: takes layer ID, property path, and layers list
-- Returns expression or error
getPropertyExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Current layers list
  Either Text PropertyExpression -- Expression or error
getPropertyExpression layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> Left ("Cannot get property expression: Layer \"" <> T.unpack layerId <> "\" not found")
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Left ("Cannot get property expression: Property \"" <> T.unpack propertyPath <> "\" not found on layer \"" <> T.unpack layerId <> "\"")
        Just prop ->
          case animatablePropertyExpression prop of
            Nothing -> Left ("Property \"" <> T.unpack propertyPath <> "\" on layer \"" <> T.unpack layerId <> "\" has no expression")
            Just expr -> Right expr

-- | Check if property has an expression
-- Pure function: takes layer ID, property path, and layers list
-- Returns true if property has an expression
hasPropertyExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Layers list
  Bool -- True if property has an expression
hasPropertyExpression layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> False
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> False
        Just prop -> isJust (animatablePropertyExpression prop)

-- | Update expression parameters
-- Pure function: takes layer ID, property path, params to update, and layers list
-- Returns updated layers list or error
-- Merges new params with existing params (new params override existing)
updateExpressionParams ::
  Text -> -- Layer ID
  Text -> -- Property path
  [(Text, ExpressionParamValue)] -> -- Params to update/add
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
updateExpressionParams layerId propertyPath newParams layers =
  case getLayerById layerId layers of
    Nothing -> Right layers
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Right layers
        Just _prop ->
          case updatePropertyInLayer layer propertyPath (\prop ->
            case animatablePropertyExpression prop of
              Nothing -> prop
              Just expr ->
                let
                  -- Merge params: new params override existing
                  existingParams = propertyExpressionParams expr
                  mergedParams = foldl (\acc (k, v) ->
                    -- Remove existing param with same key, then add new one
                    filter (\(k', _) -> k' /= k) acc ++ [(k, v)]
                    ) existingParams newParams
                in
                  prop {animatablePropertyExpression = Just (expr {propertyExpressionParams = mergedParams})}
            ) of
            Nothing -> Right layers
            Just updatedLayer ->
              let
                updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
              in
                Right updatedLayers

-- ============================================================================
-- CONVERT EXPRESSION TO KEYFRAMES (BAKE)
-- ============================================================================

-- | Convert an expression to keyframes by sampling at every frame
-- Pure function: takes layer ID, property path, start frame, end frame, sample rate, ID generator, and layers list
-- Returns updated layers list and count of keyframes created or error
-- This "bakes" the expression result into keyframes
-- After baking, the expression is disabled
convertExpressionToKeyframes ::
  Text -> -- Layer ID
  Text -> -- Property path with expression
  Maybe Double -> -- Start frame (Nothing = 1)
  Maybe Double -> -- End frame (Nothing = use composition duration)
  Double -> -- Sample rate (sample every N frames, default: 1 = every frame)
  Double -> -- Composition frame count (for end frame default)
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text (Int, [Layer]) -- (keyframes created, updated layers list) or error
convertExpressionToKeyframes layerId propertyPath mStartFrame mEndFrame sampleRate frameCount genId layers =
  -- Validate sample rate is finite and >= 1
  if not (validateFinite sampleRate) || sampleRate < 1
    then Left ("convertExpressionToKeyframes: Invalid sample rate (must be finite and >= 1): " <> T.pack (show sampleRate))
    else
      case getLayerById layerId layers of
        Nothing -> Right (0, layers)
        Just layer ->
          case findPropertyByPath layer propertyPath of
            Nothing -> Right (0, layers)
            Just prop ->
              case animatablePropertyExpression prop of
                Nothing -> Right (0, layers)
                Just expr ->
                  if not (propertyExpressionEnabled expr)
                    then Right (0, layers)
                    else
                      let
                        -- Validate and set start/end frames
                        start = case mStartFrame of
                          Nothing -> 1.0
                          Just f -> if validateFinite f && f >= 1 then f else 1.0
                        
                        end = case mEndFrame of
                          Nothing -> if validateFinite frameCount && frameCount >= 1 then frameCount else 1.0
                          Just f -> if validateFinite f && f >= 1 then f else 1.0
                        
                        -- Ensure start <= end
                        safeStart = min start end
                        safeEnd = max start end
                        
                        -- Round sample rate to integer >= 1
                        safeSampleRate = max 1.0 (fromIntegral (round sampleRate))
                        
                        -- Sample expression at each frame
                        sampleAtFrame accLayers accCount frame =
                          if frame > safeEnd
                            then Right (accCount, accLayers)
                            else
                              -- Evaluate property at this frame
                              case evaluatePropertyAtFrame layerId propertyPath frame accLayers of
                                Left _ -> sampleAtFrame accLayers accCount (frame + safeSampleRate)
                                Right (vecArray, mScalar) ->
                                  -- Convert to PropertyValue
                                  let
                                    propValue = case (vecArray, mScalar) of
                                      ([x, y, z], Nothing) -> PropertyValuePosition2DOr3D (Vec2 x y) (Just z)
                                      ([x, y], Nothing) -> PropertyValuePosition2DOr3D (Vec2 x y) Nothing
                                      ([x], Nothing) -> PropertyValueNumber x
                                      ([], Just s) -> PropertyValueNumber s
                                      _ -> PropertyValueNumber 0.0
                                    
                                    -- Add keyframe
                                    result = addKeyframeWithPropertyValue layerId propertyPath propValue (Just frame) frame genId accLayers
                                  in
                                    case result of
                                      Left _ -> sampleAtFrame accLayers accCount (frame + safeSampleRate)
                                      Right (_, updatedLayers) -> sampleAtFrame updatedLayers (accCount + 1) (frame + safeSampleRate)
                        
                        -- Clear existing keyframes and enable animation
                        -- Then sample expression
                        result1 = updatePropertyInLayer layer propertyPath (\p ->
                          p {animatablePropertyAnimated = True, animatablePropertyKeyframes = []}
                          )
                      in
                        case result1 of
                          Nothing -> Right (0, layers)
                          Just clearedLayer ->
                            let
                              clearedLayers = map (\l -> if layerId l == layerId clearedLayer then clearedLayer else l) layers
                              
                              -- Sample expression
                              result2 = sampleAtFrame clearedLayers 0 safeStart
                            in
                              case result2 of
                                Left err -> Left err
                                Right (keyframesCreated, sampledLayers) ->
                                  -- Disable the expression after baking
                                  case getLayerById layerId sampledLayers of
                                    Nothing -> Right (keyframesCreated, sampledLayers)
                                    Just sampledLayer ->
                                      case findPropertyByPath sampledLayer propertyPath of
                                        Nothing -> Right (keyframesCreated, sampledLayers)
                                        Just sampledProp ->
                                          case updatePropertyInLayer sampledLayer propertyPath (\p ->
                                            case animatablePropertyExpression p of
                                              Nothing -> p
                                              Just e -> p {animatablePropertyExpression = Just (e {propertyExpressionEnabled = False})}
                                            ) of
                                            Nothing -> Right (keyframesCreated, sampledLayers)
                                            Just finalLayer ->
                                              let
                                                finalLayers = map (\l -> if layerId l == layerId finalLayer then finalLayer else l) sampledLayers
                                              in
                                                Right (keyframesCreated, finalLayers)

-- | Check if a property has a bakeable expression
-- Pure function: takes layer ID, property path, and layers list
-- Returns true if property has an enabled expression
canBakeExpression ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Layers list
  Bool -- True if property has an enabled expression
canBakeExpression layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> False
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> False
        Just prop ->
          case animatablePropertyExpression prop of
            Nothing -> False
            Just expr -> propertyExpressionEnabled expr
