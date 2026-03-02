-- |
-- Module      : Lattice.State.Keyframe.Query
-- Description : Keyframe query utilities
--
-- Migrated from ui/src/stores/keyframeStore/query.ts
-- Pure functions for querying keyframe state and navigation
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Query
  ( getKeyframesAtFrame
  , getAllKeyframeFrames
  , findNextKeyframeFrame
  , findPrevKeyframeFrame
  , findSurroundingKeyframes
  -- Types
  , KeyframeAtFrame(..)
  ) where

import Data.List (find, sort, nub, reverse)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.Helpers (findPropertyByPath)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , PropertyValue(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives (validateFinite)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Keyframe at a specific frame with property path
data KeyframeAtFrame = KeyframeAtFrame
  { keyframeAtFramePropertyPath :: Text
  , keyframeAtFrameKeyframe :: Keyframe PropertyValue
  }
  deriving (Eq, Show)

-- ============================================================================
-- KEYFRAME QUERY UTILITIES
-- ============================================================================

-- | Get keyframes at a specific frame across all animated properties of a layer
-- Pure function: takes layer ID, frame, and layers list
-- Returns list of keyframes with their property paths
getKeyframesAtFrame ::
  Text -> -- Layer ID
  Double -> -- Frame
  [Layer] -> -- Layers list
  [KeyframeAtFrame] -- List of keyframes at frame with property paths
getKeyframesAtFrame targetLayerId frame layers =
  case getLayerById layers targetLayerId of
    Nothing -> []
    Just layer ->
      let
        -- Validate frame is finite and >= 1
        safeFrame = if validateFinite frame && frame >= 1 then frame else 1.0
        
        -- Property paths to check
        propertyPaths =
          [ "position"
          , "scale"
          , "rotation"
          , "origin"
          , "anchorPoint"
          , "rotationX"
          , "rotationY"
          , "rotationZ"
          , "orientation"
          , "opacity"
          ]
        
        -- Collect keyframes from standard properties using findPropertyByPath
        standardKeyframes = concatMap (\propPath ->
          case findPropertyByPath layer propPath of
            Nothing -> []
            Just prop ->
              if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                then
                  case find (\k -> keyframeFrame k == safeFrame) (animatablePropertyKeyframes prop) of
                    Nothing -> []
                    Just kf -> [KeyframeAtFrame propPath kf]
                else []
          ) propertyPaths
        
        -- Collect from custom properties (layerProperties is [Value] until migrated to [AnimatableProperty PropertyValue])
        customKeyframes = []
      in
        standardKeyframes ++ customKeyframes

-- | Get all keyframe frames for a layer (for timeline display)
-- Pure function: takes layer ID and layers list
-- Returns sorted list of unique frame numbers
getAllKeyframeFrames ::
  Text -> -- Layer ID
  [Layer] -> -- Layers list
  [Double] -- Sorted list of unique frame numbers
getAllKeyframeFrames targetLayerId layers =
  case getLayerById layers targetLayerId of
    Nothing -> []
    Just layer ->
      let
        -- Property paths to check
        propertyPaths =
          [ "position"
          , "scale"
          , "rotation"
          , "origin"
          , "anchorPoint"
          , "rotationX"
          , "rotationY"
          , "rotationZ"
          , "orientation"
          , "opacity"
          ]
        
        -- Collect frames from standard properties using findPropertyByPath
        standardFrames = concatMap (\propPath ->
          case findPropertyByPath layer propPath of
            Nothing -> []
            Just prop ->
              if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                then map keyframeFrame (animatablePropertyKeyframes prop)
                else []
          ) propertyPaths
        
        -- Collect from custom properties
        customFrames = concatMap (\prop ->
          if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
            then map keyframeFrame (animatablePropertyKeyframes prop)
            else []
          ) (layerProperties layer)
        
        -- Combine, remove duplicates, sort
        allFrames = nub (standardFrames ++ customFrames)
      in
        sort allFrames

-- | Find the next keyframe frame after the given frame
-- Pure function: takes current frame, layer IDs, and layers list
-- Returns next keyframe frame or error
findNextKeyframeFrame ::
  Double -> -- Current frame
  [Text] -> -- Layer IDs to search (empty = search all layers)
  [Layer] -> -- Layers list
  Either Text Double -- Next keyframe frame or error
findNextKeyframeFrame currentFrame layerIds layers =
  let
    -- Validate current frame
    safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
    
    -- Determine which layers to search
    searchLayerIds = if null layerIds
      then map layerId layers
      else layerIds
    
    -- Collect all frames from all search layers
    allFramesSet = foldl (\acc lid -> acc ++ getAllKeyframeFrames lid layers) [] searchLayerIds
    uniqueFrames = sort (nub allFramesSet)
    
    -- Find next frame
    mNextFrame = find (\f -> f > safeCurrentFrame) uniqueFrames
  in
    case mNextFrame of
      Nothing -> Left ("No next keyframe found after frame " <> T.pack (show safeCurrentFrame) <> " for layers: " <> T.intercalate ", " searchLayerIds)
      Just nextFrame -> Right nextFrame

-- | Find the previous keyframe frame before the given frame
-- Pure function: takes current frame, layer IDs, and layers list
-- Returns previous keyframe frame or error
findPrevKeyframeFrame ::
  Double -> -- Current frame
  [Text] -> -- Layer IDs to search (empty = search all layers)
  [Layer] -> -- Layers list
  Either Text Double -- Previous keyframe frame or error
findPrevKeyframeFrame currentFrame layerIds layers =
  let
    -- Validate current frame
    safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
    
    -- Determine which layers to search
    searchLayerIds = if null layerIds
      then map layerId layers
      else layerIds
    
    -- Collect all frames from all search layers
    allFramesSet = foldl (\acc lid -> acc ++ getAllKeyframeFrames lid layers) [] searchLayerIds
    uniqueFrames = sort (nub allFramesSet)
    
    -- Find previous frames (before current)
    prevFrames = filter (\f -> f < safeCurrentFrame) uniqueFrames
  in
    case prevFrames of
      [] -> Left ("No previous keyframe found before frame " <> T.pack (show safeCurrentFrame) <> " for layers: " <> T.intercalate ", " searchLayerIds)
      _ ->
        let
          reversed = reverse prevFrames
          mLastFrame = case reversed of
            [] -> Nothing
            (f : _) -> Just f
        in
          case mLastFrame of
            Nothing -> Left ("No previous keyframe found before frame " <> T.pack (show safeCurrentFrame) <> " for layers: " <> T.intercalate ", " searchLayerIds)
            Just lastFrame -> Right lastFrame

-- | Find the nearest keyframes before and after a given frame
-- Pure function: takes property and frame
-- Returns before and after keyframes (Nothing if not found)
findSurroundingKeyframes ::
  AnimatableProperty a -> -- Property to search
  Double -> -- Frame
  (Maybe (Keyframe a), Maybe (Keyframe a)) -- (before, after) keyframes
findSurroundingKeyframes property frame =
  let
    -- Validate frame
    safeFrame = if validateFinite frame && frame >= 1 then frame else 1.0
    keyframes = animatablePropertyKeyframes property
  in
    if null keyframes
      then (Nothing, Nothing)
      else
        let
          -- Find before and after
          (before, after) = findSurroundingKeyframes' keyframes safeFrame Nothing Nothing
        in
          (before, after)
  where
    findSurroundingKeyframes' ::
      [Keyframe a] ->
      Double ->
      Maybe (Keyframe a) ->
      Maybe (Keyframe a) ->
      (Maybe (Keyframe a), Maybe (Keyframe a))
    findSurroundingKeyframes' [] _ before after = (before, after)
    findSurroundingKeyframes' (kf : kfs) f before after =
      if keyframeFrame kf <= f
        then findSurroundingKeyframes' kfs f (Just kf) after
        else
          case after of
            Nothing -> (before, Just kf)
            Just _ -> (before, after)
