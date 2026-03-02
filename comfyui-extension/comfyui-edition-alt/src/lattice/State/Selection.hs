-- |
-- Module      : Lattice.State.Selection
-- Description : Pure state management functions for selection store
-- 
-- Migrated from ui/src/stores/selectionStore.ts
-- Pure query and calculation functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Selection
  ( -- Pure queries (getters)
    hasSelection
  , hasMultipleSelected
  , hasKeyframeSelection
  , hasControlPointSelection
  , singleSelectedLayerId
  , selectedControlPointCount
  -- Pure query actions
  , isLayerSelected
  , isKeyframeSelected
  , isControlPointSelected
  , getSelectedControlPointsForLayer
  -- Pure calculation helpers
  , computeRangeSelection
  , computeLayerAboveSelection
  , computeLayerBelowSelection
  -- Types
  , ControlPointSelection(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Control point selection info
data ControlPointSelection = ControlPointSelection
  { controlPointSelectionLayerId :: Text
  , controlPointSelectionPointIndex :: Int
  , controlPointSelectionGroupId :: Maybe Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON ControlPointSelection where
  toJSON (ControlPointSelection layerId pointIndex mGroupId) =
    let
      baseFields = ["layerId" .= layerId, "pointIndex" .= pointIndex]
      withGroupId = case mGroupId of
        Just g -> ("groupId" .= g) : baseFields
        Nothing -> baseFields
    in object withGroupId

instance FromJSON ControlPointSelection where
  parseJSON = withObject "ControlPointSelection" $ \o -> do
    layerId <- o .: "layerId"
    pointIndex <- o .: "pointIndex"
    mGroupId <- o .:? "groupId"
    return (ControlPointSelection layerId pointIndex mGroupId)

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if any layers are selected
-- Pure function: takes selected layer IDs set, returns boolean
hasSelection ::
  HashSet Text ->
  Bool
hasSelection selectedLayerIds = not (HS.null selectedLayerIds)

-- | Check if multiple layers are selected
-- Pure function: takes selected layer IDs set, returns boolean
hasMultipleSelected ::
  HashSet Text ->
  Bool
hasMultipleSelected selectedLayerIds = HS.size selectedLayerIds > 1

-- | Check if any keyframes are selected
-- Pure function: takes selected keyframe IDs set, returns boolean
hasKeyframeSelection ::
  HashSet Text ->
  Bool
hasKeyframeSelection selectedKeyframeIds = not (HS.null selectedKeyframeIds)

-- | Check if any control points are selected
-- Pure function: takes selected control points list, returns boolean
hasControlPointSelection ::
  [ControlPointSelection] ->
  Bool
hasControlPointSelection selectedControlPoints = not (null selectedControlPoints)

-- | Get single selected layer ID (returns Nothing if 0 or 2+ layers selected)
-- Pure function: takes selected layer IDs set, returns single ID or Nothing
singleSelectedLayerId ::
  HashSet Text ->
  Maybe Text
singleSelectedLayerId selectedLayerIds =
  if HS.size selectedLayerIds == 1
    then case HS.toList selectedLayerIds of
      [id_] -> Just id_
      [] -> Nothing  -- Empty HashSet with size 1 is impossible, but type-safe fallback
      (_ : _ : _) -> Nothing  -- Multiple elements with size 1 is impossible, but type-safe fallback
    else Nothing

-- | Get count of selected control points
-- Pure function: takes selected control points list, returns count
selectedControlPointCount ::
  [ControlPointSelection] ->
  Int
selectedControlPointCount = length

-- ════════════════════════════════════════════════════════════════════════════
--                                                  // pure // query // actions
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if a layer is selected
-- Pure function: takes selected layer IDs set and layer ID, returns boolean
isLayerSelected ::
  HashSet Text ->
  Text ->
  Bool
isLayerSelected selectedLayerIds layerId = HS.member layerId selectedLayerIds

-- | Check if a keyframe is selected
-- Pure function: takes selected keyframe IDs set and keyframe ID, returns boolean
isKeyframeSelected ::
  HashSet Text ->
  Text ->
  Bool
isKeyframeSelected selectedKeyframeIds keyframeId = HS.member keyframeId selectedKeyframeIds

-- | Check if a control point is selected
-- Pure function: takes selected control points list, layer ID, and point index, returns boolean
isControlPointSelected ::
  [ControlPointSelection] ->
  Text ->
  Int ->
  Bool
isControlPointSelected selectedControlPoints layerId pointIndex =
  any (\p -> controlPointSelectionLayerId p == layerId &&
             controlPointSelectionPointIndex p == pointIndex) selectedControlPoints

-- | Get selected control points for a specific layer
-- Pure function: takes selected control points list and layer ID, returns filtered list
getSelectedControlPointsForLayer ::
  [ControlPointSelection] ->
  Text ->
  [ControlPointSelection]
getSelectedControlPointsForLayer selectedControlPoints layerId =
  filter (\p -> controlPointSelectionLayerId p == layerId) selectedControlPoints

-- ════════════════════════════════════════════════════════════════════════════
--                                            // pure // calculation // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Compute range selection between two layer IDs
-- Pure function: takes start ID, end ID, and ordered layer IDs list, returns new selection
computeRangeSelection ::
  Text ->
  Text ->
  [Text] ->
  Maybe [Text]
computeRangeSelection startLayerId endLayerId orderedLayerIds =
  case (findIndexInList startLayerId orderedLayerIds, findIndexInList endLayerId orderedLayerIds) of
    (Just startIndex, Just endIndex) ->
      let
        minIndex = min startIndex endIndex
        maxIndex = max startIndex endIndex
      in
        Just (take (maxIndex - minIndex + 1) (drop minIndex orderedLayerIds))
    _ -> Nothing

-- | Compute layer above current selection
-- Pure function: takes selected layer IDs set, ordered layer IDs list, returns new selection
computeLayerAboveSelection ::
  HashSet Text ->
  [Text] ->
  Maybe Text
computeLayerAboveSelection selectedLayerIds orderedLayerIds =
  if null orderedLayerIds
    then Nothing
    else if HS.null selectedLayerIds
      then case orderedLayerIds of
        [] -> Nothing
        first:_ -> Just first
      else
        let
          -- Find the topmost (minimum index) selected layer
          selectedIndices = mapMaybe (\id_ -> findIndexInList id_ orderedLayerIds) (HS.toList selectedLayerIds)
          minIndex = case selectedIndices of
            [] -> Nothing
            indices -> Just (minimum indices)
        in
          case minIndex of
            Nothing -> Nothing
            Just idx ->
              let aboveIndex = idx - 1
              in
                if aboveIndex >= 0 && aboveIndex < length orderedLayerIds
                  then case drop aboveIndex orderedLayerIds of
                    [] -> Nothing
                    layerId:_ -> Just layerId
                  else Nothing

-- | Compute layer below current selection
-- Pure function: takes selected layer IDs set, ordered layer IDs list, returns new selection
computeLayerBelowSelection ::
  HashSet Text ->
  [Text] ->
  Maybe Text
computeLayerBelowSelection selectedLayerIds orderedLayerIds =
  if null orderedLayerIds
    then Nothing
    else if HS.null selectedLayerIds
      then case orderedLayerIds of
        [] -> Nothing
        _ -> case reverse orderedLayerIds of
          [] -> Nothing
          (lastLayer:remainingLayers) -> Just lastLayer  -- Explicit pattern match
      else
        let
          -- Find the bottommost (maximum index) selected layer
          selectedIndices = mapMaybe (\id_ -> findIndexInList id_ orderedLayerIds) (HS.toList selectedLayerIds)
          maxIndex = case selectedIndices of
            [] -> Nothing
            indices -> Just (maximum indices)
        in
          case maxIndex of
            Nothing -> Nothing
            Just idx ->
              let belowIndex = idx + 1
              in
                if belowIndex >= 0 && belowIndex < length orderedLayerIds
                  then case drop belowIndex orderedLayerIds of
                    [] -> Nothing
                    layerId:_ -> Just layerId
                  else Nothing

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // internal // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Find index of element in list (returns Nothing if not found)
findIndexInList ::
  Eq a =>
  a ->
  [a] ->
  Maybe Int
findIndexInList target list =
  case findIndexHelper target list 0 of
    Nothing -> Nothing
    Just idx -> Just idx
  where
    findIndexHelper :: Eq a => a -> [a] -> Int -> Maybe Int
    findIndexHelper _ [] _ = Nothing
    findIndexHelper t (x:xs) idx =
      if t == x
        then Just idx
        else findIndexHelper t xs (idx + 1)
