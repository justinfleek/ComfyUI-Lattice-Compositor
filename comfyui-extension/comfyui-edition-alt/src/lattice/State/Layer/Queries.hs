-- |
-- Module      : Lattice.State.Layer.Queries
-- Description : Query functions for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure query functions for finding and filtering layers
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Queries
  ( -- Hierarchy queries
    getLayerById
  , getLayerChildren
  , getLayerDescendants
  , getVisibleLayers
  , getDisplayedLayers
  , getRootLayers
  , getCameraLayers
  , getSelectedLayers
  , getSelectedLayer
  -- Spline queries
  , isSplineAnimated
  , hasSplinePointKeyframes
  ) where

import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import Data.Maybe (Maybe(..), isJust)
import Data.Text (Text)
import Lattice.Types.Layer
  ( Layer(..)
  , LayerType(..)
  , LayerData(..)
  )
import Lattice.Types.Animation (AnimatableProperty(..))
import Lattice.Types.LayerDataSpline
  ( SplineData(..)
  , AnimatableControlPoint(..)
  , AnimatableHandle(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // hierarchy // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Get a layer by ID from a list of layers
-- Pure function: takes layers list and ID, returns layer or Nothing
getLayerById ::
  [Layer] ->
  Text ->
  Maybe Layer
getLayerById layers targetId =
  case filter (\l -> layerId l == targetId) layers of
    [] -> Nothing
    (l : _) -> Just l  -- Return first match (IDs should be unique, but defensive)

-- | Get all children of a layer
-- Pure function: takes layers list and parent ID, returns child layers
getLayerChildren ::
  [Layer] ->
  Text ->
  [Layer]
getLayerChildren layers parentId =
  filter (\l -> layerParentId l == Just parentId) layers

-- | Get all descendants of a layer (recursive)
-- Pure function: takes layers list and ancestor ID, returns all descendant layers
getLayerDescendants ::
  [Layer] ->
  Text ->
  [Layer]
getLayerDescendants layers ancestorId =
  let
    children = getLayerChildren layers ancestorId
    childDescendants = concatMap (\child -> getLayerDescendants layers (layerId child)) children
  in
    children ++ childDescendants

-- | Get all visible layers
-- Pure function: takes layers list, returns visible layers
getVisibleLayers ::
  [Layer] ->
  [Layer]
getVisibleLayers = filter layerVisible

-- | Get layers displayed in timeline (respects minimized filter)
-- Pure function: takes layers list and hideMinimized flag, returns displayed layers
getDisplayedLayers ::
  [Layer] ->
  Bool ->
  [Layer]
getDisplayedLayers layers hideMinimized =
  if hideMinimized
    then filter (\l -> maybe True not (layerMinimized l)) layers
    else layers

-- | Get root layers (layers with no parent)
-- Pure function: takes layers list, returns root layers
getRootLayers ::
  [Layer] ->
  [Layer]
getRootLayers = filter (\l -> layerParentId l == Nothing)

-- | Get all camera layers
-- Pure function: takes layers list, returns camera layers
getCameraLayers ::
  [Layer] ->
  [Layer]
getCameraLayers = filter (\l -> layerType l == LayerTypeCamera)

-- | Get all selected layers
-- Pure function: takes layers list and selected IDs set, returns selected layers
getSelectedLayers ::
  [Layer] ->
  HashSet Text ->
  [Layer]
getSelectedLayers layers selectedIds =
  filter (\l -> HS.member (layerId l) selectedIds) layers

-- | Get the single selected layer (returns Nothing if 0 or 2+ layers selected)
-- Pure function: takes layers list and selected IDs set, returns single selected layer or Nothing
getSelectedLayer ::
  [Layer] ->
  HashSet Text ->
  Maybe Layer
getSelectedLayer layers selectedIds =
  if HS.size selectedIds == 1
    then case HS.toList selectedIds of
      [id_] -> getLayerById layers id_
      [] -> Nothing  -- Empty HashSet with size 1 is impossible, but type-safe fallback
      (_ : _ : _) -> Nothing  -- Multiple elements with size 1 is impossible, but type-safe fallback
    else Nothing

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // spline // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Check if a spline layer has animation enabled
-- Pure function: takes layer, returns True if animation is enabled
isSplineAnimated :: Layer -> Bool
isSplineAnimated layer =
  case (layerType layer, layerData layer) of
    (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
      maybe False id (splineDataAnimated splineData)
    _ -> False

-- | Check if a control point has any keyframes
-- Pure function: takes layer and point ID, returns True if point has keyframes
hasSplinePointKeyframes :: Layer -> Text -> Bool
hasSplinePointKeyframes layer pointId =
  case (layerType layer, layerData layer) of
    (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
      case splineDataAnimatedControlPoints splineData of
        Just animatedPoints ->
          case filter (\acp -> animatableControlPointId acp == pointId) animatedPoints of
            [] -> False
            [point] ->
              -- Check if any property has keyframes
              not (null (animatablePropertyKeyframes (animatableControlPointX point))) ||
              not (null (animatablePropertyKeyframes (animatableControlPointY point))) ||
              maybe False (\d -> not (null (animatablePropertyKeyframes d))) (animatableControlPointDepth point) ||
              maybe False (\(AnimatableHandle hx hy) ->
                not (null (animatablePropertyKeyframes hx)) ||
                not (null (animatablePropertyKeyframes hy))
              ) (animatableControlPointHandleIn point) ||
              maybe False (\(AnimatableHandle hx hy) ->
                not (null (animatablePropertyKeyframes hx)) ||
                not (null (animatablePropertyKeyframes hy))
              ) (animatableControlPointHandleOut point)
            _ -> False
        Nothing -> False
    _ -> False
