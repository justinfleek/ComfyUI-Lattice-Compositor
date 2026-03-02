-- |
-- Module      : Lattice.State.Layer.Hierarchy
-- Description : Hierarchy operations for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for layer parenting and 3D mode
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Hierarchy
  ( setLayerParent
  , toggleLayer3D
  ) where

import Data.Text (Text)
import Lattice.State.Layer.Queries (getLayerById, getLayerDescendants)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , PropertyType(..)
  , createAnimatableProperty
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives (Vec3(..))
import Lattice.Types.Transform
  ( LayerTransform(..)
  , Position2DOr3D(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hierarchy // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Set a layer's parent for parenting/hierarchy
-- Pure function: takes layer ID, parent ID (or Nothing to unparent), and layers list
-- Returns new layers list with updated parent, or error if layer not found or circular reference
-- Prevents self-parenting and circular parenting
setLayerParent ::
  Text -> -- Child layer ID
  Maybe Text -> -- Parent layer ID (Nothing to unparent)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with updated parent, or error
setLayerParent childLayerId mParentId layers =
  case getLayerById layers childLayerId of
    Nothing -> Left ("Layer not found: " <> childLayerId)
    Just childLayer ->
      -- Prevent self-parenting
      case mParentId of
        Just parentId ->
          if parentId == childLayerId
            then Left ("Cannot set parent: layer cannot be its own parent")
            else
              -- Prevent circular parenting
              let
                descendants = getLayerDescendants layers childLayerId
                descendantIds = map layerId descendants
              in
                if parentId `elem` descendantIds
                  then Left ("Cannot set parent: would create circular reference")
                  else Right (map (\l -> if layerId l == childLayerId then l {layerParentId = mParentId} else l) layers)
        Nothing ->
          -- Unparenting is always safe
          Right (map (\l -> if layerId l == childLayerId then l {layerParentId = Nothing} else l) layers)

-- | Toggle a layer between 2D and 3D modes
-- Pure function: takes layer ID, ID generators for 3D rotation properties, and layers list
-- Returns new layers list with toggled 3D state, or error if layer not found
-- When enabling 3D, ensures position, origin, and scale have z component, and initializes 3D rotations
-- When disabling 3D, maps Z rotation back to standard rotation
toggleLayer3D ::
  Text -> -- Layer ID
  (Text -> Text) -> -- ID generator for orientation property
  (Text -> Text) -> -- ID generator for rotationX property
  (Text -> Text) -> -- ID generator for rotationY property
  (Text -> Text) -> -- ID generator for rotationZ property
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with toggled 3D state, or error if layer not found
toggleLayer3D targetLayerId genOrientId genRotXId genRotYId genRotZId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      let
        currentThreeD = layerThreeD existingLayer
        newThreeD = not currentThreeD
        transform = layerTransform existingLayer
        
        -- When enabling 3D, ensure position, origin have z component and initialize 3D rotations
        (newPosition, newOrigin, newOrientation, newRotX, newRotY, newRotZ, newRotation) =
          if newThreeD && not currentThreeD
            then
              let
                pos = transformPosition transform
                posVal = animatablePropertyValue pos
                -- Ensure z component exists
                posValWithZ = case posVal of
                  Position2DOr3D x y mZ -> Position2DOr3D x y (Just (maybe 0.0 id mZ))
                newPos = pos {animatablePropertyValue = posValWithZ}
                
                origin = transformOrigin transform
                originVal = animatablePropertyValue origin
                -- Ensure z component exists
                originValWithZ = case originVal of
                  Position2DOr3D x y mZ -> Position2DOr3D x y (Just (maybe 0.0 id mZ))
                newOrig = origin {animatablePropertyValue = originValWithZ}
                
                -- Initialize 3D rotations if they don't exist
                newOrient = case transformOrientation transform of
                  Just _ -> transformOrientation transform
                  Nothing -> Just (createAnimatableProperty (genOrientId "orientation") "orientation" (Vec3 0.0 0.0 0.0) PropertyTypeVector3 Nothing)
                
                newRX = case transformRotationX transform of
                  Just _ -> transformRotationX transform
                  Nothing -> Just (createAnimatableProperty (genRotXId "rotationX") "rotationX" 0.0 PropertyTypeNumber Nothing)
                
                newRY = case transformRotationY transform of
                  Just _ -> transformRotationY transform
                  Nothing -> Just (createAnimatableProperty (genRotYId "rotationY") "rotationY" 0.0 PropertyTypeNumber Nothing)
                
                newRZ = case transformRotationZ transform of
                  Just _ -> transformRotationZ transform
                  Nothing ->
                    let
                      rot2D = transformRotation transform
                      rot2DVal = animatablePropertyValue rot2D
                    in
                      Just (createAnimatableProperty (genRotZId "rotationZ") "rotationZ" rot2DVal PropertyTypeNumber Nothing)
              in
                (newPos, newOrig, newOrient, newRX, newRY, newRZ, transformRotation transform)
            else
              -- Disabling 3D - map Z rotation back to standard rotation if needed
              if not newThreeD && currentThreeD
                then
                  case transformRotationZ transform of
                    Just rotZ ->
                      let
                        rot2D = transformRotation transform
                        rotZVal = animatablePropertyValue rotZ
                      in
                        (transformPosition transform, transformOrigin transform, transformOrientation transform, transformRotationX transform, transformRotationY transform, Nothing, rot2D {animatablePropertyValue = rotZVal})
                    Nothing ->
                      (transformPosition transform, transformOrigin transform, transformOrientation transform, transformRotationX transform, transformRotationY transform, transformRotationZ transform, transformRotation transform)
                else
                  (transformPosition transform, transformOrigin transform, transformOrientation transform, transformRotationX transform, transformRotationY transform, transformRotationZ transform, transformRotation transform)
        
        updatedTransform = transform
          { transformPosition = newPosition
          , transformOrigin = newOrigin
          , transformOrientation = newOrientation
          , transformRotationX = newRotX
          , transformRotationY = newRotY
          , transformRotationZ = newRotZ
          , transformRotation = newRotation
          }
        
        updatedLayer = existingLayer
          { layerThreeD = newThreeD
          , layerTransform = updatedTransform
          }
      in
        Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
