-- |
-- Module      : Lattice.State.Layer.CRUD
-- Description : CRUD operations for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for creating, reading, updating, and deleting layers
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.CRUD
  ( regenerateKeyframeIds
  , createLayer
  , deleteLayer
  , updateLayer
  , cleanUpLayerReferences
  , renameLayer
  , moveLayer
  , duplicateLayer
  , updateLayerTransform
  ) where

import Data.List (findIndex, splitAt)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.State.Layer.Types (CreateLayerOptions(..))
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , PropertyType(..)
  , createAnimatableProperty
  )
import Lattice.Types.Layer
  ( Layer(..)
  , LayerType(..)
  , LayerData(..)
  , LayerAudio(..)
  , FollowPathConstraint(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  , BlendMode(..)
  , validateFinite
  )
import Lattice.Types.Transform
  ( LayerTransform(..)
  , createDefaultTransform
  )
import Lattice.Types.LayerDataText (TextData(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // pure // transformations
-- ════════════════════════════════════════════════════════════════════════════

-- | Regenerate all keyframe IDs in a layer to avoid conflicts
-- Pure function: takes layer and ID generator function, returns new layer with regenerated keyframe IDs
--                                                                      // note
regenerateKeyframeIds ::
  (Text -> Text) ->  -- ID generator function (pure) - takes old ID, returns new ID
  Layer ->
  Layer
regenerateKeyframeIds generateId layer =
  let
    -- Regenerate keyframe IDs in an AnimatableProperty
    regeneratePropertyKeyframes ::
      AnimatableProperty a ->
      AnimatableProperty a
    regeneratePropertyKeyframes prop =
      prop
        { animatablePropertyKeyframes =
            map
              (\kf -> kf {keyframeId = generateId (keyframeId kf)})
              (animatablePropertyKeyframes prop)
        }
    
    -- Regenerate keyframe IDs in a Maybe AnimatableProperty
    regenerateMaybePropertyKeyframes ::
      Maybe (AnimatableProperty a) ->
      Maybe (AnimatableProperty a)
    regenerateMaybePropertyKeyframes mProp =
      fmap regeneratePropertyKeyframes mProp
    
    -- Regenerate transform keyframe IDs
    transform = layerTransform layer
    newTransform =
      LayerTransform
        { transformPosition = regeneratePropertyKeyframes (transformPosition transform),
          transformPositionX = regenerateMaybePropertyKeyframes (transformPositionX transform),
          transformPositionY = regenerateMaybePropertyKeyframes (transformPositionY transform),
          transformPositionZ = regenerateMaybePropertyKeyframes (transformPositionZ transform),
          transformOrigin = regeneratePropertyKeyframes (transformOrigin transform),
          transformAnchorPoint = fmap regeneratePropertyKeyframes (transformAnchorPoint transform),
          transformScale = regeneratePropertyKeyframes (transformScale transform),
          transformScaleX = regenerateMaybePropertyKeyframes (transformScaleX transform),
          transformScaleY = regenerateMaybePropertyKeyframes (transformScaleY transform),
          transformScaleZ = regenerateMaybePropertyKeyframes (transformScaleZ transform),
          transformRotation = regeneratePropertyKeyframes (transformRotation transform),
          transformOrientation = regenerateMaybePropertyKeyframes (transformOrientation transform),
          transformRotationX = regenerateMaybePropertyKeyframes (transformRotationX transform),
          transformRotationY = regenerateMaybePropertyKeyframes (transformRotationY transform),
          transformRotationZ = regenerateMaybePropertyKeyframes (transformRotationZ transform),
          transformSeparateDimensions = transformSeparateDimensions transform
        }
    
    -- Regenerate keyframe IDs in layerProperties
    newProperties = map regeneratePropertyKeyframes (layerProperties layer)
  in
    layer {layerTransform = newTransform, layerProperties = newProperties}

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // crud // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a new layer
-- Pure function: takes layer ID, type, options, composition settings, layer data, and ID generators
-- Returns new layer with default values
-- Note: Layer data must be created separately (getDefaultLayerData not yet migrated)
createLayer ::
  Text -> -- Layer ID (generated at FFI boundary)
  LayerType -> -- Layer type
  CreateLayerOptions -> -- Creation options
  Double -> -- Composition width
  Double -> -- Composition height
  Int -> -- Composition frame count
  Maybe LayerData -> -- Layer-specific data (created at FFI boundary using getDefaultLayerData)
  (Text -> Text) -> -- ID generator for transform properties
  (Text -> Text) -> -- ID generator for opacity property
  (Text -> Text) -> -- ID generator for audio properties (if needed)
  Layer
createLayer layerId layerType options compWidth compHeight frameCount mLayerData genTransformId genOpacityId genAudioId =
  let
    -- Generate transform property IDs
    posId = genTransformId "position"
    originId = genTransformId "origin"
    scaleId = genTransformId "scale"
    rotId = genTransformId "rotation"
    orientId = genTransformId "orientation"
    rotXId = genTransformId "rotationX"
    rotYId = genTransformId "rotationY"
    rotZId = genTransformId "rotationZ"
    
    -- Create default transform
    defaultTransform = createDefaultTransform posId originId scaleId rotId orientId rotXId rotYId rotZId
    
    -- Center position in composition (if position not specified in options)
    centeredTransform = case createLayerOptionsPosition options of
      Just (Vec2 x y) ->
        defaultTransform
          { transformPosition =
              (transformPosition defaultTransform)
                { animatablePropertyValue = Position2DOr3D x y (Just 0.0)
                }
          }
      Nothing ->
        defaultTransform
          { transformPosition =
              (transformPosition defaultTransform)
                { animatablePropertyValue = Position2DOr3D (compWidth / 2.0) (compHeight / 2.0) (Just 0.0)
                }
          }
    
    -- Generate layer name (use provided name or default based on type and existing layer count)
    -- Note: existing layer count not available in pure function - use provided name or type-based default
    layerName_ = case createLayerOptionsName options of
      Just name -> name
      Nothing -> T.pack (show layerType) <> " Layer" -- Simplified - FFI boundary should provide proper name
    
    -- Create opacity property
    opacityId = genOpacityId "opacity"
    opacityProp = createAnimatableProperty opacityId "opacity" 100.0 PropertyTypeNumber Nothing
    
    -- Create audio properties for video/audio layers (if needed)
    mAudio = case layerType of
      LayerTypeVideo -> Just (LayerAudio (createAnimatableProperty (genAudioId "audioLevel") "Audio Levels" 0.0 PropertyTypeNumber Nothing))
      LayerTypeAudio -> Just (LayerAudio (createAnimatableProperty (genAudioId "audioLevel") "Audio Levels" 0.0 PropertyTypeNumber Nothing))
      _ -> Nothing
    
    -- Calculate frame range (default: full composition)
    endFrame_ = fromIntegral (frameCount - 1)
    
    -- Create layer
  in
    Layer
      { layerId = layerId
      , layerName = layerName_
      , layerType = layerType
      , layerVisible = True
      , layerLocked = False
      , layerIsolate = False
      , layerMinimized = Nothing
      , layerThreeD = False
      , layerAutoOrient = Nothing
      , layerFollowPath = Nothing
      , layerAudioPathAnimation = Nothing
      , layerMotionBlur = False
      , layerMotionBlurSettings = Nothing
      , layerFlattenTransform = Nothing
      , layerQuality = Nothing
      , layerEffectsEnabled = Nothing
      , layerFrameBlending = Nothing
      , layerEffectLayer = Nothing
      , layerAdjustmentLayer = Nothing
      , layerAudioEnabled = Nothing
      , layerLabelColor = Nothing
      , layerMaterialOptions = Nothing
      , layerStartFrame = 0.0
      , layerEndFrame = endFrame_
      , layerInPoint = Just 0.0
      , layerOutPoint = Just endFrame_
      , layerTimeStretch = Nothing
      , layerStretchAnchor = Nothing
      , layerParentId = createLayerOptionsParentId options
      , layerBlendMode = BlendNormal
      , layerOpacity = opacityProp
      , layerTransform = centeredTransform
      , layerAudio = mAudio
      , layerMasks = Nothing
      , layerMatteType = Nothing
      , layerMatteLayerId = Nothing
      , layerMatteCompositionId = Nothing
      , layerPreserveTransparency = Nothing
      , layerTrackMatteType = Nothing
      , layerTrackMatteLayerId = Nothing
      , layerTrackMatteCompositionId = Nothing
      , layerProperties = []
      , layerEffects = []
      , layerLayerStyles = Nothing
      , layerData = mLayerData
      }

-- | Clean up references to a deleted layer in remaining layers
-- Pure function: takes deleted layer ID and layers list, returns layers with cleaned references
cleanUpLayerReferences :: Text -> [Layer] -> [Layer]
cleanUpLayerReferences deletedLayerId layers =
  map (cleanUpLayerReference deletedLayerId) layers
  where
    cleanUpLayerReference :: Text -> Layer -> Layer
    cleanUpLayerReference deletedId layer =
      let
        -- Clear parentId if it references deleted layer
        newParentId =
          if layerParentId layer == Just deletedId
            then Nothing
            else layerParentId layer
        
        -- Clear matteLayerId and matteType if they reference deleted layer
        (newMatteLayerId, newMatteType) =
          if layerMatteLayerId layer == Just deletedId
            then (Nothing, Nothing)
            else (layerMatteLayerId layer, layerMatteType layer)
        
        -- Clear followPath.pathLayerId if it references deleted layer
        newFollowPath =
          case layerFollowPath layer of
            Just fp@(FollowPathConstraint pathLayerId param lookAhead banking offsetY alignToPath) ->
              if pathLayerId == deletedId
                then Nothing -- Disable follow path if referenced layer is deleted
                else Just fp
            Nothing -> Nothing
        
        -- Clear textData.pathLayerId if it references deleted layer
        newData =
          case (layerType layer, layerData layer) of
            (LayerTypeText, Just (LayerDataText textData)) ->
              if textDataPathLayerId textData == deletedId
                then Just (LayerDataText (textData {textDataPathLayerId = ""}))
                else layerData layer
            _ -> layerData layer
      in
        layer
          { layerParentId = newParentId,
            layerMatteLayerId = newMatteLayerId,
            layerMatteType = newMatteType,
            layerFollowPath = newFollowPath,
            layerData = newData
          }

-- | Delete a layer by ID
-- Pure function: takes layer ID and layers list, returns new layers list without the deleted layer
-- Also cleans up references to the deleted layer in remaining layers
deleteLayer :: Text -> [Layer] -> [Layer]
deleteLayer targetLayerId layers =
  let
    -- Remove the layer
    remainingLayers = filter (\l -> layerId l /= targetLayerId) layers
    
    -- Clean up references to deleted layer
    cleanedLayers = cleanUpLayerReferences targetLayerId remainingLayers
  in
    cleanedLayers

-- | Update layer properties
-- Pure function: takes layer ID, update function, and layers list, returns new layers list with updated layer
-- Note: Locked layers can only have their 'locked' property changed
-- The update function receives the existing layer and returns the updated layer
updateLayer :: Text -> (Layer -> Layer) -> [Layer] -> Either Text [Layer]
updateLayer targetLayerId updateFn layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      -- If layer is locked, check if update is only changing 'locked' property
      if layerLocked existingLayer
        then
          let
            updatedLayer = updateFn existingLayer
            -- Check if only 'locked' property changed
            onlyLockedChanged =
              layerLocked updatedLayer /= layerLocked existingLayer &&
              -- All other fields should be the same
              layerName updatedLayer == layerName existingLayer &&
              layerType updatedLayer == layerType existingLayer &&
              layerVisible updatedLayer == layerVisible existingLayer &&
              layerIsolate updatedLayer == layerIsolate existingLayer &&
              layerThreeD updatedLayer == layerThreeD existingLayer
          in
            if onlyLockedChanged
              then Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              else Left ("Cannot update locked layer (only 'locked' property can change): " <> targetLayerId)
        else
          -- Layer is not locked, apply update
          let updatedLayer = updateFn existingLayer
          in Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)

-- | Rename a layer by ID
-- Pure function: takes layer ID, new name, and layers list, returns new layers list with renamed layer
-- Note: Cannot rename locked layers, name must not be empty
renameLayer :: Text -> Text -> [Layer] -> Either Text [Layer]
renameLayer targetLayerId newName layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      -- Cannot rename locked layers
      if layerLocked existingLayer
        then Left ("Cannot rename locked layer: " <> targetLayerId)
        else
          -- Validate name is not empty (after trimming)
          let trimmedName = T.strip newName
          in
            if T.null trimmedName
              then Left ("Cannot rename layer to empty name: " <> targetLayerId)
              else Right (map (\l -> if layerId l == targetLayerId then l {layerName = trimmedName} else l) layers)

-- | Reorder layers by moving a layer to a new index
-- Pure function: takes layer ID, new index, and layers list, returns reordered layers list
-- Clamps index to valid range [0, length-1]
moveLayer :: Text -> Int -> [Layer] -> Either Text [Layer]
moveLayer targetLayerId newIndex layers =
  if newIndex < 0
    then Left ("moveLayer: Invalid index (must be non-negative): " <> T.pack (show newIndex))
    else
      case findIndex (\l -> layerId l == targetLayerId) layers of
        Nothing -> Left ("Layer not found: " <> targetLayerId)
        Just currentIndex ->
          let
            -- Clamp index to valid range
            clampedIndex = min newIndex (length layers - 1)
            
            -- Remove layer from current position
            (before, after) = splitAt currentIndex layers
          in
            case after of
              [] -> Left ("moveLayer: Internal error - layer found but list is empty")
              (layerToMove : rest) ->
                let
                  remainingLayers = before ++ rest
                  
                  -- Insert at new position
                  -- Adjust clampedIndex if moving forward (to account for removed element)
                  adjustedIndex = if clampedIndex > currentIndex then clampedIndex - 1 else clampedIndex
                  (beforeNew, afterNew) = splitAt adjustedIndex remainingLayers
                  newLayers = beforeNew ++ [layerToMove] ++ afterNew
                in
                  Right newLayers

-- | Duplicate a layer
-- Pure function: takes layer ID, new layer ID generator, and layers list
-- Returns new layers list with duplicated layer inserted after original
-- Note: Regenerates all keyframe IDs to avoid conflicts
duplicateLayer ::
  Text -> -- Original layer ID
  (Text -> Text) -> -- ID generator for new layer ID
  (Text -> Text) -> -- ID generator for regenerating keyframe IDs
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with duplicate, or error if layer not found
duplicateLayer originalLayerId genLayerId genKeyframeId layers =
  case getLayerById layers originalLayerId of
    Nothing -> Left ("Layer not found: " <> originalLayerId)
    Just originalLayer ->
      let
        -- Generate new layer ID
        newLayerId = genLayerId originalLayerId
        
        -- Duplicate layer with new ID and name
        duplicatedLayer = originalLayer
          { layerId = newLayerId
          , layerName = layerName originalLayer <> " Copy"
          }
        
        -- Regenerate all keyframe IDs in the duplicated layer
        layerWithNewKeyframes = regenerateKeyframeIds genKeyframeId duplicatedLayer
        
        -- Find insertion index (after original)
        -- Layer existence already verified by getLayerById above
        -- Since getLayerById succeeded, findIndex must also succeed
        -- Use explicit pattern matching to make this clear
        insertionIndexResult = case findIndex (\l -> layerId l == originalLayerId) layers of
          Just idx -> Right (idx + 1)
          Nothing -> 
            -- Logic error: layer was found by getLayerById but not by findIndex
            -- This indicates a data integrity issue - should never happen
            -- Return Left to make this explicit (no error, use Either)
            Left ("duplicateLayer: Logic error - layer \"" <> originalLayerId <> "\" found by getLayerById but not by findIndex. This indicates a data integrity violation.")
      in
        case insertionIndexResult of
          Left err -> Left err
          Right insertionIndex ->
            let
              -- Insert duplicated layer at insertion index
              (before, after) = splitAt insertionIndex layers
              newLayers = before ++ [layerWithNewKeyframes] ++ after
            in
              Right newLayers

-- | Update layer transform properties (position, scale, rotation, opacity, origin/anchor)
-- Pure function: takes layer ID, transform updates, and layers list
-- Returns new layers list with updated transform, or error if layer not found or locked
-- Validates all numeric values are finite and in valid ranges
updateLayerTransform ::
  Text -> -- Layer ID
  Maybe (Vec2, Maybe Double) -> -- Position update (x, y, z?)
  Maybe Vec3 -> -- Scale update (x, y, z)
  Maybe Double -> -- Rotation update
  Maybe Double -> -- Opacity update (0-100)
  Maybe (Vec2, Maybe Double) -> -- Origin/anchor update (x, y, z?)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with updated transform, or error
updateLayerTransform targetLayerId mPosition mScale mRotation mOpacity mOrigin layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      -- Cannot update transform of locked layers
      if layerLocked existingLayer
        then Left ("Cannot update transform of locked layer: " <> targetLayerId)
        else
          let
            transform = layerTransform existingLayer
            
            -- Update position if provided
            newPosition = case mPosition of
              Nothing -> transformPosition transform
              Just (Vec2 x y, mZ) ->
                -- Validate finite
                if validateFinite x && validateFinite y && maybe True validateFinite mZ
                  then (transformPosition transform)
                    { animatablePropertyValue = Position2DOr3D x y mZ
                    }
                  else transformPosition transform -- Invalid values, keep original
            
            -- Update scale if provided
            newScale = case mScale of
              Nothing -> transformScale transform
              Just (Vec3 x y z) ->
                -- Validate finite and non-negative (scale should be positive)
                if validateFinite x && validateFinite y && validateFinite z &&
                   x >= 0 && y >= 0 && z >= 0
                  then (transformScale transform)
                    { animatablePropertyValue = Vec3 x y z
                    }
                  else transformScale transform -- Invalid values, keep original
            
            -- Update rotation if provided
            newRotation = case mRotation of
              Nothing -> transformRotation transform
              Just rot ->
                -- Validate finite
                if validateFinite rot
                  then (transformRotation transform)
                    { animatablePropertyValue = rot
                    }
                  else transformRotation transform -- Invalid values, keep original
            
            -- Update origin if provided
            newOrigin = case mOrigin of
              Nothing -> transformOrigin transform
              Just (Vec2 x y, mZ) ->
                -- Validate finite
                if validateFinite x && validateFinite y && maybe True validateFinite mZ
                  then (transformOrigin transform)
                    { animatablePropertyValue = Position2DOr3D x y mZ
                    }
                  else transformOrigin transform -- Invalid values, keep original
            
            -- Update opacity if provided (opacity is at layer level, not transform)
            newOpacity = case mOpacity of
              Nothing -> layerOpacity existingLayer
              Just op ->
                -- Validate finite and in range [0, 100]
                if validateFinite op && op >= 0 && op <= 100
                  then (layerOpacity existingLayer)
                    { animatablePropertyValue = op
                    }
                  else layerOpacity existingLayer -- Invalid values, keep original
            
            -- Create updated transform
            updatedTransform = transform
              { transformPosition = newPosition
              , transformScale = newScale
              , transformRotation = newRotation
              , transformOrigin = newOrigin
              }
            
            -- Create updated layer
            updatedLayer = existingLayer
              { layerTransform = updatedTransform
              , layerOpacity = newOpacity
              }
          in
            Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
