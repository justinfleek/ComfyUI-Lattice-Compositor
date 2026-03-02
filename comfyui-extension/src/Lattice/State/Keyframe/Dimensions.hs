-- |
-- Module      : Lattice.State.Keyframe.Dimensions
-- Description : Separate dimensions operations
--
-- Migrated from ui/src/stores/keyframeStore/dimensions.ts
-- Pure functions for separating and linking position/scale dimensions
--
-- NOTE: Full implementation requires interpolation utilities for merging keyframes
-- This is a simplified version that handles the core separation/linking logic
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Dimensions
  ( separatePositionDimensionsAction
  , linkPositionDimensionsAction
  , separateScaleDimensionsAction
  , linkScaleDimensionsAction
  , hasPositionSeparated
  , hasScaleSeparated
  ) where

import Data.List (find, nub, sort)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , Keyframe(..)
  , PropertyType(..)
  , PropertyValue(..)
  , createAnimatableProperty
  , createKeyframe
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives
  ( Position2DOr3D(..)
  , Vec2(..)
  , Vec3(..)
  , validateFinite
  )
import Lattice.Types.Transform
  ( LayerTransform(..)
  , SeparateDimensions(..)
  )

-- ============================================================================
-- SEPARATE DIMENSIONS
-- ============================================================================

-- | Separate position into individual X, Y, Z properties for independent keyframing
-- Pure function: takes layer ID, ID generator, and layers list
-- Returns updated layers list or error
-- After separation, positionX, positionY, positionZ can have different keyframes
separatePositionDimensionsAction ::
  Text -> -- Layer ID
  (Text -> Text) -> -- ID generator
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
separatePositionDimensionsAction targetLayerId genId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Right layers
    Just layer ->
      let
        transform = layerTransform layer
        positionProp = transformPosition transform
        currentValue = animatablePropertyValue positionProp
        
        -- Extract x, y, z values
        xVal = position2DOr3DX currentValue
        yVal = position2DOr3DY currentValue
        zVal = case position2DOr3DZ currentValue of
          Nothing -> 0.0
          Just z -> z
        
        -- Create separate X, Y, Z properties
        posXId = genId ("positionX_" <> targetLayerId)
        posYId = genId ("positionY_" <> targetLayerId)
        posZId = genId ("positionZ_" <> targetLayerId)
        
        posXProp = createAnimatableProperty posXId "Position X" xVal PropertyTypeNumber Nothing
        posYProp = createAnimatableProperty posYId "Position Y" yVal PropertyTypeNumber Nothing
        posZProp = createAnimatableProperty posZId "Position Z" zVal PropertyTypeNumber Nothing
        
        -- Copy keyframes to separate properties if animated
        mKeyframesResult =
          if animatablePropertyAnimated positionProp && not (null (animatablePropertyKeyframes positionProp))
            then
              let
                keyframes = animatablePropertyKeyframes positionProp
                -- Convert Position2DOr3D keyframes to Double keyframes for each component
                -- Note: keyframeValue is Position2DOr3D, not PropertyValue
                mXKeyframes = traverse (\kf ->
                  let
                    posValue = position2DOr3DX (keyframeValue kf)
                    newId = genId (keyframeId kf <> "_x")
                  in
                    createKeyframe newId (keyframeFrame kf) posValue (keyframeInterpolation kf)
                  ) keyframes
                
                mYKeyframes = traverse (\kf ->
                  let
                    posValue = position2DOr3DY (keyframeValue kf)
                    newId = genId (keyframeId kf <> "_y")
                  in
                    createKeyframe newId (keyframeFrame kf) posValue (keyframeInterpolation kf)
                  ) keyframes
                
                mZKeyframes = traverse (\kf ->
                  let
                    posValue = case position2DOr3DZ (keyframeValue kf) of
                      Nothing -> zVal
                      Just z -> z
                    newId = genId (keyframeId kf <> "_z")
                  in
                    createKeyframe newId (keyframeFrame kf) posValue (keyframeInterpolation kf)
                  ) keyframes
              in
                case (mXKeyframes, mYKeyframes, mZKeyframes) of
                  (Right xKeyframes, Right yKeyframes, Right zKeyframes) ->
                    Right ( posXProp {animatablePropertyAnimated = True, animatablePropertyKeyframes = xKeyframes}
                          , posYProp {animatablePropertyAnimated = True, animatablePropertyKeyframes = yKeyframes}
                          , posZProp {animatablePropertyAnimated = True, animatablePropertyKeyframes = zKeyframes}
                          )
                  (Left err, _, _) -> Left ("Failed to create X keyframes: " <> err)
                  (_, Left err, _) -> Left ("Failed to create Y keyframes: " <> err)
                  (_, _, Left err) -> Left ("Failed to create Z keyframes: " <> err)
            else Right (posXProp, posYProp, posZProp)
        
        -- Update transform with separate dimensions flag
        currentSepDim = transformSeparateDimensions transform
        newSepDim = case currentSepDim of
          Nothing -> Just (SeparateDimensions True False)
          Just sd -> Just (sd {separateDimensionsPosition = True})
      in
        case mKeyframesResult of
          Left err -> Left err
          Right (posXWithKeyframes, posYWithKeyframes, posZWithKeyframes) ->
            let
              newTransform = transform
                { transformPositionX = Just posXWithKeyframes
                , transformPositionY = Just posYWithKeyframes
                , transformPositionZ = Just posZWithKeyframes
                , transformSeparateDimensions = newSepDim
                }
              
              updatedLayer = layer {layerTransform = newTransform}
              updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
            in
              Right updatedLayers

-- | Link position dimensions back into a combined property
-- Pure function: takes layer ID, ID generator, and layers list
-- Returns updated layers list or error
-- Merges X, Y, Z keyframes at each unique frame
linkPositionDimensionsAction ::
  Text -> -- Layer ID
  (Text -> Text) -> -- ID generator
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
linkPositionDimensionsAction targetLayerId genId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Right layers
    Just layer ->
      let
        transform = layerTransform layer
        mPosX = transformPositionX transform
        mPosY = transformPositionY transform
        mPosZ = transformPositionZ transform
      in
        case (mPosX, mPosY) of
          (Nothing, _) -> Right layers
          (_, Nothing) -> Right layers
          (Just posX, Just posY) ->
            let
              -- Get current values
              xVal = animatablePropertyValue posX
              yVal = animatablePropertyValue posY
              zVal = case mPosZ of
                Nothing -> 0.0
                Just posZ -> animatablePropertyValue posZ
              
              -- Collect all unique frames from X, Y, Z keyframes
              xFrames = map keyframeFrame (animatablePropertyKeyframes posX)
              yFrames = map keyframeFrame (animatablePropertyKeyframes posY)
              zFrames = case mPosZ of
                Nothing -> []
                Just posZ -> map keyframeFrame (animatablePropertyKeyframes posZ)
              
              allFrames = sort (nub (xFrames ++ yFrames ++ zFrames))
              
              -- Create combined keyframes at each frame
              -- NOTE: This is simplified - full implementation would interpolate when keyframe doesn't exist
              mCombinedKeyframes = traverse (\frame ->
                let
                  -- Find keyframes at this frame (or use property value if none)
                  xKf = find (\kf -> keyframeFrame kf == frame) (animatablePropertyKeyframes posX)
                  yKf = find (\kf -> keyframeFrame kf == frame) (animatablePropertyKeyframes posY)
                  zKf = case mPosZ of
                    Nothing -> Nothing
                    Just posZ -> find (\kf -> keyframeFrame kf == frame) (animatablePropertyKeyframes posZ)
                  
                  -- Get values (use property value if no keyframe at this frame)
                  -- Note: keyframeValue for Double properties returns Double
                  xValAtFrame = case xKf of
                    Nothing -> xVal
                    Just kf -> keyframeValue kf
                  
                  yValAtFrame = case yKf of
                    Nothing -> yVal
                    Just kf -> keyframeValue kf
                  
                  zValAtFrame = case zKf of
                    Nothing -> zVal
                    Just kf -> keyframeValue kf
                  
                  -- Create combined Position2DOr3D value
                  combinedValue = Position2DOr3D xValAtFrame yValAtFrame (Just zValAtFrame)
                  
                  -- Use first available keyframe as template for interpolation/handles
                  templateKf = case (xKf, yKf, zKf) of
                    (Just kf, _, _) -> Just kf
                    (_, Just kf, _) -> Just kf
                    (_, _, Just kf) -> Just kf
                    _ -> Nothing
                  
                  -- Create combined keyframe
                  newId = genId ("kf_pos_" <> T.pack (show (floor frame)))
                  interp = case templateKf of
                    Nothing -> InterpolationBase InterpolationLinear
                    Just kf -> keyframeInterpolation kf
                in
                  createKeyframe newId frame (Position2DOr3D xValAtFrame yValAtFrame (Just zValAtFrame)) interp
                ) allFrames
              
              -- Create updated position property
              updatedPositionProp = (transformPosition transform)
                { animatablePropertyValue = Position2DOr3D xVal yVal (Just zVal)
                , animatablePropertyAnimated = case mCombinedKeyframes of
                    Right kfs -> not (null kfs)
                    Left _ -> False
                , animatablePropertyKeyframes = case mCombinedKeyframes of
                    Right kfs -> kfs
                    Left _ -> []
                }
              
              -- Update transform (clear separate properties, update flag)
              currentSepDim = transformSeparateDimensions transform
              newSepDim = case currentSepDim of
                Nothing -> Nothing
                Just sd -> Just (sd {separateDimensionsPosition = False})
              
              newTransform = transform
                { transformPosition = updatedPositionProp
                , transformPositionX = Nothing
                , transformPositionY = Nothing
                , transformPositionZ = Nothing
                , transformSeparateDimensions = newSepDim
                }
              
              updatedLayer = layer {layerTransform = newTransform}
              updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
            in
              Right updatedLayers

-- | Separate scale into individual X, Y, Z properties
-- Pure function: takes layer ID, ID generator, and layers list
-- Returns updated layers list or error
separateScaleDimensionsAction ::
  Text -> -- Layer ID
  (Text -> Text) -> -- ID generator
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
separateScaleDimensionsAction targetLayerId genId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Right layers
    Just layer ->
      let
        transform = layerTransform layer
        scaleProp = transformScale transform
        currentValue = animatablePropertyValue scaleProp
        
        -- Extract x, y, z values (scale always has z)
        xVal = vec3X currentValue
        yVal = vec3Y currentValue
        zVal = vec3Z currentValue
        
        -- Create separate X, Y, Z properties
        scaleXId = genId ("scaleX_" <> targetLayerId)
        scaleYId = genId ("scaleY_" <> targetLayerId)
        scaleZId = genId ("scaleZ_" <> targetLayerId)
        
        scaleXProp = createAnimatableProperty scaleXId "Scale X" xVal PropertyTypeNumber Nothing
        scaleYProp = createAnimatableProperty scaleYId "Scale Y" yVal PropertyTypeNumber Nothing
        scaleZProp = createAnimatableProperty scaleZId "Scale Z" zVal PropertyTypeNumber Nothing
        
        -- Copy keyframes to separate properties if animated
        mScaleKeyframesResult =
          if animatablePropertyAnimated scaleProp && not (null (animatablePropertyKeyframes scaleProp))
            then
              let
                keyframes = animatablePropertyKeyframes scaleProp
                -- Convert Vec3 keyframes to Double keyframes for each component
                -- Note: keyframeValue is Vec3, not PropertyValue
                mXKeyframes = traverse (\kf ->
                  let
                    vecValue = vec3X (keyframeValue kf)
                    newId = genId (keyframeId kf <> "_x")
                  in
                    createKeyframe newId (keyframeFrame kf) vecValue (keyframeInterpolation kf)
                  ) keyframes
                
                mYKeyframes = traverse (\kf ->
                  let
                    vecValue = vec3Y (keyframeValue kf)
                    newId = genId (keyframeId kf <> "_y")
                  in
                    createKeyframe newId (keyframeFrame kf) vecValue (keyframeInterpolation kf)
                  ) keyframes
                
                mZKeyframes = traverse (\kf ->
                  let
                    vecValue = vec3Z (keyframeValue kf)
                    newId = genId (keyframeId kf <> "_z")
                  in
                    createKeyframe newId (keyframeFrame kf) vecValue (keyframeInterpolation kf)
                  ) keyframes
              in
                case (mXKeyframes, mYKeyframes, mZKeyframes) of
                  (Right xKeyframes, Right yKeyframes, Right zKeyframes) ->
                    Right ( scaleXProp {animatablePropertyAnimated = True, animatablePropertyKeyframes = xKeyframes}
                          , scaleYProp {animatablePropertyAnimated = True, animatablePropertyKeyframes = yKeyframes}
                          , scaleZProp {animatablePropertyAnimated = True, animatablePropertyKeyframes = zKeyframes}
                          )
                  (Left err, _, _) -> Left ("Failed to create X keyframes: " <> err)
                  (_, Left err, _) -> Left ("Failed to create Y keyframes: " <> err)
                  (_, _, Left err) -> Left ("Failed to create Z keyframes: " <> err)
            else Right (scaleXProp, scaleYProp, scaleZProp)
        
        -- Update transform with separate dimensions flag
        currentSepDim = transformSeparateDimensions transform
        newSepDim = case currentSepDim of
          Nothing -> Just (SeparateDimensions False True)
          Just sd -> Just (sd {separateDimensionsScale = True})
      in
        case mScaleKeyframesResult of
          Left err -> Left err
          Right (scaleXWithKeyframes, scaleYWithKeyframes, scaleZWithKeyframes) ->
            let
              newTransform = transform
                { transformScaleX = Just scaleXWithKeyframes
                , transformScaleY = Just scaleYWithKeyframes
                , transformScaleZ = Just scaleZWithKeyframes
                , transformSeparateDimensions = newSepDim
                }
              
              updatedLayer = layer {layerTransform = newTransform}
              updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
            in
              Right updatedLayers

-- | Link scale dimensions back into a combined property
-- Pure function: takes layer ID, ID generator, and layers list
-- Returns updated layers list or error
linkScaleDimensionsAction ::
  Text -> -- Layer ID
  (Text -> Text) -> -- ID generator
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
linkScaleDimensionsAction targetLayerId genId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Right layers
    Just layer ->
      let
        transform = layerTransform layer
        mScaleX = transformScaleX transform
        mScaleY = transformScaleY transform
        mScaleZ = transformScaleZ transform
      in
        case (mScaleX, mScaleY) of
          (Nothing, _) -> Right layers
          (_, Nothing) -> Right layers
          (Just scaleX, Just scaleY) ->
            let
              -- Get current values
              xVal = animatablePropertyValue scaleX
              yVal = animatablePropertyValue scaleY
              zVal = case mScaleZ of
                Nothing -> 100.0
                Just scaleZ -> animatablePropertyValue scaleZ
              
              -- Collect all unique frames from X, Y, Z keyframes
              xFrames = map keyframeFrame (animatablePropertyKeyframes scaleX)
              yFrames = map keyframeFrame (animatablePropertyKeyframes scaleY)
              zFrames = case mScaleZ of
                Nothing -> []
                Just scaleZ -> map keyframeFrame (animatablePropertyKeyframes scaleZ)
              
              allFrames = sort (nub (xFrames ++ yFrames ++ zFrames))
              
              -- Create combined keyframes at each frame
              mCombinedKeyframes = traverse (\frame ->
                let
                  -- Find keyframes at this frame
                  xKf = find (\kf -> keyframeFrame kf == frame) (animatablePropertyKeyframes scaleX)
                  yKf = find (\kf -> keyframeFrame kf == frame) (animatablePropertyKeyframes scaleY)
                  zKf = case mScaleZ of
                    Nothing -> Nothing
                    Just scaleZ -> find (\kf -> keyframeFrame kf == frame) (animatablePropertyKeyframes scaleZ)
                  
                  -- Get values
                  xValAtFrame = case xKf of
                    Nothing -> xVal
                    Just kf -> keyframeValue kf
                  
                  yValAtFrame = case yKf of
                    Nothing -> yVal
                    Just kf -> keyframeValue kf
                  
                  zValAtFrame = case zKf of
                    Nothing -> zVal
                    Just kf -> keyframeValue kf
                  
                  -- Create combined Vec3 value
                  combinedValue = Vec3 xValAtFrame yValAtFrame zValAtFrame
                  
                  -- Use first available keyframe as template
                  templateKf = case (xKf, yKf, zKf) of
                    (Just kf, _, _) -> Just kf
                    (_, Just kf, _) -> Just kf
                    (_, _, Just kf) -> Just kf
                    _ -> Nothing
                  
                  -- Create combined keyframe
                  newId = genId ("kf_scale_" <> T.pack (show (floor frame)))
                  interp = case templateKf of
                    Nothing -> InterpolationBase InterpolationLinear
                    Just kf -> keyframeInterpolation kf
                in
                  createKeyframe newId frame combinedValue interp
                ) allFrames
              
              -- Create updated scale property
              updatedScaleProp = (transformScale transform)
                { animatablePropertyValue = Vec3 xVal yVal zVal
                , animatablePropertyAnimated = case mCombinedKeyframes of
                    Right kfs -> not (null kfs)
                    Left _ -> False
                , animatablePropertyKeyframes = case mCombinedKeyframes of
                    Right kfs -> kfs
                    Left _ -> []
                }
              
              -- Update transform (clear separate properties, update flag)
              currentSepDim = transformSeparateDimensions transform
              newSepDim = case currentSepDim of
                Nothing -> Nothing
                Just sd -> Just (sd {separateDimensionsScale = False})
              
              newTransform = transform
                { transformScale = updatedScaleProp
                , transformScaleX = Nothing
                , transformScaleY = Nothing
                , transformScaleZ = Nothing
                , transformSeparateDimensions = newSepDim
                }
              
              updatedLayer = layer {layerTransform = newTransform}
              updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
            in
              case mCombinedKeyframes of
                Left err -> Left ("Failed to create combined keyframes: " <> err)
                Right _ -> Right updatedLayers

-- | Check if a layer has separated position dimensions
-- Pure function: takes layer ID and layers list
-- Returns true if position dimensions are separated
hasPositionSeparated ::
  Text -> -- Layer ID
  [Layer] -> -- Layers list
  Bool -- True if position dimensions are separated
hasPositionSeparated targetLayerId layers =
  case getLayerById layers targetLayerId of
    Nothing -> False
    Just layer ->
      case transformSeparateDimensions (layerTransform layer) of
        Nothing -> False
        Just sepDim -> separateDimensionsPosition sepDim

-- | Check if a layer has separated scale dimensions
-- Pure function: takes layer ID and layers list
-- Returns true if scale dimensions are separated
hasScaleSeparated ::
  Text -> -- Layer ID
  [Layer] -> -- Layers list
  Bool -- True if scale dimensions are separated
hasScaleSeparated targetLayerId layers =
  case getLayerById layers targetLayerId of
    Nothing -> False
    Just layer ->
      case transformSeparateDimensions (layerTransform layer) of
        Nothing -> False
        Just sepDim -> separateDimensionsScale sepDim
