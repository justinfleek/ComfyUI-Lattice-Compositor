-- |
-- Module      : Lattice.State.Keyframe.Clipboard
-- Description : Keyframe clipboard operations
--
-- Migrated from ui/src/stores/keyframeStore/clipboard.ts
-- Pure functions for copying and pasting keyframes
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Clipboard
  ( copyKeyframes
  , pasteKeyframes
  , hasKeyframesInClipboard
  ) where

import Data.List (find, findIndex, minimumBy, sortBy)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.CRUD (addKeyframeWithPropertyValue)
import Lattice.State.Keyframe.Helpers (findPropertyByPath)
import Lattice.State.Keyframe.Interpolation (updatePropertyInLayer)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , ClipboardKeyframe(..)
  , Keyframe(..)
  , PropertyValue(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives (validateFinite)

-- ============================================================================
-- KEYFRAME CLIPBOARD (COPY/PASTE)
-- ============================================================================

-- | Keyframe selection for copy operation
data KeyframeSelection = KeyframeSelection
  { keyframeSelectionLayerId :: Text
  , keyframeSelectionPropertyPath :: Text
  , keyframeSelectionKeyframeId :: Text
  }
  deriving (Eq, Show)

-- | Copy keyframes to clipboard
-- Pure function: takes list of keyframe selections, layers list, and current clipboard state
-- Returns updated clipboard state and count of keyframes copied
-- Groups keyframes by layer and property, stores relative frame offsets from earliest keyframe
copyKeyframes ::
  [KeyframeSelection] -> -- Array of keyframe selections
  [Layer] -> -- Current layers list
  [ClipboardKeyframe] -> -- Current clipboard state
  Either Text (Int, [ClipboardKeyframe]) -- (count copied, updated clipboard) or error
copyKeyframes selections layers currentClipboard =
  if null selections
    then Right (0, currentClipboard)
    else
      let
        -- Group keyframes by layer and property
        groupedByProperty = foldl (\acc sel ->
          let
            key = keyframeSelectionLayerId sel <> ":" <> keyframeSelectionPropertyPath sel
            existingGroup = find (\g -> fst g == key) acc
          in
            case existingGroup of
              Nothing -> acc ++ [(key, (keyframeSelectionLayerId sel, keyframeSelectionPropertyPath sel, [keyframeSelectionKeyframeId sel]))]
              Just (_, (layerId, propPath, kfIds)) -> 
                map (\g -> if fst g == key then (key, (layerId, propPath, kfIds ++ [keyframeSelectionKeyframeId sel])) else g) acc
          ) [] selections
        
        -- Find the earliest frame among all selected keyframes (for relative timing)
        earliestFrameResult = foldl (\acc (_, (layerId, propPath, kfIds)) ->
          case getLayerById layerId layers of
            Nothing -> acc
            Just layer ->
              case findPropertyByPath layer propPath of
                Nothing -> acc
                Just prop ->
                  let
                    selectedKeyframes = filter (\kf -> keyframeId kf `elem` kfIds) (animatablePropertyKeyframes prop)
                    frames = map keyframeFrame selectedKeyframes
                    validFrames = filter (\f -> validateFinite f && f >= 1) frames
                  in
                    case (acc, validFrames) of
                      (Nothing, []) -> Nothing
                      (Nothing, fs) -> Just (minimum fs)
                      (Just currentMin, []) -> Just currentMin
                      (Just currentMin, fs) -> Just (min currentMin (minimum fs))
          ) Nothing groupedByProperty
        
        earliestFrame = case earliestFrameResult of
          Nothing -> 1.0 -- Default to frame 1 if no valid frames found
          Just f -> f
      in
        if earliestFrameResult == Nothing
          then Right (0, currentClipboard)
          else
            let
              -- Build clipboard entries with relative frame offsets
              clipboardEntries = foldl (\acc (_, (layerId, propPath, kfIds)) ->
                case getLayerById layerId layers of
                  Nothing -> acc
                  Just layer ->
                    case findPropertyByPath layer propPath of
                      Nothing -> acc
                      Just prop ->
                        let
                          selectedKeyframes = filter (\kf -> keyframeId kf `elem` kfIds) (animatablePropertyKeyframes prop)
                          validKeyframes = filter (\kf -> validateFinite (keyframeFrame kf) && keyframeFrame kf >= 1) selectedKeyframes
                        in
                          if null validKeyframes
                            then acc
                            else
                              -- Clone keyframes and store relative frame offsets
                              let
                                clonedKeyframes = map (\kf ->
                                  let
                                    relativeFrame = keyframeFrame kf - earliestFrame
                                    -- Ensure relative frame is valid (>= 0)
                                    safeRelativeFrame = if relativeFrame >= 0 then relativeFrame else 0.0
                                  in
                                    kf {keyframeFrame = safeRelativeFrame}
                                  ) validKeyframes
                              in
                                acc ++ [ClipboardKeyframe layerId propPath clonedKeyframes]
                ) [] groupedByProperty
              
              totalCopied = sum (map (\entry -> length (clipboardKeyframeKeyframes entry)) clipboardEntries)
            in
              Right (totalCopied, clipboardEntries)

-- | Paste keyframes from clipboard to a target property
-- Pure function: takes target layer ID, optional target property path, current frame, ID generator, layers list, and clipboard state
-- Returns created keyframes and updated layers list or error
-- If targetPropertyPath is Nothing, uses original property path from clipboard entry
pasteKeyframes ::
  Text -> -- Target layer ID
  Maybe Text -> -- Target property path (Nothing = use original from clipboard)
  Double -> -- Current frame (for applying offsets)
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  [ClipboardKeyframe] -> -- Clipboard state
  Either Text ([Keyframe PropertyValue], [Layer]) -- (created keyframes, updated layers) or error
pasteKeyframes targetLayerId mTargetPropertyPath currentFrame genId layers clipboard =
  if null clipboard
    then Right ([], layers)
    else
      case getLayerById targetLayerId layers of
        Nothing -> Right ([], layers)
        Just targetLayer ->
          let
            -- Validate current frame is finite and >= 1
            safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
            
            -- Process each clipboard entry
            processClipboardEntry accLayers accCreated (ClipboardKeyframe origLayerId origPropPath keyframes) =
              -- Determine which property to paste to
              let
                propPath = case mTargetPropertyPath of
                  Nothing -> origPropPath
                  Just path -> path
                
                -- Get current target layer from accLayers
                mCurrentTargetLayer = getLayerById targetLayerId accLayers
              in
                case mCurrentTargetLayer of
                  Nothing -> (accLayers, accCreated)
                  Just currentTargetLayer ->
                    -- Find property on target layer
                    case findPropertyByPath currentTargetLayer propPath of
                      Nothing -> (accLayers, accCreated)
                      Just prop ->
                        -- Enable animation if not already (using updatePropertyInLayer)
                        let
                          mUpdatedLayerWithAnimation = updatePropertyInLayer currentTargetLayer propPath (\p -> p {animatablePropertyAnimated = True})
                          baseLayers = case mUpdatedLayerWithAnimation of
                            Nothing -> accLayers
                            Just updatedLayer -> map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) accLayers
                          
                          -- Paste each keyframe with new IDs and adjusted frames
                          pasteKeyframeToLayer kf (accLayerList, accCreatedList) =
                            let
                              newFrame = safeCurrentFrame + keyframeFrame kf
                              -- Ensure new frame is >= 1
                              clampedFrame = if validateFinite newFrame && newFrame >= 1 then newFrame else 1.0
                              
                              -- Add keyframe using addKeyframeWithPropertyValue
                              result = addKeyframeWithPropertyValue targetLayerId propPath (keyframeValue kf) (Just clampedFrame) clampedFrame genId accLayerList
                            in
                              case result of
                                Left _ -> (accLayerList, accCreatedList)
                                Right (createdKf, updatedLayers) -> (updatedLayers, accCreatedList ++ [createdKf])
                          
                          -- Paste all keyframes
                          (finalLayers, created) = foldl pasteKeyframeToLayer (baseLayers, accCreated) keyframes
                        in
                          (finalLayers, created)
            
            -- Process all clipboard entries
            (updatedLayers, createdKeyframes) = foldl (\acc entry -> processClipboardEntry (fst acc) (snd acc) entry) (layers, []) clipboard
          in
            Right (createdKeyframes, updatedLayers)

-- | Check if clipboard has keyframes
-- Pure function: takes clipboard state
-- Returns true if clipboard has keyframes
hasKeyframesInClipboard ::
  [ClipboardKeyframe] -> -- Clipboard state
  Bool -- True if clipboard has keyframes
hasKeyframesInClipboard clipboard = not (null clipboard)
