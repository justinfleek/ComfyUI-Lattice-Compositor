-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Layer Factory
-- |
-- | Creates layers from various sources including AI generation results.
-- | Ensures proper layer initialization with correct types and defaults.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.Services.LayerFactory
  ( createLayerFromGeneration
  , module Types
  ) where

import Prelude

import Data.Array (length) as Array
import Data.Array (uncons) as Array
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (toCharArray, fromCharArray, length) as String
import Lattice.Primitives
  ( NonEmptyString(..)
  , mkNonEmptyString
  , FrameNumber(..)
  , Percentage(..)
  , mkPercentage
  , PositiveFloat(..)
  , mkPositiveFloat
  )
import Lattice.Project
  ( LayerType(..)
  , BlendMode(..)
  , TrackMatteMode(..)
  , LayerBase
  )
import Lattice.UI.Layout.WorkspaceLayout.Types (GenerationMode(..))
import Lattice.Services.LayerFactory.Types (GeneratedAsset, GeneratedLayer) as Types
import Lattice.Services.LayerFactory.Types (GeneratedAsset, GeneratedLayer)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // factory
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a layer and asset from generation results
-- |
-- | Takes the generation mode, frames, and metadata to create:
-- | 1. An asset containing the frame data
-- | 2. A layer referencing that asset
createLayerFromGeneration
  :: { mode :: GenerationMode
     , frames :: Array String
     , prompt :: String
     , model :: String
     , seed :: Int
     , width :: Int
     , height :: Int
     , layerId :: String
     , assetId :: String
     , currentFrame :: Int
     , totalFrames :: Int
     }
  -> Maybe GeneratedLayer
createLayerFromGeneration config = do
  -- Validate we have frames
  if Array.length config.frames == 0
    then Nothing
    else do
      -- Create IDs
      layerIdNes <- mkNonEmptyString config.layerId
      assetIdNes <- mkNonEmptyString config.assetId
      
      -- Determine layer type based on mode
      let layerType = modeToLayerType config.mode
      
      -- Determine if this is video (multiple frames)
      let isVideo = Array.length config.frames > 1
      
      -- Create layer name from prompt (truncated)
      let layerName = truncatePrompt config.prompt 30
      layerNameNes <- mkNonEmptyString layerName
      
      -- Calculate end frame
      let frameCount = Array.length config.frames
      let endFrame = config.currentFrame + frameCount - 1
      
      -- Build the layer
      let layer = createDefaultLayer
            { id: layerIdNes
            , name: layerNameNes
            , layerType: layerType
            , startFrame: FrameNumber config.currentFrame
            , endFrame: FrameNumber (min endFrame (config.totalFrames - 1))
            }
      
      -- Build the asset
      let asset =
            { id: assetIdNes
            , frames: config.frames
            , isVideo: isVideo
            , width: config.width
            , height: config.height
            , model: config.model
            , prompt: config.prompt
            , seed: config.seed
            }
      
      pure { layer, asset }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Map generation mode to layer type
modeToLayerType :: GenerationMode -> LayerType
modeToLayerType = case _ of
  TextToImage  -> LTTextToImage
  ImageEdit    -> LTInpaint
  ImageToVideo -> LTImageToVideo
  TextToVideo  -> LTTextToVideo
  TextTo3D     -> LTModel

-- | Truncate prompt for layer name
truncatePrompt :: String -> Int -> String
truncatePrompt prompt maxLen =
  if String.length prompt <= maxLen
    then prompt
    else takeStr maxLen prompt <> "..."
  where
    takeStr :: Int -> String -> String
    takeStr n s = String.fromCharArray (takeArray n (String.toCharArray s))
    
    takeArray :: forall a. Int -> Array a -> Array a
    takeArray n arr = case n of
      0 -> []
      _ -> case Array.uncons arr of
        Nothing -> []
        Just { head: x, tail: xs } -> [x] <> takeArray (n - 1) xs

-- | Create a layer with default values
createDefaultLayer
  :: { id :: NonEmptyString
     , name :: NonEmptyString
     , layerType :: LayerType
     , startFrame :: FrameNumber
     , endFrame :: FrameNumber
     }
  -> LayerBase
createDefaultLayer config =
  { id: config.id
  , name: config.name
  , layerType: config.layerType
  , visible: true
  , locked: false
  , solo: false
  , shy: false
  , enabled: true
  , selected: false
  , collapsed: false
  , guideLayer: false
  , is3D: false
  , blendMode: BMNormal
  , opacity: defaultPercentage
  , startFrame: config.startFrame
  , endFrame: config.endFrame
  , inPoint: config.startFrame
  , outPoint: config.endFrame
  , stretch: defaultPositiveFloat
  , parentId: Nothing
  , trackMatteMode: TMNone
  , trackMatteLayerId: Nothing
  , motionBlur: false
  , qualitySetting: Nothing
  , samplingQuality: Nothing
  , preserveTransparency: false
  , frameBlending: false
  , timeRemapEnabled: false
  }
  where
    defaultPercentage :: Percentage
    defaultPercentage = case mkPercentage 100.0 of
      Just p -> p
      Nothing -> Percentage 100.0
    
    defaultPositiveFloat :: PositiveFloat
    defaultPositiveFloat = case mkPositiveFloat 1.0 of
      Just p -> p
      Nothing -> PositiveFloat 1.0
