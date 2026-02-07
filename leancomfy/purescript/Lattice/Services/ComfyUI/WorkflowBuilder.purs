-- | Lattice.Services.ComfyUI.WorkflowBuilder - Workflow node helpers
-- |
-- | Pure functions for building ComfyUI workflow nodes.
-- | Node factories and common patterns.
-- |
-- | Source: ui/src/services/comfyui/workflowTemplates.ts (helpers section)

module Lattice.Services.ComfyUI.WorkflowBuilder
  ( -- * Node ID Management
    NodeIdState
  , initialNodeIdState
  , nextNodeId
    -- * Node Creation
  , createNode
  , conn
    -- * Common Node Patterns
  , addCheckpointLoader
  , addVAELoader
  , addCLIPTextEncode
  , addLoadImage
  , addImageResize
  , addVAEEncode
  , addVAEDecode
  , addKSampler
  , addVideoOutput
  , addEmptyLatent
    -- * Wan Specific
  , addWanModelLoader
  , addWanVAELoader
  , addWanTextEncoder
  , addWanTextEncode
  , addWanVAEDecode
    -- * Validation
  , validateWorkflowParams
  , validateDimension
  , validateFrameCount
  , validateFps
    -- * Seed Generation
  , generateSeed
  , ensureValidSeed
  ) where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Int (toNumber)
import Data.Array as Array
import Effect (Effect)
import Effect.Random (randomInt)

import Lattice.Services.ComfyUI.WorkflowTypes
  ( WorkflowParams
  , ValidationResult
  , ValidationConstants
  , validationConstants
  )

--------------------------------------------------------------------------------
-- Node ID Management
--------------------------------------------------------------------------------

-- | State for node ID generation
type NodeIdState = { counter :: Int }

-- | Initial state
initialNodeIdState :: NodeIdState
initialNodeIdState = { counter: 1 }

-- | Get next node ID and updated state
nextNodeId :: NodeIdState -> { id :: String, state :: NodeIdState }
nextNodeId state =
  { id: show state.counter
  , state: { counter: state.counter + 1 }
  }

--------------------------------------------------------------------------------
-- Node Creation
--------------------------------------------------------------------------------

-- | Create a node record (returns Foreign-compatible structure)
-- | In PureScript, we represent this as a record that will be
-- | serialized to JSON for the ComfyUI API
type NodeRecord =
  { class_type :: String
  , inputs :: Array { name :: String, value :: NodeInputValue }
  , _meta :: Maybe { title :: String }
  }

-- | Node input value types
data NodeInputValue
  = InputString String
  | InputInt Int
  | InputNumber Number
  | InputBool Boolean
  | InputConnection String Int  -- nodeId, outputIndex
  | InputArray (Array NodeInputValue)
  | InputNull

-- | Create a basic node
createNode :: String -> Array { name :: String, value :: NodeInputValue } -> Maybe String -> NodeRecord
createNode classType inputs mTitle =
  { class_type: classType
  , inputs: inputs
  , _meta: map (\t -> { title: t }) mTitle
  }

-- | Create a connection reference
conn :: String -> Int -> NodeInputValue
conn nodeId outputIndex = InputConnection nodeId outputIndex

-- | Create connection with default output index 0
conn0 :: String -> NodeInputValue
conn0 nodeId = InputConnection nodeId 0

--------------------------------------------------------------------------------
-- Common Node Patterns
--------------------------------------------------------------------------------

-- | Add checkpoint loader node
addCheckpointLoader :: String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addCheckpointLoader checkpoint state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "CheckpointLoaderSimple"
         [ { name: "ckpt_name", value: InputString checkpoint } ]
         (Just "Load Checkpoint")
     , state: newState
     }

-- | Add VAE loader node
addVAELoader :: String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addVAELoader vae state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "VAELoader"
         [ { name: "vae_name", value: InputString vae } ]
         (Just "Load VAE")
     , state: newState
     }

-- | Add CLIP text encode node
addCLIPTextEncode :: String -> String -> Int -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addCLIPTextEncode clipNodeId text title state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "CLIPTextEncode"
         [ { name: "clip", value: conn clipNodeId 1 }
         , { name: "text", value: InputString text }
         ]
         (Just title)
     , state: newState
     }

-- | Add load image node
addLoadImage :: String -> Maybe String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addLoadImage imageName mTitle state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "LoadImage"
         [ { name: "image", value: InputString imageName } ]
         mTitle
     , state: newState
     }

-- | Add image resize node
addImageResize :: String -> Int -> Int -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addImageResize imageNodeId width height state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "ImageResize"
         [ { name: "image", value: conn0 imageNodeId }
         , { name: "width", value: InputInt width }
         , { name: "height", value: InputInt height }
         , { name: "interpolation", value: InputString "lanczos" }
         , { name: "method", value: InputString "fill / crop" }
         , { name: "condition", value: InputString "always" }
         , { name: "multiple_of", value: InputInt 8 }
         ]
         (Just "Resize Image")
     , state: newState
     }

-- | Add VAE encode node
addVAEEncode :: String -> String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addVAEEncode imageNodeId vaeNodeId state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "VAEEncode"
         [ { name: "pixels", value: conn0 imageNodeId }
         , { name: "vae", value: conn0 vaeNodeId }
         ]
         (Just "VAE Encode")
     , state: newState
     }

-- | Add VAE decode node
addVAEDecode :: String -> String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addVAEDecode samplesNodeId vaeNodeId state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "VAEDecode"
         [ { name: "samples", value: conn0 samplesNodeId }
         , { name: "vae", value: conn0 vaeNodeId }
         ]
         (Just "VAE Decode")
     , state: newState
     }

-- | KSampler parameters
type KSamplerParams =
  { seed :: Maybe Int
  , steps :: Maybe Int
  , cfg :: Maybe Number
  , denoise :: Maybe Number
  }

-- | Add KSampler node
addKSampler
  :: String  -- model
  -> String  -- positive
  -> String  -- negative
  -> String  -- latent
  -> KSamplerParams
  -> NodeIdState
  -> Effect { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addKSampler modelId positiveId negativeId latentId params state = do
  seed <- ensureValidSeed params.seed
  let { id, state: newState } = nextNodeId state
  pure
    { nodeId: id
    , node: createNode "KSampler"
        [ { name: "model", value: conn0 modelId }
        , { name: "positive", value: conn0 positiveId }
        , { name: "negative", value: conn0 negativeId }
        , { name: "latent_image", value: conn0 latentId }
        , { name: "seed", value: InputInt seed }
        , { name: "steps", value: InputInt (fromMaybe 20 params.steps) }
        , { name: "cfg", value: InputNumber (fromMaybe 7.0 params.cfg) }
        , { name: "sampler_name", value: InputString "euler" }
        , { name: "scheduler", value: InputString "normal" }
        , { name: "denoise", value: InputNumber (clampDenoise (fromMaybe 1.0 params.denoise)) }
        ]
        (Just "KSampler")
    , state: newState
    }

-- | Add video output node
addVideoOutput :: String -> Int -> Maybe String -> Maybe String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addVideoOutput imagesNodeId fps mFormat mFilename state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "VHS_VideoCombine"
         [ { name: "images", value: conn0 imagesNodeId }
         , { name: "frame_rate", value: InputInt fps }
         , { name: "loop_count", value: InputInt 0 }
         , { name: "filename_prefix", value: InputString (fromMaybe "lattice_output" mFilename) }
         , { name: "format", value: InputString (fromMaybe "video/h264-mp4" mFormat) }
         , { name: "pingpong", value: InputBool false }
         , { name: "save_output", value: InputBool true }
         , { name: "audio", value: InputNull }
         , { name: "meta_batch", value: InputNull }
         ]
         (Just "Video Output")
     , state: newState
     }

-- | Add empty latent image node
addEmptyLatent :: Int -> Int -> Int -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addEmptyLatent width height batchSize state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "EmptyLatentImage"
         [ { name: "width", value: InputInt width }
         , { name: "height", value: InputInt height }
         , { name: "batch_size", value: InputInt batchSize }
         ]
         (Just "Empty Latent")
     , state: newState
     }

--------------------------------------------------------------------------------
-- Wan Specific Nodes
--------------------------------------------------------------------------------

-- | Add Wan model loader
addWanModelLoader :: String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addWanModelLoader model state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "DownloadAndLoadWan2_1Model"
         [ { name: "model", value: InputString model }
         , { name: "base_precision", value: InputString "bf16" }
         , { name: "quantization", value: InputString "disabled" }
         ]
         (Just "Load Wan Model")
     , state: newState
     }

-- | Add Wan VAE loader
addWanVAELoader :: NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addWanVAELoader state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "DownloadAndLoadWanVAE"
         [ { name: "vae", value: InputString "wan_2.1_vae.safetensors" }
         , { name: "precision", value: InputString "bf16" }
         ]
         (Just "Load Wan VAE")
     , state: newState
     }

-- | Add Wan text encoder loader
addWanTextEncoder :: NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addWanTextEncoder state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "DownloadAndLoadWanTextEncoder"
         [ { name: "text_encoder", value: InputString "umt5-xxl-enc-bf16.safetensors" }
         , { name: "precision", value: InputString "bf16" }
         ]
         (Just "Load Text Encoder")
     , state: newState
     }

-- | Add Wan text encode node
addWanTextEncode :: String -> String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addWanTextEncode encoderNodeId prompt state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "WanTextEncode"
         [ { name: "text_encoder", value: conn0 encoderNodeId }
         , { name: "prompt", value: InputString prompt }
         , { name: "force_offload", value: InputBool true }
         ]
         (Just "Positive Prompt")
     , state: newState
     }

-- | Add Wan VAE decode node
addWanVAEDecode :: String -> String -> NodeIdState -> { nodeId :: String, node :: NodeRecord, state :: NodeIdState }
addWanVAEDecode vaeNodeId samplesNodeId state =
  let { id, state: newState } = nextNodeId state
  in { nodeId: id
     , node: createNode "WanVAEDecode"
         [ { name: "vae", value: conn0 vaeNodeId }
         , { name: "samples", value: conn0 samplesNodeId }
         , { name: "enable_vae_tiling", value: InputBool true }
         , { name: "tile_sample_min_height", value: InputInt 240 }
         , { name: "tile_sample_min_width", value: InputInt 240 }
         , { name: "tile_overlap_factor_height", value: InputNumber 0.2 }
         , { name: "tile_overlap_factor_width", value: InputNumber 0.2 }
         ]
         (Just "VAE Decode")
     , state: newState
     }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate workflow parameters
validateWorkflowParams :: WorkflowParams -> ValidationResult
validateWorkflowParams params =
  let
    vc = validationConstants
    widthErrors = validateDimension "width" params.width vc
    heightErrors = validateDimension "height" params.height vc
    frameErrors = validateFrameCount params.frameCount vc
    fpsErrors = validateFps params.fps vc
    allErrors = widthErrors <> heightErrors <> frameErrors <> fpsErrors
  in
    { valid: Array.null allErrors
    , errors: allErrors
    , warnings: []
    }

-- | Validate a dimension value
validateDimension :: String -> Int -> ValidationConstants -> Array String
validateDimension name value vc
  | value < vc.minDimension = ["Invalid " <> name <> ": " <> show value <> ". Must be at least " <> show vc.minDimension <> "."]
  | value > vc.maxDimension = ["Invalid " <> name <> ": " <> show value <> ". Must be at most " <> show vc.maxDimension <> "."]
  | otherwise = []

-- | Validate frame count
validateFrameCount :: Int -> ValidationConstants -> Array String
validateFrameCount value vc
  | value <= 0 = ["Invalid frameCount: " <> show value <> ". Must be a positive number."]
  | value > vc.maxFrameCount = ["Invalid frameCount: " <> show value <> ". Must be at most " <> show vc.maxFrameCount <> "."]
  | otherwise = []

-- | Validate FPS
validateFps :: Int -> ValidationConstants -> Array String
validateFps value vc
  | value <= 0 = ["Invalid fps: " <> show value <> ". Must be a positive number."]
  | value > vc.maxFps = ["Invalid fps: " <> show value <> ". Must be at most " <> show vc.maxFps <> "."]
  | otherwise = []

--------------------------------------------------------------------------------
-- Seed Helpers
--------------------------------------------------------------------------------

-- | Generate a random seed
generateSeed :: Effect Int
generateSeed = randomInt 0 2147483647

-- | Ensure a valid seed value
ensureValidSeed :: Maybe Int -> Effect Int
ensureValidSeed (Just seed)
  | seed >= 0 = pure seed
  | otherwise = generateSeed
ensureValidSeed Nothing = generateSeed

-- | Clamp denoise value to [0, 1]
clampDenoise :: Number -> Number
clampDenoise n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n
