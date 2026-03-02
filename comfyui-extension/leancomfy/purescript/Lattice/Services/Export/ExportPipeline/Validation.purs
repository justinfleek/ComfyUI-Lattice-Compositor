-- | Lattice.Services.Export.ExportPipeline.Validation - Config validation
-- |
-- | Pure validation functions for export configuration.
-- |
-- | Source: ui/src/services/export/exportPipeline.ts

module Lattice.Services.Export.ExportPipeline.Validation
  ( -- * Validation
    validateConfig
  , ValidationError(..)
  , ValidationResult
    -- * Individual Validators
  , validateDimensions
  , validateFrameRange
  , validateFps
  , validatePrompt
    -- * Helper Functions
  , needsPrompt
  , requiresDepthMap
  , requiresCameraData
  ) where

import Prelude
import Data.Array (concat, filter, null)
import Data.Maybe (Maybe(..), isNothing)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

import Lattice.Services.Export.ExportPipeline.Types (ExportConfig)
import Lattice.Services.Export.CameraExport.Types (ExportTarget(..))

--------------------------------------------------------------------------------
-- Validation Types
--------------------------------------------------------------------------------

-- | Validation error
data ValidationError
  = ErrorWidthOutOfRange Int
  | ErrorHeightOutOfRange Int
  | ErrorFrameCountOutOfRange Int
  | ErrorFpsOutOfRange Int
  | ErrorInvalidStartFrame Int Int
  | ErrorInvalidEndFrame Int Int
  | ErrorPromptRequired
  | ErrorNoOutputSelected
  | ErrorComfyUIServerRequired

derive instance Generic ValidationError _
instance Show ValidationError where show = genericShow
instance Eq ValidationError where eq = genericEq

-- | Convert validation error to message
errorToMessage :: ValidationError -> String
errorToMessage = case _ of
  ErrorWidthOutOfRange w ->
    "Width must be between 64 and 4096, got " <> show w
  ErrorHeightOutOfRange h ->
    "Height must be between 64 and 4096, got " <> show h
  ErrorFrameCountOutOfRange fc ->
    "Frame count must be between 1 and 1000, got " <> show fc
  ErrorFpsOutOfRange fps ->
    "FPS must be between 1 and 120, got " <> show fps
  ErrorInvalidStartFrame start total ->
    "Start frame " <> show start <> " is invalid (total frames: " <> show total <> ")"
  ErrorInvalidEndFrame end start ->
    "End frame " <> show end <> " must be greater than start frame " <> show start
  ErrorPromptRequired ->
    "Prompt is required for this export target"
  ErrorNoOutputSelected ->
    "At least one output type must be selected"
  ErrorComfyUIServerRequired ->
    "ComfyUI server URL is required for auto-queue"

-- | Validation result
type ValidationResult =
  { valid :: Boolean
  , errors :: Array String
  , warnings :: Array String
  }

--------------------------------------------------------------------------------
-- Main Validation
--------------------------------------------------------------------------------

-- | Validate full export configuration
validateConfig :: ExportConfig -> ValidationResult
validateConfig config =
  let
    dimErrors = validateDimensions config.width config.height
    frameErrors = validateFrameRange config.startFrame config.endFrame config.frameCount
    fpsErrors = validateFps config.fps
    promptErrors = validatePrompt config.target config.prompt
    outputErrors = validateOutputSelection config
    serverErrors = validateServerConfig config

    allErrors = concat
      [ dimErrors
      , frameErrors
      , fpsErrors
      , promptErrors
      , outputErrors
      , serverErrors
      ]

    warnings = generateWarnings config
  in
    { valid: null allErrors
    , errors: map errorToMessage allErrors
    , warnings
    }

--------------------------------------------------------------------------------
-- Individual Validators
--------------------------------------------------------------------------------

-- | Validate width and height
validateDimensions :: Int -> Int -> Array ValidationError
validateDimensions width height =
  filter (_ /= ErrorWidthOutOfRange 0)  -- dummy filter for type
    $ concat
        [ if width < 64 || width > 4096
            then [ErrorWidthOutOfRange width]
            else []
        , if height < 64 || height > 4096
            then [ErrorHeightOutOfRange height]
            else []
        ]

-- | Validate frame range
validateFrameRange :: Int -> Int -> Int -> Array ValidationError
validateFrameRange startFrame endFrame frameCount =
  concat
    [ if frameCount < 1 || frameCount > 1000
        then [ErrorFrameCountOutOfRange frameCount]
        else []
    , if startFrame < 0 || startFrame >= frameCount
        then [ErrorInvalidStartFrame startFrame frameCount]
        else []
    , if endFrame <= startFrame || endFrame > frameCount
        then [ErrorInvalidEndFrame endFrame startFrame]
        else []
    ]

-- | Validate FPS
validateFps :: Int -> Array ValidationError
validateFps fps =
  if fps < 1 || fps > 120
    then [ErrorFpsOutOfRange fps]
    else []

-- | Validate prompt requirement
validatePrompt :: ExportTarget -> String -> Array ValidationError
validatePrompt target prompt =
  if needsPrompt target && prompt == ""
    then [ErrorPromptRequired]
    else []

-- | Validate output selection
validateOutputSelection :: ExportConfig -> Array ValidationError
validateOutputSelection config =
  if not config.exportDepthMap
     && not config.exportControlImages
     && not config.exportCameraData
     && not config.exportReferenceFrame
     && not config.exportLastFrame
    then [ErrorNoOutputSelected]
    else []

-- | Validate server configuration
validateServerConfig :: ExportConfig -> Array ValidationError
validateServerConfig config =
  if config.autoQueueWorkflow && isNothing config.comfyuiServer
    then [ErrorComfyUIServerRequired]
    else []

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Check if target requires a prompt
needsPrompt :: ExportTarget -> Boolean
needsPrompt = case _ of
  TargetFullMatrices -> false
  _ -> true

-- | Check if target requires depth map
requiresDepthMap :: ExportTarget -> Boolean
requiresDepthMap = case _ of
  TargetMotionCtrl -> true
  TargetMotionCtrlSVD -> true
  TargetUni3CCamera -> true
  _ -> false

-- | Check if target requires camera data
requiresCameraData :: ExportTarget -> Boolean
requiresCameraData = case _ of
  TargetMotionCtrl -> true
  TargetMotionCtrlSVD -> true
  TargetUni3CCamera -> true
  TargetUni3CMotion -> true
  TargetWan22FunCamera -> true
  TargetAnimateDiffCameraCtrl -> true
  _ -> false

--------------------------------------------------------------------------------
-- Warnings
--------------------------------------------------------------------------------

-- | Generate warnings for configuration
generateWarnings :: ExportConfig -> Array String
generateWarnings config =
  concat
    [ dimensionWarnings config.width config.height
    , frameCountWarnings config.frameCount config.target
    , qualityWarnings config
    ]

-- | Dimension warnings
dimensionWarnings :: Int -> Int -> Array String
dimensionWarnings width height =
  concat
    [ if width `mod` 8 /= 0
        then ["Width " <> show width <> " is not divisible by 8, may cause issues"]
        else []
    , if height `mod` 8 /= 0
        then ["Height " <> show height <> " is not divisible by 8, may cause issues"]
        else []
    , if width > 1024 || height > 1024
        then ["Large dimensions may require significant GPU memory"]
        else []
    ]

-- | Frame count warnings
frameCountWarnings :: Int -> ExportTarget -> Array String
frameCountWarnings frameCount target =
  let
    recommendedMax = case target of
      TargetWan22FunCamera -> 81
      _ -> 120
  in
    if frameCount > recommendedMax
      then ["Frame count " <> show frameCount <> " exceeds recommended max " <> show recommendedMax <> " for " <> show target]
      else []

-- | Quality settings warnings
qualityWarnings :: ExportConfig -> Array String
qualityWarnings config =
  concat
    [ case config.steps of
        Just s | s < 20 -> ["Low step count (" <> show s <> ") may reduce quality"]
        _ -> []
    , case config.cfgScale of
        Just c | c > 15.0 -> ["High CFG scale (" <> show c <> ") may cause artifacts"]
        _ -> []
    ]

