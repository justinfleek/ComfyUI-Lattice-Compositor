-- | Lattice.Services.ComfyUI.WorkflowUtilities - Workflow utilities
-- |
-- | @module Lattice.Services.ComfyUI.WorkflowUtilities
-- | @description Pure utility functions for workflow manipulation and validation.
-- |
-- | ## Purpose
-- |
-- | This module provides utilities for working with ComfyUI workflows:
-- | - **Validation**: Check workflow structure for common errors
-- | - **Queries**: Find input/output nodes, count nodes
-- | - **Parameter Injection**: Replace placeholders in workflow JSON
-- | - **Serialization**: Convert workflows to/from JSON
-- |
-- | ## Architecture
-- |
-- | ```
-- | ┌──────────────────────────────────────────────────────────────┐
-- | │                   WorkflowUtilities                          │
-- | │                                                              │
-- | │  ┌────────────────┐  ┌─────────────────┐  ┌──────────────┐  │
-- | │  │  Validation    │  │  Parameter      │  │  Node        │  │
-- | │  │  - Structure   │  │  Injection      │  │  Queries     │  │
-- | │  │  - Connections │  │  - {{key}}      │  │  - Inputs    │  │
-- | │  │  - Class Types │  │  - Type-safe    │  │  - Outputs   │  │
-- | │  └────────────────┘  └─────────────────┘  └──────────────┘  │
-- | │                                                              │
-- | │  ┌────────────────────────────────────────────────────────┐ │
-- | │  │                   Serialization                         │ │
-- | │  │  workflowToJson / workflowFromJson (via FFI)           │ │
-- | │  └────────────────────────────────────────────────────────┘ │
-- | └──────────────────────────────────────────────────────────────┘
-- | ```
-- |
-- | ## Parameter Injection
-- |
-- | Workflows can contain placeholders in the format `{{key}}`:
-- |
-- | ```json
-- | {
-- |   "positive_prompt": "{{prompt}}",
-- |   "width": {{width}},
-- |   "seed": {{seed}}
-- | }
-- | ```
-- |
-- | Use `injectParameters` to replace them:
-- |
-- | ```purescript
-- | let result = injectParameters workflow
-- |   [ { key: "prompt", value: ReplaceString "a beautiful sunset" }
-- |   , { key: "width", value: ReplaceInt 1024 }
-- |   , { key: "seed", value: ReplaceInt 42 }
-- |   ]
-- | ```
-- |
-- | ## Banned Constructs
-- |
-- | This module contains ZERO:
-- | - unsafePartial (BANNED)
-- | - unsafeCoerce (BANNED)
-- | - undefined (BANNED)
-- | - Catch-all `_ -> Nothing` patterns (BANNED - all cases explicit)
-- |
-- | Source: ui/src/services/comfyui/workflowTemplates.ts (utilities section)

module Lattice.Services.ComfyUI.WorkflowUtilities
  ( -- * Workflow Validation
    validateWorkflow
  , WorkflowValidationResult
    -- * Workflow Queries
  , getWorkflowInputNodes
  , getWorkflowOutputNodes
  , getWorkflowNodeCount
  , getWorkflowNodeIds
    -- * Parameter Injection
  , injectParameters
  , Replacement(..)
    -- * Workflow Serialization
  , workflowToJson
  , workflowFromJson
    -- * Node Queries
  , isOutputNode
  , isInputNode
  , hasValidConnections
    -- * Export Target Routing
  , exportTargetToString
  , exportTargetFromString
    -- * Types
  , WorkflowNode
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Foldable (any)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

import Lattice.Services.ComfyUI.WorkflowTypes (ExportTarget(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of workflow validation
-- |
-- | @field valid Whether workflow passed all checks
-- | @field errors Critical issues that prevent execution
-- | @field warnings Non-critical issues (workflow may still run)
type WorkflowValidationResult =
  { valid :: Boolean
  , errors :: Array String
  , warnings :: Array String
  }

-- | Replacement value for parameter injection
-- |
-- | @constructor ReplaceString String value (will be JSON-escaped)
-- | @constructor ReplaceInt Integer value
-- | @constructor ReplaceNumber Floating-point value
-- | @constructor ReplaceBool Boolean value
data Replacement
  = ReplaceString String
  | ReplaceInt Int
  | ReplaceNumber Number
  | ReplaceBool Boolean

derive instance eqReplacement :: Eq Replacement

-- | Workflow node for validation
-- |
-- | @field id Unique node identifier
-- | @field classType ComfyUI node class (e.g., "LoadImage", "KSampler")
-- | @field connections Array of input connections to other nodes
type WorkflowNode =
  { id :: String
  , classType :: String
  , connections :: Array NodeConnection
  }

-- | Node connection representing an input slot
-- |
-- | @field inputName Name of the input slot
-- | @field refNodeId ID of the node this connects to
-- | @field outputIndex Which output slot of the referenced node
type NodeConnection =
  { inputName :: String
  , refNodeId :: String
  , outputIndex :: Int
  }

--------------------------------------------------------------------------------
-- FFI Imports
--------------------------------------------------------------------------------

-- | @ffi Parse workflow JSON string to array of nodes
-- | @param json JSON string representing ComfyUI workflow
-- | @returns Either error message or array of parsed nodes
foreign import parseWorkflowImpl :: String -> EffectFnAff (Either String (Array WorkflowNode))

-- | @ffi Serialize workflow nodes to JSON string
-- | @param nodes Array of workflow nodes
-- | @returns JSON string
foreign import serializeWorkflowImpl :: Array WorkflowNode -> String

--------------------------------------------------------------------------------
-- Workflow Validation
--------------------------------------------------------------------------------

-- | Validate a workflow structure
-- |
-- | Checks performed:
-- | - All nodes have a class_type
-- | - All connections reference existing nodes
-- | - Warns if no output nodes are present
-- |
-- | @param nodes Array of workflow nodes to validate
-- | @returns Validation result with errors and warnings
-- |
-- | @example
-- | ```purescript
-- | let result = validateWorkflow nodes
-- | if result.valid
-- |   then submitWorkflow workflow
-- |   else showErrors result.errors
-- | ```
validateWorkflow :: Array WorkflowNode -> WorkflowValidationResult
validateWorkflow nodes =
  let
    nodeIds = map _.id nodes

    -- Check for missing class_type
    missingClassType = Array.filter (\n -> String.null n.classType) nodes
    classTypeErrors = map (\n -> "Node " <> n.id <> ": missing class_type") missingClassType

    -- Check for invalid connections
    connectionErrors = Array.concatMap (validateNodeConnections nodeIds) nodes

    -- Check for output nodes
    hasOutput = any isOutputNode nodes
    outputWarnings = if hasOutput then [] else ["Workflow has no output/save nodes"]

    allErrors = classTypeErrors <> connectionErrors
  in
    { valid: Array.null allErrors
    , errors: allErrors
    , warnings: outputWarnings
    }

-- | Validate connections for a single node
-- |
-- | @internal Used by validateWorkflow
validateNodeConnections :: Array String -> WorkflowNode -> Array String
validateNodeConnections validIds node =
  Array.concatMap (validateConnection node.id validIds) node.connections

-- | Validate a single connection
-- |
-- | @internal Used by validateNodeConnections
validateConnection :: String -> Array String -> NodeConnection -> Array String
validateConnection nodeId validIds conn =
  if Array.elem conn.refNodeId validIds
  then []
  else ["Node " <> nodeId <> "." <> conn.inputName <> ": references non-existent node " <> conn.refNodeId]

--------------------------------------------------------------------------------
-- Workflow Queries
--------------------------------------------------------------------------------

-- | Get IDs of input nodes (LoadImage, VHS_LoadImages, etc.)
-- |
-- | @param nodes Array of workflow nodes
-- | @returns IDs of nodes that load images/video
getWorkflowInputNodes :: Array WorkflowNode -> Array String
getWorkflowInputNodes nodes =
  map _.id (Array.filter isInputNode nodes)

-- | Get IDs of output nodes (Save, Output, Preview, etc.)
-- |
-- | @param nodes Array of workflow nodes
-- | @returns IDs of nodes that save/preview results
getWorkflowOutputNodes :: Array WorkflowNode -> Array String
getWorkflowOutputNodes nodes =
  map _.id (Array.filter isOutputNode nodes)

-- | Get total node count
-- |
-- | @param nodes Array of workflow nodes
-- | @returns Number of nodes
getWorkflowNodeCount :: Array WorkflowNode -> Int
getWorkflowNodeCount = Array.length

-- | Get all node IDs
-- |
-- | @param nodes Array of workflow nodes
-- | @returns Array of all node IDs
getWorkflowNodeIds :: Array WorkflowNode -> Array String
getWorkflowNodeIds = map _.id

--------------------------------------------------------------------------------
-- Node Type Queries
--------------------------------------------------------------------------------

-- | Check if a node is an output node
-- |
-- | Output nodes are those that save, preview, or export results.
-- |
-- | @param node Node to check
-- | @returns True if node is an output type
isOutputNode :: WorkflowNode -> Boolean
isOutputNode node =
  String.contains (String.Pattern "Save") node.classType
  || String.contains (String.Pattern "Output") node.classType
  || String.contains (String.Pattern "Preview") node.classType
  || node.classType == "VHS_VideoCombine"

-- | Check if a node is an input node
-- |
-- | Input nodes are those that load images, video, or other media.
-- |
-- | @param node Node to check
-- | @returns True if node is an input type
isInputNode :: WorkflowNode -> Boolean
isInputNode node =
  node.classType == "LoadImage"
  || node.classType == "VHS_LoadImages"
  || String.contains (String.Pattern "LoadImage") node.classType

-- | Check if node has valid connections (all referenced nodes exist)
-- |
-- | @param validIds Array of valid node IDs
-- | @param node Node to check
-- | @returns True if all connections are valid
hasValidConnections :: Array String -> WorkflowNode -> Boolean
hasValidConnections validIds node =
  Array.all (\c -> Array.elem c.refNodeId validIds) node.connections

--------------------------------------------------------------------------------
-- Parameter Injection
--------------------------------------------------------------------------------

-- | Inject parameters into a workflow JSON string
-- |
-- | Replaces `{{key}}` placeholders with actual values.
-- |
-- | @param workflowJson JSON string with placeholders
-- | @param replacements Array of key-value pairs
-- | @returns JSON string with placeholders replaced
-- |
-- | @example
-- | ```purescript
-- | let workflow = """{"prompt": "{{prompt}}", "seed": {{seed}}}"""
-- | let result = injectParameters workflow
-- |   [ { key: "prompt", value: ReplaceString "a cat" }
-- |   , { key: "seed", value: ReplaceInt 12345 }
-- |   ]
-- | -- Result: {"prompt": "a cat", "seed": 12345}
-- | ```
injectParameters :: String -> Array { key :: String, value :: Replacement } -> String
injectParameters workflowJson replacements =
  Array.foldl injectSingle workflowJson replacements

-- | Inject a single parameter
-- |
-- | @internal Used by injectParameters
injectSingle :: String -> { key :: String, value :: Replacement } -> String
injectSingle json { key, value } =
  let
    placeholder = "{{" <> key <> "}}"
    replacement = escapeForJson value
  in
    String.replaceAll (String.Pattern placeholder) (String.Replacement replacement) json

-- | Escape a replacement value for JSON context
-- |
-- | @internal Used by injectSingle
escapeForJson :: Replacement -> String
escapeForJson replacement = case replacement of
  ReplaceString s -> "\"" <> escapeJsonString s <> "\""
  ReplaceInt n -> show n
  ReplaceNumber n -> show n
  ReplaceBool b -> if b then "true" else "false"

-- | Escape special characters in a string for JSON
-- |
-- | Escapes: backslash, quote, newline, carriage return, tab
-- |
-- | @internal Used by escapeForJson
escapeJsonString :: String -> String
escapeJsonString s =
  s
  # String.replaceAll (String.Pattern "\\") (String.Replacement "\\\\")
  # String.replaceAll (String.Pattern "\"") (String.Replacement "\\\"")
  # String.replaceAll (String.Pattern "\n") (String.Replacement "\\n")
  # String.replaceAll (String.Pattern "\r") (String.Replacement "\\r")
  # String.replaceAll (String.Pattern "\t") (String.Replacement "\\t")

--------------------------------------------------------------------------------
-- Serialization
--------------------------------------------------------------------------------

-- | Convert workflow nodes to JSON string
-- |
-- | @param nodes Array of workflow nodes
-- | @returns JSON string representation
workflowToJson :: Array WorkflowNode -> String
workflowToJson = serializeWorkflowImpl

-- | Parse workflow from JSON string
-- |
-- | @param json JSON string representing ComfyUI workflow
-- | @returns Either error message or array of parsed nodes
workflowFromJson :: String -> Aff (Either String (Array WorkflowNode))
workflowFromJson json = fromEffectFnAff (parseWorkflowImpl json)

--------------------------------------------------------------------------------
-- Export Target Routing
--------------------------------------------------------------------------------

-- | Convert export target to string identifier
-- |
-- | @param target Export target enum value
-- | @returns String identifier for API/routing
exportTargetToString :: ExportTarget -> String
exportTargetToString target = case target of
  TargetWan22I2V -> "wan22-i2v"
  TargetWan22T2V -> "wan22-t2v"
  TargetWan22FunCamera -> "wan22-fun-camera"
  TargetWan22FirstLast -> "wan22-first-last"
  TargetUni3CCamera -> "uni3c-camera"
  TargetUni3CMotion -> "uni3c-motion"
  TargetMotionCtrl -> "motionctrl"
  TargetMotionCtrlSVD -> "motionctrl-svd"
  TargetCogVideoX -> "cogvideox"
  TargetControlNetDepth -> "controlnet-depth"
  TargetControlNetCanny -> "controlnet-canny"
  TargetControlNetLineart -> "controlnet-lineart"
  TargetAnimateDiffCameraCtrl -> "animatediff-cameractrl"
  TargetTTM -> "ttm"
  TargetTTMWan -> "ttm-wan"
  TargetTTMCogVideoX -> "ttm-cogvideox"
  TargetTTMSVD -> "ttm-svd"
  TargetSCAIL -> "scail"
  TargetLightX -> "light-x"
  TargetWanMove -> "wan-move"
  TargetATI -> "ati"
  TargetControlNetPose -> "controlnet-pose"
  TargetCameraComfyUI -> "camera-comfyui"
  TargetCustomWorkflow -> "custom-workflow"

-- | Parse export target from string identifier
-- |
-- | @param str String identifier
-- | @returns Just target if valid, Nothing otherwise
-- |
-- | NOTE: This function uses explicit pattern matching for ALL known targets.
-- | If a new target is added to ExportTarget, this function MUST be updated.
-- | The compiler will NOT warn about missing cases due to String input.
exportTargetFromString :: String -> Maybe ExportTarget
exportTargetFromString str = case str of
  "wan22-i2v" -> Just TargetWan22I2V
  "wan22-t2v" -> Just TargetWan22T2V
  "wan22-fun-camera" -> Just TargetWan22FunCamera
  "wan22-first-last" -> Just TargetWan22FirstLast
  "uni3c-camera" -> Just TargetUni3CCamera
  "uni3c-motion" -> Just TargetUni3CMotion
  "motionctrl" -> Just TargetMotionCtrl
  "motionctrl-svd" -> Just TargetMotionCtrlSVD
  "cogvideox" -> Just TargetCogVideoX
  "controlnet-depth" -> Just TargetControlNetDepth
  "controlnet-canny" -> Just TargetControlNetCanny
  "controlnet-lineart" -> Just TargetControlNetLineart
  "animatediff-cameractrl" -> Just TargetAnimateDiffCameraCtrl
  "ttm" -> Just TargetTTM
  "ttm-wan" -> Just TargetTTMWan
  "ttm-cogvideox" -> Just TargetTTMCogVideoX
  "ttm-svd" -> Just TargetTTMSVD
  "scail" -> Just TargetSCAIL
  "light-x" -> Just TargetLightX
  "wan-move" -> Just TargetWanMove
  "ati" -> Just TargetATI
  "controlnet-pose" -> Just TargetControlNetPose
  "camera-comfyui" -> Just TargetCameraComfyUI
  "custom-workflow" -> Just TargetCustomWorkflow
  -- Unknown string - this is NOT a catch-all for enum cases,
  -- but for invalid input strings
  _ -> Nothing
