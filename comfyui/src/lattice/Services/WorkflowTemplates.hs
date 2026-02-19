-- |
-- Module      : Lattice.Services.WorkflowTemplates
-- Description : Pure workflow template validation and node creation functions
-- 
-- Migrated from ui/src/services/comfyui/workflowTemplates.ts
-- Pure validation and node creation functions for ComfyUI workflow generation
-- Note: Workflow generation functions deferred (require state refactoring)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.WorkflowTemplates
  ( -- Types
    ComfyUINode(..)
  , NodeConnection(..)
  , WorkflowValidationResult(..)
  -- Validation constants
  , minDimension
  , maxDimension
  , maxFrameCount
  , maxFps
  -- Validation functions
  , validateWorkflowParams
  , validateWorkflow
  -- Node creation functions
  , createNode
  , createConnection
  -- Analysis functions
  , getWorkflowInputNodes
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (Maybe(..))
import Data.Aeson (Value(..), ToJSON(..), FromJSON(..), object, (.=), (.:), (.:?), withArray, withObject)
import Data.Aeson.Types (Parser)
import Data.Vector ((!))
import qualified Data.Vector as V

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | ComfyUI node connection (nodeId, outputIndex)
data NodeConnection = NodeConnection
  { connectionNodeId :: Text
  , connectionOutputIndex :: Int
  }
  deriving (Eq, Show)

instance ToJSON NodeConnection where
  toJSON (NodeConnection nodeId outputIndex) = toJSON [toJSON nodeId, toJSON outputIndex]

instance FromJSON NodeConnection where
  parseJSON = withArray "NodeConnection" $ \arr ->
    if V.length arr == 2
    then do
      nodeId <- parseJSON (arr ! 0)
      outputIndex <- parseJSON (arr ! 1)
      return (NodeConnection nodeId outputIndex)
    else fail "NodeConnection must be array of length 2"

-- | ComfyUI node metadata
data NodeMeta = NodeMeta
  { nodeMetaTitle :: Maybe Text
  }
  deriving (Eq, Show)

instance ToJSON NodeMeta where
  toJSON (NodeMeta title) = object $ maybe [] (\t -> ["title" .= t]) title

instance FromJSON NodeMeta where
  parseJSON = withObject "NodeMeta" $ \o -> NodeMeta <$> o .:? "title"

-- | ComfyUI node
data ComfyUINode = ComfyUINode
  { nodeClassType :: Text
  , nodeInputs :: Map Text Value  -- JSON value for flexibility
  , nodeMeta :: Maybe NodeMeta
  }
  deriving (Eq, Show)

instance ToJSON ComfyUINode where
  toJSON (ComfyUINode classType inputs meta) =
    case meta of
      Nothing -> object ["class_type" .= classType, "inputs" .= inputs]
      Just m -> object ["class_type" .= classType, "inputs" .= inputs, "_meta" .= m]

instance FromJSON ComfyUINode where
  parseJSON = withObject "ComfyUINode" $ \o ->
    ComfyUINode <$> o .: "class_type"
                <*> o .: "inputs"
                <*> o .:? "_meta"

-- | Workflow validation result
data WorkflowValidationResult = WorkflowValidationResult
  { validationValid :: Bool
  , validationErrors :: [Text]
  , validationWarnings :: [Text]
  }
  deriving (Eq, Show)

-- | ComfyUI workflow (map of node ID to node)
type ComfyUIWorkflow = Map Text ComfyUINode

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // constants
-- ════════════════════════════════════════════════════════════════════════════

minDimension :: Int
minDimension = 64

maxDimension :: Int
maxDimension = 8192

maxFrameCount :: Int
maxFrameCount = 10000

maxFps :: Double
maxFps = 120.0

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // validation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate workflow parameters
-- Pure function: same inputs → same outputs
-- Returns Left with error messages or Right () if valid
-- Note: MotionData validation deferred (requires schema migration)
validateWorkflowParams ::
  Int ->      -- width
  Int ->      -- height
  Int ->      -- frameCount
  Double ->   -- fps
  Either [Text] ()
validateWorkflowParams width height frameCount fps =
  let errors = concat
        [ validateDimension width "width"
        , validateDimension height "height"
        , validateFrameCount frameCount
        , validateFps fps
        ]
  in if null errors then Right () else Left errors

validateDimension :: Int -> Text -> [Text]
validateDimension dim name =
  if dim < minDimension
  then [name <> " must be at least " <> T.pack (show minDimension)]
  else if dim > maxDimension
       then [name <> " must be at most " <> T.pack (show maxDimension)]
       else []

validateFrameCount :: Int -> [Text]
validateFrameCount frameCount =
  if frameCount <= 0
  then ["frameCount must be a positive number"]
  else if frameCount > maxFrameCount
       then ["frameCount must be at most " <> T.pack (show maxFrameCount)]
       else []

validateFps :: Double -> [Text]
validateFps fps =
  if fps <= 0.0
  then ["fps must be a positive number"]
  else if fps > maxFps
       then ["fps must be at most " <> T.pack (show maxFps)]
       else []

-- | Validate a ComfyUI workflow
-- Pure function: same inputs → same outputs
validateWorkflow :: ComfyUIWorkflow -> WorkflowValidationResult
validateWorkflow workflow =
  let nodeIds = Map.keys workflow
      errors = concatMap (validateNode nodeIds) (Map.toList workflow)
      warnings = checkOutputNodes workflow
  in WorkflowValidationResult (null errors) errors warnings

validateNode :: [Text] -> (Text, ComfyUINode) -> [Text]
validateNode nodeIds (nodeId, node) =
  let classTypeErrors = if T.null (nodeClassType node)
                        then ["Node " <> nodeId <> ": missing class_type"]
                        else []
      connectionErrors = validateConnections nodeIds nodeId (nodeInputs node)
  in classTypeErrors ++ connectionErrors

validateConnections :: [Text] -> Text -> Map Text Value -> [Text]
validateConnections nodeIds nodeId inputs =
  concatMap (\(inputName, inputValue) ->
    case parseConnection inputValue of
      Just (refNodeId, _) ->
        if refNodeId `elem` nodeIds
        then []
        else ["Node " <> nodeId <> "." <> inputName <> ": references non-existent node " <> refNodeId]
      Nothing -> []
  ) (Map.toList inputs)

parseConnection :: Value -> Maybe (Text, Int)
parseConnection val = case val of
  Array arr ->
    if V.length arr == 2
    then case (arr ! 0, arr ! 1) of
           (String nodeId, Number outputIndex) ->
             Just (nodeId, floor outputIndex)
           _ -> Nothing
    else Nothing
  _ -> Nothing

checkOutputNodes :: ComfyUIWorkflow -> [Text]
checkOutputNodes workflow =
  let hasOutput = any (\node ->
        let classType = nodeClassType node
        in "Save" `T.isInfixOf` classType ||
           "Output" `T.isInfixOf` classType ||
           "Preview" `T.isInfixOf` classType
        ) (Map.elems workflow)
  in if hasOutput then [] else ["Workflow has no output/save nodes"]

-- ════════════════════════════════════════════════════════════════════════════
--                                             // node // creation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a ComfyUI node
-- Pure function: same inputs → same outputs
createNode ::
  Text ->                    -- classType
  Map Text Value ->          -- inputs
  Maybe Text ->              -- optional title
  ComfyUINode
createNode classType inputs title =
  ComfyUINode classType inputs (fmap (\t -> NodeMeta (Just t)) title)

-- | Create a node connection
-- Pure function: same inputs → same outputs
createConnection :: Text -> Int -> NodeConnection
createConnection nodeId outputIndex = NodeConnection nodeId outputIndex

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // analysis // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Get input nodes in workflow (LoadImage nodes)
-- Pure function: same inputs → same outputs
getWorkflowInputNodes :: ComfyUIWorkflow -> [Text]
getWorkflowInputNodes workflow =
  map fst (filter (\(_, node) ->
    let classType = nodeClassType node
    in classType == "LoadImage" ||
       classType == "VHS_LoadImages" ||
       "LoadImage" `T.isInfixOf` classType
  ) (Map.toList workflow))
