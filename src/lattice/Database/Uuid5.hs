-- |
-- Module      : Lattice.Database.Uuid5
-- Description : UUID5 (Deterministic Name-Based UUID) Implementation
-- 
-- RFC 4122 compliant UUID5 generation for deterministic ID tracking.
-- All IDs in the system use UUID5 for deterministic tracking.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Database.Uuid5
  ( Uuid5(..)
  , uuid5
  , generateLayerId
  , generateKeyframeId
  , generateCompositionId
  , generateEffectId
  , generateTextAnimatorId
  , generatePropertyDriverId
  , generateCameraId
  , generateCameraKeyframeId
  , generateParticleSystemId
  , generateParticleEmitterId
  , generateParticleForceId
  , generatePhysicsBodyId
  , generatePhysicsJointId
  , generateExportJobId
  , generatePresetId
  , generateTemplateId
  , generateAssetId
  , generateChatMessageId
  , generateMarkerId
  , generateMeshWarpPinId
  , generateAudioAnalysisId
  , generateAIModelId
  , generateSegmentationId
  , generateVectorizationId
  , generateTemplateExposedPropertyId
  , generateEventId
  , generateMetricId
  , generateProjectId
  , generateFeatureFlagId
  , generatePhysicsSpaceId
  , generateAudioTrackId
  , generateAudioReactivityId
  , generateCameraPathId
  , generateLayerMaskId
  , generateLayerStylesId
  , generateExpressionId
  , generateRenderSettingsId
  , generateExportTemplateId
  , generatePreprocessorId
  , generateMeshWarpMeshId
  , generatePhysicsClothId
  , generatePhysicsRagdollId
  , generatePhysicsRigidBodyId
  , generateParticleId
  , generateParticleGroupId
  , generateParticleConnectionId
  , generateParticleTrailId
  , generateParticleSubEmitterId
  , generateAudioBeatId
  , generateAudioPeakId
  , generateMidiNoteId
  , generateMidiCCId
  , generateNestedCompId
  , generateCompInstanceId
  , generateTextLayerId
  , generateSplineControlPointId
  , generateSplineAnchorPointId
  , generateShapePathId
  , generateShapePathCommandId
  , generateGuideId
  , generateSpriteSheetId
  , generateSpriteFrameId
  , generateSvgDocumentId
  , generateSvgPathId
  , generateMaterialId
  , generateTextureId
  , generateMeshId
  , generateMeshVertexId
  , generateMeshFaceId
  , generateRenderFrameId
  , generateRenderTileId
  , generateWorkflowNodeId
  , generateWorkflowConnectionId
  , generateToolCallId
  , generateUserActionId
  , generateSessionId
  , generateCacheEntryId
  , generateFrameCacheEntryId
  , generateTimelineTrackId
  , generateTimelineClipId
  , generateColorStopId
  , generateGradientId
  , generateFilterId
  , generateBlendModeOverrideId
  , generateTransformConstraintId
  , generateParentConstraintId
  , generateLookAtConstraintId
  , generatePathConstraintId
  , generatePoseBoneId
  , generatePoseKeyframeId
  , generateControlPointId
  , generateDeformationHandleId
  , generateLightId
  , generateEnvironmentMapId
  , generateShaderId
  , generateShaderUniformId
  , generateComputeShaderId
  , generateRenderPassId
  , generateRenderTargetId
  , generatePostProcessingEffectId
  , generateViewportId
  , generateSelectionId
  , generateClipboardEntryId
  , generateUndoRedoStateId
  , generateHistoryEntryId
  , generateWorkspaceLayoutId
  , generateWorkspacePanelId
  , generateKeyboardShortcutId
  , generatePluginId
  , generatePluginInstanceId
  , generatePluginHookId
  , generateWebhookId
  , generateWebhookEventId
  , generateApiKeyId
  , generateApiRequestId
  , generateSubscriptionId
  , generatePaymentId
  , generateNotificationId
  , generateCollaborationSessionId
  , generateCollaborationChangeId
  , generateCommentId
  , generateReviewId
  , generateReviewCommentId
  , generateTagId
  , generateTagAssignmentId
  , generateCollectionId
  , generateCollectionItemId
  , generateSearchQueryId
  , generateSearchResultId
  , generateBookmarkId
  , generateFavoriteId
  , generateShareLinkId
  , generateDownloadId
  , generateImportJobId
  , generateImportItemId
  , generateSyncJobId
  , generateBackupId
  , generateRestorePointId
  , generateVersionId
  , generateBranchId
  , generateCommitId
  , generateDiffId
  , generateMergeId
  , generateConflictId
  , generateResolutionId
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Crypto.Hash.SHA1 as SHA1
import qualified Data.ByteString as BS
import Data.Bits (Bits(..), (.&.), (.|.), shiftR)
import Data.Word (Word8)

-- | UUID5 namespace
newtype Uuid5Namespace = Uuid5Namespace Text
  deriving (Show, Eq)

-- | UUID5 value (deterministic UUID)
newtype Uuid5 = Uuid5 { unUuid5 :: Text }
  deriving (Show, Eq, Ord)

-- | Lattice-specific namespace
latticeNamespace :: Uuid5Namespace
latticeNamespace = Uuid5Namespace "a1b2c3d4-e5f6-4789-a012-3456789abcde"

-- | Generate UUID5 from namespace and name (RFC 4122)
uuid5 :: Uuid5Namespace -> Text -> Uuid5
uuid5 (Uuid5Namespace namespace) name = 
  let
    -- Convert namespace UUID to bytes (remove hyphens)
    namespaceBytes = uuidToBytes namespace
    -- Convert name to UTF-8 bytes
    nameBytes = TE.encodeUtf8 name
    -- Concatenate namespace + name
    combined = BS.append namespaceBytes nameBytes
    -- Compute SHA-1 hash
    hash = SHA1.hash combined
    -- Extract first 16 bytes
    hashBytes = BS.take 16 hash
    -- Set version (5) and variant bits
    uuidBytes = BS.pack $ zipWith setVersionVariant (BS.unpack hashBytes) [0..]
    -- Convert to UUID string
  in
    Uuid5 (bytesToUuid uuidBytes)
  where
    uuidToBytes :: Text -> BS.ByteString
    uuidToBytes uuid = 
      let hex = T.replace "-" "" uuid
          bytes = map (readHexByte . T.unpack) $ chunksOf 2 hex
      in BS.pack bytes
    
    readHexByte :: String -> Word8
    readHexByte [a, b] = fromIntegral $ (hexDigit a * 16) + hexDigit b
    readHexByte _ = 0
    
    hexDigit :: Char -> Int
    hexDigit c
      | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
      | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
      | c >= 'A' && c <= 'F' = fromEnum c - fromEnum 'A' + 10
      | otherwise = 0
    
    chunksOf :: Int -> Text -> [Text]
    chunksOf n txt
      | T.null txt = []
      | otherwise = T.take n txt : chunksOf n (T.drop n txt)
    
    setVersionVariant :: Word8 -> Int -> Word8
    setVersionVariant byte idx
      | idx == 6 = (byte .&. 0x0f) .|. 0x50  -- Version 5
      | idx == 8 = (byte .&. 0x3f) .|. 0x80  -- Variant RFC 4122
      | otherwise = byte
    
    bytesToUuid :: BS.ByteString -> Text
    bytesToUuid bytes =
      let hex = T.concat $ map (T.pack . showHex) $ BS.unpack bytes
          parts = [T.take 8 hex, T.take 4 (T.drop 8 hex), T.take 4 (T.drop 12 hex), 
                   T.take 4 (T.drop 16 hex), T.drop 20 hex]
      in T.intercalate "-" parts
    
    showHex :: Word8 -> String
    showHex w = 
      let hex = "0123456789abcdef"
          high = fromIntegral ((w `shiftR` 4) .&. 0x0f) :: Int
          low = fromIntegral (w .&. 0x0f) :: Int
      in [hex !! high, hex !! low]

-- Helper functions for all entity types
generateLayerId :: Text -> Maybe Text -> Int -> Uuid5
generateLayerId layerName parentId index =
  let name = case parentId of
        Nothing -> T.concat [layerName, ":root:", T.pack (show index)]
        Just pid -> T.concat [layerName, ":", pid, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateKeyframeId :: Text -> Text -> Int -> Text -> Uuid5
generateKeyframeId layerId propertyPath frame value =
  let name = T.concat [layerId, ":", propertyPath, ":", T.pack (show frame), ":", value]
  in uuid5 latticeNamespace name

generateCompositionId :: Text -> Text -> Int -> Uuid5
generateCompositionId projectId compositionName index =
  let name = T.concat ["composition:", projectId, ":", compositionName, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateEffectId :: Text -> Text -> Int -> Uuid5
generateEffectId layerId effectType orderIndex =
  let name = T.concat ["effect:", layerId, ":", effectType, ":", T.pack (show orderIndex)]
  in uuid5 latticeNamespace name

generateTextAnimatorId :: Text -> Text -> Int -> Uuid5
generateTextAnimatorId textLayerId animatorType orderIndex =
  let name = T.concat ["text-animator:", textLayerId, ":", animatorType, ":", T.pack (show orderIndex)]
  in uuid5 latticeNamespace name

generatePropertyDriverId :: Text -> Text -> Uuid5
generatePropertyDriverId layerId propertyPath =
  let name = T.concat ["property-driver:", layerId, ":", propertyPath]
  in uuid5 latticeNamespace name

generateCameraId :: Text -> Text -> Int -> Uuid5
generateCameraId compositionId cameraName index =
  let name = T.concat ["camera:", compositionId, ":", cameraName, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateCameraKeyframeId :: Text -> Int -> Uuid5
generateCameraKeyframeId cameraId frame =
  let name = T.concat ["camera-keyframe:", cameraId, ":", T.pack (show frame)]
  in uuid5 latticeNamespace name

generateParticleSystemId :: Text -> Int -> Uuid5
generateParticleSystemId layerId index =
  let name = T.concat ["particle-system:", layerId, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateParticleEmitterId :: Text -> Int -> Uuid5
generateParticleEmitterId particleSystemId index =
  let name = T.concat ["particle-emitter:", particleSystemId, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateParticleForceId :: Text -> Text -> Int -> Uuid5
generateParticleForceId particleSystemId forceType index =
  let name = T.concat ["particle-force:", particleSystemId, ":", forceType, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generatePhysicsBodyId :: Text -> Text -> Int -> Uuid5
generatePhysicsBodyId physicsSpaceId layerId index =
  let name = T.concat ["physics-body:", physicsSpaceId, ":", layerId, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generatePhysicsJointId :: Text -> Text -> Text -> Text -> Uuid5
generatePhysicsJointId physicsSpaceId bodyAId bodyBId jointType =
  let name = T.concat ["physics-joint:", physicsSpaceId, ":", bodyAId, ":", bodyBId, ":", jointType]
  in uuid5 latticeNamespace name

generateExportJobId :: Text -> Maybe Text -> Int -> Uuid5
generateExportJobId projectId compositionId timestamp =
  let compPart = maybe "global" id compositionId
      name = T.concat ["export-job:", projectId, ":", compPart, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generatePresetId :: Text -> Text -> Maybe Text -> Uuid5
generatePresetId presetName presetType projectId =
  let projPart = maybe "global" id projectId
      name = T.concat ["preset:", presetType, ":", presetName, ":", projPart]
  in uuid5 latticeNamespace name

generateTemplateId :: Text -> Maybe Text -> Text -> Uuid5
generateTemplateId templateName projectId version =
  let projPart = maybe "global" id projectId
      name = T.concat ["template:", templateName, ":", projPart, ":", version]
  in uuid5 latticeNamespace name

generateAssetId :: Text -> Text -> Text -> Uuid5
generateAssetId projectId assetName assetType =
  let name = T.concat ["asset:", projectId, ":", assetType, ":", assetName]
  in uuid5 latticeNamespace name

generateChatMessageId :: Maybe Text -> Text -> Int -> Text -> Uuid5
generateChatMessageId projectId role timestamp contentHash =
  let projPart = maybe "global" id projectId
      name = T.concat ["chat-message:", projPart, ":", role, ":", T.pack (show timestamp), ":", contentHash]
  in uuid5 latticeNamespace name

generateMarkerId :: Text -> Int -> Text -> Uuid5
generateMarkerId compositionId frame label =
  let name = T.concat ["marker:", compositionId, ":", T.pack (show frame), ":", label]
  in uuid5 latticeNamespace name

generateMeshWarpPinId :: Text -> Int -> Uuid5
generateMeshWarpPinId layerId pinIndex =
  let name = T.concat ["mesh-warp-pin:", layerId, ":", T.pack (show pinIndex)]
  in uuid5 latticeNamespace name

generateAudioAnalysisId :: Text -> Text -> Int -> Uuid5
generateAudioAnalysisId audioTrackId analysisType frame =
  let name = T.concat ["audio-analysis:", audioTrackId, ":", analysisType, ":", T.pack (show frame)]
  in uuid5 latticeNamespace name

generateAIModelId :: Text -> Text -> Uuid5
generateAIModelId modelName provider =
  let name = T.concat ["ai-model:", provider, ":", modelName]
  in uuid5 latticeNamespace name

generateSegmentationId :: Text -> Text -> Int -> Uuid5
generateSegmentationId layerId method timestamp =
  let name = T.concat ["segmentation:", layerId, ":", method, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateVectorizationId :: Text -> Text -> Int -> Uuid5
generateVectorizationId layerId method timestamp =
  let name = T.concat ["vectorization:", layerId, ":", method, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateTemplateExposedPropertyId :: Text -> Text -> Uuid5
generateTemplateExposedPropertyId templateId propertyPath =
  let name = T.concat ["template-property:", templateId, ":", propertyPath]
  in uuid5 latticeNamespace name

generateEventId :: Text -> Maybe Text -> Int -> Text -> Uuid5
generateEventId eventType projectId timestamp dataHash =
  let projPart = maybe "global" id projectId
      name = T.concat ["event:", eventType, ":", projPart, ":", T.pack (show timestamp), ":", dataHash]
  in uuid5 latticeNamespace name

generateMetricId :: Text -> Maybe Text -> Int -> Uuid5
generateMetricId metricName projectId timestamp =
  let projPart = maybe "global" id projectId
      name = T.concat ["metric:", metricName, ":", projPart, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateProjectId :: Text -> Int -> Uuid5
generateProjectId projectName timestamp =
  let name = T.concat ["project:", projectName, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateFeatureFlagId :: Text -> Uuid5
generateFeatureFlagId flagName =
  let name = T.concat ["feature-flag:", flagName]
  in uuid5 latticeNamespace name

generatePhysicsSpaceId :: Text -> Uuid5
generatePhysicsSpaceId compositionId =
  let name = T.concat ["physics-space:", compositionId]
  in uuid5 latticeNamespace name

generateAudioTrackId :: Text -> Text -> Int -> Uuid5
generateAudioTrackId compositionId trackName index =
  let name = T.concat ["audio-track:", compositionId, ":", trackName, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateAudioReactivityId :: Text -> Text -> Text -> Uuid5
generateAudioReactivityId layerId audioTrackId propertyPath =
  let name = T.concat ["audio-reactivity:", layerId, ":", audioTrackId, ":", propertyPath]
  in uuid5 latticeNamespace name

generateCameraPathId :: Text -> Uuid5
generateCameraPathId cameraId =
  let name = T.concat ["camera-path:", cameraId]
  in uuid5 latticeNamespace name

generateLayerMaskId :: Text -> Text -> Int -> Uuid5
generateLayerMaskId layerId maskName index =
  let name = T.concat ["layer-mask:", layerId, ":", maskName, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateLayerStylesId :: Text -> Uuid5
generateLayerStylesId layerId =
  let name = T.concat ["layer-styles:", layerId]
  in uuid5 latticeNamespace name

generateExpressionId :: Text -> Text -> Uuid5
generateExpressionId layerId propertyPath =
  let name = T.concat ["expression:", layerId, ":", propertyPath]
  in uuid5 latticeNamespace name

generateRenderSettingsId :: Text -> Uuid5
generateRenderSettingsId compositionId =
  let name = T.concat ["render-settings:", compositionId]
  in uuid5 latticeNamespace name

generateExportTemplateId :: Text -> Maybe Text -> Uuid5
generateExportTemplateId templateName projectId =
  let projPart = maybe "global" id projectId
      name = T.concat ["export-template:", templateName, ":", projPart]
  in uuid5 latticeNamespace name

generatePreprocessorId :: Text -> Uuid5
generatePreprocessorId preprocessorName =
  let name = T.concat ["preprocessor:", preprocessorName]
  in uuid5 latticeNamespace name

generateMeshWarpMeshId :: Text -> Uuid5
generateMeshWarpMeshId layerId =
  let name = T.concat ["mesh-warp-mesh:", layerId]
  in uuid5 latticeNamespace name

generatePhysicsClothId :: Text -> Text -> Uuid5
generatePhysicsClothId physicsSpaceId layerId =
  let name = T.concat ["physics-cloth:", physicsSpaceId, ":", layerId]
  in uuid5 latticeNamespace name

generatePhysicsRagdollId :: Text -> Text -> Uuid5
generatePhysicsRagdollId physicsSpaceId layerId =
  let name = T.concat ["physics-ragdoll:", physicsSpaceId, ":", layerId]
  in uuid5 latticeNamespace name

generatePhysicsRigidBodyId :: Text -> Uuid5
generatePhysicsRigidBodyId physicsBodyId =
  let name = T.concat ["physics-rigid-body:", physicsBodyId]
  in uuid5 latticeNamespace name

-- | Generate UUID5 for an individual particle
-- CRITICAL: Every particle needs UUID5 for determinism at scale.
-- For 400k particles per layer, this ensures:
-- - Same seed + index = same particle ID
-- - Deterministic tracking across frames
-- - No collisions (SHA-1 hash space)
-- - Memory efficient (just string IDs)
generateParticleId :: Text -> Text -> Int -> Int -> Int -> Uuid5
generateParticleId layerId emitterId particleIndex spawnFrame seed =
  let name = T.concat ["particle:", layerId, ":", emitterId, ":", T.pack (show particleIndex), ":", T.pack (show spawnFrame), ":", T.pack (show seed)]
  in uuid5 latticeNamespace name

generateParticleGroupId :: Text -> Text -> Int -> Uuid5
generateParticleGroupId layerId groupName index =
  let name = T.concat ["particle-group:", layerId, ":", groupName, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateParticleConnectionId :: Text -> Text -> Text -> Text -> Uuid5
generateParticleConnectionId particleSystemId particleAId particleBId connectionType =
  let (idA, idB) = if particleAId < particleBId then (particleAId, particleBId) else (particleBId, particleAId)
      name = T.concat ["particle-connection:", particleSystemId, ":", connectionType, ":", idA, ":", idB]
  in uuid5 latticeNamespace name

generateParticleTrailId :: Text -> Int -> Uuid5
generateParticleTrailId particleId trailIndex =
  let name = T.concat ["particle-trail:", particleId, ":", T.pack (show trailIndex)]
  in uuid5 latticeNamespace name

generateParticleSubEmitterId :: Text -> Text -> Int -> Uuid5
generateParticleSubEmitterId parentParticleId subEmitterType instanceIndex =
  let name = T.concat ["particle-sub-emitter:", parentParticleId, ":", subEmitterType, ":", T.pack (show instanceIndex)]
  in uuid5 latticeNamespace name

generateAudioBeatId :: Text -> Int -> Int -> Uuid5
generateAudioBeatId audioTrackId frame beatIndex =
  let name = T.concat ["audio-beat:", audioTrackId, ":", T.pack (show frame), ":", T.pack (show beatIndex)]
  in uuid5 latticeNamespace name

generateAudioPeakId :: Text -> Int -> Text -> Uuid5
generateAudioPeakId audioTrackId frame frequencyBand =
  let name = T.concat ["audio-peak:", audioTrackId, ":", T.pack (show frame), ":", frequencyBand]
  in uuid5 latticeNamespace name

generateMidiNoteId :: Text -> Int -> Int -> Int -> Int -> Uuid5
generateMidiNoteId midiTrackId channel note frame velocity =
  let name = T.concat ["midi-note:", midiTrackId, ":", T.pack (show channel), ":", T.pack (show note), ":", T.pack (show frame), ":", T.pack (show velocity)]
  in uuid5 latticeNamespace name

generateMidiCCId :: Text -> Int -> Int -> Int -> Int -> Uuid5
generateMidiCCId midiTrackId channel ccNumber frame value =
  let name = T.concat ["midi-cc:", midiTrackId, ":", T.pack (show channel), ":", T.pack (show ccNumber), ":", T.pack (show frame), ":", T.pack (show value)]
  in uuid5 latticeNamespace name

generateNestedCompId :: Text -> Text -> Int -> Uuid5
generateNestedCompId parentCompId nestedCompId instanceIndex =
  let name = T.concat ["nested-comp:", parentCompId, ":", nestedCompId, ":", T.pack (show instanceIndex)]
  in uuid5 latticeNamespace name

generateCompInstanceId :: Text -> Int -> Int -> Uuid5
generateCompInstanceId compId startFrame endFrame =
  let name = T.concat ["comp-instance:", compId, ":", T.pack (show startFrame), ":", T.pack (show endFrame)]
  in uuid5 latticeNamespace name

generateTextLayerId :: Text -> Uuid5
generateTextLayerId layerId =
  let name = T.concat ["text-layer:", layerId]
  in uuid5 latticeNamespace name

generateSplineControlPointId :: Text -> Int -> Int -> Uuid5
generateSplineControlPointId splineLayerId pointIndex segmentIndex =
  let name = T.concat ["spline-control-point:", splineLayerId, ":", T.pack (show segmentIndex), ":", T.pack (show pointIndex)]
  in uuid5 latticeNamespace name

generateSplineAnchorPointId :: Text -> Int -> Uuid5
generateSplineAnchorPointId splineLayerId anchorIndex =
  let name = T.concat ["spline-anchor-point:", splineLayerId, ":", T.pack (show anchorIndex)]
  in uuid5 latticeNamespace name

generateShapePathId :: Text -> Int -> Uuid5
generateShapePathId layerId pathIndex =
  let name = T.concat ["shape-path:", layerId, ":", T.pack (show pathIndex)]
  in uuid5 latticeNamespace name

generateShapePathCommandId :: Text -> Int -> Uuid5
generateShapePathCommandId pathId commandIndex =
  let name = T.concat ["shape-path-command:", pathId, ":", T.pack (show commandIndex)]
  in uuid5 latticeNamespace name

generateGuideId :: Text -> Text -> Int -> Uuid5
generateGuideId compositionId guideType index =
  let name = T.concat ["guide:", compositionId, ":", guideType, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateSpriteSheetId :: Text -> Text -> Int -> Uuid5
generateSpriteSheetId projectId spriteSheetName timestamp =
  let name = T.concat ["sprite-sheet:", projectId, ":", spriteSheetName, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateSpriteFrameId :: Text -> Int -> Uuid5
generateSpriteFrameId spriteSheetId frameIndex =
  let name = T.concat ["sprite-frame:", spriteSheetId, ":", T.pack (show frameIndex)]
  in uuid5 latticeNamespace name

generateSvgDocumentId :: Text -> Text -> Int -> Uuid5
generateSvgDocumentId projectId svgName timestamp =
  let name = T.concat ["svg-document:", projectId, ":", svgName, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateSvgPathId :: Text -> Int -> Uuid5
generateSvgPathId svgDocumentId pathIndex =
  let name = T.concat ["svg-path:", svgDocumentId, ":", T.pack (show pathIndex)]
  in uuid5 latticeNamespace name

generateMaterialId :: Text -> Text -> Text -> Uuid5
generateMaterialId projectId materialName materialType =
  let name = T.concat ["material:", projectId, ":", materialType, ":", materialName]
  in uuid5 latticeNamespace name

generateTextureId :: Text -> Text -> Text -> Uuid5
generateTextureId projectId textureName textureType =
  let name = T.concat ["texture:", projectId, ":", textureType, ":", textureName]
  in uuid5 latticeNamespace name

generateMeshId :: Text -> Text -> Text -> Uuid5
generateMeshId projectId meshName meshType =
  let name = T.concat ["mesh:", projectId, ":", meshType, ":", meshName]
  in uuid5 latticeNamespace name

generateMeshVertexId :: Text -> Int -> Uuid5
generateMeshVertexId meshId vertexIndex =
  let name = T.concat ["mesh-vertex:", meshId, ":", T.pack (show vertexIndex)]
  in uuid5 latticeNamespace name

generateMeshFaceId :: Text -> Int -> Uuid5
generateMeshFaceId meshId faceIndex =
  let name = T.concat ["mesh-face:", meshId, ":", T.pack (show faceIndex)]
  in uuid5 latticeNamespace name

generateRenderFrameId :: Text -> Int -> Uuid5
generateRenderFrameId exportJobId frame =
  let name = T.concat ["render-frame:", exportJobId, ":", T.pack (show frame)]
  in uuid5 latticeNamespace name

generateRenderTileId :: Text -> Int -> Int -> Uuid5
generateRenderTileId renderFrameId tileX tileY =
  let name = T.concat ["render-tile:", renderFrameId, ":", T.pack (show tileX), ":", T.pack (show tileY)]
  in uuid5 latticeNamespace name

generateWorkflowNodeId :: Text -> Text -> Int -> Uuid5
generateWorkflowNodeId workflowId nodeType nodeIndex =
  let name = T.concat ["workflow-node:", workflowId, ":", nodeType, ":", T.pack (show nodeIndex)]
  in uuid5 latticeNamespace name

generateWorkflowConnectionId :: Text -> Text -> Text -> Int -> Int -> Uuid5
generateWorkflowConnectionId workflowId sourceNodeId targetNodeId outputIndex inputIndex =
  let name = T.concat ["workflow-connection:", workflowId, ":", sourceNodeId, ":", targetNodeId, ":", T.pack (show outputIndex), ":", T.pack (show inputIndex)]
  in uuid5 latticeNamespace name

generateToolCallId :: Text -> Text -> Int -> Uuid5
generateToolCallId chatMessageId toolName callIndex =
  let name = T.concat ["tool-call:", chatMessageId, ":", toolName, ":", T.pack (show callIndex)]
  in uuid5 latticeNamespace name

generateUserActionId :: Text -> Text -> Int -> Uuid5
generateUserActionId userId actionType timestamp =
  let name = T.concat ["user-action:", userId, ":", actionType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateSessionId :: Text -> Int -> Uuid5
generateSessionId userId timestamp =
  let name = T.concat ["session:", userId, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateCacheEntryId :: Text -> Text -> Uuid5
generateCacheEntryId cacheKey cacheType =
  let name = T.concat ["cache-entry:", cacheType, ":", cacheKey]
  in uuid5 latticeNamespace name

generateFrameCacheEntryId :: Text -> Int -> Text -> Uuid5
generateFrameCacheEntryId layerId frame cacheType =
  let name = T.concat ["frame-cache-entry:", layerId, ":", T.pack (show frame), ":", cacheType]
  in uuid5 latticeNamespace name

generateTimelineTrackId :: Text -> Text -> Int -> Uuid5
generateTimelineTrackId compositionId trackType trackIndex =
  let name = T.concat ["timeline-track:", compositionId, ":", trackType, ":", T.pack (show trackIndex)]
  in uuid5 latticeNamespace name

generateTimelineClipId :: Text -> Int -> Int -> Uuid5
generateTimelineClipId trackId startFrame endFrame =
  let name = T.concat ["timeline-clip:", trackId, ":", T.pack (show startFrame), ":", T.pack (show endFrame)]
  in uuid5 latticeNamespace name

generateColorStopId :: Text -> Int -> Uuid5
generateColorStopId gradientId stopIndex =
  let name = T.concat ["color-stop:", gradientId, ":", T.pack (show stopIndex)]
  in uuid5 latticeNamespace name

generateGradientId :: Text -> Text -> Int -> Uuid5
generateGradientId layerId gradientType index =
  let name = T.concat ["gradient:", layerId, ":", gradientType, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateFilterId :: Text -> Text -> Int -> Uuid5
generateFilterId layerId filterType index =
  let name = T.concat ["filter:", layerId, ":", filterType, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateBlendModeOverrideId :: Text -> Text -> Uuid5
generateBlendModeOverrideId layerId targetLayerId =
  let name = T.concat ["blend-mode-override:", layerId, ":", targetLayerId]
  in uuid5 latticeNamespace name

generateTransformConstraintId :: Text -> Text -> Uuid5
generateTransformConstraintId layerId constraintType =
  let name = T.concat ["transform-constraint:", layerId, ":", constraintType]
  in uuid5 latticeNamespace name

generateParentConstraintId :: Text -> Text -> Uuid5
generateParentConstraintId layerId parentLayerId =
  let name = T.concat ["parent-constraint:", layerId, ":", parentLayerId]
  in uuid5 latticeNamespace name

generateLookAtConstraintId :: Text -> Text -> Uuid5
generateLookAtConstraintId layerId targetLayerId =
  let name = T.concat ["look-at-constraint:", layerId, ":", targetLayerId]
  in uuid5 latticeNamespace name

generatePathConstraintId :: Text -> Text -> Uuid5
generatePathConstraintId layerId pathLayerId =
  let name = T.concat ["path-constraint:", layerId, ":", pathLayerId]
  in uuid5 latticeNamespace name

generatePoseBoneId :: Text -> Text -> Int -> Uuid5
generatePoseBoneId poseLayerId boneName boneIndex =
  let name = T.concat ["pose-bone:", poseLayerId, ":", boneName, ":", T.pack (show boneIndex)]
  in uuid5 latticeNamespace name

generatePoseKeyframeId :: Text -> Text -> Int -> Uuid5
generatePoseKeyframeId poseLayerId boneId frame =
  let name = T.concat ["pose-keyframe:", poseLayerId, ":", boneId, ":", T.pack (show frame)]
  in uuid5 latticeNamespace name

generateControlPointId :: Text -> Text -> Int -> Uuid5
generateControlPointId layerId controlPointType pointIndex =
  let name = T.concat ["control-point:", layerId, ":", controlPointType, ":", T.pack (show pointIndex)]
  in uuid5 latticeNamespace name

generateDeformationHandleId :: Text -> Int -> Uuid5
generateDeformationHandleId layerId handleIndex =
  let name = T.concat ["deformation-handle:", layerId, ":", T.pack (show handleIndex)]
  in uuid5 latticeNamespace name

generateLightId :: Text -> Text -> Int -> Uuid5
generateLightId compositionId lightType lightIndex =
  let name = T.concat ["light:", compositionId, ":", lightType, ":", T.pack (show lightIndex)]
  in uuid5 latticeNamespace name

generateEnvironmentMapId :: Text -> Text -> Uuid5
generateEnvironmentMapId projectId envMapName =
  let name = T.concat ["environment-map:", projectId, ":", envMapName]
  in uuid5 latticeNamespace name

generateShaderId :: Text -> Text -> Text -> Uuid5
generateShaderId projectId shaderName shaderType =
  let name = T.concat ["shader:", projectId, ":", shaderType, ":", shaderName]
  in uuid5 latticeNamespace name

generateShaderUniformId :: Text -> Text -> Uuid5
generateShaderUniformId shaderId uniformName =
  let name = T.concat ["shader-uniform:", shaderId, ":", uniformName]
  in uuid5 latticeNamespace name

generateComputeShaderId :: Text -> Text -> Uuid5
generateComputeShaderId projectId shaderName =
  let name = T.concat ["compute-shader:", projectId, ":", shaderName]
  in uuid5 latticeNamespace name

generateRenderPassId :: Text -> Text -> Int -> Uuid5
generateRenderPassId compositionId passType passIndex =
  let name = T.concat ["render-pass:", compositionId, ":", passType, ":", T.pack (show passIndex)]
  in uuid5 latticeNamespace name

generateRenderTargetId :: Text -> Int -> Uuid5
generateRenderTargetId renderPassId targetIndex =
  let name = T.concat ["render-target:", renderPassId, ":", T.pack (show targetIndex)]
  in uuid5 latticeNamespace name

generatePostProcessingEffectId :: Text -> Text -> Int -> Uuid5
generatePostProcessingEffectId compositionId effectType index =
  let name = T.concat ["post-processing-effect:", compositionId, ":", effectType, ":", T.pack (show index)]
  in uuid5 latticeNamespace name

generateViewportId :: Text -> Int -> Uuid5
generateViewportId compositionId viewportIndex =
  let name = T.concat ["viewport:", compositionId, ":", T.pack (show viewportIndex)]
  in uuid5 latticeNamespace name

generateSelectionId :: Text -> Int -> Uuid5
generateSelectionId userId timestamp =
  let name = T.concat ["selection:", userId, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateClipboardEntryId :: Text -> Text -> Int -> Uuid5
generateClipboardEntryId userId entryType timestamp =
  let name = T.concat ["clipboard-entry:", userId, ":", entryType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateUndoRedoStateId :: Text -> Int -> Uuid5
generateUndoRedoStateId projectId stateIndex =
  let name = T.concat ["undo-redo-state:", projectId, ":", T.pack (show stateIndex)]
  in uuid5 latticeNamespace name

generateHistoryEntryId :: Text -> Int -> Uuid5
generateHistoryEntryId projectId entryIndex =
  let name = T.concat ["history-entry:", projectId, ":", T.pack (show entryIndex)]
  in uuid5 latticeNamespace name

generateWorkspaceLayoutId :: Text -> Text -> Uuid5
generateWorkspaceLayoutId userId layoutName =
  let name = T.concat ["workspace-layout:", userId, ":", layoutName]
  in uuid5 latticeNamespace name

generateWorkspacePanelId :: Text -> Text -> Int -> Uuid5
generateWorkspacePanelId layoutId panelType panelIndex =
  let name = T.concat ["workspace-panel:", layoutId, ":", panelType, ":", T.pack (show panelIndex)]
  in uuid5 latticeNamespace name

generateKeyboardShortcutId :: Text -> Text -> Uuid5
generateKeyboardShortcutId actionId keyCombo =
  let name = T.concat ["keyboard-shortcut:", actionId, ":", keyCombo]
  in uuid5 latticeNamespace name

generatePluginId :: Text -> Text -> Uuid5
generatePluginId pluginName pluginVersion =
  let name = T.concat ["plugin:", pluginName, ":", pluginVersion]
  in uuid5 latticeNamespace name

generatePluginInstanceId :: Text -> Int -> Uuid5
generatePluginInstanceId pluginId instanceIndex =
  let name = T.concat ["plugin-instance:", pluginId, ":", T.pack (show instanceIndex)]
  in uuid5 latticeNamespace name

generatePluginHookId :: Text -> Text -> Uuid5
generatePluginHookId pluginId hookName =
  let name = T.concat ["plugin-hook:", pluginId, ":", hookName]
  in uuid5 latticeNamespace name

generateWebhookId :: Text -> Text -> Uuid5
generateWebhookId projectId webhookName =
  let name = T.concat ["webhook:", projectId, ":", webhookName]
  in uuid5 latticeNamespace name

generateWebhookEventId :: Text -> Text -> Int -> Uuid5
generateWebhookEventId webhookId eventType timestamp =
  let name = T.concat ["webhook-event:", webhookId, ":", eventType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateApiKeyId :: Text -> Text -> Uuid5
generateApiKeyId userId keyName =
  let name = T.concat ["api-key:", userId, ":", keyName]
  in uuid5 latticeNamespace name

generateApiRequestId :: Text -> Text -> Int -> Uuid5
generateApiRequestId apiKeyId requestHash timestamp =
  let name = T.concat ["api-request:", apiKeyId, ":", requestHash, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateSubscriptionId :: Text -> Text -> Uuid5
generateSubscriptionId userId subscriptionType =
  let name = T.concat ["subscription:", userId, ":", subscriptionType]
  in uuid5 latticeNamespace name

generatePaymentId :: Text -> Int -> Uuid5
generatePaymentId subscriptionId paymentIndex =
  let name = T.concat ["payment:", subscriptionId, ":", T.pack (show paymentIndex)]
  in uuid5 latticeNamespace name

generateNotificationId :: Text -> Text -> Int -> Uuid5
generateNotificationId userId notificationType timestamp =
  let name = T.concat ["notification:", userId, ":", notificationType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateCollaborationSessionId :: Text -> Text -> Int -> Uuid5
generateCollaborationSessionId projectId userId timestamp =
  let name = T.concat ["collaboration-session:", projectId, ":", userId, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateCollaborationChangeId :: Text -> Int -> Uuid5
generateCollaborationChangeId sessionId changeIndex =
  let name = T.concat ["collaboration-change:", sessionId, ":", T.pack (show changeIndex)]
  in uuid5 latticeNamespace name

generateCommentId :: Text -> Int -> Text -> Int -> Uuid5
generateCommentId compositionId frame userId commentIndex =
  let name = T.concat ["comment:", compositionId, ":", T.pack (show frame), ":", userId, ":", T.pack (show commentIndex)]
  in uuid5 latticeNamespace name

generateReviewId :: Text -> Text -> Int -> Uuid5
generateReviewId projectId reviewerId timestamp =
  let name = T.concat ["review:", projectId, ":", reviewerId, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateReviewCommentId :: Text -> Int -> Uuid5
generateReviewCommentId reviewId commentIndex =
  let name = T.concat ["review-comment:", reviewId, ":", T.pack (show commentIndex)]
  in uuid5 latticeNamespace name

generateTagId :: Text -> Text -> Uuid5
generateTagId projectId tagName =
  let name = T.concat ["tag:", projectId, ":", tagName]
  in uuid5 latticeNamespace name

generateTagAssignmentId :: Text -> Text -> Text -> Uuid5
generateTagAssignmentId tagId entityId entityType =
  let name = T.concat ["tag-assignment:", tagId, ":", entityType, ":", entityId]
  in uuid5 latticeNamespace name

generateCollectionId :: Text -> Text -> Uuid5
generateCollectionId projectId collectionName =
  let name = T.concat ["collection:", projectId, ":", collectionName]
  in uuid5 latticeNamespace name

generateCollectionItemId :: Text -> Int -> Uuid5
generateCollectionItemId collectionId itemIndex =
  let name = T.concat ["collection-item:", collectionId, ":", T.pack (show itemIndex)]
  in uuid5 latticeNamespace name

generateSearchQueryId :: Text -> Text -> Int -> Uuid5
generateSearchQueryId userId queryHash timestamp =
  let name = T.concat ["search-query:", userId, ":", queryHash, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateSearchResultId :: Text -> Int -> Uuid5
generateSearchResultId queryId resultIndex =
  let name = T.concat ["search-result:", queryId, ":", T.pack (show resultIndex)]
  in uuid5 latticeNamespace name

generateBookmarkId :: Text -> Text -> Text -> Uuid5
generateBookmarkId userId entityId entityType =
  let name = T.concat ["bookmark:", userId, ":", entityType, ":", entityId]
  in uuid5 latticeNamespace name

generateFavoriteId :: Text -> Text -> Text -> Uuid5
generateFavoriteId userId entityId entityType =
  let name = T.concat ["favorite:", userId, ":", entityType, ":", entityId]
  in uuid5 latticeNamespace name

generateShareLinkId :: Text -> Text -> Int -> Uuid5
generateShareLinkId projectId shareType timestamp =
  let name = T.concat ["share-link:", projectId, ":", shareType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateDownloadId :: Text -> Int -> Uuid5
generateDownloadId shareLinkId downloadIndex =
  let name = T.concat ["download:", shareLinkId, ":", T.pack (show downloadIndex)]
  in uuid5 latticeNamespace name

generateImportJobId :: Text -> Text -> Int -> Uuid5
generateImportJobId projectId importType timestamp =
  let name = T.concat ["import-job:", projectId, ":", importType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateImportItemId :: Text -> Int -> Uuid5
generateImportItemId importJobId itemIndex =
  let name = T.concat ["import-item:", importJobId, ":", T.pack (show itemIndex)]
  in uuid5 latticeNamespace name

generateSyncJobId :: Text -> Text -> Int -> Uuid5
generateSyncJobId projectId syncType timestamp =
  let name = T.concat ["sync-job:", projectId, ":", syncType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateBackupId :: Text -> Text -> Int -> Uuid5
generateBackupId projectId backupType timestamp =
  let name = T.concat ["backup:", projectId, ":", backupType, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateRestorePointId :: Text -> Int -> Uuid5
generateRestorePointId projectId timestamp =
  let name = T.concat ["restore-point:", projectId, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateVersionId :: Text -> Text -> Uuid5
generateVersionId projectId versionNumber =
  let name = T.concat ["version:", projectId, ":", versionNumber]
  in uuid5 latticeNamespace name

generateBranchId :: Text -> Text -> Uuid5
generateBranchId projectId branchName =
  let name = T.concat ["branch:", projectId, ":", branchName]
  in uuid5 latticeNamespace name

generateCommitId :: Text -> Text -> Uuid5
generateCommitId branchId commitHash =
  let name = T.concat ["commit:", branchId, ":", commitHash]
  in uuid5 latticeNamespace name

generateDiffId :: Text -> Text -> Uuid5
generateDiffId commitId filePath =
  let name = T.concat ["diff:", commitId, ":", filePath]
  in uuid5 latticeNamespace name

generateMergeId :: Text -> Text -> Int -> Uuid5
generateMergeId sourceBranchId targetBranchId timestamp =
  let name = T.concat ["merge:", sourceBranchId, ":", targetBranchId, ":", T.pack (show timestamp)]
  in uuid5 latticeNamespace name

generateConflictId :: Text -> Int -> Uuid5
generateConflictId mergeId conflictIndex =
  let name = T.concat ["conflict:", mergeId, ":", T.pack (show conflictIndex)]
  in uuid5 latticeNamespace name

generateResolutionId :: Text -> Uuid5
generateResolutionId conflictId =
  let name = T.concat ["resolution:", conflictId]
  in uuid5 latticeNamespace name
