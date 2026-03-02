-- | Lattice.Utils.Uuid5.EntityType - Entity type definitions
-- |
-- | @module Lattice.Utils.Uuid5.EntityType
-- | @description Entity types for typed ID generation.
-- |
-- | Source: leancomfy/lean/Lattice/Utils/Uuid5.lean

module Lattice.Utils.Uuid5.EntityType
  ( EntityType(..)
  , entityTypeToPrefix
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Entity Types
--------------------------------------------------------------------------------

-- | Entity types for typed ID generation
data EntityType
  = EntityLayer
  | EntityKeyframe
  | EntityComposition
  | EntityEffect
  | EntityTextAnimator
  | EntityPropertyDriver
  | EntityCamera
  | EntityCameraKeyframe
  | EntityParticleSystem
  | EntityParticleEmitter
  | EntityParticleForce
  | EntityParticle
  | EntityParticleGroup
  | EntityParticleConnection
  | EntityParticleTrail
  | EntityParticleSubEmitter
  | EntityPhysicsBody
  | EntityPhysicsJoint
  | EntityPhysicsSpace
  | EntityPhysicsCloth
  | EntityPhysicsRagdoll
  | EntityPhysicsRigidBody
  | EntityExportJob
  | EntityPreset
  | EntityTemplate
  | EntityAsset
  | EntityChatMessage
  | EntityMarker
  | EntityMeshWarpPin
  | EntityMeshWarpMesh
  | EntityAudioAnalysis
  | EntityAudioTrack
  | EntityAudioReactivity
  | EntityAudioBeat
  | EntityAudioPeak
  | EntityAIModel
  | EntitySegmentation
  | EntityVectorization
  | EntityTemplateProperty
  | EntityEvent
  | EntityMetric
  | EntityProject
  | EntityFeatureFlag
  | EntityLayerMask
  | EntityLayerStyles
  | EntityExpression
  | EntityRenderSettings
  | EntityExportTemplate
  | EntityPreprocessor
  | EntityCameraPath
  | EntityMidiNote
  | EntityMidiCC
  | EntityNestedComp
  | EntityCompInstance
  | EntityTextLayer
  | EntitySplineControlPoint
  | EntitySplineAnchorPoint
  | EntityShapePath
  | EntityShapePathCommand
  | EntityGuide
  | EntitySpriteSheet
  | EntitySpriteFrame
  | EntitySvgDocument
  | EntitySvgPath
  | EntityMaterial
  | EntityTexture
  | EntityMesh
  | EntityMeshVertex
  | EntityMeshFace
  | EntityRenderFrame
  | EntityRenderTile
  | EntityWorkflowNode
  | EntityWorkflowConnection
  | EntityToolCall
  | EntityUserAction
  | EntitySession
  | EntityCacheEntry
  | EntityFrameCacheEntry
  | EntityTimelineTrack
  | EntityTimelineClip
  | EntityColorStop
  | EntityGradient
  | EntityFilter
  | EntityBlendModeOverride
  | EntityTransformConstraint
  | EntityParentConstraint
  | EntityLookAtConstraint
  | EntityPathConstraint
  | EntityPoseBone
  | EntityPoseKeyframe
  | EntityControlPoint
  | EntityDeformationHandle
  | EntityLight
  | EntityEnvironmentMap
  | EntityShader
  | EntityShaderUniform
  | EntityComputeShader
  | EntityRenderPass
  | EntityRenderTarget
  | EntityPostProcessingEffect
  | EntityViewport
  | EntitySelection
  | EntityClipboardEntry
  | EntityUndoRedoState
  | EntityHistoryEntry
  | EntityWorkspaceLayout
  | EntityWorkspacePanel
  | EntityKeyboardShortcut
  | EntityPlugin
  | EntityPluginInstance
  | EntityPluginHook
  | EntityWebhook
  | EntityWebhookEvent
  | EntityApiKey
  | EntityApiRequest
  | EntitySubscription
  | EntityPayment
  | EntityNotification
  | EntityCollaborationSession
  | EntityCollaborationChange
  | EntityComment
  | EntityReview
  | EntityReviewComment
  | EntityTag
  | EntityTagAssignment
  | EntityCollection
  | EntityCollectionItem
  | EntitySearchQuery
  | EntitySearchResult
  | EntityBookmark
  | EntityFavorite
  | EntityShareLink
  | EntityDownload
  | EntityImportJob
  | EntityImportItem
  | EntitySyncJob
  | EntityBackup
  | EntityRestorePoint
  | EntityVersion
  | EntityBranch
  | EntityCommit
  | EntityDiff
  | EntityMerge
  | EntityConflict
  | EntityResolution

derive instance Generic EntityType _
derive instance Eq EntityType

instance Show EntityType where
  show = genericShow

--------------------------------------------------------------------------------
-- Prefix Mapping
--------------------------------------------------------------------------------

-- | Convert entity type to prefix string
entityTypeToPrefix :: EntityType -> String
entityTypeToPrefix = case _ of
  EntityLayer -> "layer"
  EntityKeyframe -> "keyframe"
  EntityComposition -> "composition"
  EntityEffect -> "effect"
  EntityTextAnimator -> "text-animator"
  EntityPropertyDriver -> "property-driver"
  EntityCamera -> "camera"
  EntityCameraKeyframe -> "camera-keyframe"
  EntityParticleSystem -> "particle-system"
  EntityParticleEmitter -> "particle-emitter"
  EntityParticleForce -> "particle-force"
  EntityParticle -> "particle"
  EntityParticleGroup -> "particle-group"
  EntityParticleConnection -> "particle-connection"
  EntityParticleTrail -> "particle-trail"
  EntityParticleSubEmitter -> "particle-sub-emitter"
  EntityPhysicsBody -> "physics-body"
  EntityPhysicsJoint -> "physics-joint"
  EntityPhysicsSpace -> "physics-space"
  EntityPhysicsCloth -> "physics-cloth"
  EntityPhysicsRagdoll -> "physics-ragdoll"
  EntityPhysicsRigidBody -> "physics-rigid-body"
  EntityExportJob -> "export-job"
  EntityPreset -> "preset"
  EntityTemplate -> "template"
  EntityAsset -> "asset"
  EntityChatMessage -> "chat-message"
  EntityMarker -> "marker"
  EntityMeshWarpPin -> "mesh-warp-pin"
  EntityMeshWarpMesh -> "mesh-warp-mesh"
  EntityAudioAnalysis -> "audio-analysis"
  EntityAudioTrack -> "audio-track"
  EntityAudioReactivity -> "audio-reactivity"
  EntityAudioBeat -> "audio-beat"
  EntityAudioPeak -> "audio-peak"
  EntityAIModel -> "ai-model"
  EntitySegmentation -> "segmentation"
  EntityVectorization -> "vectorization"
  EntityTemplateProperty -> "template-property"
  EntityEvent -> "event"
  EntityMetric -> "metric"
  EntityProject -> "project"
  EntityFeatureFlag -> "feature-flag"
  EntityLayerMask -> "layer-mask"
  EntityLayerStyles -> "layer-styles"
  EntityExpression -> "expression"
  EntityRenderSettings -> "render-settings"
  EntityExportTemplate -> "export-template"
  EntityPreprocessor -> "preprocessor"
  EntityCameraPath -> "camera-path"
  EntityMidiNote -> "midi-note"
  EntityMidiCC -> "midi-cc"
  EntityNestedComp -> "nested-comp"
  EntityCompInstance -> "comp-instance"
  EntityTextLayer -> "text-layer"
  EntitySplineControlPoint -> "spline-control-point"
  EntitySplineAnchorPoint -> "spline-anchor-point"
  EntityShapePath -> "shape-path"
  EntityShapePathCommand -> "shape-path-command"
  EntityGuide -> "guide"
  EntitySpriteSheet -> "sprite-sheet"
  EntitySpriteFrame -> "sprite-frame"
  EntitySvgDocument -> "svg-document"
  EntitySvgPath -> "svg-path"
  EntityMaterial -> "material"
  EntityTexture -> "texture"
  EntityMesh -> "mesh"
  EntityMeshVertex -> "mesh-vertex"
  EntityMeshFace -> "mesh-face"
  EntityRenderFrame -> "render-frame"
  EntityRenderTile -> "render-tile"
  EntityWorkflowNode -> "workflow-node"
  EntityWorkflowConnection -> "workflow-connection"
  EntityToolCall -> "tool-call"
  EntityUserAction -> "user-action"
  EntitySession -> "session"
  EntityCacheEntry -> "cache-entry"
  EntityFrameCacheEntry -> "frame-cache-entry"
  EntityTimelineTrack -> "timeline-track"
  EntityTimelineClip -> "timeline-clip"
  EntityColorStop -> "color-stop"
  EntityGradient -> "gradient"
  EntityFilter -> "filter"
  EntityBlendModeOverride -> "blend-mode-override"
  EntityTransformConstraint -> "transform-constraint"
  EntityParentConstraint -> "parent-constraint"
  EntityLookAtConstraint -> "look-at-constraint"
  EntityPathConstraint -> "path-constraint"
  EntityPoseBone -> "pose-bone"
  EntityPoseKeyframe -> "pose-keyframe"
  EntityControlPoint -> "control-point"
  EntityDeformationHandle -> "deformation-handle"
  EntityLight -> "light"
  EntityEnvironmentMap -> "environment-map"
  EntityShader -> "shader"
  EntityShaderUniform -> "shader-uniform"
  EntityComputeShader -> "compute-shader"
  EntityRenderPass -> "render-pass"
  EntityRenderTarget -> "render-target"
  EntityPostProcessingEffect -> "post-processing-effect"
  EntityViewport -> "viewport"
  EntitySelection -> "selection"
  EntityClipboardEntry -> "clipboard-entry"
  EntityUndoRedoState -> "undo-redo-state"
  EntityHistoryEntry -> "history-entry"
  EntityWorkspaceLayout -> "workspace-layout"
  EntityWorkspacePanel -> "workspace-panel"
  EntityKeyboardShortcut -> "keyboard-shortcut"
  EntityPlugin -> "plugin"
  EntityPluginInstance -> "plugin-instance"
  EntityPluginHook -> "plugin-hook"
  EntityWebhook -> "webhook"
  EntityWebhookEvent -> "webhook-event"
  EntityApiKey -> "api-key"
  EntityApiRequest -> "api-request"
  EntitySubscription -> "subscription"
  EntityPayment -> "payment"
  EntityNotification -> "notification"
  EntityCollaborationSession -> "collaboration-session"
  EntityCollaborationChange -> "collaboration-change"
  EntityComment -> "comment"
  EntityReview -> "review"
  EntityReviewComment -> "review-comment"
  EntityTag -> "tag"
  EntityTagAssignment -> "tag-assignment"
  EntityCollection -> "collection"
  EntityCollectionItem -> "collection-item"
  EntitySearchQuery -> "search-query"
  EntitySearchResult -> "search-result"
  EntityBookmark -> "bookmark"
  EntityFavorite -> "favorite"
  EntityShareLink -> "share-link"
  EntityDownload -> "download"
  EntityImportJob -> "import-job"
  EntityImportItem -> "import-item"
  EntitySyncJob -> "sync-job"
  EntityBackup -> "backup"
  EntityRestorePoint -> "restore-point"
  EntityVersion -> "version"
  EntityBranch -> "branch"
  EntityCommit -> "commit"
  EntityDiff -> "diff"
  EntityMerge -> "merge"
  EntityConflict -> "conflict"
  EntityResolution -> "resolution"
