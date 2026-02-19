{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module      : Lattice.Utils.Uuid5
Description : UUID5 (Deterministic Name-Based UUID) Implementation
Copyright   : (c) Lattice, 2026
License     : MIT

Generates deterministic UUIDs based on namespace and name using SHA-1 hashing.
This ensures the same input always produces the same UUID, enabling deterministic
ID generation for layers, keyframes, and other entities.

RFC 4122 compliant UUID5 implementation.

Source: lattice-core/lean/Lattice/Utils/Uuid5.lean
-}

module Lattice.Utils.Uuid5
  ( -- * Namespaces
    pattern UUID5_NAMESPACE_DNS
  , pattern UUID5_NAMESPACE_URL
  , pattern UUID5_NAMESPACE_OID
  , pattern UUID5_NAMESPACE_X500
  , pattern LATTICE_NAMESPACE
    -- * Core UUID5 Function
  , uuid5
    -- * SHA-1
  , sha1
    -- * UUID Parsing
  , uuidToBytes
  , bytesToUuid
    -- * Entity Types
  , EntityType(..)
  , generateId
  ) where

import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR, complement, rotateL)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word8, Word32)
import GHC.Generics (Generic)
import Numeric (showHex)
import Data.Char (digitToInt, isHexDigit)
import Data.List (intercalate)

--------------------------------------------------------------------------------
-- Namespaces
--------------------------------------------------------------------------------

-- | Standard UUID5 namespaces (RFC 4122)
pattern UUID5_NAMESPACE_DNS :: Text
pattern UUID5_NAMESPACE_DNS = "6ba7b810-9dad-11d1-80b4-00c04fd430c8"

pattern UUID5_NAMESPACE_URL :: Text
pattern UUID5_NAMESPACE_URL = "6ba7b811-9dad-11d1-80b4-00c04fd430c8"

pattern UUID5_NAMESPACE_OID :: Text
pattern UUID5_NAMESPACE_OID = "6ba7b812-9dad-11d1-80b4-00c04fd430c8"

pattern UUID5_NAMESPACE_X500 :: Text
pattern UUID5_NAMESPACE_X500 = "6ba7b814-9dad-11d1-80b4-00c04fd430c8"

-- | Lattice-specific namespace for layer/keyframe IDs
pattern LATTICE_NAMESPACE :: Text
pattern LATTICE_NAMESPACE = "a1b2c3d4-e5f6-4789-a012-3456789abcde"

--------------------------------------------------------------------------------
-- SHA-1 Implementation
--------------------------------------------------------------------------------

-- | SHA-1 initial hash values
sha1H0, sha1H1, sha1H2, sha1H3, sha1H4 :: Word32
sha1H0 = 0x67452301
sha1H1 = 0xEFCDAB89
sha1H2 = 0x98BADCFE
sha1H3 = 0x10325476
sha1H4 = 0xC3D2E1F0

-- | SHA-1 round constants
sha1K :: Int -> Word32
sha1K i
  | i < 20 = 0x5A827999
  | i < 40 = 0x6ED9EBA1
  | i < 60 = 0x8F1BBCDC
  | otherwise = 0xCA62C1D6

-- | SHA-1 f function
sha1F :: Int -> Word32 -> Word32 -> Word32 -> Word32
sha1F i b c d
  | i < 20 = (b .&. c) .|. (complement b .&. d)
  | i < 40 = b `xor` c `xor` d
  | i < 60 = (b .&. c) .|. (b .&. d) .|. (c .&. d)
  | otherwise = b `xor` c `xor` d

-- | Convert 4 bytes to Word32 (big-endian)
bytesToWord32BE :: Word8 -> Word8 -> Word8 -> Word8 -> Word32
bytesToWord32BE b0 b1 b2 b3 =
  (fromIntegral b0 `shiftL` 24) .|.
  (fromIntegral b1 `shiftL` 16) .|.
  (fromIntegral b2 `shiftL` 8) .|.
  fromIntegral b3

-- | Convert Word32 to 4 bytes (big-endian)
word32ToBytessBE :: Word32 -> [Word8]
word32ToBytessBE x =
  [ fromIntegral (x `shiftR` 24)
  , fromIntegral (x `shiftR` 16)
  , fromIntegral (x `shiftR` 8)
  , fromIntegral x
  ]

-- | Pad message for SHA-1
sha1Pad :: ByteString -> ByteString
sha1Pad msg =
  let msgLen = BS.length msg
      bitLen = fromIntegral msgLen * 8 :: Word64
      -- Calculate padding: need (msgLen + 1 + padLen + 8) % 64 == 0
      padLen = (55 - msgLen `mod` 64 + 64) `mod` 64 + 1
      padding = BS.cons 0x80 (BS.replicate (padLen - 1) 0)
      -- 64-bit big-endian length
      lenBytes = BS.pack
        [ fromIntegral (bitLen `shiftR` 56)
        , fromIntegral (bitLen `shiftR` 48)
        , fromIntegral (bitLen `shiftR` 40)
        , fromIntegral (bitLen `shiftR` 32)
        , fromIntegral (bitLen `shiftR` 24)
        , fromIntegral (bitLen `shiftR` 16)
        , fromIntegral (bitLen `shiftR` 8)
        , fromIntegral bitLen
        ]
  in msg <> padding <> lenBytes

type Word64 = Word

-- | Process a single 512-bit chunk
sha1ProcessChunk :: ByteString -> Int -> (Word32, Word32, Word32, Word32, Word32)
                 -> (Word32, Word32, Word32, Word32, Word32)
sha1ProcessChunk chunk offset (h0, h1, h2, h3, h4) =
  let -- Build message schedule (80 words)
      getWord32 i =
        let idx = offset + i * 4
        in bytesToWord32BE
             (BS.index chunk idx)
             (BS.index chunk (idx + 1))
             (BS.index chunk (idx + 2))
             (BS.index chunk (idx + 3))

      -- First 16 words from chunk
      w0_15 = map getWord32 [0..15]

      -- Extend to 80 words
      extend ws i =
        let val = (ws !! (i - 3)) `xor` (ws !! (i - 8)) `xor`
                  (ws !! (i - 14)) `xor` (ws !! (i - 16))
        in ws ++ [rotateL val 1]

      w = foldl extend w0_15 [16..79]

      -- Main loop
      step (a, b, c, d, e) i =
        let f = sha1F i b c d
            k = sha1K i
            temp = rotateL a 5 + f + e + k + (w !! i)
        in (temp, a, rotateL b 30, c, d)

      (a', b', c', d', e') = foldl step (h0, h1, h2, h3, h4) [0..79]

  in (h0 + a', h1 + b', h2 + c', h3 + d', h4 + e')

-- | Compute SHA-1 hash
sha1 :: ByteString -> ByteString
sha1 input =
  let padded = sha1Pad input
      numChunks = BS.length padded `div` 64

      processChunks (h0, h1, h2, h3, h4) chunkIdx =
        sha1ProcessChunk padded (chunkIdx * 64) (h0, h1, h2, h3, h4)

      (h0, h1, h2, h3, h4) = foldl processChunks
        (sha1H0, sha1H1, sha1H2, sha1H3, sha1H4)
        [0 .. numChunks - 1]

  in BS.pack $ concatMap word32ToBytessBE [h0, h1, h2, h3, h4]

--------------------------------------------------------------------------------
-- UUID Parsing and Formatting
--------------------------------------------------------------------------------

-- | Parse a hex character
hexCharToInt :: Char -> Int
hexCharToInt c
  | isHexDigit c = digitToInt c
  | otherwise = 0

-- | Parse UUID string to bytes
uuidToBytes :: Text -> ByteString
uuidToBytes uuid =
  let hex = T.filter (/= '-') uuid
      pairs = T.chunksOf 2 hex
      toByte t = fromIntegral $
        hexCharToInt (T.index t 0) * 16 + hexCharToInt (T.index t 1)
  in BS.pack $ map toByte pairs

-- | Convert bytes to UUID string
bytesToUuid :: ByteString -> Text
bytesToUuid bytes =
  let hex = concatMap (\b -> let h = showHex b "" in if length h == 1 then "0" ++ h else h) (BS.unpack bytes)
      parts = [ take 8 hex
              , take 4 (drop 8 hex)
              , take 4 (drop 12 hex)
              , take 4 (drop 16 hex)
              , drop 20 hex
              ]
  in T.pack $ intercalate "-" parts

--------------------------------------------------------------------------------
-- UUID5 Generation
--------------------------------------------------------------------------------

-- | Generate UUID5 (deterministic name-based UUID)
uuid5 :: Text -> Text -> Text
uuid5 name namespace =
  let namespaceBytes = uuidToBytes namespace
      nameBytes = TE.encodeUtf8 name
      combined = namespaceBytes <> nameBytes
      hash = sha1 combined
      -- Take first 16 bytes
      uuidBytes = BS.take 16 hash
      -- Set version (5) and variant bits
      byte6 = (BS.index uuidBytes 6 .&. 0x0F) .|. 0x50
      byte8 = (BS.index uuidBytes 8 .&. 0x3F) .|. 0x80
      uuidBytes' = BS.take 6 uuidBytes <>
                   BS.singleton byte6 <>
                   BS.singleton (BS.index uuidBytes 7) <>
                   BS.singleton byte8 <>
                   BS.drop 9 uuidBytes
  in bytesToUuid uuidBytes'

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
  deriving stock (Eq, Show, Generic)

-- | Convert entity type to prefix string
entityTypeToPrefix :: EntityType -> Text
entityTypeToPrefix = \case
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

-- | Generate a typed ID for an entity
generateId :: EntityType -> [Text] -> Text
generateId entityType parts =
  let name = T.intercalate ":" (entityTypeToPrefix entityType : parts)
  in uuid5 name LATTICE_NAMESPACE
