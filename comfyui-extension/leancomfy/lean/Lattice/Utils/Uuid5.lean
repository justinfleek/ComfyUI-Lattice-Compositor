/-
  Lattice.Utils.Uuid5 - UUID5 (Deterministic Name-Based UUID) Implementation

  Generates deterministic UUIDs based on namespace and name using SHA-1 hashing.
  This ensures the same input always produces the same UUID, enabling deterministic
  ID generation for layers, keyframes, and other entities.

  RFC 4122 compliant UUID5 implementation.

  Source: ui/src/utils/uuid5.ts
-/

namespace Lattice.Utils.Uuid5

/-! ## Standard UUID5 Namespaces (RFC 4122) -/

def UUID5_NAMESPACE_DNS : String := "6ba7b810-9dad-11d1-80b4-00c04fd430c8"
def UUID5_NAMESPACE_URL : String := "6ba7b811-9dad-11d1-80b4-00c04fd430c8"
def UUID5_NAMESPACE_OID : String := "6ba7b812-9dad-11d1-80b4-00c04fd430c8"
def UUID5_NAMESPACE_X500 : String := "6ba7b814-9dad-11d1-80b4-00c04fd430c8"

/-- Lattice-specific namespace for layer/keyframe IDs -/
def LATTICE_NAMESPACE : String := "a1b2c3d4-e5f6-4789-a012-3456789abcde"

/-! ## Helper Functions -/

/-- Parse a hex character to its numeric value -/
def hexCharToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Convert a Nat to a hex string with padding -/
def natToHex (n : Nat) (width : Nat) : String :=
  let hexChars := "0123456789abcdef"
  let rec go (val : Nat) (acc : String) (remaining : Nat) : String :=
    if remaining == 0 then acc
    else go (val / 16) (hexChars.get! (val % 16) :: acc.data).asString (remaining - 1)
  go n "" width

/-- Convert a byte to 2-char hex string -/
def byteToHex (b : UInt8) : String :=
  natToHex b.toNat 2

/-! ## SHA-1 Implementation -/

/-- SHA-1 constants -/
private def sha1_h0 : UInt32 := 0x67452301
private def sha1_h1 : UInt32 := 0xEFCDAB89
private def sha1_h2 : UInt32 := 0x98BADCFE
private def sha1_h3 : UInt32 := 0x10325476
private def sha1_h4 : UInt32 := 0xC3D2E1F0

/-- SHA-1 round constants -/
private def sha1_k (i : Nat) : UInt32 :=
  if i < 20 then 0x5A827999
  else if i < 40 then 0x6ED9EBA1
  else if i < 60 then 0x8F1BBCDC
  else 0xCA62C1D6

/-- Rotate left for UInt32 -/
private def rotl32 (x : UInt32) (n : Nat) : UInt32 :=
  (x <<< n.toUInt32) ||| (x >>> (32 - n).toUInt32)

/-- SHA-1 f function -/
private def sha1_f (i : Nat) (b c d : UInt32) : UInt32 :=
  if i < 20 then (b &&& c) ||| ((~~~b) &&& d)
  else if i < 40 then b ^^^ c ^^^ d
  else if i < 60 then (b &&& c) ||| (b &&& d) ||| (c &&& d)
  else b ^^^ c ^^^ d

/-- Convert bytes to UInt32 (big-endian) -/
private def bytesToUInt32BE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) |||
  (b2.toUInt32 <<< 8) ||| b3.toUInt32

/-- Convert UInt32 to bytes (big-endian) -/
private def uint32ToBytessBE (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- Pad message for SHA-1 -/
private def sha1Pad (msg : ByteArray) : ByteArray :=
  let msgLen := msg.size
  let bitLen := msgLen * 8
  -- Calculate padding length: need (msgLen + 1 + padLen + 8) % 64 == 0
  let padLen := (55 - msgLen % 64 + 64) % 64 + 1
  let padded := msg.push 0x80
  let padded := (List.replicate (padLen - 1) 0).foldl ByteArray.push padded
  -- Append length as 64-bit big-endian
  let padded := padded.push ((bitLen >>> 56).toUInt8)
  let padded := padded.push ((bitLen >>> 48).toUInt8)
  let padded := padded.push ((bitLen >>> 40).toUInt8)
  let padded := padded.push ((bitLen >>> 32).toUInt8)
  let padded := padded.push ((bitLen >>> 24).toUInt8)
  let padded := padded.push ((bitLen >>> 16).toUInt8)
  let padded := padded.push ((bitLen >>> 8).toUInt8)
  let padded := padded.push (bitLen.toUInt8)
  padded

/-- Process a 512-bit chunk -/
private def sha1ProcessChunk (chunk : ByteArray) (offset : Nat) (h : UInt32 × UInt32 × UInt32 × UInt32 × UInt32)
    : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 :=
  let (h0, h1, h2, h3, h4) := h
  -- Initialize message schedule
  let w := Array.mkArray 80 (0 : UInt32)
  -- Copy chunk into first 16 words
  let w := (List.range 16).foldl (fun w i =>
    let idx := offset + i * 4
    let val := bytesToUInt32BE
      (chunk.get! idx) (chunk.get! (idx + 1))
      (chunk.get! (idx + 2)) (chunk.get! (idx + 3))
    w.set! i val) w
  -- Extend to 80 words
  let w := (List.range' 16 64).foldl (fun w i =>
    let val := w[i - 3]! ^^^ w[i - 8]! ^^^ w[i - 14]! ^^^ w[i - 16]!
    w.set! i (rotl32 val 1)) w
  -- Initialize working variables
  let (a, b, c, d, e) := (h0, h1, h2, h3, h4)
  -- Main loop
  let (a, b, c, d, e) := (List.range 80).foldl (fun (a, b, c, d, e) i =>
    let f := sha1_f i b c d
    let k := sha1_k i
    let temp := rotl32 a 5 + f + e + k + w[i]!
    (temp, a, rotl32 b 30, c, d)) (a, b, c, d, e)
  (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e)

/-- Compute SHA-1 hash of a byte array -/
def sha1 (data : ByteArray) : ByteArray :=
  let padded := sha1Pad data
  let numChunks := padded.size / 64
  let init := (sha1_h0, sha1_h1, sha1_h2, sha1_h3, sha1_h4)
  let (h0, h1, h2, h3, h4) := (List.range numChunks).foldl
    (fun h i => sha1ProcessChunk padded (i * 64) h) init
  -- Convert to bytes
  let result := ByteArray.empty
  let result := (uint32ToBytessBE h0).foldl ByteArray.push result
  let result := (uint32ToBytessBE h1).foldl ByteArray.push result
  let result := (uint32ToBytessBE h2).foldl ByteArray.push result
  let result := (uint32ToBytessBE h3).foldl ByteArray.push result
  let result := (uint32ToBytessBE h4).foldl ByteArray.push result
  result

/-! ## UUID Parsing and Formatting -/

/-- Parse UUID string to bytes -/
def uuidToBytes (uuid : String) : ByteArray :=
  let hex := uuid.replace "-" ""
  let chars := hex.data
  let rec go (cs : List Char) (acc : ByteArray) : ByteArray :=
    match cs with
    | c1 :: c2 :: rest =>
      let byte := (hexCharToNat c1 * 16 + hexCharToNat c2).toUInt8
      go rest (acc.push byte)
    | _ => acc
  go chars ByteArray.empty

/-- Convert bytes to UUID string -/
def bytesToUuid (bytes : ByteArray) : String :=
  let hex := bytes.data.map byteToHex |>.foldl (· ++ ·) ""
  s!"{hex.take 8}-{hex.drop 8 |>.take 4}-{hex.drop 12 |>.take 4}-{hex.drop 16 |>.take 4}-{hex.drop 20}"

/-! ## UUID5 Generation -/

/-- Generate UUID5 (deterministic name-based UUID) -/
def uuid5 (name : String) (namespace : String := LATTICE_NAMESPACE) : String :=
  -- Convert namespace UUID to bytes
  let namespaceBytes := uuidToBytes namespace
  -- Convert name to UTF-8 bytes
  let nameBytes := name.toUTF8
  -- Concatenate namespace + name
  let combined := namespaceBytes ++ nameBytes
  -- Compute SHA-1 hash
  let hash := sha1 combined
  -- Take first 16 bytes
  let uuidBytes := ByteArray.mk (hash.data.take 16).toArray
  -- Set version (5) and variant bits
  let byte6 := (uuidBytes.get! 6 &&& 0x0F) ||| 0x50  -- Version 5
  let byte8 := (uuidBytes.get! 8 &&& 0x3F) ||| 0x80  -- Variant RFC 4122
  let uuidBytes := uuidBytes.set! 6 byte6
  let uuidBytes := uuidBytes.set! 8 byte8
  bytesToUuid uuidBytes

/-! ## Entity Type for Typed ID Generation -/

/-- Entity types for ID generation -/
inductive EntityType where
  | layer
  | keyframe
  | composition
  | effect
  | textAnimator
  | propertyDriver
  | camera
  | cameraKeyframe
  | particleSystem
  | particleEmitter
  | particleForce
  | particle
  | particleGroup
  | particleConnection
  | particleTrail
  | particleSubEmitter
  | physicsBody
  | physicsJoint
  | physicsSpace
  | physicsCloth
  | physicsRagdoll
  | physicsRigidBody
  | exportJob
  | preset
  | template
  | asset
  | chatMessage
  | marker
  | meshWarpPin
  | meshWarpMesh
  | audioAnalysis
  | audioTrack
  | audioReactivity
  | audioBeat
  | audioPeak
  | aiModel
  | segmentation
  | vectorization
  | templateProperty
  | event
  | metric
  | project
  | featureFlag
  | layerMask
  | layerStyles
  | expression
  | renderSettings
  | exportTemplate
  | preprocessor
  | cameraPath
  | midiNote
  | midiCC
  | nestedComp
  | compInstance
  | textLayer
  | splineControlPoint
  | splineAnchorPoint
  | shapePath
  | shapePathCommand
  | guide
  | spriteSheet
  | spriteFrame
  | svgDocument
  | svgPath
  | material
  | texture
  | mesh
  | meshVertex
  | meshFace
  | renderFrame
  | renderTile
  | workflowNode
  | workflowConnection
  | toolCall
  | userAction
  | session
  | cacheEntry
  | frameCacheEntry
  | timelineTrack
  | timelineClip
  | colorStop
  | gradient
  | filter
  | blendModeOverride
  | transformConstraint
  | parentConstraint
  | lookAtConstraint
  | pathConstraint
  | poseBone
  | poseKeyframe
  | controlPoint
  | deformationHandle
  | light
  | environmentMap
  | shader
  | shaderUniform
  | computeShader
  | renderPass
  | renderTarget
  | postProcessingEffect
  | viewport
  | selection
  | clipboardEntry
  | undoRedoState
  | historyEntry
  | workspaceLayout
  | workspacePanel
  | keyboardShortcut
  | plugin
  | pluginInstance
  | pluginHook
  | webhook
  | webhookEvent
  | apiKey
  | apiRequest
  | subscription
  | payment
  | notification
  | collaborationSession
  | collaborationChange
  | comment
  | review
  | reviewComment
  | tag
  | tagAssignment
  | collection
  | collectionItem
  | searchQuery
  | searchResult
  | bookmark
  | favorite
  | shareLink
  | download
  | importJob
  | importItem
  | syncJob
  | backup
  | restorePoint
  | version
  | branch
  | commit
  | diff
  | merge
  | conflict
  | resolution
  deriving Repr, BEq

/-- Convert entity type to prefix string -/
def EntityType.toPrefix : EntityType → String
  | layer => "layer"
  | keyframe => "keyframe"
  | composition => "composition"
  | effect => "effect"
  | textAnimator => "text-animator"
  | propertyDriver => "property-driver"
  | camera => "camera"
  | cameraKeyframe => "camera-keyframe"
  | particleSystem => "particle-system"
  | particleEmitter => "particle-emitter"
  | particleForce => "particle-force"
  | particle => "particle"
  | particleGroup => "particle-group"
  | particleConnection => "particle-connection"
  | particleTrail => "particle-trail"
  | particleSubEmitter => "particle-sub-emitter"
  | physicsBody => "physics-body"
  | physicsJoint => "physics-joint"
  | physicsSpace => "physics-space"
  | physicsCloth => "physics-cloth"
  | physicsRagdoll => "physics-ragdoll"
  | physicsRigidBody => "physics-rigid-body"
  | exportJob => "export-job"
  | preset => "preset"
  | template => "template"
  | asset => "asset"
  | chatMessage => "chat-message"
  | marker => "marker"
  | meshWarpPin => "mesh-warp-pin"
  | meshWarpMesh => "mesh-warp-mesh"
  | audioAnalysis => "audio-analysis"
  | audioTrack => "audio-track"
  | audioReactivity => "audio-reactivity"
  | audioBeat => "audio-beat"
  | audioPeak => "audio-peak"
  | aiModel => "ai-model"
  | segmentation => "segmentation"
  | vectorization => "vectorization"
  | templateProperty => "template-property"
  | event => "event"
  | metric => "metric"
  | project => "project"
  | featureFlag => "feature-flag"
  | layerMask => "layer-mask"
  | layerStyles => "layer-styles"
  | expression => "expression"
  | renderSettings => "render-settings"
  | exportTemplate => "export-template"
  | preprocessor => "preprocessor"
  | cameraPath => "camera-path"
  | midiNote => "midi-note"
  | midiCC => "midi-cc"
  | nestedComp => "nested-comp"
  | compInstance => "comp-instance"
  | textLayer => "text-layer"
  | splineControlPoint => "spline-control-point"
  | splineAnchorPoint => "spline-anchor-point"
  | shapePath => "shape-path"
  | shapePathCommand => "shape-path-command"
  | guide => "guide"
  | spriteSheet => "sprite-sheet"
  | spriteFrame => "sprite-frame"
  | svgDocument => "svg-document"
  | svgPath => "svg-path"
  | material => "material"
  | texture => "texture"
  | mesh => "mesh"
  | meshVertex => "mesh-vertex"
  | meshFace => "mesh-face"
  | renderFrame => "render-frame"
  | renderTile => "render-tile"
  | workflowNode => "workflow-node"
  | workflowConnection => "workflow-connection"
  | toolCall => "tool-call"
  | userAction => "user-action"
  | session => "session"
  | cacheEntry => "cache-entry"
  | frameCacheEntry => "frame-cache-entry"
  | timelineTrack => "timeline-track"
  | timelineClip => "timeline-clip"
  | colorStop => "color-stop"
  | gradient => "gradient"
  | filter => "filter"
  | blendModeOverride => "blend-mode-override"
  | transformConstraint => "transform-constraint"
  | parentConstraint => "parent-constraint"
  | lookAtConstraint => "look-at-constraint"
  | pathConstraint => "path-constraint"
  | poseBone => "pose-bone"
  | poseKeyframe => "pose-keyframe"
  | controlPoint => "control-point"
  | deformationHandle => "deformation-handle"
  | light => "light"
  | environmentMap => "environment-map"
  | shader => "shader"
  | shaderUniform => "shader-uniform"
  | computeShader => "compute-shader"
  | renderPass => "render-pass"
  | renderTarget => "render-target"
  | postProcessingEffect => "post-processing-effect"
  | viewport => "viewport"
  | selection => "selection"
  | clipboardEntry => "clipboard-entry"
  | undoRedoState => "undo-redo-state"
  | historyEntry => "history-entry"
  | workspaceLayout => "workspace-layout"
  | workspacePanel => "workspace-panel"
  | keyboardShortcut => "keyboard-shortcut"
  | plugin => "plugin"
  | pluginInstance => "plugin-instance"
  | pluginHook => "plugin-hook"
  | webhook => "webhook"
  | webhookEvent => "webhook-event"
  | apiKey => "api-key"
  | apiRequest => "api-request"
  | subscription => "subscription"
  | payment => "payment"
  | notification => "notification"
  | collaborationSession => "collaboration-session"
  | collaborationChange => "collaboration-change"
  | comment => "comment"
  | review => "review"
  | reviewComment => "review-comment"
  | tag => "tag"
  | tagAssignment => "tag-assignment"
  | collection => "collection"
  | collectionItem => "collection-item"
  | searchQuery => "search-query"
  | searchResult => "search-result"
  | bookmark => "bookmark"
  | favorite => "favorite"
  | shareLink => "share-link"
  | download => "download"
  | importJob => "import-job"
  | importItem => "import-item"
  | syncJob => "sync-job"
  | backup => "backup"
  | restorePoint => "restore-point"
  | version => "version"
  | branch => "branch"
  | commit => "commit"
  | diff => "diff"
  | merge => "merge"
  | conflict => "conflict"
  | resolution => "resolution"

/-- Generate a typed ID for an entity -/
def generateId (entityType : EntityType) (parts : List String) : String :=
  let name := entityType.toPrefix :: parts |>.intersperse ":" |>.foldl (· ++ ·) ""
  uuid5 name

end Lattice.Utils.Uuid5
