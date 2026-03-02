/**
 * UUID5 (Deterministic Name-Based UUID) Implementation
 *
 * Generates deterministic UUIDs based on namespace and name using SHA-1 hashing.
 * This ensures the same input always produces the same UUID, enabling deterministic
 * ID generation for layers, keyframes, and other entities.
 *
 * RFC 4122 compliant UUID5 implementation.
 */

/**
 * Standard UUID5 namespaces (RFC 4122)
 */
export const UUID5_NAMESPACES = {
  DNS: "6ba7b810-9dad-11d1-80b4-00c04fd430c8",
  URL: "6ba7b811-9dad-11d1-80b4-00c04fd430c8",
  OID: "6ba7b812-9dad-11d1-80b4-00c04fd430c8",
  X500: "6ba7b814-9dad-11d1-80b4-00c04fd430c8",
} as const;

/**
 * Lattice-specific namespace for layer/keyframe IDs
 */
export const LATTICE_NAMESPACE = "a1b2c3d4-e5f6-4789-a012-3456789abcde";

/**
 * Parse UUID string to bytes
 */
function uuidToBytes(uuid: string): Uint8Array {
  // Remove hyphens and convert to bytes
  const hex = uuid.replace(/-/g, "");
  const bytes = new Uint8Array(16);
  for (let i = 0; i < 16; i++) {
    bytes[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  }
  return bytes;
}

/**
 * Convert bytes to UUID string
 */
function bytesToUuid(bytes: Uint8Array): string {
  const hex = Array.from(bytes)
    .map((b) => b.toString(16).padStart(2, "0"))
    .join("");
  return `${hex.slice(0, 8)}-${hex.slice(8, 12)}-${hex.slice(12, 16)}-${hex.slice(16, 20)}-${hex.slice(20)}`;
}

/**
 * Generate UUID5 (deterministic name-based UUID)
 *
 * @param name - The name to generate UUID from
 * @param namespace - UUID namespace (default: LATTICE_NAMESPACE)
 * @returns Deterministic UUID5 string
 */
export function uuid5(
  name: string,
  namespace: string = LATTICE_NAMESPACE,
): string {
  // Convert namespace UUID to bytes
  const namespaceBytes = uuidToBytes(namespace);

  // Convert name to UTF-8 bytes
  const nameBytes = new TextEncoder().encode(name);

  // Concatenate namespace + name
  const combined = new Uint8Array(namespaceBytes.length + nameBytes.length);
  combined.set(namespaceBytes, 0);
  combined.set(nameBytes, namespaceBytes.length);

  // Compute SHA-1 hash
  // Note: Web Crypto API doesn't have sync SHA-1, so we use SubtleCrypto
  // For deterministic behavior, we need to use a synchronous hash
  // Fallback: Use a simple hash function if crypto.subtle is not available
  const hash = sha1Sync(combined);

  // Set version (5) and variant bits
  const uuidBytes = new Uint8Array(16);
  uuidBytes.set(hash.slice(0, 16), 0);
  uuidBytes[6] = (uuidBytes[6] & 0x0f) | 0x50; // Version 5
  uuidBytes[8] = (uuidBytes[8] & 0x3f) | 0x80; // Variant RFC 4122

  return bytesToUuid(uuidBytes);
}

/**
 * Synchronous SHA-1 implementation for deterministic UUID5
 * Uses a simple hash function since Web Crypto API is async
 * This is RFC 4122 compliant for UUID5 generation
 */
function sha1Sync(data: Uint8Array): Uint8Array {
  // Simple SHA-1-like hash for deterministic UUID5
  // For production, consider using a proper SHA-1 library
  // This implementation provides deterministic hashing for UUID5
  let h0 = 0x67452301;
  let h1 = 0xefcdab89;
  let h2 = 0x98badcfe;
  let h3 = 0x10325476;
  let h4 = 0xc3d2e1f0;

  // Pre-processing: pad message
  const msgLength = data.length;
  const bitLength = msgLength * 8;
  const padding = new Uint8Array(((msgLength + 9 + 63) >> 6) * 64);
  padding.set(data, 0);
  padding[msgLength] = 0x80;

  // Append length (big-endian)
  const lengthBytes = new Uint8Array(8);
  const view = new DataView(lengthBytes.buffer);
  view.setUint32(0, Math.floor(bitLength / 0x100000000), false);
  view.setUint32(4, bitLength & 0xffffffff, false);
  padding.set(lengthBytes, padding.length - 8);

  // Process message in 512-bit chunks
  for (let chunkStart = 0; chunkStart < padding.length; chunkStart += 64) {
    const w = new Uint32Array(80);
    const chunk = padding.slice(chunkStart, chunkStart + 64);

    // Copy chunk into first 16 words
    for (let i = 0; i < 16; i++) {
      w[i] =
        (chunk[i * 4] << 24) |
        (chunk[i * 4 + 1] << 16) |
        (chunk[i * 4 + 2] << 8) |
        chunk[i * 4 + 3];
    }

    // Extend to 80 words
    for (let i = 16; i < 80; i++) {
      w[i] =
        ((w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]) << 1) |
        ((w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]) >>> 31);
    }

    // Initialize hash value for this chunk
    let a = h0;
    let b = h1;
    let c = h2;
    let d = h3;
    let e = h4;

    // Main loop
    for (let i = 0; i < 80; i++) {
      let f: number;
      let k: number;

      if (i < 20) {
        f = (b & c) | (~b & d);
        k = 0x5a827999;
      } else if (i < 40) {
        f = b ^ c ^ d;
        k = 0x6ed9eba1;
      } else if (i < 60) {
        f = (b & c) | (b & d) | (c & d);
        k = 0x8f1bbcdc;
      } else {
        f = b ^ c ^ d;
        k = 0xca62c1d6;
      }

      const temp = ((a << 5) | (a >>> 27)) + f + e + k + w[i];
      e = d;
      d = c;
      c = (b << 30) | (b >>> 2);
      b = a;
      a = temp;
    }

    // Add this chunk's hash to result
    h0 = (h0 + a) | 0;
    h1 = (h1 + b) | 0;
    h2 = (h2 + c) | 0;
    h3 = (h3 + d) | 0;
    h4 = (h4 + e) | 0;
  }

  // Produce final hash value
  const hash = new Uint8Array(20);
  const hashView = new DataView(hash.buffer);
  hashView.setUint32(0, h0 >>> 0, false);
  hashView.setUint32(4, h1 >>> 0, false);
  hashView.setUint32(8, h2 >>> 0, false);
  hashView.setUint32(12, h3 >>> 0, false);
  hashView.setUint32(16, h4 >>> 0, false);

  return hash;
}

/**
 * Generate deterministic UUID5 for a layer based on its properties
 */
export function generateLayerId(
  layerName: string,
  parentId: string | null,
  index: number,
): string {
  const name = `${layerName}:${parentId ?? "root"}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a keyframe based on its properties
 * Returns `kf_${frame}_${uuid5Hash}` format for backwards compatibility
 */
export function generateKeyframeId(
  layerId: string,
  propertyPath: string,
  frame: number,
  value: string | number,
): string {
  const name = `${layerId}:${propertyPath}:${frame}:${value}`;
  const uuid = uuid5(name, LATTICE_NAMESPACE);
  // Return kf_ prefixed format with frame for compatibility with existing tests/code
  return `kf_${frame}_${uuid.replace(/-/g, "").slice(0, 16)}`;
}

/**
 * Generate deterministic UUID5 for a composition
 */
export function generateCompositionId(
  projectId: string,
  compositionName: string,
  index: number,
): string {
  const name = `composition:${projectId}:${compositionName}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an effect
 */
export function generateEffectId(
  layerId: string,
  effectType: string,
  orderIndex: number,
): string {
  const name = `effect:${layerId}:${effectType}:${orderIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a text animator
 */
export function generateTextAnimatorId(
  textLayerId: string,
  animatorType: string,
  orderIndex: number,
): string {
  const name = `text-animator:${textLayerId}:${animatorType}:${orderIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a property driver
 */
export function generatePropertyDriverId(
  layerId: string,
  propertyPath: string,
): string {
  const name = `property-driver:${layerId}:${propertyPath}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a camera
 */
export function generateCameraId(
  compositionId: string,
  cameraName: string,
  index: number,
): string {
  const name = `camera:${compositionId}:${cameraName}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a camera keyframe
 */
export function generateCameraKeyframeId(
  cameraId: string,
  frame: number,
): string {
  const name = `camera-keyframe:${cameraId}:${frame}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a particle system
 */
export function generateParticleSystemId(
  layerId: string,
  index: number,
): string {
  const name = `particle-system:${layerId}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a particle emitter
 */
export function generateParticleEmitterId(
  particleSystemId: string,
  index: number,
): string {
  const name = `particle-emitter:${particleSystemId}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a particle force
 */
export function generateParticleForceId(
  particleSystemId: string,
  forceType: string,
  index: number,
): string {
  const name = `particle-force:${particleSystemId}:${forceType}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a physics body
 */
export function generatePhysicsBodyId(
  physicsSpaceId: string,
  layerId: string,
  index: number,
): string {
  const name = `physics-body:${physicsSpaceId}:${layerId}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a physics joint
 */
export function generatePhysicsJointId(
  physicsSpaceId: string,
  bodyAId: string,
  bodyBId: string,
  jointType: string,
): string {
  const name = `physics-joint:${physicsSpaceId}:${bodyAId}:${bodyBId}:${jointType}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an export job
 */
export function generateExportJobId(
  projectId: string,
  compositionId: string | null,
  timestamp: number,
): string {
  const compPart = compositionId ?? "global";
  const name = `export-job:${projectId}:${compPart}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a preset
 */
export function generatePresetId(
  presetName: string,
  presetType: string,
  projectId: string | null,
): string {
  const projPart = projectId ?? "global";
  const name = `preset:${presetType}:${presetName}:${projPart}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a template
 */
export function generateTemplateId(
  templateName: string,
  projectId: string | null,
  version: string,
): string {
  const projPart = projectId ?? "global";
  const name = `template:${templateName}:${projPart}:${version}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an asset
 */
export function generateAssetId(
  projectId: string,
  assetName: string,
  assetType: string,
): string {
  const name = `asset:${projectId}:${assetType}:${assetName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a chat message
 */
export function generateChatMessageId(
  projectId: string | null,
  role: string,
  timestamp: number,
  contentHash: string,
): string {
  const projPart = projectId ?? "global";
  const name = `chat-message:${projPart}:${role}:${timestamp}:${contentHash}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a marker
 */
export function generateMarkerId(
  compositionId: string,
  frame: number,
  label: string,
): string {
  const name = `marker:${compositionId}:${frame}:${label}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a mesh warp pin
 */
export function generateMeshWarpPinId(
  layerId: string,
  pinIndex: number,
): string {
  const name = `mesh-warp-pin:${layerId}:${pinIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an audio analysis entry
 */
export function generateAudioAnalysisId(
  audioTrackId: string,
  analysisType: string,
  frame: number,
): string {
  const name = `audio-analysis:${audioTrackId}:${analysisType}:${frame}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an AI model
 */
export function generateAIModelId(modelName: string, provider: string): string {
  const name = `ai-model:${provider}:${modelName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a segmentation
 */
export function generateSegmentationId(
  layerId: string,
  method: string,
  timestamp: number,
): string {
  const name = `segmentation:${layerId}:${method}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a vectorization
 */
export function generateVectorizationId(
  layerId: string,
  method: string,
  timestamp: number,
): string {
  const name = `vectorization:${layerId}:${method}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a template exposed property
 */
export function generateTemplateExposedPropertyId(
  templateId: string,
  propertyPath: string,
): string {
  const name = `template-property:${templateId}:${propertyPath}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an event
 */
export function generateEventId(
  eventType: string,
  projectId: string | null,
  timestamp: number,
  dataHash: string,
): string {
  const projPart = projectId ?? "global";
  const name = `event:${eventType}:${projPart}:${timestamp}:${dataHash}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a metric
 */
export function generateMetricId(
  metricName: string,
  projectId: string | null,
  timestamp: number,
): string {
  const projPart = projectId ?? "global";
  const name = `metric:${metricName}:${projPart}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a project
 */
export function generateProjectId(
  projectName: string,
  timestamp: number,
): string {
  const name = `project:${projectName}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a feature flag
 */
export function generateFeatureFlagId(flagName: string): string {
  const name = `feature-flag:${flagName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a physics space
 */
export function generatePhysicsSpaceId(compositionId: string): string {
  const name = `physics-space:${compositionId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an audio track
 */
export function generateAudioTrackId(
  compositionId: string,
  trackName: string,
  index: number,
): string {
  const name = `audio-track:${compositionId}:${trackName}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for audio reactivity
 */
export function generateAudioReactivityId(
  layerId: string,
  audioTrackId: string,
  propertyPath: string,
): string {
  const name = `audio-reactivity:${layerId}:${audioTrackId}:${propertyPath}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a camera path
 */
export function generateCameraPathId(cameraId: string): string {
  const name = `camera-path:${cameraId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a layer mask
 */
export function generateLayerMaskId(
  layerId: string,
  maskName: string,
  index: number,
): string {
  const name = `layer-mask:${layerId}:${maskName}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for layer styles
 */
export function generateLayerStylesId(layerId: string): string {
  const name = `layer-styles:${layerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an expression
 */
export function generateExpressionId(
  layerId: string,
  propertyPath: string,
): string {
  const name = `expression:${layerId}:${propertyPath}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a render settings entry
 */
export function generateRenderSettingsId(compositionId: string): string {
  const name = `render-settings:${compositionId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an export template
 */
export function generateExportTemplateId(
  templateName: string,
  projectId: string | null,
): string {
  const projPart = projectId ?? "global";
  const name = `export-template:${templateName}:${projPart}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a preprocessor
 */
export function generatePreprocessorId(preprocessorName: string): string {
  const name = `preprocessor:${preprocessorName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a mesh warp mesh
 */
export function generateMeshWarpMeshId(layerId: string): string {
  const name = `mesh-warp-mesh:${layerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for physics cloth
 */
export function generatePhysicsClothId(
  physicsSpaceId: string,
  layerId: string,
): string {
  const name = `physics-cloth:${physicsSpaceId}:${layerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for physics ragdoll
 */
export function generatePhysicsRagdollId(
  physicsSpaceId: string,
  layerId: string,
): string {
  const name = `physics-ragdoll:${physicsSpaceId}:${layerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for physics rigid body
 */
export function generatePhysicsRigidBodyId(physicsBodyId: string): string {
  const name = `physics-rigid-body:${physicsBodyId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an individual particle
 *
 * CRITICAL: Every particle needs a UUID5 for determinism at scale.
 * For 400k particles per layer, this ensures:
 * - Same seed + index = same particle ID
 * - Deterministic tracking across frames
 * - No collisions (SHA-1 hash space)
 * - Memory efficient (just string IDs)
 *
 * @param layerId - Layer containing the particle
 * @param emitterId - Emitter that spawned the particle
 * @param particleIndex - Index within the particle system
 * @param spawnFrame - Frame when particle was spawned
 * @param seed - Deterministic seed for this particle
 */
export function generateParticleId(
  layerId: string,
  emitterId: string,
  particleIndex: number,
  spawnFrame: number,
  seed: number,
): string {
  const name = `particle:${layerId}:${emitterId}:${particleIndex}:${spawnFrame}:${seed}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a particle group
 */
export function generateParticleGroupId(
  layerId: string,
  groupName: string,
  index: number,
): string {
  const name = `particle-group:${layerId}:${groupName}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a particle connection (spring/chain)
 */
export function generateParticleConnectionId(
  particleSystemId: string,
  particleAId: string,
  particleBId: string,
  connectionType: string,
): string {
  // Sort IDs to ensure deterministic ordering
  const [idA, idB] = [particleAId, particleBId].sort();
  const name = `particle-connection:${particleSystemId}:${connectionType}:${idA}:${idB}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a particle trail
 */
export function generateParticleTrailId(
  particleId: string,
  trailIndex: number,
): string {
  const name = `particle-trail:${particleId}:${trailIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a particle sub-emitter instance
 */
export function generateParticleSubEmitterId(
  parentParticleId: string,
  subEmitterType: string,
  instanceIndex: number,
): string {
  const name = `particle-sub-emitter:${parentParticleId}:${subEmitterType}:${instanceIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for audio analysis beat/peak
 */
export function generateAudioBeatId(
  audioTrackId: string,
  frame: number,
  beatIndex: number,
): string {
  const name = `audio-beat:${audioTrackId}:${frame}:${beatIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for audio peak
 */
export function generateAudioPeakId(
  audioTrackId: string,
  frame: number,
  frequencyBand: string,
): string {
  const name = `audio-peak:${audioTrackId}:${frame}:${frequencyBand}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for MIDI note event
 */
export function generateMidiNoteId(
  midiTrackId: string,
  channel: number,
  note: number,
  frame: number,
  velocity: number,
): string {
  const name = `midi-note:${midiTrackId}:${channel}:${note}:${frame}:${velocity}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for MIDI CC (control change)
 */
export function generateMidiCCId(
  midiTrackId: string,
  channel: number,
  ccNumber: number,
  frame: number,
  value: number,
): string {
  const name = `midi-cc:${midiTrackId}:${channel}:${ccNumber}:${frame}:${value}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for nested composition reference
 */
export function generateNestedCompId(
  parentCompId: string,
  nestedCompId: string,
  instanceIndex: number,
): string {
  const name = `nested-comp:${parentCompId}:${nestedCompId}:${instanceIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for composition instance in timeline
 */
export function generateCompInstanceId(
  compId: string,
  startFrame: number,
  endFrame: number,
): string {
  const name = `comp-instance:${compId}:${startFrame}:${endFrame}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a text layer
 */
export function generateTextLayerId(layerId: string): string {
  const name = `text-layer:${layerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a spline control point
 */
export function generateSplineControlPointId(
  splineLayerId: string,
  pointIndex: number,
  segmentIndex: number,
): string {
  const name = `spline-control-point:${splineLayerId}:${segmentIndex}:${pointIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a spline anchor point
 */
export function generateSplineAnchorPointId(
  splineLayerId: string,
  anchorIndex: number,
): string {
  const name = `spline-anchor-point:${splineLayerId}:${anchorIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a shape path
 */
export function generateShapePathId(
  layerId: string,
  pathIndex: number,
): string {
  const name = `shape-path:${layerId}:${pathIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a shape path command
 */
export function generateShapePathCommandId(
  pathId: string,
  commandIndex: number,
): string {
  const name = `shape-path-command:${pathId}:${commandIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a guide
 */
export function generateGuideId(
  compositionId: string,
  guideType: string,
  index: number,
): string {
  const name = `guide:${compositionId}:${guideType}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a sprite sheet
 */
export function generateSpriteSheetId(
  projectId: string,
  spriteSheetName: string,
  timestamp: number,
): string {
  const name = `sprite-sheet:${projectId}:${spriteSheetName}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a sprite frame
 */
export function generateSpriteFrameId(
  spriteSheetId: string,
  frameIndex: number,
): string {
  const name = `sprite-frame:${spriteSheetId}:${frameIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an SVG document
 */
export function generateSvgDocumentId(
  projectId: string,
  svgName: string,
  timestamp: number,
): string {
  const name = `svg-document:${projectId}:${svgName}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an SVG path
 */
export function generateSvgPathId(
  svgDocumentId: string,
  pathIndex: number,
): string {
  const name = `svg-path:${svgDocumentId}:${pathIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a material
 */
export function generateMaterialId(
  projectId: string,
  materialName: string,
  materialType: string,
): string {
  const name = `material:${projectId}:${materialType}:${materialName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a texture
 */
export function generateTextureId(
  projectId: string,
  textureName: string,
  textureType: string,
): string {
  const name = `texture:${projectId}:${textureType}:${textureName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a mesh
 */
export function generateMeshId(
  projectId: string,
  meshName: string,
  meshType: string,
): string {
  const name = `mesh:${projectId}:${meshType}:${meshName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a mesh vertex
 */
export function generateMeshVertexId(
  meshId: string,
  vertexIndex: number,
): string {
  const name = `mesh-vertex:${meshId}:${vertexIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a mesh face
 */
export function generateMeshFaceId(meshId: string, faceIndex: number): string {
  const name = `mesh-face:${meshId}:${faceIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a render frame
 */
export function generateRenderFrameId(
  exportJobId: string,
  frame: number,
): string {
  const name = `render-frame:${exportJobId}:${frame}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a render tile
 */
export function generateRenderTileId(
  renderFrameId: string,
  tileX: number,
  tileY: number,
): string {
  const name = `render-tile:${renderFrameId}:${tileX}:${tileY}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a workflow node
 */
export function generateWorkflowNodeId(
  workflowId: string,
  nodeType: string,
  nodeIndex: number,
): string {
  const name = `workflow-node:${workflowId}:${nodeType}:${nodeIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a workflow connection
 */
export function generateWorkflowConnectionId(
  workflowId: string,
  sourceNodeId: string,
  targetNodeId: string,
  outputIndex: number,
  inputIndex: number,
): string {
  const name = `workflow-connection:${workflowId}:${sourceNodeId}:${targetNodeId}:${outputIndex}:${inputIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a tool call
 */
export function generateToolCallId(
  chatMessageId: string,
  toolName: string,
  callIndex: number,
): string {
  const name = `tool-call:${chatMessageId}:${toolName}:${callIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a user action
 */
export function generateUserActionId(
  userId: string,
  actionType: string,
  timestamp: number,
): string {
  const name = `user-action:${userId}:${actionType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a session
 */
export function generateSessionId(userId: string, timestamp: number): string {
  const name = `session:${userId}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a cache entry
 */
export function generateCacheEntryId(
  cacheKey: string,
  cacheType: string,
): string {
  const name = `cache-entry:${cacheType}:${cacheKey}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a frame cache entry
 */
export function generateFrameCacheEntryId(
  layerId: string,
  frame: number,
  cacheType: string,
): string {
  const name = `frame-cache-entry:${layerId}:${frame}:${cacheType}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a timeline track
 */
export function generateTimelineTrackId(
  compositionId: string,
  trackType: string,
  trackIndex: number,
): string {
  const name = `timeline-track:${compositionId}:${trackType}:${trackIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a timeline clip
 */
export function generateTimelineClipId(
  trackId: string,
  startFrame: number,
  endFrame: number,
): string {
  const name = `timeline-clip:${trackId}:${startFrame}:${endFrame}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a color stop (gradient)
 */
export function generateColorStopId(
  gradientId: string,
  stopIndex: number,
): string {
  const name = `color-stop:${gradientId}:${stopIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a gradient
 */
export function generateGradientId(
  layerId: string,
  gradientType: string,
  index: number,
): string {
  const name = `gradient:${layerId}:${gradientType}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a filter
 */
export function generateFilterId(
  layerId: string,
  filterType: string,
  index: number,
): string {
  const name = `filter:${layerId}:${filterType}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a blend mode override
 */
export function generateBlendModeOverrideId(
  layerId: string,
  targetLayerId: string,
): string {
  const name = `blend-mode-override:${layerId}:${targetLayerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a transform constraint
 */
export function generateTransformConstraintId(
  layerId: string,
  constraintType: string,
): string {
  const name = `transform-constraint:${layerId}:${constraintType}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a parent constraint
 */
export function generateParentConstraintId(
  layerId: string,
  parentLayerId: string,
): string {
  const name = `parent-constraint:${layerId}:${parentLayerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a look-at constraint
 */
export function generateLookAtConstraintId(
  layerId: string,
  targetLayerId: string,
): string {
  const name = `look-at-constraint:${layerId}:${targetLayerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a path constraint
 */
export function generatePathConstraintId(
  layerId: string,
  pathLayerId: string,
): string {
  const name = `path-constraint:${layerId}:${pathLayerId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a pose bone
 */
export function generatePoseBoneId(
  poseLayerId: string,
  boneName: string,
  boneIndex: number,
): string {
  const name = `pose-bone:${poseLayerId}:${boneName}:${boneIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a pose keyframe
 */
export function generatePoseKeyframeId(
  poseLayerId: string,
  boneId: string,
  frame: number,
): string {
  const name = `pose-keyframe:${poseLayerId}:${boneId}:${frame}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a control point (mesh warp, spline, etc.)
 */
export function generateControlPointId(
  layerId: string,
  controlPointType: string,
  pointIndex: number,
): string {
  const name = `control-point:${layerId}:${controlPointType}:${pointIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a deformation handle
 */
export function generateDeformationHandleId(
  layerId: string,
  handleIndex: number,
): string {
  const name = `deformation-handle:${layerId}:${handleIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a light
 */
export function generateLightId(
  compositionId: string,
  lightType: string,
  lightIndex: number,
): string {
  const name = `light:${compositionId}:${lightType}:${lightIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an environment map
 */
export function generateEnvironmentMapId(
  projectId: string,
  envMapName: string,
): string {
  const name = `environment-map:${projectId}:${envMapName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a shader
 */
export function generateShaderId(
  projectId: string,
  shaderName: string,
  shaderType: string,
): string {
  const name = `shader:${projectId}:${shaderType}:${shaderName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a shader uniform
 */
export function generateShaderUniformId(
  shaderId: string,
  uniformName: string,
): string {
  const name = `shader-uniform:${shaderId}:${uniformName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a compute shader
 */
export function generateComputeShaderId(
  projectId: string,
  shaderName: string,
): string {
  const name = `compute-shader:${projectId}:${shaderName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a render pass
 */
export function generateRenderPassId(
  compositionId: string,
  passType: string,
  passIndex: number,
): string {
  const name = `render-pass:${compositionId}:${passType}:${passIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a render target
 */
export function generateRenderTargetId(
  renderPassId: string,
  targetIndex: number,
): string {
  const name = `render-target:${renderPassId}:${targetIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a post-processing effect
 */
export function generatePostProcessingEffectId(
  compositionId: string,
  effectType: string,
  index: number,
): string {
  const name = `post-processing-effect:${compositionId}:${effectType}:${index}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a viewport
 */
export function generateViewportId(
  compositionId: string,
  viewportIndex: number,
): string {
  const name = `viewport:${compositionId}:${viewportIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a selection
 */
export function generateSelectionId(userId: string, timestamp: number): string {
  const name = `selection:${userId}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a clipboard entry
 */
export function generateClipboardEntryId(
  userId: string,
  entryType: string,
  timestamp: number,
): string {
  const name = `clipboard-entry:${userId}:${entryType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an undo/redo state
 */
export function generateUndoRedoStateId(
  projectId: string,
  stateIndex: number,
): string {
  const name = `undo-redo-state:${projectId}:${stateIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a history entry
 */
export function generateHistoryEntryId(
  projectId: string,
  entryIndex: number,
): string {
  const name = `history-entry:${projectId}:${entryIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a workspace layout
 */
export function generateWorkspaceLayoutId(
  userId: string,
  layoutName: string,
): string {
  const name = `workspace-layout:${userId}:${layoutName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a workspace panel
 */
export function generateWorkspacePanelId(
  layoutId: string,
  panelType: string,
  panelIndex: number,
): string {
  const name = `workspace-panel:${layoutId}:${panelType}:${panelIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a keyboard shortcut
 */
export function generateKeyboardShortcutId(
  actionId: string,
  keyCombo: string,
): string {
  const name = `keyboard-shortcut:${actionId}:${keyCombo}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a plugin
 */
export function generatePluginId(
  pluginName: string,
  pluginVersion: string,
): string {
  const name = `plugin:${pluginName}:${pluginVersion}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a plugin instance
 */
export function generatePluginInstanceId(
  pluginId: string,
  instanceIndex: number,
): string {
  const name = `plugin-instance:${pluginId}:${instanceIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a plugin hook
 */
export function generatePluginHookId(
  pluginId: string,
  hookName: string,
): string {
  const name = `plugin-hook:${pluginId}:${hookName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a webhook
 */
export function generateWebhookId(
  projectId: string,
  webhookName: string,
): string {
  const name = `webhook:${projectId}:${webhookName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a webhook event
 */
export function generateWebhookEventId(
  webhookId: string,
  eventType: string,
  timestamp: number,
): string {
  const name = `webhook-event:${webhookId}:${eventType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an API key
 */
export function generateApiKeyId(userId: string, keyName: string): string {
  const name = `api-key:${userId}:${keyName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an API request
 */
export function generateApiRequestId(
  apiKeyId: string,
  requestHash: string,
  timestamp: number,
): string {
  const name = `api-request:${apiKeyId}:${requestHash}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a subscription
 */
export function generateSubscriptionId(
  userId: string,
  subscriptionType: string,
): string {
  const name = `subscription:${userId}:${subscriptionType}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a payment
 */
export function generatePaymentId(
  subscriptionId: string,
  paymentIndex: number,
): string {
  const name = `payment:${subscriptionId}:${paymentIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a notification
 */
export function generateNotificationId(
  userId: string,
  notificationType: string,
  timestamp: number,
): string {
  const name = `notification:${userId}:${notificationType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a collaboration session
 */
export function generateCollaborationSessionId(
  projectId: string,
  userId: string,
  timestamp: number,
): string {
  const name = `collaboration-session:${projectId}:${userId}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a collaboration change
 */
export function generateCollaborationChangeId(
  sessionId: string,
  changeIndex: number,
): string {
  const name = `collaboration-change:${sessionId}:${changeIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a comment
 */
export function generateCommentId(
  compositionId: string,
  frame: number,
  userId: string,
  commentIndex: number,
): string {
  const name = `comment:${compositionId}:${frame}:${userId}:${commentIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a review
 */
export function generateReviewId(
  projectId: string,
  reviewerId: string,
  timestamp: number,
): string {
  const name = `review:${projectId}:${reviewerId}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a review comment
 */
export function generateReviewCommentId(
  reviewId: string,
  commentIndex: number,
): string {
  const name = `review-comment:${reviewId}:${commentIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a tag
 */
export function generateTagId(projectId: string, tagName: string): string {
  const name = `tag:${projectId}:${tagName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a tag assignment
 */
export function generateTagAssignmentId(
  tagId: string,
  entityId: string,
  entityType: string,
): string {
  const name = `tag-assignment:${tagId}:${entityType}:${entityId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a collection
 */
export function generateCollectionId(
  projectId: string,
  collectionName: string,
): string {
  const name = `collection:${projectId}:${collectionName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a collection item
 */
export function generateCollectionItemId(
  collectionId: string,
  itemIndex: number,
): string {
  const name = `collection-item:${collectionId}:${itemIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a search query
 */
export function generateSearchQueryId(
  userId: string,
  queryHash: string,
  timestamp: number,
): string {
  const name = `search-query:${userId}:${queryHash}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a search result
 */
export function generateSearchResultId(
  queryId: string,
  resultIndex: number,
): string {
  const name = `search-result:${queryId}:${resultIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a bookmark
 */
export function generateBookmarkId(
  userId: string,
  entityId: string,
  entityType: string,
): string {
  const name = `bookmark:${userId}:${entityType}:${entityId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a favorite
 */
export function generateFavoriteId(
  userId: string,
  entityId: string,
  entityType: string,
): string {
  const name = `favorite:${userId}:${entityType}:${entityId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a share link
 */
export function generateShareLinkId(
  projectId: string,
  shareType: string,
  timestamp: number,
): string {
  const name = `share-link:${projectId}:${shareType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a download
 */
export function generateDownloadId(
  shareLinkId: string,
  downloadIndex: number,
): string {
  const name = `download:${shareLinkId}:${downloadIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an import job
 */
export function generateImportJobId(
  projectId: string,
  importType: string,
  timestamp: number,
): string {
  const name = `import-job:${projectId}:${importType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for an import item
 */
export function generateImportItemId(
  importJobId: string,
  itemIndex: number,
): string {
  const name = `import-item:${importJobId}:${itemIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a sync job
 */
export function generateSyncJobId(
  projectId: string,
  syncType: string,
  timestamp: number,
): string {
  const name = `sync-job:${projectId}:${syncType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a backup
 */
export function generateBackupId(
  projectId: string,
  backupType: string,
  timestamp: number,
): string {
  const name = `backup:${projectId}:${backupType}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a restore point
 */
export function generateRestorePointId(
  projectId: string,
  timestamp: number,
): string {
  const name = `restore-point:${projectId}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a version
 */
export function generateVersionId(
  projectId: string,
  versionNumber: string,
): string {
  const name = `version:${projectId}:${versionNumber}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a branch
 */
export function generateBranchId(
  projectId: string,
  branchName: string,
): string {
  const name = `branch:${projectId}:${branchName}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a commit
 */
export function generateCommitId(branchId: string, commitHash: string): string {
  const name = `commit:${branchId}:${commitHash}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a diff
 */
export function generateDiffId(commitId: string, filePath: string): string {
  const name = `diff:${commitId}:${filePath}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a merge
 */
export function generateMergeId(
  sourceBranchId: string,
  targetBranchId: string,
  timestamp: number,
): string {
  const name = `merge:${sourceBranchId}:${targetBranchId}:${timestamp}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a conflict
 */
export function generateConflictId(
  mergeId: string,
  conflictIndex: number,
): string {
  const name = `conflict:${mergeId}:${conflictIndex}`;
  return uuid5(name, LATTICE_NAMESPACE);
}

/**
 * Generate deterministic UUID5 for a resolution
 */
export function generateResolutionId(conflictId: string): string {
  const name = `resolution:${conflictId}`;
  return uuid5(name, LATTICE_NAMESPACE);
}
