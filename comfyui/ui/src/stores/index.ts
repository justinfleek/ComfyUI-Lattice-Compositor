/**
 * Store Exports
 *
 * Central export for all Pinia stores.
 * Import stores from this file for cleaner imports.
 */

export {
  type AnimationStoreType,
  type AnimationStoreAccess,
  useAnimationStore,
} from "./animationStore";
export { type AudioStore, useAudioStore } from "./audioStore";
export {
  type ExpressionStoreType,
  type ExpressionStoreAccess,
  useExpressionStore,
} from "./expressionStore";
// Note: compositorStore removed - all functionality migrated to domain stores
// Note: historyStore removed - history is managed by projectStore
// Domain-specific stores (Phase 1+ migration targets)
export {
  type LayerStoreType,
  type LayerSourceReplacement,
  type CreateLayerOptions,
  type DeleteLayerOptions,
  type DuplicateLayerOptions,
  type SequenceLayersOptions,
  type ExponentialScaleOptions,
  type TimeStretchOptions,
  useLayerStore,
} from "./layerStore";
export { type PlaybackStore, usePlaybackStore } from "./playbackStore";
export { type SelectionStore, useSelectionStore } from "./selectionStore";
export { type ProjectStoreAccess, useProjectStore } from "./projectStore";
export { type MarkerStoreAccess, useMarkerStore } from "./markerStore";
export { useUIStore } from "./uiStore";
// Phase 2 stores
export {
  type KeyframeStoreType,
  type KeyframeStoreAccess,
  useKeyframeStore,
} from "./keyframeStore";
// Phase 3 stores
export {
  type EffectStoreType,
  type EffectStoreAccess,
  type LayerStyleStore,
  useEffectStore,
} from "./effectStore";
export {
  type AudioKeyframeStoreAccess,
  useAudioKeyframeStore,
} from "./audioKeyframeStore";
// Phase 4 stores
export {
  type CameraStoreAccess,
  useCameraStore,
} from "./cameraStore";
export {
  type PhysicsStoreAccess,
  usePhysicsStore,
} from "./physicsStore";
// AI/ML stores
export {
  type DecompositionStoreAccess,
  useDecompositionStore,
} from "./decompositionStore";
export {
  type SegmentationStoreAccess,
  useSegmentationStore,
} from "./segmentationStore";