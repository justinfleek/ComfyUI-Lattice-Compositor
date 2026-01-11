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
// Main compositor store (legacy - being refactored into domain stores)
export { useCompositorStore } from "./compositorStore";
export { type HistoryStore, useHistoryStore } from "./historyStore";
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
