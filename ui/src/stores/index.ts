/**
 * Store Exports
 *
 * Central export for all Pinia stores.
 * Import stores from this file for cleaner imports.
 */

export { type AudioStore, useAudioStore } from "./audioStore";
// Main compositor store (legacy - being refactored)
export { useCompositorStore } from "./compositorStore";
export { type HistoryStore, useHistoryStore } from "./historyStore";
// Domain-specific stores
export { type PlaybackStore, usePlaybackStore } from "./playbackStore";
export { type SelectionStore, useSelectionStore } from "./selectionStore";
