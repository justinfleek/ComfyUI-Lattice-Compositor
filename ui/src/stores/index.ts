/**
 * Store Exports
 *
 * Central export for all Pinia stores.
 * Import stores from this file for cleaner imports.
 */

// Main compositor store (legacy - being refactored)
export { useCompositorStore } from './compositorStore';

// Domain-specific stores
export { usePlaybackStore, type PlaybackStore } from './playbackStore';
export { useAudioStore, type AudioStore } from './audioStore';
export { useSelectionStore, type SelectionStore } from './selectionStore';
export { useHistoryStore, type HistoryStore } from './historyStore';
