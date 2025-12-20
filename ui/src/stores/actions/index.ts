/**
 * Store Actions Index
 *
 * Extracted action modules for compositorStore.
 * These modules provide implementations that can be called from the store
 * to reduce the main store file size.
 */

// Segmentation actions (Vision model integration)
export * from './segmentationActions';

// Camera actions
export * from './cameraActions';

// Effect actions
export * from './effectActions';

// Layer actions
export * from './layerActions';

// Keyframe actions
export * from './keyframeActions';

// Project actions (history, save/load, autosave)
export * from './projectActions';

// Audio actions (loading, analysis, reactive mappings)
export * from './audioActions';

// Property driver actions (expressions/links)
export * from './propertyDriverActions';

// Cache actions (frame caching)
export * from './cacheActions';
