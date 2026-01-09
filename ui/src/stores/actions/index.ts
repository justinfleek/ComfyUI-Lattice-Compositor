/**
 * Store Actions Index
 *
 * Extracted action modules for compositorStore.
 * These modules provide implementations that can be called from the store
 * to reduce the main store file size.
 */

// Audio actions (loading, analysis, reactive mappings)
export * from "./audioActions";
// Cache actions (frame caching)
export * from "./cacheActions";
// Camera actions
export * from "./cameraActions";
// Effect actions
export * from "./effectActions";

// Keyframe actions
export * from "./keyframeActions";
// Layer actions
export * from "./layerActions";
// Layer decomposition actions (Qwen-Image-Layered integration)
export * from "./layerDecompositionActions";
// Layer style actions (Photoshop-style layer effects)
export * from "./layerStyleActions";
// Physics actions (Newton Physics Simulation)
export * from "./physicsActions";
// Project actions (history, save/load, autosave)
export * from "./projectActions";
// Property driver actions (expressions/links)
export * from "./propertyDriverActions";
// Segmentation actions (Vision model integration)
export * from "./segmentationActions";

// Text Animator actions (Tutorial 06)
export * from "./textAnimatorActions";
