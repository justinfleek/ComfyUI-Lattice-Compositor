// ============================================================
// TYPES INDEX - Barrel export for all type modules
// ============================================================
// This file re-exports all types for backwards compatibility.
// Import from '@/types' or '@/types/project' will work the same.
// ============================================================

// Animation types (foundational - no dependencies)
export * from './animation';

// Blend modes (foundational - no dependencies)
export * from './blendModes';

// Transform types (depends on animation)
export * from './transform';

// Mask types (depends on animation)
export * from './masks';

// Spline types (depends on animation)
export * from './spline';

// Text types (depends on animation)
export * from './text';

// Particle types (depends on animation, blendModes)
export * from './particles';

// Previously extracted type files
export * from './effects';
export * from './shapes';
export * from './essentialGraphics';
export * from './layerStyles';
export * from './meshWarp';
export * from './physics';
export * from './camera';
export * from './cameraTracking';
export * from './dataAsset';
export * from './export';
export * from './presets';

// New modular type files (December 2025)
export * from './assets';
export * from './layerData';

// Main project types (depends on all above)
export * from './project';
