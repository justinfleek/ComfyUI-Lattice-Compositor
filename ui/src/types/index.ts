// ============================================================
// TYPES INDEX - Barrel export for all type modules
// ============================================================
// NOTE: For conflicting exports, import directly from the specific module.
// ============================================================

// Core foundational types
export * from './animation';
export * from './blendModes';
// Transform - exclude AutoOrientMode (defined in project.ts)
export type {
  Vec2,
  Vec3,
  LayerTransform,
  MotionBlurType,
  LayerMotionBlurSettings,
  LayerMaterialOptions,
  FollowPathConstraint
} from './transform';
export { createDefaultTransform, normalizeLayerTransform, createFollowPathConstraint } from './transform';

export * from './masks';
export * from './spline';
export * from './text';
export * from './particles';

// Feature-specific types
// Effects - exclude AnimationPreset (conflicts with presets.ts)
export type {
  EffectCategory,
  EffectParameter,
  Effect,
  EffectInstance,
  EffectParameterType,
  EffectDefinition
} from './effects';
export { getAnimatableType, EFFECT_DEFINITIONS } from './effects';

// Shapes - primary source for GradientDef, GradientStop, createDefaultStroke
export * from './shapes';

// TemplateBuilder - some conflicts handled
export * from './templateBuilder';

// LayerStyles - has its own RGBA, GradientDef, GradientStop (different from shapes.ts)
// Import directly from '@/types/layerStyles' if needed
// export * from './layerStyles';  // Disabled due to GradientDef/GradientStop conflicts

export * from './meshWarp';
export * from './physics';
export * from './camera';
export * from './cameraTracking';
export * from './dataAsset';
export * from './export';
export * from './presets';
export * from './assets';
export * from './layerData';

// Project types - DO NOT use export * to avoid conflicts
// Import these directly from '@/types/project' instead
