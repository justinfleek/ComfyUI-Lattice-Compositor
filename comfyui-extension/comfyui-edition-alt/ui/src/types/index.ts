// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                            // types // index
// ════════════════════════════════════════════════════════════════════════════
//                                                                      // note
// ════════════════════════════════════════════════════════════════════════════

// Core foundational types
export * from "./animation";
export * from "./blendModes";
// Feature-specific types
// Effects - exclude AnimationPreset (conflicts with presets.ts)
export type {
  Effect,
  EffectCategory,
  EffectDefinition,
  EffectInstance,
  EffectParameter,
  EffectParameterType,
} from "./effects";
export { EFFECT_DEFINITIONS, getAnimatableType } from "./effects";

export * from "./masks";
export * from "./particles";
// Shapes - primary source for GradientDef, GradientStop, createDefaultStroke
export * from "./shapes";
export * from "./spline";
// TemplateBuilder - some conflicts handled
export * from "./templateBuilder";
export * from "./text";
// Transform - exclude AutoOrientMode (defined in project.ts)
export type {
  FollowPathConstraint,
  LayerMaterialOptions,
  LayerMotionBlurSettings,
  LayerTransform,
  MotionBlurType,
  Vec2,
  Vec3,
} from "./transform";
export {
  createDefaultTransform,
  createFollowPathConstraint,
  normalizeLayerTransform,
} from "./transform";

// LayerStyles - has its own RGBA, GradientDef, GradientStop (different from shapes.ts)
// Import directly from '@/types/layerStyles' if needed
// export * from './layerStyles';  // Disabled due to GradientDef/GradientStop conflicts

export * from "./assets";
export * from "./camera";
export * from "./cameraTracking";
export * from "./dataAsset";
export * from "./export";
export * from "./layerData";
export * from "./meshWarp";
export * from "./physics";
export * from "./presets";

// Project types - DO NOT use export * to avoid conflicts
// Import these directly from '@/types/project' instead
