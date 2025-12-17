/**
 * Vision-Guided Authoring Module
 *
 * AI-assisted trajectory and path suggestion for motion graphics.
 *
 * USAGE:
 * ```typescript
 * import { motionIntentResolver, motionIntentTranslator } from '@/services/visionAuthoring';
 *
 * // 1. Get AI suggestions
 * const intent = await motionIntentResolver.suggestPaths(sceneContext);
 *
 * // 2. Translate to keyframes (deterministic)
 * const result = motionIntentTranslator.translateSplineIntent(
 *   intent.splineIntents[0],
 *   width,
 *   height
 * );
 *
 * // 3. User reviews and accepts
 * if (userAccepts) {
 *   store.createSplineLayer(result.newSplines[0]);
 * }
 *
 * // 4. MotionEngine evaluates (AI no longer involved)
 * ```
 */

// Types
export type {
  // Scene context
  SceneContext,
  SegmentationMask,

  // Intent types
  CameraMotionIntent,
  SplineMotionIntent,
  ParticleMotionIntent,
  LayerMotionIntent,
  MotionIntentResult,

  // Motion types
  CameraMotionType,
  MotionIntensity,
  EasingType,
  SplineUsage,
  ParticleBehavior,
  LayerMotionType,

  // Suggestion types
  PointSuggestion,
  TrajectorySuggestion,
  PathSuggestionResult,
  DepthLayer,

  // Translation types
  KeyframeBatch,
  TranslationResult,
  NewLayerSpec,
  NewSplineSpec,

  // Configuration
  VisionModelId,
  VisionModelConfig,
  DepthModelId,
  DepthEstimationResult,
  SegmentationModelId,
  SegmentationRequest,
  SegmentationResult,
} from './types';

// Services
export { MotionIntentResolver, motionIntentResolver } from './MotionIntentResolver';
export { MotionIntentTranslator, motionIntentTranslator } from './MotionIntentTranslator';

// Re-export ControlPoint from types for convenience
export type { ControlPoint } from './types';
