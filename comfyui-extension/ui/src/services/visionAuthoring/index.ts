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

// Services
export {
  MotionIntentResolver,
  motionIntentResolver,
} from "./MotionIntentResolver";
export {
  MotionIntentTranslator,
  motionIntentTranslator,
} from "./MotionIntentTranslator";
// Types
// Re-export ControlPoint from types for convenience
export type {
  // Intent types
  CameraMotionIntent,
  // Motion types
  CameraMotionType,
  ControlPoint,
  DepthEstimationResult,
  DepthLayer,
  DepthModelId,
  EasingType,
  // Translation types
  KeyframeBatch,
  LayerMotionIntent,
  LayerMotionType,
  MotionIntensity,
  MotionIntentResult,
  NewLayerSpec,
  NewSplineSpec,
  ParticleBehavior,
  ParticleMotionIntent,
  PathSuggestionResult,
  // Suggestion types
  PointSuggestion,
  // Scene context
  SceneContext,
  SegmentationMask,
  SegmentationModelId,
  SegmentationRequest,
  SegmentationResult,
  SplineMotionIntent,
  SplineUsage,
  TrajectorySuggestion,
  TranslationResult,
  VisionModelConfig,
  // Configuration
  VisionModelId,
} from "./types";
