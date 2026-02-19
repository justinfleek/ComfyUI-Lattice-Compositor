/**
 * Expression System - Barrel Re-export
 *
 * This file re-exports all expression functionality from the expressions/ directory.
 * For new code, import directly from '@/services/expressions' or specific submodules.
 *
 * Submodules:
 * - expressions/types: Type definitions
 * - expressions/easing: Easing functions
 * - expressions/motionExpressions: Inertia, bounce, elastic
 * - expressions/loopExpressions: repeatAfter, repeatBefore
 * - expressions/jitterExpressions: jitter, temporalJitter
 * - expressions/expressionHelpers: Value operations
 * - expressions/vectorMath: Vector operations
 * - expressions/coordinateConversion: Coordinate conversion
 * - expressions/audioExpressions: Audio reactivity
 * - expressions/textAnimator: Per-character animation
 * - expressions/expressionEvaluator: Core evaluation
 * - expressions/layerContentExpressions: sourceRectAtTime, textSource
 * - expressions/expressionPresets: Preset configurations
 * - expressions/expressionValidation: Syntax validation
 * - expressions/expressionNamespaces: Convenience namespaces
 */

// Re-export everything from the expressions module
export * from "./expressions/index";
