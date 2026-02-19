/**
 * Expression Actions
 *
 * Expression CRUD operations - delegates to keyframeStore where expression
 * data is stored alongside keyframe data.
 */

import type { PropertyExpression } from "@/types/animation";
import { useKeyframeStore } from "../keyframeStore";
import type { ExpressionStoreAccess } from "./types";

/**
 * Set a property expression
 * Note: store parameter kept for API compatibility but keyframeStore uses its own state
 */
export function setPropertyExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  expression: PropertyExpression,
): boolean {
  return useKeyframeStore().setPropertyExpression(
    layerId,
    propertyPath,
    expression,
  );
}

/**
 * Enable expression on a property
 */
export function enablePropertyExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  expressionName: string = "custom",
  params: Record<string, number | string | boolean> = {},
): boolean {
  return useKeyframeStore().enablePropertyExpression(
    layerId,
    propertyPath,
    expressionName,
    params,
  );
}

/**
 * Disable expression on a property
 */
export function disablePropertyExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().disablePropertyExpression(
    layerId,
    propertyPath,
  );
}

/**
 * Toggle expression enabled state
 */
export function togglePropertyExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().togglePropertyExpression(
    layerId,
    propertyPath,
  );
}

/**
 * Remove expression from property
 */
export function removePropertyExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().removePropertyExpression(
    layerId,
    propertyPath,
  );
}

/**
 * Get expression for a property
 */
export function getPropertyExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): PropertyExpression | undefined {
  return useKeyframeStore().getPropertyExpression(layerId, propertyPath);
}

/**
 * Check if property has an expression
 */
export function hasPropertyExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().hasPropertyExpression(layerId, propertyPath);
}

/**
 * Update expression parameters
 */
export function updateExpressionParams(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  params: Record<string, number | string | boolean>,
): boolean {
  return useKeyframeStore().updateExpressionParams(
    layerId,
    propertyPath,
    params,
  );
}

/**
 * Check if a property has a bakeable expression
 */
export function canBakeExpression(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().canBakeExpression(layerId, propertyPath);
}

/**
 * Convert expression to keyframes (bake expression)
 * Cross-domain: calls keyframeStore to create keyframes
 */
export function convertExpressionToKeyframes(
  _store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  startFrame?: number,
  endFrame?: number,
  sampleRate?: number,
): number {
  return useKeyframeStore().convertExpressionToKeyframes(
    layerId,
    propertyPath,
    startFrame,
    endFrame,
    sampleRate,
  );
}
