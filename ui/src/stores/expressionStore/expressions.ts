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
 */
export function setPropertyExpression(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  expression: PropertyExpression,
): boolean {
  return useKeyframeStore().setPropertyExpression(
    store,
    layerId,
    propertyPath,
    expression,
  );
}

/**
 * Enable expression on a property
 */
export function enablePropertyExpression(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  expressionName: string = "custom",
  params: Record<string, number | string | boolean> = {},
): boolean {
  return useKeyframeStore().enablePropertyExpression(
    store,
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
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().disablePropertyExpression(
    store,
    layerId,
    propertyPath,
  );
}

/**
 * Toggle expression enabled state
 */
export function togglePropertyExpression(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().togglePropertyExpression(
    store,
    layerId,
    propertyPath,
  );
}

/**
 * Remove expression from property
 */
export function removePropertyExpression(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().removePropertyExpression(
    store,
    layerId,
    propertyPath,
  );
}

/**
 * Get expression for a property
 */
export function getPropertyExpression(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): PropertyExpression | undefined {
  return useKeyframeStore().getPropertyExpression(store, layerId, propertyPath);
}

/**
 * Check if property has an expression
 */
export function hasPropertyExpression(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().hasPropertyExpression(store, layerId, propertyPath);
}

/**
 * Update expression parameters
 */
export function updateExpressionParams(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  params: Record<string, number | string | boolean>,
): boolean {
  return useKeyframeStore().updateExpressionParams(
    store,
    layerId,
    propertyPath,
    params,
  );
}

/**
 * Check if a property has a bakeable expression
 */
export function canBakeExpression(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
): boolean {
  return useKeyframeStore().canBakeExpression(store, layerId, propertyPath);
}

/**
 * Convert expression to keyframes (bake expression)
 * Cross-domain: calls keyframeStore to create keyframes
 */
export function convertExpressionToKeyframes(
  store: ExpressionStoreAccess,
  layerId: string,
  propertyPath: string,
  startFrame?: number,
  endFrame?: number,
  sampleRate?: number,
): number {
  return useKeyframeStore().convertExpressionToKeyframes(
    store,
    layerId,
    propertyPath,
    startFrame,
    endFrame,
    sampleRate,
  );
}
