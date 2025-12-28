/**
 * Keyframe Expression Actions
 *
 * Handles property expressions: set, enable, disable, toggle, remove, get.
 * Also includes expression-to-keyframe conversion (baking).
 *
 * Extracted from keyframeActions.ts for modularity.
 */

import { storeLogger } from '@/utils/logger';
import type { Layer, AnimatableProperty, Keyframe, PropertyExpression } from '@/types/project';
import { markLayerDirty } from '@/services/layerEvaluationCache';
import { findPropertyByPath, KeyframeStore } from '../keyframeActions';

// ============================================================================
// EXPRESSION METHODS
// ============================================================================

/**
 * Set an expression on a property
 */
export function setPropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  expression: PropertyExpression
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) {
    storeLogger.warn('setPropertyExpression: layer not found:', layerId);
    return false;
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    storeLogger.warn('setPropertyExpression: property not found:', propertyPath);
    return false;
  }

  property.expression = expression;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  storeLogger.debug('Set expression on', propertyPath, ':', expression.name);
  return true;
}

/**
 * Enable expression on a property (creates default if not exists)
 */
export function enablePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  expressionName: string = 'custom',
  params: Record<string, number | string | boolean> = {}
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  const expression: PropertyExpression = {
    enabled: true,
    type: expressionName === 'custom' ? 'custom' : 'preset',
    name: expressionName,
    params
  };

  property.expression = expression;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

/**
 * Disable expression on a property (keeps expression data for re-enabling)
 */
export function disablePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.enabled = false;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

/**
 * Toggle expression enabled state
 */
export function togglePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.enabled = !property.expression.enabled;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return property.expression.enabled;
}

/**
 * Remove expression from a property
 */
export function removePropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  delete property.expression;
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

/**
 * Get expression on a property
 */
export function getPropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): PropertyExpression | undefined {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return undefined;

  const property = findPropertyByPath(layer, propertyPath);
  return property?.expression;
}

/**
 * Check if property has an expression
 */
export function hasPropertyExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  return property?.expression !== undefined;
}

/**
 * Update expression parameters
 */
export function updateExpressionParams(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string,
  params: Record<string, number | string | boolean>
): boolean {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property || !property.expression) return false;

  property.expression.params = { ...property.expression.params, ...params };
  store.project.meta.modified = new Date().toISOString();
  markLayerDirty(layerId);
  store.pushHistory();

  return true;
}

// ============================================================================
// CONVERT EXPRESSION TO KEYFRAMES (BAKE)
// ============================================================================

export interface BakeExpressionStore extends KeyframeStore {
  fps: number;
  frameCount: number;
  evaluatePropertyAtFrame(layerId: string, propertyPath: string, frame: number): any;
}

/**
 * Convert an expression to keyframes by sampling at every frame.
 * This "bakes" the expression result into keyframes.
 *
 * @param store - Store with expression evaluation capability
 * @param layerId - Layer ID
 * @param propertyPath - Property path with expression
 * @param startFrame - Start frame (default: 0)
 * @param endFrame - End frame (default: composition duration)
 * @param sampleRate - Sample every N frames (default: 1 = every frame)
 * @returns Number of keyframes created
 */
export function convertExpressionToKeyframes(
  store: BakeExpressionStore,
  layerId: string,
  propertyPath: string,
  startFrame?: number,
  endFrame?: number,
  sampleRate: number = 1
): number {
  const layer = store.getLayerById(layerId);
  if (!layer) {
    storeLogger.warn('convertExpressionToKeyframes: layer not found:', layerId);
    return 0;
  }

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) {
    storeLogger.warn('convertExpressionToKeyframes: property not found:', propertyPath);
    return 0;
  }

  if (!property.expression?.enabled) {
    storeLogger.warn('convertExpressionToKeyframes: no active expression on property');
    return 0;
  }

  const start = startFrame ?? 0;
  const end = endFrame ?? store.frameCount;
  // Validate sampleRate (Math.round(NaN) = NaN, Math.max(1, NaN) = NaN)
  const rate = Number.isFinite(sampleRate) ? Math.max(1, Math.round(sampleRate)) : 1;

  // Clear existing keyframes
  property.keyframes = [];
  property.animated = true;

  let keyframesCreated = 0;

  // Sample expression at each frame
  for (let frame = start; frame <= end; frame += rate) {
    const value = store.evaluatePropertyAtFrame(layerId, propertyPath, frame);

    if (value !== undefined && value !== null) {
      const keyframe: Keyframe<any> = {
        id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        frame,
        value,
        interpolation: 'linear',
        inHandle: { frame: 0, value: 0, enabled: false },
        outHandle: { frame: 0, value: 0, enabled: false },
        controlMode: 'smooth'
      };

      property.keyframes.push(keyframe);
      keyframesCreated++;
    }
  }

  // Disable the expression after baking
  if (property.expression) {
    property.expression.enabled = false;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.info('convertExpressionToKeyframes: created', keyframesCreated, 'keyframes');
  return keyframesCreated;
}

/**
 * Check if a property has a bakeable expression
 */
export function canBakeExpression(
  store: KeyframeStore,
  layerId: string,
  propertyPath: string
): boolean {
  const layer = store.getLayerById(layerId);
  if (!layer) return false;

  const property = findPropertyByPath(layer, propertyPath);
  if (!property) return false;

  return property.expression?.enabled === true;
}
