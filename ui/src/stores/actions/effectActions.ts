/**
 * Effect Actions
 *
 * Layer effect management including adding, removing, updating, and reordering.
 */

import type { Layer, EffectInstance, InterpolationType, Composition } from '@/types/project';
import { createEffectInstance } from '@/types/effects';
import { interpolateProperty } from '@/services/interpolation';

export interface EffectStore {
  project: {
    meta: { modified: string };
  };
  currentFrame: number;
  getActiveCompLayers(): Layer[];
  getActiveComp(): Composition | null;
  pushHistory(): void;
}

/**
 * Add effect to layer
 */
export function addEffectToLayer(
  store: EffectStore,
  layerId: string,
  effectKey: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer) return;

  const effect = createEffectInstance(effectKey);
  if (!effect) return;

  if (!layer.effects) {
    layer.effects = [];
  }
  layer.effects.push(effect);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Remove effect from layer
 */
export function removeEffectFromLayer(
  store: EffectStore,
  layerId: string,
  effectId: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.effects) return;

  const index = layer.effects.findIndex(e => e.id === effectId);
  if (index >= 0) {
    layer.effects.splice(index, 1);
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
  }
}

/**
 * Update effect parameter value
 */
export function updateEffectParameter(
  store: EffectStore,
  layerId: string,
  effectId: string,
  paramKey: string,
  value: any
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.effects) return;

  const effect = layer.effects.find(e => e.id === effectId);
  if (!effect || !effect.parameters[paramKey]) return;

  effect.parameters[paramKey].value = value;
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Toggle effect parameter animation state
 */
export function setEffectParamAnimated(
  store: EffectStore,
  layerId: string,
  effectId: string,
  paramKey: string,
  animated: boolean
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.effects) return;

  const effect = layer.effects.find(e => e.id === effectId);
  if (!effect || !effect.parameters[paramKey]) return;

  const param = effect.parameters[paramKey];
  param.animated = animated;

  // If enabling animation and no keyframes exist, add one at current frame
  if (animated && (!param.keyframes || param.keyframes.length === 0)) {
    param.keyframes = [{
      id: `kf_${Date.now()}`,
      frame: store.currentFrame,
      value: param.value,
      interpolation: 'linear' as InterpolationType,
      inHandle: { frame: -5, value: 0, enabled: false },
      outHandle: { frame: 5, value: 0, enabled: false },
      controlMode: 'smooth' as const,
    }];
  }

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Toggle effect enabled state
 */
export function toggleEffect(
  store: EffectStore,
  layerId: string,
  effectId: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.effects) return;

  const effect = layer.effects.find(e => e.id === effectId);
  if (!effect) return;

  effect.enabled = !effect.enabled;
  store.project.meta.modified = new Date().toISOString();
}

/**
 * Reorder effects in stack
 */
export function reorderEffects(
  store: EffectStore,
  layerId: string,
  fromIndex: number,
  toIndex: number
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.effects) return;

  if (fromIndex < 0 || fromIndex >= layer.effects.length) return;
  if (toIndex < 0 || toIndex >= layer.effects.length) return;

  const [effect] = layer.effects.splice(fromIndex, 1);
  layer.effects.splice(toIndex, 0, effect);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Duplicate effect on layer
 */
export function duplicateEffect(
  store: EffectStore,
  layerId: string,
  effectId: string
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.effects) return;

  const effect = layer.effects.find(e => e.id === effectId);
  if (!effect) return;

  // Deep clone the effect
  const duplicate: EffectInstance = structuredClone(effect);
  duplicate.id = `effect_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
  duplicate.name = `${effect.name} Copy`;

  // Insert after original
  const index = layer.effects.findIndex(e => e.id === effectId);
  layer.effects.splice(index + 1, 0, duplicate);

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();
}

/**
 * Get evaluated effect parameter value at a given frame
 */
export function getEffectParameterValue(
  store: EffectStore,
  layerId: string,
  effectId: string,
  paramKey: string,
  frame?: number
): any {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || !layer.effects) return null;

  const effect = layer.effects.find(e => e.id === effectId);
  if (!effect || !effect.parameters[paramKey]) return null;

  const param = effect.parameters[paramKey];
  const targetFrame = frame ?? (store.getActiveComp()?.currentFrame ?? 0);

  // Use interpolation if animated
  if (param.animated && param.keyframes.length > 0) {
    return interpolateProperty(param, targetFrame);
  }

  return param.value;
}
