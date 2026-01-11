/**
 * Text Animator Actions - CRUD Operations
 *
 * Add, remove, update, and get text animators.
 */

import { createTextAnimator } from "@/services/textAnimator";
import { createAnimatableProperty } from "@/types/animation";
import type { TextAnimator } from "@/types/text";
import {
  getTextLayer,
  getTextData,
  ensureAnimatorsArray,
  updateModified,
} from "./helpers";
import type { TextAnimatorStore, AddTextAnimatorConfig } from "./types";

// ============================================================================
// CREATE
// ============================================================================

/**
 * Add a text animator to a text layer
 */
export function addTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  config: AddTextAnimatorConfig = {},
): TextAnimator | undefined {
  const layer = getTextLayer(store, layerId);
  if (!layer) return undefined;

  const textData = getTextData(layer);
  if (!textData) return undefined;

  store.pushHistory();
  ensureAnimatorsArray(textData);

  // Create new animator
  const animator = createTextAnimator(config.name);

  // Apply property configuration if provided
  if (config.properties) {
    if (config.properties.position) {
      animator.properties.position = createAnimatableProperty(
        "Position",
        config.properties.position.value,
        "position",
      );
    }
    if (config.properties.scale) {
      animator.properties.scale = createAnimatableProperty(
        "Scale",
        config.properties.scale.value,
        "position",
      );
    }
    if (config.properties.rotation !== undefined) {
      animator.properties.rotation = createAnimatableProperty(
        "Rotation",
        config.properties.rotation.value,
        "number",
      );
    }
    if (config.properties.opacity !== undefined) {
      animator.properties.opacity = createAnimatableProperty(
        "Opacity",
        config.properties.opacity.value,
        "number",
      );
    }
    if (config.properties.tracking !== undefined) {
      animator.properties.tracking = createAnimatableProperty(
        "Tracking",
        config.properties.tracking.value,
        "number",
      );
    }
    if (config.properties.fillColor) {
      animator.properties.fillColor = createAnimatableProperty(
        "Fill Color",
        config.properties.fillColor.value,
        "color",
      );
    }
    if (config.properties.strokeColor) {
      animator.properties.strokeColor = createAnimatableProperty(
        "Stroke Color",
        config.properties.strokeColor.value,
        "color",
      );
    }
    if (config.properties.strokeWidth !== undefined) {
      animator.properties.strokeWidth = createAnimatableProperty(
        "Stroke Width",
        config.properties.strokeWidth.value,
        "number",
      );
    }
    if (config.properties.blur) {
      animator.properties.blur = createAnimatableProperty(
        "Blur",
        config.properties.blur.value,
        "position",
      );
    }
  }

  textData.animators?.push(animator);
  updateModified(store);

  return animator;
}

// ============================================================================
// DELETE
// ============================================================================

/**
 * Remove a text animator from a text layer
 */
export function removeTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const index = textData.animators.findIndex((a) => a.id === animatorId);
  if (index === -1) return false;

  store.pushHistory();
  textData.animators.splice(index, 1);
  updateModified(store);

  return true;
}

// ============================================================================
// UPDATE
// ============================================================================

/**
 * Update a text animator's properties
 */
export function updateTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  updates: Partial<TextAnimator>,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find((a) => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  // Apply updates
  if (updates.name !== undefined) animator.name = updates.name;
  if (updates.enabled !== undefined) animator.enabled = updates.enabled;
  if (updates.properties) {
    Object.assign(animator.properties, updates.properties);
  }
  if (updates.rangeSelector) {
    Object.assign(animator.rangeSelector, updates.rangeSelector);
  }

  updateModified(store);
  return true;
}

// ============================================================================
// READ
// ============================================================================

/**
 * Get a text animator by ID
 */
export function getTextAnimator(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
): TextAnimator | undefined {
  const layer = getTextLayer(store, layerId);
  if (!layer) return undefined;

  const textData = getTextData(layer);
  if (!textData?.animators) return undefined;

  return textData.animators.find((a) => a.id === animatorId);
}

/**
 * Get all text animators for a layer
 */
export function getTextAnimators(
  store: TextAnimatorStore,
  layerId: string,
): TextAnimator[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return [];

  return textData.animators;
}
