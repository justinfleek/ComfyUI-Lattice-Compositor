/**
 * Text Animator Actions - Computed Values
 *
 * Functions for computing character transforms and selection values.
 */

import {
  calculateCharacterInfluence,
  calculateCompleteCharacterInfluence,
  getAnimatableValue,
} from "@/services/textAnimator";
import { getTextLayer, getTextData, hexToRgbaObject } from "./helpers";
import type { TextAnimatorStore, CharacterTransform } from "./types";

// ============================================================================
// COMPUTED VALUES
// ============================================================================

/**
 * Get computed transforms for all characters at a specific frame
 *
 * This is the KEY function for testing - it returns the exact transform
 * values that would be applied to each character mesh at the given frame.
 */
export function getCharacterTransforms(
  store: TextAnimatorStore,
  layerId: string,
  frame: number,
): CharacterTransform[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer);
  if (!textData) return [];

  const text = textData.text || "";
  const totalChars = text.length;
  if (totalChars === 0) return [];

  const animators = textData.animators || [];
  const comp = store.getActiveComp();
  const fps = comp?.settings?.fps || 16;

  // Initialize transforms with base values
  const transforms: CharacterTransform[] = [];
  for (let i = 0; i < totalChars; i++) {
    transforms.push({
      index: i,
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      scale: { x: 100, y: 100 },
      opacity: 100,
      tracking: 0,
    });
  }

  // Apply each animator
  for (const animator of animators) {
    if (!animator.enabled) continue;

    const props = animator.properties;

    for (let i = 0; i < totalChars; i++) {
      // Calculate influence (0-1) for this character
      const influence = calculateCompleteCharacterInfluence(
        i,
        totalChars,
        animator,
        frame,
        fps,
      );

      // Skip if no influence
      if (influence <= 0.001) continue;

      // Apply position offset (with keyframe interpolation)
      if (props.position) {
        const posVal = getAnimatableValue(props.position, frame);
        transforms[i].position.x += posVal.x * influence;
        transforms[i].position.y += posVal.y * influence;
      }

      // Apply scale (with keyframe interpolation)
      if (props.scale) {
        const scaleVal = getAnimatableValue(props.scale, frame);
        // Scale is additive offset from 100%
        // At influence=1, full offset applied; at influence=0, no change
        transforms[i].scale.x += (scaleVal.x - 100) * influence;
        transforms[i].scale.y += (scaleVal.y - 100) * influence;
      }

      // Apply rotation (with keyframe interpolation)
      if (props.rotation) {
        const rotVal = getAnimatableValue(props.rotation, frame);
        transforms[i].rotation.z += rotVal * influence;
      }

      // Apply opacity (with keyframe interpolation)
      if (props.opacity !== undefined) {
        const opacityVal = getAnimatableValue(props.opacity, frame);
        // Opacity offset: at influence=1, opacity moves toward animator value
        // Formula: current + (target - 100) * influence
        transforms[i].opacity += (opacityVal - 100) * influence;
      }

      // Apply tracking (with keyframe interpolation)
      if (props.tracking) {
        const trackingVal = getAnimatableValue(props.tracking, frame);
        transforms[i].tracking += trackingVal * influence;
      }

      // Apply fillColor (with keyframe interpolation)
      if (props.fillColor) {
        const fillColorHex = getAnimatableValue(
          props.fillColor,
          frame,
        ) as string;
        const fillColorRgba = hexToRgbaObject(fillColorHex);

        // Initialize fillColor if not present
        if (transforms[i].fillColor === undefined) {
          transforms[i].fillColor = { r: 0, g: 0, b: 0, a: 255 };
        }

        // Apply color offset with influence (additive)
        const fillColor = transforms[i].fillColor!;
        fillColor.r += (fillColorRgba.r - 0) * influence;
        fillColor.g += (fillColorRgba.g - 0) * influence;
        fillColor.b += (fillColorRgba.b - 0) * influence;
        // Alpha is typically not additive, but we'll apply it proportionally
        fillColor.a = Math.round(255 - (255 - fillColorRgba.a) * influence);
      }

      // Apply strokeWidth (with keyframe interpolation)
      if (props.strokeWidth !== undefined) {
        const strokeWidthVal = getAnimatableValue(
          props.strokeWidth,
          frame,
        ) as number;

        // Initialize strokeWidth if not present
        const currentStrokeWidth = transforms[i].strokeWidth ?? 0;

        // Apply stroke width offset with influence (additive)
        transforms[i].strokeWidth =
          currentStrokeWidth + (strokeWidthVal - 0) * influence;
      }
    }
  }

  // Clamp final values
  for (const t of transforms) {
    t.opacity = Math.max(0, Math.min(100, t.opacity));
    t.scale.x = Math.max(0, t.scale.x);
    t.scale.y = Math.max(0, t.scale.y);
    if (t.fillColor !== undefined) {
      t.fillColor.r = Math.max(0, Math.min(255, Math.round(t.fillColor.r)));
      t.fillColor.g = Math.max(0, Math.min(255, Math.round(t.fillColor.g)));
      t.fillColor.b = Math.max(0, Math.min(255, Math.round(t.fillColor.b)));
      t.fillColor.a = Math.max(0, Math.min(255, Math.round(t.fillColor.a)));
    }
    if (t.strokeWidth !== undefined) {
      t.strokeWidth = Math.max(0, t.strokeWidth);
    }
  }

  return transforms;
}

/**
 * Get selection values (influence 0-100) for each character from a specific animator
 *
 * This exposes the raw selector calculation for testing selector math.
 */
export function getSelectionValues(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  frame: number,
): number[] {
  const layer = getTextLayer(store, layerId);
  if (!layer) return [];

  const textData = getTextData(layer);
  if (!textData) return [];

  const text = textData.text || "";
  const totalChars = text.length;
  if (totalChars === 0) return [];

  const animator = textData.animators?.find((a) => a.id === animatorId);
  if (!animator) return [];

  const comp = store.getActiveComp();
  const fps = comp?.settings?.fps || 16;

  const values: number[] = [];
  for (let i = 0; i < totalChars; i++) {
    const influence = calculateCompleteCharacterInfluence(
      i,
      totalChars,
      animator,
      frame,
      fps,
    );
    // Return as percentage (0-100)
    values.push(influence * 100);
  }

  return values;
}

/**
 * Get raw range selector value for a specific character
 * (without wiggly/expression modifiers)
 */
export function getRangeSelectionValue(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  charIndex: number,
  frame: number,
): number {
  const layer = getTextLayer(store, layerId);
  if (!layer) return 0;

  const textData = getTextData(layer);
  if (!textData) return 0;

  const text = textData.text || "";
  const totalChars = text.length;
  if (totalChars === 0 || charIndex < 0 || charIndex >= totalChars) return 0;

  const animator = textData.animators?.find((a) => a.id === animatorId);
  if (!animator) return 0;

  const influence = calculateCharacterInfluence(
    charIndex,
    totalChars,
    animator.rangeSelector,
    frame,
  );

  // Return as percentage (0-100)
  return influence * 100;
}
