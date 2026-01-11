/**
 * Text Animator Actions - Utility Functions
 *
 * Property setters, content accessors, and helper queries.
 */

import { createAnimatableProperty } from "@/types/animation";
import type { TextAnimatorProperties } from "@/types/text";
import {
  getTextLayer,
  getTextData,
  updateModified,
  isRgbaObject,
  rgbaObjectToHex,
} from "./helpers";
import type { TextAnimatorStore } from "./types";

// ============================================================================
// PROPERTY SETTERS
// ============================================================================

/**
 * Set animator property value
 */
export function setAnimatorPropertyValue(
  store: TextAnimatorStore,
  layerId: string,
  animatorId: string,
  propertyName: keyof TextAnimatorProperties,
  value: unknown,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData || !textData.animators) return false;

  const animator = textData.animators.find((a) => a.id === animatorId);
  if (!animator) return false;

  store.pushHistory();

  const propName = String(propertyName);

  // Handle RGBA color objects - convert to hex string for storage
  let normalizedValue = value;
  let valueType: "number" | "position" | "color" | "enum" | "vector3" =
    "number";

  if (isRgbaObject(value)) {
    // Convert RGBA object to hex string
    normalizedValue = rgbaObjectToHex(value);
    valueType = "color";
  } else if (
    typeof value === "object" &&
    value !== null &&
    "x" in value &&
    "y" in value
  ) {
    // Position/scale object
    valueType = "position";
  } else if (typeof value === "number") {
    valueType = "number";
  } else if (typeof value === "string") {
    valueType = "color";
  }

  const props = animator.properties as Record<string, unknown>;
  if (!props[propName]) {
    props[propName] = createAnimatableProperty(
      propName,
      normalizedValue,
      valueType,
    );
  } else {
    (props[propName] as { value: unknown }).value = normalizedValue;
  }

  updateModified(store);
  return true;
}

// ============================================================================
// QUERIES
// ============================================================================

/**
 * Check if a layer has any text animators
 */
export function hasTextAnimators(
  store: TextAnimatorStore,
  layerId: string,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  return !!(textData?.animators && textData.animators.length > 0);
}

// ============================================================================
// TEXT CONTENT
// ============================================================================

/**
 * Get text content from a text layer
 */
export function getTextContent(
  store: TextAnimatorStore,
  layerId: string,
): string {
  const layer = getTextLayer(store, layerId);
  if (!layer) return "";

  const textData = getTextData(layer);
  return textData?.text || "";
}

/**
 * Set text content on a text layer
 */
export function setTextContent(
  store: TextAnimatorStore,
  layerId: string,
  text: string,
): boolean {
  const layer = getTextLayer(store, layerId);
  if (!layer) return false;

  const textData = getTextData(layer);
  if (!textData) return false;

  store.pushHistory();
  textData.text = text;
  updateModified(store);
  return true;
}
