/**
 * Layer Style Actions - Core Operations
 *
 * Enable/disable styles and update style properties.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { LayerStyles } from "@/types/layerStyles";
import {
  createDefaultBevelEmboss,
  createDefaultBlendingOptions,
  createDefaultColorOverlay,
  createDefaultDropShadow,
  createDefaultGradientOverlay,
  createDefaultInnerGlow,
  createDefaultInnerShadow,
  createDefaultOuterGlow,
  createDefaultSatin,
  createDefaultStroke,
} from "@/types/layerStyles";
import { storeLogger } from "@/utils/logger";
import {
  type LayerStyleStore,
  getLayerById,
  ensureLayerStyles,
  updateModified,
} from "./types";

// ============================================================================
// ENABLE/DISABLE
// ============================================================================

/**
 * Enable or disable all layer styles for a layer
 */
export function setLayerStylesEnabled(
  store: LayerStyleStore,
  layerId: string,
  enabled: boolean,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("setLayerStylesEnabled: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = enabled;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("setLayerStylesEnabled", { layerId, enabled });
}

/**
 * Enable or disable a specific style type
 */
export function setStyleEnabled(
  store: LayerStyleStore,
  layerId: string,
  styleType: keyof LayerStyles,
  enabled: boolean,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("setStyleEnabled: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  const styles = ensureLayerStyles(layer);

  // Create default style if enabling and doesn't exist
  if (enabled && !styles[styleType]) {
    switch (styleType) {
      case "dropShadow":
        styles.dropShadow = createDefaultDropShadow();
        break;
      case "innerShadow":
        styles.innerShadow = createDefaultInnerShadow();
        break;
      case "outerGlow":
        styles.outerGlow = createDefaultOuterGlow();
        break;
      case "innerGlow":
        styles.innerGlow = createDefaultInnerGlow();
        break;
      case "bevelEmboss":
        styles.bevelEmboss = createDefaultBevelEmboss();
        break;
      case "satin":
        styles.satin = createDefaultSatin();
        break;
      case "colorOverlay":
        styles.colorOverlay = createDefaultColorOverlay();
        break;
      case "gradientOverlay":
        styles.gradientOverlay = createDefaultGradientOverlay();
        break;
      case "stroke":
        styles.stroke = createDefaultStroke();
        break;
      case "blendingOptions":
        styles.blendingOptions = createDefaultBlendingOptions();
        break;
    }
  }

  // Set enabled state
  const style = styles[styleType];
  if (style && typeof style === "object" && "enabled" in style) {
    (style as { enabled: boolean }).enabled = enabled;
  }

  // Also enable master styles if enabling a child
  if (enabled && !styles.enabled) {
    styles.enabled = true;
  }

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("setStyleEnabled", { layerId, styleType, enabled });
}

// ============================================================================
// UPDATE PROPERTIES
// ============================================================================

/**
 * Update a property on a specific style
 */
export function updateStyleProperty<
  T extends keyof LayerStyles,
  K extends keyof NonNullable<LayerStyles[T]>,
>(
  store: LayerStyleStore,
  layerId: string,
  styleType: T,
  property: K,
  value: unknown,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("updateStyleProperty: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  const style = styles[styleType] as Record<string, unknown> | undefined;

  if (!style) {
    storeLogger.warn("updateStyleProperty: Style not found", {
      layerId,
      styleType,
    });
    return;
  }

  // Handle animatable properties
  const prop = style[property as string];
  if (
    prop &&
    typeof prop === "object" &&
    prop !== null &&
    "value" in prop
  ) {
    (prop as { value: unknown }).value = value;
  } else {
    style[property as string] = value;
  }

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("updateStyleProperty", {
    layerId,
    styleType,
    property,
    value,
  });
}

/**
 * Set entire style configuration
 */
export function setStyle<T extends keyof LayerStyles>(
  store: LayerStyleStore,
  layerId: string,
  styleType: T,
  styleConfig: LayerStyles[T],
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("setStyle: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  Object.assign(styles, { [styleType]: styleConfig });

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("setStyle", { layerId, styleType });
}

/**
 * Set all layer styles at once
 */
export function setLayerStyles(
  store: LayerStyleStore,
  layerId: string,
  layerStyles: LayerStyles,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("setLayerStyles: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  layer.layerStyles = layerStyles;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("setLayerStyles", { layerId });
}
