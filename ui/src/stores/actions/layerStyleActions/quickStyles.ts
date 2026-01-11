/**
 * Layer Style Actions - Quick Style Helpers
 *
 * Convenience functions for adding common layer styles.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { RGBA } from "@/types/layerStyles";
import {
  createDefaultBevelEmboss,
  createDefaultColorOverlay,
  createDefaultDropShadow,
  createDefaultOuterGlow,
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
// QUICK STYLE HELPERS
// ============================================================================

/**
 * Add a drop shadow with specified parameters
 */
export function addDropShadow(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    color?: RGBA;
    angle?: number;
    distance?: number;
    spread?: number;
    size?: number;
    opacity?: number;
  },
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = true;

  const shadow = createDefaultDropShadow();

  if (options) {
    if (options.color) shadow.color.value = options.color;
    if (options.angle !== undefined) shadow.angle.value = options.angle;
    if (options.distance !== undefined)
      shadow.distance.value = options.distance;
    if (options.spread !== undefined) shadow.spread.value = options.spread;
    if (options.size !== undefined) shadow.size.value = options.size;
    if (options.opacity !== undefined) shadow.opacity.value = options.opacity;
  }

  styles.dropShadow = shadow;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("addDropShadow", { layerId, options });
}

/**
 * Add a stroke with specified parameters
 */
export function addStroke(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    color?: RGBA;
    size?: number;
    position?: "outside" | "inside" | "center";
    opacity?: number;
  },
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = true;

  const stroke = createDefaultStroke();

  if (options) {
    if (options.color) stroke.color.value = options.color;
    if (options.size !== undefined) stroke.size.value = options.size;
    if (options.position) stroke.position = options.position;
    if (options.opacity !== undefined) stroke.opacity.value = options.opacity;
  }

  styles.stroke = stroke;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("addStroke", { layerId, options });
}

/**
 * Add an outer glow with specified parameters
 */
export function addOuterGlow(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    color?: RGBA;
    spread?: number;
    size?: number;
    opacity?: number;
  },
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = true;

  const glow = createDefaultOuterGlow();

  if (options) {
    if (options.color) glow.color.value = options.color;
    if (options.spread !== undefined) glow.spread.value = options.spread;
    if (options.size !== undefined) glow.size.value = options.size;
    if (options.opacity !== undefined) glow.opacity.value = options.opacity;
  }

  styles.outerGlow = glow;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("addOuterGlow", { layerId, options });
}

/**
 * Add a color overlay with specified parameters
 */
export function addColorOverlay(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    color?: RGBA;
    opacity?: number;
    blendMode?: string;
  },
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = true;

  const overlay = createDefaultColorOverlay();

  if (options) {
    if (options.color) overlay.color.value = options.color;
    if (options.opacity !== undefined) overlay.opacity.value = options.opacity;
    if (options.blendMode)
      overlay.blendMode = options.blendMode as typeof overlay.blendMode;
  }

  styles.colorOverlay = overlay;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("addColorOverlay", { layerId, options });
}

/**
 * Add bevel and emboss with specified parameters
 */
export function addBevelEmboss(
  store: LayerStyleStore,
  layerId: string,
  options?: {
    style?:
      | "outer-bevel"
      | "inner-bevel"
      | "emboss"
      | "pillow-emboss"
      | "stroke-emboss";
    technique?: "smooth" | "chisel-hard" | "chisel-soft";
    depth?: number;
    direction?: "up" | "down";
    size?: number;
    soften?: number;
    angle?: number;
    altitude?: number;
  },
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) return;

  store.pushHistory();
  const styles = ensureLayerStyles(layer);
  styles.enabled = true;

  const bevel = createDefaultBevelEmboss();

  if (options) {
    if (options.style) bevel.style = options.style;
    if (options.technique) bevel.technique = options.technique;
    if (options.depth !== undefined) bevel.depth.value = options.depth;
    if (options.direction) bevel.direction = options.direction;
    if (options.size !== undefined) bevel.size.value = options.size;
    if (options.soften !== undefined) bevel.soften.value = options.soften;
    if (options.angle !== undefined) bevel.angle.value = options.angle;
    if (options.altitude !== undefined) bevel.altitude.value = options.altitude;
  }

  styles.bevelEmboss = bevel;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("addBevelEmboss", { layerId, options });
}
