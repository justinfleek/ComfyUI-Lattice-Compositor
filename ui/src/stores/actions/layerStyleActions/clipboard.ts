/**
 * Layer Style Actions - Clipboard Operations
 *
 * Copy, paste, and clear layer styles.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { LayerStyles } from "@/types/layerStyles";
import { storeLogger } from "@/utils/logger";
import {
  type LayerStyleStore,
  getLayerById,
  updateModified,
} from "./types";

// ============================================================================
// COPY/PASTE LAYER STYLES
// ============================================================================

/**
 * Copy layer styles from a layer
 * Returns the copied styles (caller is responsible for storing in clipboard)
 */
export function copyLayerStyles(
  store: LayerStyleStore,
  layerId: string,
): LayerStyles | null {
  const layer = getLayerById(store, layerId);
  if (!layer || !layer.layerStyles) {
    storeLogger.warn("copyLayerStyles: Layer or styles not found", { layerId });
    return null;
  }

  // Deep clone the styles
  const copied = JSON.parse(JSON.stringify(layer.layerStyles));

  storeLogger.debug("copyLayerStyles", { layerId });
  return copied;
}

/**
 * Paste layer styles to a layer
 * Styles must be provided (from effectStore clipboard)
 */
export function pasteLayerStyles(
  store: LayerStyleStore,
  layerId: string,
  styles?: LayerStyles,
): void {
  if (!styles) {
    storeLogger.warn("pasteLayerStyles: No styles provided");
    return;
  }

  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("pasteLayerStyles: Layer not found", { layerId });
    return;
  }

  store.pushHistory();

  // Deep clone to avoid reference issues
  layer.layerStyles = JSON.parse(JSON.stringify(styles));

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("pasteLayerStyles", { layerId });
}

/**
 * Paste layer styles to multiple layers
 * Styles must be provided (from effectStore clipboard)
 */
export function pasteLayerStylesToMultiple(
  store: LayerStyleStore,
  layerIds: string[],
  styles?: LayerStyles,
): void {
  if (!styles) {
    storeLogger.warn("pasteLayerStylesToMultiple: No styles provided");
    return;
  }

  store.pushHistory();

  for (const layerId of layerIds) {
    const layer = getLayerById(store, layerId);
    if (layer) {
      layer.layerStyles = JSON.parse(JSON.stringify(styles));
      markLayerDirty(layerId);
    }
  }

  updateModified(store);
  storeLogger.debug("pasteLayerStylesToMultiple", { layerIds });
}

/**
 * Clear layer styles from a layer
 */
export function clearLayerStyles(
  store: LayerStyleStore,
  layerId: string,
): void {
  const layer = getLayerById(store, layerId);
  if (!layer) {
    storeLogger.warn("clearLayerStyles: Layer not found", { layerId });
    return;
  }

  store.pushHistory();
  layer.layerStyles = undefined;

  markLayerDirty(layerId);
  updateModified(store);

  storeLogger.debug("clearLayerStyles", { layerId });
}
