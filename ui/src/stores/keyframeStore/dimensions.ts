/**
 * Separate Dimensions Operations
 *
 * Separate and link position/scale dimensions for independent keyframing.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import {
  linkPositionDimensions,
  linkScaleDimensions,
  separatePositionDimensions,
  separateScaleDimensions,
} from "@/types/transform";
import { useLayerStore } from "@/stores/layerStore";
import type { KeyframeStoreAccess } from "./types";

// ============================================================================
// SEPARATE DIMENSIONS
// ============================================================================

/**
 * Separate position into individual X, Y, Z properties for independent keyframing.
 * After separation, positionX, positionY, positionZ can have different keyframes.
 */
export function separatePositionDimensionsAction(
  store: KeyframeStoreAccess,
  layerId: string,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  separatePositionDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Link position dimensions back into a combined property.
 * Merges X, Y, Z keyframes at each unique frame.
 */
export function linkPositionDimensionsAction(
  store: KeyframeStoreAccess,
  layerId: string,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  linkPositionDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Separate scale into individual X, Y, Z properties.
 */
export function separateScaleDimensionsAction(
  store: KeyframeStoreAccess,
  layerId: string,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  separateScaleDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Link scale dimensions back into a combined property.
 */
export function linkScaleDimensionsAction(
  store: KeyframeStoreAccess,
  layerId: string,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  linkScaleDimensions(layer.transform);

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return true;
}

/**
 * Check if a layer has separated position dimensions.
 */
export function hasPositionSeparated(
  store: KeyframeStoreAccess,
  layerId: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(store, layerId);
  if (!layer) return false;
  return layer.transform.separateDimensions?.position === true;
}

/**
 * Check if a layer has separated scale dimensions.
 */
export function hasScaleSeparated(
  store: KeyframeStoreAccess,
  layerId: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(store, layerId);
  if (!layer) return false;
  return layer.transform.separateDimensions?.scale === true;
}
