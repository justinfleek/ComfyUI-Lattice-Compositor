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
import { useProjectStore } from "../projectStore";

// ============================================================================
// SEPARATE DIMENSIONS
// ============================================================================

/**
 * Separate position into individual X, Y, Z properties for independent keyframing.
 * After separation, positionX, positionY, positionZ can have different keyframes.
 */
export function separatePositionDimensionsAction(
  layerId: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  separatePositionDimensions(layer.transform);

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return true;
}

/**
 * Link position dimensions back into a combined property.
 * Merges X, Y, Z keyframes at each unique frame.
 */
export function linkPositionDimensionsAction(
  layerId: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  linkPositionDimensions(layer.transform, layerId);

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return true;
}

/**
 * Separate scale into individual X, Y, Z properties.
 */
export function separateScaleDimensionsAction(
  layerId: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  separateScaleDimensions(layer.transform);

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return true;
}

/**
 * Link scale dimensions back into a combined property.
 */
export function linkScaleDimensionsAction(
  layerId: string,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) return false;

  linkScaleDimensions(layer.transform, layerId);

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return true;
}

/**
 * Check if a layer has separated position dimensions.
 */
export function hasPositionSeparated(
  layerId: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
  if (!layer) return false;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const separateDimensions = (layer.transform != null && typeof layer.transform === "object" && "separateDimensions" in layer.transform && layer.transform.separateDimensions != null && typeof layer.transform.separateDimensions === "object") ? layer.transform.separateDimensions : undefined;
  const positionSeparated = (separateDimensions != null && typeof separateDimensions === "object" && "position" in separateDimensions && typeof separateDimensions.position === "boolean" && separateDimensions.position) ? true : false;
  return positionSeparated === true;
}

/**
 * Check if a layer has separated scale dimensions.
 */
export function hasScaleSeparated(
  layerId: string,
): boolean {
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);
  if (!layer) return false;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const separateDimensions = (layer.transform != null && typeof layer.transform === "object" && "separateDimensions" in layer.transform && layer.transform.separateDimensions != null && typeof layer.transform.separateDimensions === "object") ? layer.transform.separateDimensions : undefined;
  const scaleSeparated = (separateDimensions != null && typeof separateDimensions === "object" && "scale" in separateDimensions && typeof separateDimensions.scale === "boolean" && separateDimensions.scale) ? true : false;
  return scaleSeparated === true;
}
