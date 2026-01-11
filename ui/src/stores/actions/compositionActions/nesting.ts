/**
 * Composition Actions - Nesting
 *
 * Nest selected layers into a new composition.
 */

import type { Composition, Layer, NestedCompData } from "@/types/project";
import {
  createAnimatableProperty,
  createDefaultTransform,
} from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useSelectionStore } from "../../selectionStore";
import { createComposition } from "./crud";
import type { CompositionStore } from "./types";

// ============================================================================
// NESTING
// ============================================================================

/**
 * Nest selected layers into a new composition
 */
export function nestSelectedLayers(
  store: CompositionStore,
  name?: string,
): Composition | null {
  if (store.selectedLayerIds.length === 0) {
    storeLogger.warn("No layers selected for nesting");
    return null;
  }

  const activeComp = store.project.compositions[store.activeCompositionId];
  if (!activeComp) return null;

  // Create new composition with same settings
  const nestedComp = createComposition(
    store,
    name || "Nested Comp",
    activeComp.settings,
    true,
  );

  // Move selected layers to nested comp
  const selectedLayers = activeComp.layers.filter((l) =>
    store.selectedLayerIds.includes(l.id),
  );

  // Guard against empty array (selected IDs may not exist in current comp)
  if (selectedLayers.length === 0) {
    storeLogger.warn("Selected layers not found in active composition");
    return null;
  }

  // Find earliest startFrame to normalize timing
  const earliestIn = Math.min(
    ...selectedLayers.map((l) => l.startFrame ?? l.inPoint ?? 0),
  );

  // Move layers to nested comp and adjust timing
  for (const layer of selectedLayers) {
    // Adjust timing relative to nested comp start (update both new and legacy properties)
    const layerStart = layer.startFrame ?? layer.inPoint ?? 0;
    const layerEnd = layer.endFrame ?? layer.outPoint ?? 80;
    layer.startFrame = layerStart - earliestIn;
    layer.endFrame = layerEnd - earliestIn;
    layer.inPoint = layer.startFrame;
    layer.outPoint = layer.endFrame;

    // Remove from parent
    const idx = activeComp.layers.indexOf(layer);
    if (idx >= 0) {
      activeComp.layers.splice(idx, 1);
    }

    // Add to nested comp
    nestedComp.layers.push(layer);
  }

  // Update nested comp duration to fit layers
  const maxOut = Math.max(
    ...nestedComp.layers.map((l) => l.endFrame ?? l.outPoint ?? 80),
  );
  nestedComp.settings.frameCount = maxOut + 1;
  nestedComp.settings.duration =
    nestedComp.settings.frameCount / nestedComp.settings.fps;

  // Create nested comp layer in parent composition
  const nestedEndFrame = earliestIn + nestedComp.settings.frameCount - 1;
  const nestedCompLayer: Layer = {
    id: `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    name: nestedComp.name,
    type: "nestedComp",
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    // Timing (primary properties)
    startFrame: earliestIn,
    endFrame: nestedEndFrame,
    // Backwards compatibility aliases
    inPoint: earliestIn,
    outPoint: nestedEndFrame,
    parentId: null,
    transform: createDefaultTransform(),
    opacity: createAnimatableProperty("opacity", 100, "number"),
    properties: [],
    effects: [],
    blendMode: "normal",
    motionBlur: false,
    data: {
      compositionId: nestedComp.id,
      // Speed map (new naming)
      speedMapEnabled: false,
      // Backwards compatibility
      timeRemapEnabled: false,
      flattenTransform: false,
    } as NestedCompData,
  };

  activeComp.layers.push(nestedCompLayer);

  // Clear selection
  useSelectionStore().clearLayerSelection();

  // Switch back to parent composition
  store.activeCompositionId = activeComp.id;

  storeLogger.debug("Nested layers into:", nestedComp.name);
  return nestedComp;
}
