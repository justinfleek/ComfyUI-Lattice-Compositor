/**
 * Layer Clipboard Operations
 *
 * Copy, paste, and cut operations for layers.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import { toRaw } from "vue";
import type { ClipboardKeyframe, Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useSelectionStore } from "../selectionStore";
import { useProjectStore } from "../projectStore";
import { generateLayerId } from "@/utils/uuid5";
import { deleteLayer, regenerateKeyframeIds } from "./crud";
import type { LayerState } from "./types";

// ============================================================================
// CLIPBOARD STATE HELPERS
// ============================================================================

/**
 * Set clipboard contents
 */
export function setClipboard(
  state: LayerState,
  layers: Layer[],
  keyframes: ClipboardKeyframe[] = [],
): void {
  state.clipboard = {
    layers: JSON.parse(JSON.stringify(layers)),
    keyframes: JSON.parse(JSON.stringify(keyframes)),
  };
  storeLogger.debug(
    `Clipboard set: ${layers.length} layers, ${keyframes.length} keyframes`,
  );
}

/**
 * Clear clipboard contents
 */
export function clearClipboard(state: LayerState): void {
  state.clipboard = { layers: [], keyframes: [] };
}

/**
 * Get clipboard layers (deep copy to prevent mutation)
 */
export function getClipboardLayers(state: LayerState): Layer[] {
  return JSON.parse(JSON.stringify(state.clipboard.layers));
}

// ============================================================================
// LAYER CLIPBOARD OPERATIONS
// ============================================================================

/**
 * Copy selected layers to clipboard
 *
 * @param state - The layer store state
 * @param compositorStore - The compositor store instance
 */
export function copySelectedLayers(
  state: LayerState,
): void {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const selection = useSelectionStore();
  const selectedLayers = layers.filter((l: Layer) =>
    selection.selectedLayerIds.includes(l.id),
  );
  if (selectedLayers.length === 0) return;

  // Deep clone to clipboard
  state.clipboard.layers = selectedLayers.map((layer: Layer) =>
    structuredClone(toRaw(layer)),
  );
  storeLogger.debug(
    `Copied ${state.clipboard.layers.length} layer(s) to clipboard`,
  );
}

/**
 * Paste layers from clipboard
 *
 * @param state - The layer store state
 * @returns Array of pasted layers
 */
export function pasteLayers(
  state: LayerState,
): Layer[] {
  const projectStore = useProjectStore();
  if (state.clipboard.layers.length === 0) return [];

  const layers = projectStore.getActiveCompLayers();
  const pastedLayers: Layer[] = [];

  for (const clipboardLayer of state.clipboard.layers) {
    const newLayer: Layer = structuredClone(clipboardLayer);
    const copyIndex = layers.filter((l: Layer) => l.name.startsWith(`${clipboardLayer.name} Copy`)).length;
    newLayer.id = generateLayerId(`${clipboardLayer.name} Copy`, null, copyIndex);
    newLayer.name = `${clipboardLayer.name} Copy`;
    regenerateKeyframeIds(newLayer);
    newLayer.parentId = null;
    layers.unshift(newLayer);
    pastedLayers.push(newLayer);
  }

  useSelectionStore().selectLayers(pastedLayers.map((l) => l.id));
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  storeLogger.debug(`Pasted ${pastedLayers.length} layer(s)`);
  return pastedLayers;
}

/**
 * Cut selected layers (copy + delete)
 *
 * @param state - The layer store state
 */
export function cutSelectedLayers(
  state: LayerState,
): void {
  copySelectedLayers(state);
  const layerIds = [...useSelectionStore().selectedLayerIds];
  for (const id of layerIds) {
    deleteLayer(id);
  }
}
