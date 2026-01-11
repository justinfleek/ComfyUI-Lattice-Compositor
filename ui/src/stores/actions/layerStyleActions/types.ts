/**
 * Layer Style Actions - Types and Helpers
 *
 * Shared types and utility functions for layer style operations.
 */

import type { LayerStyles } from "@/types/layerStyles";
import { createDefaultLayerStyles } from "@/types/layerStyles";
import type { Layer } from "@/types/project";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface LayerStyleStore {
  project: {
    meta: { modified: string };
  };
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
}

// ============================================================================
// HELPERS
// ============================================================================

/**
 * Get a layer by ID from the active composition
 */
export function getLayerById(
  store: LayerStyleStore,
  layerId: string,
): Layer | undefined {
  const layers = store.getActiveCompLayers();
  return layers.find((l) => l.id === layerId);
}

/**
 * Ensure layer has layerStyles initialized
 */
export function ensureLayerStyles(layer: Layer): LayerStyles {
  if (!layer.layerStyles) {
    layer.layerStyles = createDefaultLayerStyles();
  }
  return layer.layerStyles;
}

/**
 * Update modified timestamp
 */
export function updateModified(store: LayerStyleStore): void {
  store.project.meta.modified = new Date().toISOString();
}
