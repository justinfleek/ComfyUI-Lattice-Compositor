/**
 * Layer Hierarchy Operations
 *
 * Parenting, 3D toggle, and hierarchy query operations.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import type { Layer } from "@/types/project";
import { createAnimatableProperty } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useSelectionStore } from "../selectionStore";
import { useProjectStore } from "../projectStore";
import { deleteLayer, duplicateLayer } from "./crud";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                 // parenting
// ════════════════════════════════════════════════════════════════════════════

/**
 * Set a layer's parent for parenting/hierarchy
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the child layer
 * @param parentId - ID of the parent layer (or null to unparent)
 */
export function setLayerParent(
  layerId: string,
  parentId: string | null,
): void {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const layer = layers.find((l: Layer) => l.id === layerId);
  if (!layer) return;

  // Prevent self-parenting
  if (parentId === layerId) return;

  // Prevent circular parenting
  if (parentId) {
    const getDescendants = (id: string): Set<string> => {
      const descendants = new Set<string>();
      const children = layers.filter((l: Layer) => l.parentId === id);
      for (const child of children) {
        descendants.add(child.id);
        const childDescendants = getDescendants(child.id);
        childDescendants.forEach((d: string) => descendants.add(d));
      }
      return descendants;
    };

    const descendants = getDescendants(layerId);
    if (descendants.has(parentId)) {
      storeLogger.warn("Cannot set parent: would create circular reference");
      return;
    }
  }

  layer.parentId = parentId;
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

// ════════════════════════════════════════════════════════════════════════════
// 3D MODE
// ════════════════════════════════════════════════════════════════════════════

/**
 * Toggle a layer between 2D and 3D modes
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to toggle
 */
export function toggleLayer3D(
  layerId: string,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) return;

  layer.threeD = !layer.threeD;

  if (layer.threeD) {
    const t = layer.transform;

    // Force reactivity by replacing the entire value objects
    // Position - always create new object with z
    const pos = t.position.value as { x: number; y: number; z?: number };
    const posZ = "z" in pos && typeof pos.z === "number" ? pos.z : 0;
    t.position.value = { x: pos.x, y: pos.y, z: posZ };
    t.position.type = "vector3";

    // Origin (formerly Anchor Point)
    const originProp = t.origin || t.anchorPoint;
    if (originProp) {
      const orig = originProp.value as { x: number; y: number; z?: number };
      const origZ = "z" in orig && typeof orig.z === "number" ? orig.z : 0;
      originProp.value = { x: orig.x, y: orig.y, z: origZ };
      originProp.type = "vector3";
    }

    // Scale
    const scl = t.scale.value as { x: number; y: number; z?: number };
    const sclZ = "z" in scl && typeof scl.z === "number" ? scl.z : 100;
    t.scale.value = { x: scl.x, y: scl.y, z: sclZ };
    t.scale.type = "vector3";

    // Initialize 3D rotations
    if (!t.orientation) {
      t.orientation = createAnimatableProperty(
        "orientation",
        { x: 0, y: 0, z: 0 },
        "vector3",
      );
    }
    if (!t.rotationX) {
      t.rotationX = createAnimatableProperty("rotationX", 0, "number");
    }
    if (!t.rotationY) {
      t.rotationY = createAnimatableProperty("rotationY", 0, "number");
    }
    if (!t.rotationZ) {
      t.rotationZ = createAnimatableProperty("rotationZ", 0, "number");
      // Copy existing 2D rotation to Z rotation
      t.rotationZ.value = t.rotation.value;
    }
  } else {
    // Reverting to 2D
    // Map Z rotation back to standard rotation
    if (layer.transform.rotationZ) {
      layer.transform.rotation.value = layer.transform.rotationZ.value;
    }
  }

  projectStore.project.meta.modified = new Date().toISOString();
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // selection // helpers
// ════════════════════════════════════════════════════════════════════════════

/**
 * Select a layer (delegates to selectionStore)
 * @param _compositorStore - Unused, kept for API consistency
 * @param layerId - The layer ID to select
 * @param addToSelection - Whether to add to existing selection
 */
export function selectLayer(
  layerId: string,
  addToSelection = false,
): void {
  const selection = useSelectionStore();
  if (addToSelection) {
    selection.addToSelection(layerId);
  } else {
    selection.selectLayer(layerId);
  }
}

/**
 * Deselect a layer (delegates to selectionStore)
 * @param layerId - The layer ID to deselect
 */
export function deselectLayer(
  layerId: string,
): void {
  useSelectionStore().removeFromSelection(layerId);
}

/**
 * Clear all layer selection (delegates to selectionStore)
 */
export function clearSelection(): void {
  useSelectionStore().clearLayerSelection();
}

/**
 * Select all layers in the active composition
 */
export function selectAllLayers(): void {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const selection = useSelectionStore();
  selection.selectLayers(layers.map((l: Layer) => l.id));
}

/**
 * Delete all selected layers
 */
export function deleteSelectedLayers(): void {
  const projectStore = useProjectStore();
  const selection = useSelectionStore();
  const layerIds = [...selection.selectedLayerIds];
  
  layerIds.forEach((id: string) => {
    deleteLayer(id);
  });
  
  selection.clearLayerSelection();
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

/**
 * Duplicate all selected layers
 * @returns Array of new layer IDs
 */
export function duplicateSelectedLayers(): string[] {
  const projectStore = useProjectStore();
  const selection = useSelectionStore();
  const newLayerIds: string[] = [];
  
  selection.selectedLayerIds.forEach((id: string) => {
    const newLayer = duplicateLayer(id);
    if (newLayer) {
      newLayerIds.push(newLayer.id);
    }
  });
  
  // Select the duplicated layers
  if (newLayerIds.length > 0) {
    selection.selectLayers(newLayerIds);
  }
  
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
  
  return newLayerIds;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                      // hierarchy // queries
// ════════════════════════════════════════════════════════════════════════════

/**
 * Get a layer by ID from the active composition
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to find
 * @returns The layer or null if not found
 */
export function getLayerById(
  layerId: string,
): Layer | null {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  // Type proof: find(...) ∈ Layer | undefined → Layer | null
  const foundLayer = layers.find((l: Layer) => l.id === layerId);
  return foundLayer !== undefined ? foundLayer : null;
}

/**
 * Get all children of a layer
 * @param compositorStore - The compositor store instance
 * @param layerId - The parent layer ID
 * @returns Array of child layers
 */
export function getLayerChildren(
  layerId: string,
): Layer[] {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  return layers.filter((l: Layer) => l.parentId === layerId);
}

/**
 * Get all descendants of a layer (recursive)
 * @param layerId - The ancestor layer ID
 * @returns Array of all descendant layers
 */
export function getLayerDescendants(
  layerId: string,
): Layer[] {
  const descendants: Layer[] = [];
  const children = getLayerChildren(layerId);

  for (const child of children) {
    descendants.push(child);
    descendants.push(...getLayerDescendants(child.id));
  }

  return descendants;
}

/**
 * Get all visible layers from active composition
 * @returns Array of visible layers
 */
export function getVisibleLayers(): Layer[] {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  return layers.filter((l: Layer) => l.visible);
}

/**
 * Get layers displayed in timeline (respects minimized filter)
 * @param hideMinimized - Whether to hide minimized layers (default: false)
 * @returns Array of displayed layers
 */
export function getDisplayedLayers(
  hideMinimized = false,
): Layer[] {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  if (hideMinimized) {
    return layers.filter((l: Layer) => !l.minimized);
  }
  return layers;
}

/**
 * Get root layers (layers with no parent)
 * @returns Array of root layers
 */
export function getRootLayers(): Layer[] {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  return layers.filter((l: Layer) => !l.parentId);
}

/**
 * Get all camera layers in the active composition
 * @returns Array of camera layers
 */
export function getCameraLayers(): Layer[] {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  return layers.filter((l: Layer) => l.type === "camera");
}

/**
 * Get all selected layers in the active composition
 * @returns Array of selected layers
 */
export function getSelectedLayers(): Layer[] {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const selectionStore = useSelectionStore();
  return layers.filter((l: Layer) =>
    selectionStore.selectedLayerIds.includes(l.id),
  );
}

/**
 * Get the single selected layer (returns null if 0 or 2+ layers selected)
 * @returns The selected layer or null
 */
export function getSelectedLayer(): Layer {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  if (selectionStore.selectedLayerIds.length !== 1) {
    throw new Error(`[LayerStore] Cannot get selected layer: Expected exactly 1 selected layer, found ${selectionStore.selectedLayerIds.length}`);
  }
  const layers = projectStore.getActiveCompLayers();
  const selectedId = selectionStore.selectedLayerIds[0];
  const layer = layers.find((l: Layer) => l.id === selectedId);
  if (layer === null || layer === undefined) {
    throw new Error(`[LayerStore] Cannot get selected layer: Layer with ID "${selectedId}" not found in active composition`);
  }
  return layer;
}
