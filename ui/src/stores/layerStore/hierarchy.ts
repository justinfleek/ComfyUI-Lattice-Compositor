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
import type { CompositorStoreAccess } from "./types";

// ============================================================================
// PARENTING
// ============================================================================

/**
 * Set a layer's parent for parenting/hierarchy
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the child layer
 * @param parentId - ID of the parent layer (or null to unparent)
 */
export function setLayerParent(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  parentId: string | null,
): void {
  const layers = compositorStore.getActiveCompLayers();
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
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
}

// ============================================================================
// 3D MODE
// ============================================================================

/**
 * Toggle a layer between 2D and 3D modes
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to toggle
 */
export function toggleLayer3D(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): void {
  const layer = compositorStore
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

  compositorStore.project.meta.modified = new Date().toISOString();
}

// ============================================================================
// SELECTION HELPERS
// ============================================================================

/**
 * Select a layer (delegates to selectionStore)
 * @param _compositorStore - Unused, kept for API consistency
 * @param layerId - The layer ID to select
 * @param addToSelection - Whether to add to existing selection
 */
export function selectLayer(
  _compositorStore: CompositorStoreAccess,
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
 * @param _compositorStore - Unused, kept for API consistency
 * @param layerId - The layer ID to deselect
 */
export function deselectLayer(
  _compositorStore: CompositorStoreAccess,
  layerId: string,
): void {
  useSelectionStore().removeFromSelection(layerId);
}

/**
 * Clear all layer selection (delegates to selectionStore)
 * @param _compositorStore - Unused, kept for API consistency
 */
export function clearSelection(_compositorStore: CompositorStoreAccess): void {
  useSelectionStore().clearLayerSelection();
}

// ============================================================================
// HIERARCHY QUERIES
// ============================================================================

/**
 * Get a layer by ID from the active composition
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to find
 * @returns The layer or null if not found
 */
export function getLayerById(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): Layer | null {
  const layers = compositorStore.getActiveCompLayers?.() ?? [];
  return layers.find((l: Layer) => l.id === layerId) ?? null;
}

/**
 * Get all children of a layer
 * @param compositorStore - The compositor store instance
 * @param layerId - The parent layer ID
 * @returns Array of child layers
 */
export function getLayerChildren(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): Layer[] {
  const layers = compositorStore.getActiveCompLayers?.() ?? [];
  return layers.filter((l: Layer) => l.parentId === layerId);
}

/**
 * Get all descendants of a layer (recursive)
 * @param compositorStore - The compositor store instance
 * @param layerId - The ancestor layer ID
 * @returns Array of all descendant layers
 */
export function getLayerDescendants(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): Layer[] {
  const descendants: Layer[] = [];
  const children = getLayerChildren(compositorStore, layerId);

  for (const child of children) {
    descendants.push(child);
    descendants.push(...getLayerDescendants(compositorStore, child.id));
  }

  return descendants;
}
