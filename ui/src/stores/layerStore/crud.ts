/**
 * Layer CRUD Operations
 *
 * Core create, read, update, delete operations for layers.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import { toRaw } from "vue";
import type {
  AnimatableProperty,
  AnyLayerData,
  Keyframe,
  Layer,
  PropertyValue,
} from "@/types/project";
import { createAnimatableProperty, createDefaultTransform } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { clearLayerCache, markLayerDirty } from "@/services/layerEvaluationCache";
import { useSelectionStore } from "../selectionStore";
import { getDefaultLayerData } from "../actions/layer/layerDefaults";
import type { CompositorStoreAccess, DeleteLayerOptions } from "./types";
import { getLayerById } from "./hierarchy";

// ============================================================================
// LAYER CREATION
// ============================================================================

/**
 * Create a new layer of the specified type
 *
 * @param compositorStore - The compositor store instance (for project access)
 * @param type - The layer type to create
 * @param name - Optional layer name
 * @returns The created layer
 */
export function createLayer(
  compositorStore: CompositorStoreAccess,
  type: Layer["type"],
  name?: string,
): Layer {
  const id = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

  // Get type-specific data from layer defaults module
  const layerData = getDefaultLayerData(type, {
    width: compositorStore.project.composition.width,
    height: compositorStore.project.composition.height,
  });

  // Initialize audio props for video/audio layers
  let audioProps;
  if (type === "video" || type === "audio") {
    audioProps = {
      level: createAnimatableProperty("Audio Levels", 0, "number"),
    };
  }

  // Initialize layer-specific properties
  let layerProperties: AnimatableProperty<PropertyValue>[] = [];

  // Spline layer properties for timeline
  if (type === "spline") {
    const splineData = layerData as unknown as {
      strokeWidth?: number;
      strokeOpacity?: number;
    };
    layerProperties = [
      createAnimatableProperty(
        "Stroke Width",
        splineData?.strokeWidth ?? 2,
        "number",
        "Stroke",
      ),
      createAnimatableProperty(
        "Stroke Opacity",
        splineData?.strokeOpacity ?? 100,
        "number",
        "Stroke",
      ),
      createAnimatableProperty("Trim Start", 0, "number", "Trim Paths"),
      createAnimatableProperty("Trim End", 100, "number", "Trim Paths"),
      createAnimatableProperty("Trim Offset", 0, "number", "Trim Paths"),
    ];
  }

  const comp = compositorStore.getActiveComp();
  const layers = compositorStore.getActiveCompLayers();

  // Create transform with position centered in composition
  const compWidth =
    comp?.settings.width || compositorStore.project.composition.width || 1920;
  const compHeight =
    comp?.settings.height || compositorStore.project.composition.height || 1080;
  const centeredTransform = createDefaultTransform();
  centeredTransform.position.value = { x: compWidth / 2, y: compHeight / 2 };

  const layer: Layer = {
    id,
    name:
      name ||
      `${type.charAt(0).toUpperCase() + type.slice(1)} ${layers.length + 1}`,
    type,
    visible: true,
    locked: false,
    isolate: false,
    threeD: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: (comp?.settings.frameCount || 81) - 1,
    inPoint: 0,
    outPoint: (comp?.settings.frameCount || 81) - 1,
    parentId: null,
    blendMode: "normal",
    opacity: createAnimatableProperty("opacity", 100, "number"),
    transform: centeredTransform,
    audio: audioProps,
    properties: layerProperties,
    effects: [],
    data: layerData as Layer["data"],
  };

  if (type === "camera") {
    storeLogger.warn("Use createCameraLayer() for camera layers");
  }

  storeLogger.debug("[layerStore] Creating layer:", {
    id: layer.id,
    type: layer.type,
    name: layer.name,
  });

  layers.unshift(layer);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();

  return layer;
}

// ============================================================================
// LAYER DELETION
// ============================================================================

/**
 * Delete a layer by ID
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to delete
 * @param options - Optional configuration
 */
export function deleteLayer(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  options?: DeleteLayerOptions,
): void {
  const layers = compositorStore.getActiveCompLayers();
  const index = layers.findIndex((l: Layer) => l.id === layerId);
  if (index === -1) return;

  layers.splice(index, 1);

  // Clean up references to deleted layer
  for (const layer of layers) {
    if (layer.parentId === layerId) {
      layer.parentId = null;
    }
    if (layer.matteLayerId === layerId) {
      layer.matteLayerId = undefined;
      layer.matteType = undefined;
    }
    if (layer.followPath?.pathLayerId === layerId) {
      layer.followPath.enabled = false;
      layer.followPath.pathLayerId = "";
    }
    if (
      layer.type === "text" &&
      layer.data &&
      (layer.data as unknown as Record<string, unknown>).pathLayerId === layerId
    ) {
      (layer.data as unknown as Record<string, unknown>).pathLayerId = null;
    }
  }

  // Remove from selection
  if (options?.onRemoveFromSelection) {
    options.onRemoveFromSelection(layerId);
  } else {
    useSelectionStore().removeFromSelection(layerId);
  }

  clearLayerCache(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();

  if (!options?.skipHistory) {
    compositorStore.pushHistory();
  }
}

// ============================================================================
// LAYER UPDATE
// ============================================================================

/**
 * Update layer properties
 * Note: Locked layers can only have their 'locked' property changed.
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to update
 * @param updates - Partial layer updates
 */
export function updateLayer(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  updates: Partial<Layer>,
): void {
  const layer = compositorStore.getActiveCompLayers().find((l: Layer) => l.id === layerId);
  if (!layer) return;

  // If layer is locked, only allow changing the 'locked' property itself
  if (layer.locked) {
    const updateKeys = Object.keys(updates);
    const onlyChangingLocked =
      updateKeys.length === 1 && updateKeys[0] === "locked";
    if (!onlyChangingLocked) {
      storeLogger.warn("Cannot update locked layer:", layerId);
      return;
    }
  }

  Object.assign(layer, updates);
  markLayerDirty(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
}

/**
 * Update layer-specific data (e.g., text content, image path, etc.)
 * Note: Cannot update data on locked layers.
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to update
 * @param dataUpdates - Partial layer data updates
 */
export function updateLayerData(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  dataUpdates: Partial<AnyLayerData> & Record<string, unknown>,
): void {
  const layer = compositorStore.getActiveCompLayers().find((l: Layer) => l.id === layerId);
  if (!layer || !layer.data) return;

  if (layer.locked) {
    storeLogger.warn("Cannot update data on locked layer:", layerId);
    return;
  }

  layer.data = { ...toRaw(layer.data), ...dataUpdates } as Layer["data"];
  markLayerDirty(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
}

// ============================================================================
// LAYER DUPLICATION
// ============================================================================

/**
 * Regenerate all keyframe IDs in a layer to avoid conflicts
 * @internal
 */
export function regenerateKeyframeIds(layer: Layer): void {
  type TransformProp = AnimatableProperty<PropertyValue> | undefined;

  if (layer.transform) {
    const transformRecord = layer.transform as unknown as Record<
      string,
      TransformProp
    >;
    for (const key of Object.keys(layer.transform)) {
      const prop = transformRecord[key];
      if (prop?.keyframes) {
        prop.keyframes = prop.keyframes.map((kf: Keyframe<PropertyValue>) => ({
          ...kf,
          id: crypto.randomUUID(),
        }));
      }
    }
  }
  if (layer.properties) {
    for (const prop of layer.properties) {
      if (prop.keyframes) {
        prop.keyframes = prop.keyframes.map((kf: Keyframe<PropertyValue>) => ({
          ...kf,
          id: crypto.randomUUID(),
        }));
      }
    }
  }
}

/**
 * Duplicate a layer
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to duplicate
 * @returns The duplicated layer or null if not found
 */
export function duplicateLayer(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): Layer | null {
  const layers = compositorStore.getActiveCompLayers();
  const original = layers.find((l: Layer) => l.id === layerId);
  if (!original) return null;

  // Deep clone the layer - use toRaw to handle Vue reactive proxies
  const duplicate: Layer = structuredClone(toRaw(original));

  // Generate new IDs
  duplicate.id = crypto.randomUUID();
  duplicate.name = `${original.name} Copy`;

  // Generate new keyframe IDs to avoid conflicts
  regenerateKeyframeIds(duplicate);

  // Insert after the original
  const index = layers.findIndex((l: Layer) => l.id === layerId);
  layers.splice(index, 0, duplicate);

  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();

  return duplicate;
}

// ============================================================================
// LAYER REORDERING
// ============================================================================

/**
 * Reorder layers by moving a layer to a new index
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to move
 * @param newIndex - Target index position
 */
export function moveLayer(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  newIndex: number,
): void {
  if (!Number.isInteger(newIndex) || newIndex < 0) {
    storeLogger.warn("moveLayer: Invalid index:", newIndex);
    return;
  }

  const layers = compositorStore.getActiveCompLayers();
  const currentIndex = layers.findIndex((l: Layer) => l.id === layerId);
  if (currentIndex === -1) return;

  const clampedIndex = Math.min(newIndex, layers.length - 1);
  const [layer] = layers.splice(currentIndex, 1);
  layers.splice(clampedIndex, 0, layer);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
}

// ============================================================================
// LAYER RENAME
// ============================================================================

/**
 * Rename a layer by ID
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to rename
 * @param newName - The new name for the layer
 */
export function renameLayer(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  newName: string,
): void {
  const layer = getLayerById(compositorStore, layerId);
  if (!layer) return;

  // Cannot rename locked layers
  if (layer.locked) {
    storeLogger.warn("Cannot rename locked layer:", layerId);
    return;
  }

  // Validate name is not empty
  const trimmedName = newName.trim();
  if (!trimmedName) {
    storeLogger.warn("Cannot rename layer to empty name:", layerId);
    return;
  }

  layer.name = trimmedName;
  markLayerDirty(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
}

// ============================================================================
// LAYER TRANSFORM UPDATE
// ============================================================================

/**
 * Update layer transform properties (position, scale, rotation, opacity, origin/anchor)
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID
 * @param updates - Object with transform properties to update
 */
export function updateLayerTransform(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  updates: {
    position?: { x: number; y: number; z?: number };
    scale?: { x: number; y: number; z?: number };
    rotation?: number;
    opacity?: number;
    origin?: { x: number; y: number; z?: number };
    anchor?: { x: number; y: number; z?: number }; // Alias for origin
  },
): void {
  const layer = getLayerById(compositorStore, layerId);
  if (!layer?.transform) return;

  // Cannot update transform of locked layers
  if (layer.locked) {
    storeLogger.warn("Cannot update transform of locked layer:", layerId);
    return;
  }

  if (updates.position !== undefined && layer.transform.position) {
    // Validate position values are finite
    const { x, y, z } = updates.position;
    if (!Number.isFinite(x) || !Number.isFinite(y) || (z !== undefined && !Number.isFinite(z))) {
      storeLogger.warn("updateLayerTransform: Invalid position values (NaN/Infinity)", { x, y, z });
      return;
    }
    layer.transform.position.value = updates.position;
  }
  if (updates.scale !== undefined && layer.transform.scale) {
    // Validate scale values are finite
    const { x, y, z } = updates.scale;
    if (!Number.isFinite(x) || !Number.isFinite(y) || (z !== undefined && !Number.isFinite(z))) {
      storeLogger.warn("updateLayerTransform: Invalid scale values (NaN/Infinity)", { x, y, z });
      return;
    }
    layer.transform.scale.value = updates.scale;
  }
  if (updates.rotation !== undefined && layer.transform.rotation) {
    // Validate rotation is finite
    if (!Number.isFinite(updates.rotation)) {
      storeLogger.warn("updateLayerTransform: Invalid rotation value (NaN/Infinity)", updates.rotation);
      return;
    }
    layer.transform.rotation.value = updates.rotation;
  }
  if (updates.opacity !== undefined) {
    // Validate opacity is finite and in valid range
    if (!Number.isFinite(updates.opacity) || updates.opacity < 0 || updates.opacity > 100) {
      storeLogger.warn("updateLayerTransform: Invalid opacity value", updates.opacity);
      return;
    }
    // Opacity is at layer level (layer.opacity), not transform level
    if (
      layer.opacity &&
      typeof layer.opacity === "object" &&
      "value" in layer.opacity
    ) {
      layer.opacity.value = updates.opacity;
    }
  }
  // Handle origin/anchor (anchor is alias for origin)
  const originUpdate = updates.origin ?? updates.anchor;
  if (originUpdate !== undefined && layer.transform.origin) {
    // Validate origin values are finite
    const { x, y, z } = originUpdate;
    if (!Number.isFinite(x) || !Number.isFinite(y) || (z !== undefined && !Number.isFinite(z))) {
      storeLogger.warn("updateLayerTransform: Invalid origin values (NaN/Infinity)", { x, y, z });
      return;
    }
    layer.transform.origin.value = originUpdate;
  }

  markLayerDirty(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();
  compositorStore.pushHistory();
}

// ============================================================================
// LAYER TOGGLE OPERATIONS
// ============================================================================

/**
 * Toggle locked state for selected layers
 *
 * @param compositorStore - The compositor store instance
 */
export function toggleLayerLock(compositorStore: CompositorStoreAccess): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  compositorStore.pushHistory();

  for (const id of selectedIds) {
    const layer = getLayerById(compositorStore, id);
    if (layer) {
      layer.locked = !layer.locked;
      markLayerDirty(id);
    }
  }

  compositorStore.project.meta.modified = new Date().toISOString();
}

/**
 * Toggle visibility for selected layers
 *
 * @param compositorStore - The compositor store instance
 */
export function toggleLayerVisibility(
  compositorStore: CompositorStoreAccess,
): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  compositorStore.pushHistory();

  for (const id of selectedIds) {
    const layer = getLayerById(compositorStore, id);
    if (layer) {
      layer.visible = !layer.visible;
      markLayerDirty(id);
    }
  }

  compositorStore.project.meta.modified = new Date().toISOString();
}

/**
 * Toggle isolate (solo) state for selected layers
 * Isolate shows only this layer, hiding all others
 *
 * @param compositorStore - The compositor store instance
 */
export function toggleLayerSolo(compositorStore: CompositorStoreAccess): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  compositorStore.pushHistory();

  for (const id of selectedIds) {
    const layer = getLayerById(compositorStore, id);
    if (layer) {
      layer.isolate = !layer.isolate;
      markLayerDirty(id);
    }
  }

  compositorStore.project.meta.modified = new Date().toISOString();
}

// ============================================================================
// LAYER ORDERING OPERATIONS
// ============================================================================

/**
 * Move selected layers to the front (top of stack, index 0)
 *
 * @param compositorStore - The compositor store instance
 */
export function bringToFront(compositorStore: CompositorStoreAccess): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = compositorStore.getActiveCompLayers();
  if (layers.length === 0) return;

  compositorStore.pushHistory();

  // Get selected layers in reverse order (to maintain relative order when moved to front)
  const selectedLayers = selectedIds
    .map((id) => {
      const index = layers.findIndex((l: Layer) => l.id === id);
      return index !== -1 ? { layer: layers[index], index } : null;
    })
    .filter(
      (
        item,
      ): item is { layer: Layer; index: number } => item !== null,
    )
    .sort((a, b) => b.index - a.index); // Sort descending to move from bottom to top

  // Remove selected layers from their current positions
  for (const { layer } of selectedLayers) {
    const index = layers.findIndex((l: Layer) => l.id === layer.id);
    if (index !== -1) {
      layers.splice(index, 1);
    }
  }

  // Insert at front (index 0) in reverse order to maintain relative order
  for (let i = selectedLayers.length - 1; i >= 0; i--) {
    layers.splice(0, 0, selectedLayers[i].layer);
    markLayerDirty(selectedLayers[i].layer.id);
  }

  compositorStore.project.meta.modified = new Date().toISOString();
}

/**
 * Move selected layers to the back (bottom of stack, last index)
 *
 * @param compositorStore - The compositor store instance
 */
export function sendToBack(compositorStore: CompositorStoreAccess): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = compositorStore.getActiveCompLayers();
  if (layers.length === 0) return;

  compositorStore.pushHistory();

  // Get selected layers in order (to maintain relative order when moved to back)
  const selectedLayers = selectedIds
    .map((id) => {
      const index = layers.findIndex((l: Layer) => l.id === id);
      return index !== -1 ? { layer: layers[index], index } : null;
    })
    .filter(
      (
        item,
      ): item is { layer: Layer; index: number } => item !== null,
    )
    .sort((a, b) => a.index - b.index); // Sort ascending to move from top to bottom

  // Remove selected layers from their current positions
  for (const { layer } of selectedLayers) {
    const index = layers.findIndex((l: Layer) => l.id === layer.id);
    if (index !== -1) {
      layers.splice(index, 1);
    }
  }

  // Insert at back (end of array) in order to maintain relative order
  for (const { layer } of selectedLayers) {
    layers.push(layer);
    markLayerDirty(layer.id);
  }

  compositorStore.project.meta.modified = new Date().toISOString();
}

/**
 * Move selected layers forward by one position (toward index 0)
 *
 * @param compositorStore - The compositor store instance
 */
export function bringForward(compositorStore: CompositorStoreAccess): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = compositorStore.getActiveCompLayers();
  if (layers.length === 0) return;

  compositorStore.pushHistory();

  // Get selected layer IDs sorted by current index (ascending - top to bottom)
  const selectedIndices = selectedIds
    .map((id) => {
      const index = layers.findIndex((l: Layer) => l.id === id);
      return index !== -1 ? { id, index } : null;
    })
    .filter(
      (item): item is { id: string; index: number } => item !== null,
    )
    .sort((a, b) => a.index - b.index);

  // Move each layer forward (toward index 0) by one position
  // Process top-to-bottom and recalculate indices after each move to handle adjacent layers
  for (const { id } of selectedIndices) {
    const currentIndex = layers.findIndex((l: Layer) => l.id === id);
    if (currentIndex > 0) {
      // Swap with layer above
      const [movedLayer] = layers.splice(currentIndex, 1);
      layers.splice(currentIndex - 1, 0, movedLayer);
      markLayerDirty(id);
    }
  }

  compositorStore.project.meta.modified = new Date().toISOString();
}

/**
 * Move selected layers backward by one position (away from index 0)
 *
 * @param compositorStore - The compositor store instance
 */
export function sendBackward(compositorStore: CompositorStoreAccess): void {
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = compositorStore.getActiveCompLayers();
  if (layers.length === 0) return;

  compositorStore.pushHistory();

  // Get selected layer IDs sorted by current index (descending - bottom to top)
  const selectedIndices = selectedIds
    .map((id) => {
      const index = layers.findIndex((l: Layer) => l.id === id);
      return index !== -1 ? { id, index } : null;
    })
    .filter(
      (item): item is { id: string; index: number } => item !== null,
    )
    .sort((a, b) => b.index - a.index); // Sort descending to move from bottom to top

  // Move each layer backward (away from index 0) by one position
  // Process bottom-to-top and recalculate indices after each move to handle adjacent layers
  for (const { id } of selectedIndices) {
    const currentIndex = layers.findIndex((l: Layer) => l.id === id);
    if (currentIndex < layers.length - 1) {
      // Swap with layer below
      const [movedLayer] = layers.splice(currentIndex, 1);
      layers.splice(currentIndex + 1, 0, movedLayer);
      markLayerDirty(id);
    }
  }

  compositorStore.project.meta.modified = new Date().toISOString();
}
