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

