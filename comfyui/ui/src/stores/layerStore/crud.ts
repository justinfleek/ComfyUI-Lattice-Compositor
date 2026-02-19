/**
 * Layer CRUD Operations
 *
 * Core create, read, update, delete operations for layers.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { toRaw } from "vue";
import type {
  AnimatableProperty,
  Keyframe,
  Layer,
  PropertyValue,
  TextData,
} from "@/types/project";
import { createAnimatableProperty, createDefaultTransform } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { clearLayerCache, markLayerDirty } from "@/services/layerEvaluationCache";
import { useSelectionStore } from "../selectionStore";
import { useProjectStore } from "../projectStore";
import { getDefaultLayerData } from "../actions/layer/layerDefaults";
import type { DeleteLayerOptions } from "./types";
import { getLayerById } from "./hierarchy";
import { generateKeyframeId, generateLayerId } from "@/utils/uuid5";
import type { EffectInstance } from "@/types/effects";
import type { TextAnimator } from "@/types/project";
import type { LayerMask } from "@/types/masks";
import type { AnimatableControlPoint, SplineData } from "@/types/spline";
import { safeFrame } from "@/stores/keyframeStore/helpers";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // layer // creation
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Create a new layer of the specified type
 *
 * @param type - The layer type to create
 * @param name - Optional layer name
 * @returns The created layer
 */
export function createLayer(
  type: Layer["type"],
  name?: string,
): Layer {
  const projectStore = useProjectStore();
  const id = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

  // Get type-specific data from layer defaults module
  const layerData = getDefaultLayerData(type, {
    width: projectStore.project.composition.width,
    height: projectStore.project.composition.height,
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
    const splineData = layerData as SplineData;
    layerProperties = [
      createAnimatableProperty(
        "Stroke Width",
        (() => {
          // Type proof: strokeWidth ∈ ℝ ∪ {undefined} → ℝ
          const strokeWidthValue = splineData.strokeWidth;
          return isFiniteNumber(strokeWidthValue) && strokeWidthValue >= 0 ? strokeWidthValue : 2;
        })(),
        "number",
        "Stroke",
      ),
      createAnimatableProperty(
        "Stroke Opacity",
        (() => {
          // Type proof: strokeOpacity ∈ ℝ ∪ {undefined} → ℝ
          const strokeOpacityValue = splineData.strokeOpacity;
          return isFiniteNumber(strokeOpacityValue) && strokeOpacityValue >= 0 && strokeOpacityValue <= 100 ? strokeOpacityValue : 100;
        })(),
        "number",
        "Stroke",
      ),
      createAnimatableProperty("Trim Start", 0, "number", "Trim Paths"),
      createAnimatableProperty("Trim End", 100, "number", "Trim Paths"),
      createAnimatableProperty("Trim Offset", 0, "number", "Trim Paths"),
    ];
  }

  const comp = projectStore.getActiveComp();
  const layers = projectStore.getActiveCompLayers();

  // Create transform with position centered in composition
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const compSettings = (comp != null && typeof comp === "object" && "settings" in comp && comp.settings != null && typeof comp.settings === "object") ? comp.settings : undefined;
  const compWidthValue = (compSettings != null && typeof compSettings === "object" && "width" in compSettings && typeof compSettings.width === "number") ? compSettings.width : undefined;
  const compWidth = compWidthValue != null ? compWidthValue : (projectStore.project.composition.width != null ? projectStore.project.composition.width : 1920);
  const compHeightValue = (compSettings != null && typeof compSettings === "object" && "height" in compSettings && typeof compSettings.height === "number") ? compSettings.height : undefined;
  const compHeight = compHeightValue != null ? compHeightValue : (projectStore.project.composition.height != null ? projectStore.project.composition.height : 1080);
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
    endFrame: ((compSettings != null && typeof compSettings === "object" && "frameCount" in compSettings && typeof compSettings.frameCount === "number") ? compSettings.frameCount : 81) - 1,
    inPoint: 0,
    outPoint: ((compSettings != null && typeof compSettings === "object" && "frameCount" in compSettings && typeof compSettings.frameCount === "number") ? compSettings.frameCount : 81) - 1,
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
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return layer;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                        // layer // deletion
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Delete a layer by ID
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to delete
 * @param options - Optional configuration
 */
export function deleteLayer(
  layerId: string,
  options?: DeleteLayerOptions,
): void {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
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
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const followPath = (layer != null && typeof layer === "object" && "followPath" in layer && layer.followPath != null && typeof layer.followPath === "object") ? layer.followPath : undefined;
    const followPathLayerId = (followPath != null && typeof followPath === "object" && "pathLayerId" in followPath && typeof followPath.pathLayerId === "string") ? followPath.pathLayerId : undefined;
    if (followPathLayerId === layerId && followPath) {
      followPath.enabled = false;
      followPath.pathLayerId = "";
    }
    if (
      layer.type === "text" &&
      layer.data &&
      (layer.data as TextData).pathLayerId === layerId
    ) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null assignments
      (layer.data as TextData).pathLayerId = "";
    }
  }

  // Remove from selection
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const onRemoveFromSelection = (options != null && typeof options === "object" && "onRemoveFromSelection" in options && typeof options.onRemoveFromSelection === "function") ? options.onRemoveFromSelection : undefined;
  if (onRemoveFromSelection != null) {
    onRemoveFromSelection(layerId);
  } else {
    useSelectionStore().removeFromSelection(layerId);
  }

  clearLayerCache(layerId);
  projectStore.project.meta.modified = new Date().toISOString();

  const skipHistory = (options != null && typeof options === "object" && "skipHistory" in options && typeof options.skipHistory === "boolean") ? options.skipHistory : undefined;
  if (!skipHistory) {
    projectStore.pushHistory();
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                          // layer // update
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Update layer properties
 * Note: Locked layers can only have their 'locked' property changed.
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to update
 * @param updates - Partial layer updates
 */
export function updateLayer(
  layerId: string,
  updates: Partial<Layer>,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l: Layer) => l.id === layerId);
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
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
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
  layerId: string,
  dataUpdates: Partial<Layer["data"] & { physics?: import("@/types/physics").PhysicsLayerData }>,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore.getActiveCompLayers().find((l: Layer) => l.id === layerId);
  if (!layer || !layer.data) return;

  if (layer.locked) {
    storeLogger.warn("Cannot update data on locked layer:", layerId);
    return;
  }

  layer.data = { ...toRaw(layer.data), ...dataUpdates } as Layer["data"];
  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                     // layer // duplication
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Regenerate all keyframe IDs in a layer to avoid conflicts
 * Uses correct property paths for deterministic ID generation
 * @internal
 */
export function regenerateKeyframeIds(layer: Layer): void {
  if (layer.transform) {
    const transformProps: Array<{ prop: AnimatableProperty<PropertyValue> | undefined; path: string }> = [
      { prop: layer.transform.position, path: "transform.position" },
      { prop: layer.transform.origin, path: "transform.origin" },
      { prop: layer.transform.anchorPoint, path: "transform.anchorPoint" },
      { prop: layer.transform.scale, path: "transform.scale" },
      { prop: layer.transform.positionX, path: "transform.positionX" },
      { prop: layer.transform.positionY, path: "transform.positionY" },
      { prop: layer.transform.positionZ, path: "transform.positionZ" },
      { prop: layer.transform.scaleX, path: "transform.scaleX" },
      { prop: layer.transform.scaleY, path: "transform.scaleY" },
      { prop: layer.transform.scaleZ, path: "transform.scaleZ" },
      { prop: layer.transform.rotation, path: "transform.rotation" },
      { prop: layer.transform.orientation, path: "transform.orientation" },
      { prop: layer.transform.rotationX, path: "transform.rotationX" },
      { prop: layer.transform.rotationY, path: "transform.rotationY" },
      { prop: layer.transform.rotationZ, path: "transform.rotationZ" },
    ];

    for (const { prop, path } of transformProps) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (prop != null && typeof prop === "object" && "keyframes" in prop && prop.keyframes != null && Array.isArray(prop.keyframes)) {
        prop.keyframes = prop.keyframes.map((kf: Keyframe<PropertyValue>) => {
          const valueStr = typeof kf.value === "object" && kf.value !== null && "x" in kf.value && "y" in kf.value
            ? `${(kf.value as { x: number; y: number }).x},${(kf.value as { x: number; y: number }).y}${"z" in kf.value ? `,${(kf.value as { x: number; y: number; z?: number }).z}` : ""}`
            : String(kf.value);
          return {
            ...kf,
            id: generateKeyframeId(layer.id, path, safeFrame(kf.frame, 0), valueStr),
          };
        });
      }
    }
  }
  if (layer.properties) {
    for (const prop of layer.properties) {
      if (prop.keyframes) {
        // Explicit check: prop.name and prop.id may be undefined, use fallback
        const propName = prop.name;
        const propId = prop.id;
        const propertyPath = (typeof propName === "string" && propName.length > 0) ? propName : ((typeof propId === "string" && propId.length > 0) ? propId : "property");
        prop.keyframes = prop.keyframes.map((kf: Keyframe<PropertyValue>) => {
          const valueStr = typeof kf.value === "object" && kf.value !== null && "x" in kf.value && "y" in kf.value
            ? `${(kf.value as { x: number; y: number }).x},${(kf.value as { x: number; y: number }).y}${"z" in kf.value ? `,${(kf.value as { x: number; y: number; z?: number }).z}` : ""}`
            : String(kf.value);
          return {
            ...kf,
            id: generateKeyframeId(layer.id, propertyPath, safeFrame(kf.frame, 0), valueStr),
          };
        });
      }
    }
  }

  // Regenerate keyframe IDs for effect parameters
  if (layer.effects && Array.isArray(layer.effects)) {
    for (const effect of layer.effects) {
      if (effect.parameters) {
        for (const [paramKey, param] of Object.entries(effect.parameters)) {
          if (param && param.keyframes && Array.isArray(param.keyframes) && param.keyframes.length > 0) {
            const propertyPath = `effects.${effect.id}.${paramKey}`;
            param.keyframes = param.keyframes.map((kf: Keyframe<PropertyValue>) => {
              const valueStr = typeof kf.value === "object" && kf.value !== null && "x" in kf.value && "y" in kf.value
                ? `${(kf.value as { x: number; y: number }).x},${(kf.value as { x: number; y: number }).y}${"z" in kf.value ? `,${(kf.value as { x: number; y: number; z?: number }).z}` : ""}`
                : String(kf.value);
              return {
                ...kf,
                id: generateKeyframeId(layer.id, propertyPath, safeFrame(kf.frame, 0), valueStr),
              };
            });
          }
        }
      }
    }
  }

  // Regenerate keyframe IDs for text animators
  if (layer.type === "text" && layer.data) {
    const textData = layer.data as TextData;
    if (textData.animators && Array.isArray(textData.animators)) {
      for (const animator of textData.animators) {
        // Range selector properties
        if (animator.rangeSelector) {
          const rangeProps: Array<{ prop: AnimatableProperty<number>; path: string }> = [
            { prop: animator.rangeSelector.start, path: `textAnimator.${animator.id}.rangeSelector.start` },
            { prop: animator.rangeSelector.end, path: `textAnimator.${animator.id}.rangeSelector.end` },
            { prop: animator.rangeSelector.offset, path: `textAnimator.${animator.id}.rangeSelector.offset` },
          ];

          for (const { prop, path } of rangeProps) {
            if (prop && prop.keyframes && Array.isArray(prop.keyframes) && prop.keyframes.length > 0) {
              prop.keyframes = prop.keyframes.map((kf: Keyframe<number>) => {
                // Explicit check: kf.value is number (never null/undefined per type system)
                const valueStr = String(kf.value);
                return {
                  ...kf,
                  id: generateKeyframeId(layer.id, path, safeFrame(kf.frame, 0), valueStr),
                };
              });
            }
          }
        }

        // Animator properties
        if (animator.properties) {
          for (const [propertyName, property] of Object.entries(animator.properties)) {
            if (property && property.keyframes && Array.isArray(property.keyframes) && property.keyframes.length > 0) {
              const propertyPath = `textAnimator.${animator.id}.${propertyName}`;
              // Text animator properties can be PropertyValue (number, Vec2, Vec3, etc.)
              property.keyframes = property.keyframes.map((kf) => {
                const valueStr = typeof kf.value === "object" && kf.value !== null && "x" in kf.value && "y" in kf.value
                  ? `${(kf.value as { x: number; y: number }).x},${(kf.value as { x: number; y: number }).y}${"z" in kf.value ? `,${(kf.value as { x: number; y: number; z?: number }).z}` : ""}`
                  : String(kf.value);
                return {
                  ...kf,
                  id: generateKeyframeId(layer.id, propertyPath, safeFrame(kf.frame, 0), valueStr),
                };
              });
            }
          }
        }
      }
    }
  }

  // Regenerate keyframe IDs for mask properties
  if (layer.masks && Array.isArray(layer.masks)) {
    for (const mask of layer.masks) {
      // Mask opacity, feather, expansion are PropertyValue (number)
      const maskProps: Array<{ prop: AnimatableProperty<number>; path: string }> = [
        { prop: mask.opacity, path: `masks.${mask.id}.opacity` },
        { prop: mask.feather, path: `masks.${mask.id}.feather` },
        { prop: mask.expansion, path: `masks.${mask.id}.expansion` },
      ];

      // Optional feather properties
      if (mask.featherX) {
        maskProps.push({ prop: mask.featherX, path: `masks.${mask.id}.featherX` });
      }
      if (mask.featherY) {
        maskProps.push({ prop: mask.featherY, path: `masks.${mask.id}.featherY` });
      }

      // Handle numeric mask properties (opacity, feather, expansion)
      for (const { prop, path } of maskProps) {
        if (prop && prop.keyframes && Array.isArray(prop.keyframes) && prop.keyframes.length > 0) {
          prop.keyframes = prop.keyframes.map((kf: Keyframe<number>) => {
            // Explicit check: kf.value is number (never null/undefined per type system)
            const valueStr = String(kf.value);
            return {
              ...kf,
              id: generateKeyframeId(layer.id, path, safeFrame(kf.frame, 0), valueStr),
            };
          });
        }
      }

      // Handle mask path separately (MaskPath type, not PropertyValue)
      if (mask.path && mask.path.keyframes && Array.isArray(mask.path.keyframes) && mask.path.keyframes.length > 0) {
        mask.path.keyframes = mask.path.keyframes.map((kf) => {
          const valueStr = typeof kf.value === "object" && kf.value !== null && "vertices" in kf.value
            ? JSON.stringify(kf.value) // Mask path is complex object, use JSON string
            : String(kf.value);
          return {
            ...kf,
            id: generateKeyframeId(layer.id, `masks.${mask.id}.path`, safeFrame(kf.frame, 0), valueStr),
          };
        });
      }
    }
  }

  // Regenerate keyframe IDs for spline control point properties
  if (layer.type === "spline" && layer.data) {
    const splineData = layer.data as SplineData;
    if (splineData.animatedControlPoints && Array.isArray(splineData.animatedControlPoints)) {
      for (const point of splineData.animatedControlPoints) {
        const pointProps: Array<{ prop: AnimatableProperty<number>; path: string }> = [
          { prop: point.x, path: `spline.${point.id}.x` },
          { prop: point.y, path: `spline.${point.id}.y` },
        ];

        // Optional depth property
        if (point.depth) {
          pointProps.push({ prop: point.depth, path: `spline.${point.id}.depth` });
        }

        // Optional handle properties
        if (point.handleIn) {
          pointProps.push(
            { prop: point.handleIn.x, path: `spline.${point.id}.handleIn.x` },
            { prop: point.handleIn.y, path: `spline.${point.id}.handleIn.y` },
          );
        }
        if (point.handleOut) {
          pointProps.push(
            { prop: point.handleOut.x, path: `spline.${point.id}.handleOut.x` },
            { prop: point.handleOut.y, path: `spline.${point.id}.handleOut.y` },
          );
        }

        for (const { prop, path } of pointProps) {
          if (prop && prop.keyframes && Array.isArray(prop.keyframes) && prop.keyframes.length > 0) {
            prop.keyframes = prop.keyframes.map((kf: Keyframe<number>) => {
              // Explicit check: kf.value is number (never null/undefined per type system)
              const valueStr = String(kf.value);
              return {
                ...kf,
                id: generateKeyframeId(layer.id, path, safeFrame(kf.frame, 0), valueStr),
              };
            });
          }
        }
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
  layerId: string,
): Layer {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const original = layers.find((l: Layer) => l.id === layerId);
  if (!original) {
    throw new Error(`[LayerStore] Cannot duplicate layer: Layer "${layerId}" not found`);
  }

  // Deep clone the layer - use toRaw to handle Vue reactive proxies
  const duplicate: Layer = structuredClone(toRaw(original));

  // Generate new IDs deterministically based on original + copy index
  const copyIndex = layers.filter((l: Layer) => l.name.startsWith(`${original.name} Copy`)).length;
  duplicate.id = generateLayerId(`${original.name} Copy`, original.parentId, copyIndex);
  duplicate.name = `${original.name} Copy`;

  // Generate new keyframe IDs to avoid conflicts
  regenerateKeyframeIds(duplicate);

  // Insert after the original
  const index = layers.findIndex((l: Layer) => l.id === layerId);
  layers.splice(index, 0, duplicate);

  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();

  return duplicate;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // layer // reordering
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Reorder layers by moving a layer to a new index
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the layer to move
 * @param newIndex - Target index position
 */
export function moveLayer(
  layerId: string,
  newIndex: number,
): void {
  const projectStore = useProjectStore();
  if (!Number.isInteger(newIndex) || newIndex < 0) {
    storeLogger.warn("moveLayer: Invalid index:", newIndex);
    return;
  }

  const layers = projectStore.getActiveCompLayers();
  const currentIndex = layers.findIndex((l: Layer) => l.id === layerId);
  if (currentIndex === -1) return;

  const clampedIndex = Math.min(newIndex, layers.length - 1);
  const [layer] = layers.splice(currentIndex, 1);
  layers.splice(clampedIndex, 0, layer);
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                          // layer // rename
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Rename a layer by ID
 *
 * @param layerId - The layer ID to rename
 * @param newName - The new name for the layer
 */
export function renameLayer(
  layerId: string,
  newName: string,
): void {
  const projectStore = useProjectStore();
  const layer = getLayerById(layerId);
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
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                             // layer // transform // update
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Update layer transform properties (position, scale, rotation, opacity, origin/anchor)
 *
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID
 * @param updates - Object with transform properties to update
 */
export function updateLayerTransform(
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
  const projectStore = useProjectStore();
  const layer = getLayerById(layerId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (layer == null || typeof layer !== "object" || !("transform" in layer) || layer.transform == null) return;

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
  // Type proof: originUpdate ∈ {x, y, z?} | undefined
  const originUpdate = updates.origin !== undefined ? updates.origin : updates.anchor;
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
  projectStore.project.meta.modified = new Date().toISOString();
  projectStore.pushHistory();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                            // layer // toggle // operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Toggle locked state for selected layers
 *
 * @param compositorStore - The compositor store instance
 */
export function toggleLayerLock(): void {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  projectStore.pushHistory();

  for (const id of selectedIds) {
    const layer = getLayerById(id);
    if (layer) {
      layer.locked = !layer.locked;
      markLayerDirty(id);
    }
  }

  projectStore.project.meta.modified = new Date().toISOString();
}

/**
 * Toggle visibility for selected layers
 *
 * @param compositorStore - The compositor store instance
 */
export function toggleLayerVisibility(): void {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  projectStore.pushHistory();

  for (const id of selectedIds) {
    const layer = getLayerById(id);
    if (layer) {
      layer.visible = !layer.visible;
      markLayerDirty(id);
    }
  }

  projectStore.project.meta.modified = new Date().toISOString();
}

/**
 * Toggle isolate (solo) state for selected layers
 * Isolate shows only this layer, hiding all others
 *
 * @param compositorStore - The compositor store instance
 */
export function toggleLayerSolo(): void {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  projectStore.pushHistory();

  for (const id of selectedIds) {
    const layer = getLayerById(id);
    if (layer) {
      layer.isolate = !layer.isolate;
      markLayerDirty(id);
    }
  }

  projectStore.project.meta.modified = new Date().toISOString();
}

// ═══════════════════════════════════════════════════════════════════════════
//                                          // layer // ordering // operations
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Move selected layers to the front (top of stack, index 0)
 *
 * @param compositorStore - The compositor store instance
 */
export function bringToFront(): void {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = projectStore.getActiveCompLayers();
  if (layers.length === 0) return;

  projectStore.pushHistory();

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

  projectStore.project.meta.modified = new Date().toISOString();
}

/**
 * Move selected layers to the back (bottom of stack, last index)
 *
 * @param compositorStore - The compositor store instance
 */
export function sendToBack(): void {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = projectStore.getActiveCompLayers();
  if (layers.length === 0) return;

  projectStore.pushHistory();

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

  projectStore.project.meta.modified = new Date().toISOString();
}

/**
 * Move selected layers forward by one position (toward index 0)
 *
 * @param compositorStore - The compositor store instance
 */
export function bringForward(): void {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = projectStore.getActiveCompLayers();
  if (layers.length === 0) return;

  projectStore.pushHistory();

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

  projectStore.project.meta.modified = new Date().toISOString();
}

/**
 * Move selected layers backward by one position (away from index 0)
 *
 * @param compositorStore - The compositor store instance
 */
export function sendBackward(): void {
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const layers = projectStore.getActiveCompLayers();
  if (layers.length === 0) return;

  projectStore.pushHistory();

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

  projectStore.project.meta.modified = new Date().toISOString();
}
