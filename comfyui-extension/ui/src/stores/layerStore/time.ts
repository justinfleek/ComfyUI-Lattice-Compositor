/**
 * Layer Time Operations
 *
 * Time stretch, reverse, freeze frame, split, and speed map operations.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import type { AnimatableProperty, Layer, NestedCompData } from "@/types/project";
import { createAnimatableProperty, isLayerOfType } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { TimeStretchOptions } from "./types";
import { useProjectStore } from "../projectStore";
import { useAnimationStore } from "../animationStore";
import { generateKeyframeId } from "@/utils/uuid5";

// ============================================================================
// INTERNAL TYPES
// ============================================================================

type SpeedMappableData = {
  speedMapEnabled: boolean;
  speedMap?: AnimatableProperty<number>;
  timeRemapEnabled?: boolean;
  timeRemap?: AnimatableProperty<number>;
};

// ============================================================================
// TIME STRETCH
// ============================================================================

/**
 * Apply time stretch to a video or nested comp layer
 * @param layerId - The layer ID to stretch
 * @param options - Time stretch options
 */
export function timeStretchLayer(
  layerId: string,
  options: TimeStretchOptions,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for time stretch:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("Time stretch only works on video/nestedComp layers");
    return;
  }

  projectStore.pushHistory();

  layer.startFrame = options.newStartFrame;
  layer.endFrame = options.newEndFrame;

  if (isLayerOfType(layer, "video") && layer.data) {
    layer.data.speed = options.speed;
  } else if (layer.type === "nestedComp" && layer.data) {
    const nestedData = layer.data as NestedCompData;
    if (nestedData.timewarpEnabled && nestedData.timewarpSpeed) {
      nestedData.timewarpSpeed.value = options.speed * 100;
    }
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(
    `Time stretched layer ${layer.name}: ${options.stretchFactor}% ` +
      `(speed: ${options.speed.toFixed(2)}, hold: ${options.holdInPlace})`,
  );
}

// ============================================================================
// REVERSE
// ============================================================================

/**
 * Reverse layer playback
 * @param layerId - The layer ID to reverse
 */
export function reverseLayer(
  layerId: string,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for reverse:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("Reverse only works on video/nestedComp layers");
    return;
  }

  projectStore.pushHistory();

  if (isLayerOfType(layer, "video") && layer.data) {
    // Type proof: speed ∈ ℝ ∪ {undefined} → ℝ
    const speedValue = layer.data.speed;
    const speed = isFiniteNumber(speedValue) && speedValue !== 0 ? speedValue : 1;
    layer.data.speed = -speed;
  } else if (layer.type === "nestedComp" && layer.data) {
    const nestedData = layer.data as NestedCompData;
    if (nestedData.timewarpEnabled && nestedData.timewarpSpeed) {
      nestedData.timewarpSpeed.value = -nestedData.timewarpSpeed.value;
    }
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Reversed layer: ${layer.name}`);
}

// ============================================================================
// FREEZE FRAME
// ============================================================================

/**
 * Create a freeze frame at the current playhead position
 * @param layerId - The layer ID to freeze
 */
export function freezeFrameAtPlayhead(
  layerId: string,
): void {
  const projectStore = useProjectStore();
  const animationStore = useAnimationStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for freeze frame:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("Freeze frame only works on video/nestedComp layers");
    return;
  }

  projectStore.pushHistory();

  const activeComp = projectStore.getActiveComp();
  // Type proof: currentFrame ∈ ℕ ∪ {undefined} → ℕ
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const currentFrameValue = (activeComp != null && typeof activeComp === "object" && "currentFrame" in activeComp && typeof activeComp.currentFrame === "number") ? activeComp.currentFrame : undefined;
  const currentFrame = isFiniteNumber(currentFrameValue) && Number.isInteger(currentFrameValue) && currentFrameValue >= 0 ? currentFrameValue : 0;
  const fps = projectStore.getFps();
  const sourceTime = currentFrame / fps;

  if (layer.data) {
    const data = layer.data as SpeedMappableData;
    data.speedMapEnabled = true;

    if (!data.speedMap) {
      data.speedMap = createAnimatableProperty(
        "Speed Map",
        sourceTime,
        "number",
      );
    }

    // Deterministic ID generation: same layer/property/frame/value always produces same ID
    const propertyPath = "speedMap";
    const valueStr = String(sourceTime);
    const endFrame = (() => {
      // Type proof: endFrame ∈ ℕ ∪ {undefined} → ℕ
      const endFrameValue = layer.endFrame;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const settings = (activeComp != null && typeof activeComp === "object" && "settings" in activeComp && activeComp.settings != null && typeof activeComp.settings === "object") ? activeComp.settings : undefined;
      const frameCountValue = (settings != null && typeof settings === "object" && "frameCount" in settings && typeof settings.frameCount === "number") ? settings.frameCount : undefined;
      const endFrameCalc = isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0
        ? endFrameValue
        : (isFiniteNumber(frameCountValue) && Number.isInteger(frameCountValue) && frameCountValue > 0 ? frameCountValue : 81);
      return endFrameCalc - 1;
    })();
    
    data.speedMap.keyframes = [
      {
        id: generateKeyframeId(layerId, propertyPath, currentFrame, valueStr),
        frame: currentFrame,
        value: sourceTime,
        interpolation: "hold" as const,
        controlMode: "smooth" as const,
        inHandle: { frame: -5, value: 0, enabled: true },
        outHandle: { frame: 5, value: 0, enabled: true },
      },
      {
        id: generateKeyframeId(layerId, propertyPath, endFrame, valueStr),
        frame: endFrame,
        value: sourceTime,
        interpolation: "hold" as const,
        controlMode: "smooth" as const,
        inHandle: { frame: -5, value: 0, enabled: true },
        outHandle: { frame: 5, value: 0, enabled: true },
      },
    ];

    data.speedMap.value = sourceTime;
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(
    `Created freeze frame on ${layer.name} at frame ${currentFrame}`,
  );
}

// ============================================================================
// SPLIT LAYER
// ============================================================================

/**
 * Split layer at the current playhead position
 * @param layerId - The layer ID to split
 * @returns The new layer created from the split, or null on failure
 */
export function splitLayerAtPlayhead(
  layerId: string,
): Layer | null {
  const projectStore = useProjectStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    throw new Error(`[LayerStore] Cannot split layer: Layer "${layerId}" not found`);
  }

  const activeComp = projectStore.getActiveComp();
  // Type proof: currentFrame ∈ ℕ ∪ {undefined} → ℕ
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const currentFrameValue = (activeComp != null && typeof activeComp === "object" && "currentFrame" in activeComp && typeof activeComp.currentFrame === "number") ? activeComp.currentFrame : undefined;
  const currentFrame = isFiniteNumber(currentFrameValue) && Number.isInteger(currentFrameValue) && currentFrameValue >= 0 ? currentFrameValue : 0;
  // Type proof: startFrame ∈ ℕ ∪ {undefined} → ℕ
  const startFrameValue = layer.startFrame;
  const startFrame = isFiniteNumber(startFrameValue) && Number.isInteger(startFrameValue) && startFrameValue >= 0 ? startFrameValue : 0;
  // Type proof: endFrame ∈ ℕ ∪ {undefined} → ℕ
  const endFrameValue = layer.endFrame;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (activeComp != null && typeof activeComp === "object" && "settings" in activeComp && activeComp.settings != null && typeof activeComp.settings === "object") ? activeComp.settings : undefined;
  const frameCountValue = (settings != null && typeof settings === "object" && "frameCount" in settings && typeof settings.frameCount === "number") ? settings.frameCount : undefined;
  const endFrame = isFiniteNumber(endFrameValue) && Number.isInteger(endFrameValue) && endFrameValue >= 0
    ? endFrameValue
    : (isFiniteNumber(frameCountValue) && Number.isInteger(frameCountValue) && frameCountValue > 0 ? frameCountValue : 81);

  if (currentFrame <= startFrame || currentFrame >= endFrame) {
    throw new Error(`[LayerStore] Cannot split layer: Split point ${currentFrame} must be within layer bounds (${startFrame} < frame < ${endFrame})`);
  }

  projectStore.pushHistory();

  const newLayerId = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const newLayer: Layer = {
    ...JSON.parse(JSON.stringify(layer)),
    id: newLayerId,
    name: `${layer.name} (split)`,
  };

  layer.endFrame = currentFrame;
  newLayer.startFrame = currentFrame;
  newLayer.endFrame = endFrame;

  if (isLayerOfType(newLayer, "video") && newLayer.data) {
    const fps = projectStore.getFps();
    // Type proof: startTime ∈ ℝ ∪ {undefined} → ℝ
    const startTimeValue = newLayer.data.startTime;
    const originalStartTime = isFiniteNumber(startTimeValue) && startTimeValue >= 0 ? startTimeValue : 0;
    // Type proof: speed ∈ ℝ ∪ {undefined} → ℝ
    const speedValue = newLayer.data.speed;
    const speed = isFiniteNumber(speedValue) && speedValue !== 0 ? speedValue : 1;
    const frameOffset = currentFrame - startFrame;
    const timeOffset = (frameOffset / fps) * speed;
    newLayer.data.startTime = originalStartTime + timeOffset;
  }

  const layers = projectStore.getActiveCompLayers();
  const originalIndex = layers.findIndex((l: Layer) => l.id === layerId);
  layers.splice(originalIndex + 1, 0, newLayer);

  markLayerDirty(layerId);
  markLayerDirty(newLayerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Split layer ${layer.name} at frame ${currentFrame}`);

  return newLayer;
}

// ============================================================================
// SPEED MAP (TIME REMAPPING)
// ============================================================================

/**
 * Enable SpeedMap (time remapping) on a video or nested comp layer
 * @param layerId - The layer ID
 * @param fps - Optional fps override
 */
export function enableSpeedMap(
  layerId: string,
  fps?: number,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for enableSpeedMap:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("SpeedMap only works on video/nestedComp layers");
    return;
  }

  projectStore.pushHistory();

  const activeComp = projectStore.getActiveComp();
  // Type proof: fps ∈ ℝ ∪ {undefined} → ℝ
  const fpsValue = fps;
  const compositionFps = isFiniteNumber(fpsValue) && fpsValue > 0 ? fpsValue : projectStore.getFps();
  // Type proof: startFrame ∈ ℕ ∪ {undefined} → ℕ
  const layerStartFrameValue = layer.startFrame;
  const layerStartFrame = isFiniteNumber(layerStartFrameValue) && Number.isInteger(layerStartFrameValue) && layerStartFrameValue >= 0 ? layerStartFrameValue : 0;
  // Type proof: endFrame ∈ ℕ ∪ {undefined} → ℕ
  const layerEndFrameValue = layer.endFrame;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const settings = (activeComp != null && typeof activeComp === "object" && "settings" in activeComp && activeComp.settings != null && typeof activeComp.settings === "object") ? activeComp.settings : undefined;
  const activeCompFrameCountValue = (settings != null && typeof settings === "object" && "frameCount" in settings && typeof settings.frameCount === "number") ? settings.frameCount : undefined;
  const layerEndFrame = isFiniteNumber(layerEndFrameValue) && Number.isInteger(layerEndFrameValue) && layerEndFrameValue >= 0
    ? layerEndFrameValue
    : (isFiniteNumber(activeCompFrameCountValue) && Number.isInteger(activeCompFrameCountValue) && activeCompFrameCountValue > 0 ? activeCompFrameCountValue : 81);

  if (layer.data) {
    const data = layer.data as SpeedMappableData;
    data.speedMapEnabled = true;
    data.timeRemapEnabled = true;

    if (!data.speedMap || data.speedMap.keyframes.length === 0) {
      const startSourceTime = 0;
      const layerDuration = layerEndFrame - layerStartFrame;
      const endSourceTime = layerDuration / compositionFps;

      data.speedMap = createAnimatableProperty(
        "Speed Map",
        startSourceTime,
        "number",
      );
      data.speedMap.animated = true;
      // Deterministic ID generation: same layer/property/frame/value always produces same ID
      const propertyPath = "speedMap";
      const startValueStr = String(startSourceTime);
      const endValueStr = String(endSourceTime);
      
      data.speedMap.keyframes = [
        {
          id: generateKeyframeId(layerId, propertyPath, layerStartFrame, startValueStr),
          frame: layerStartFrame,
          value: startSourceTime,
          interpolation: "linear" as const,
          controlMode: "smooth" as const,
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
        },
        {
          id: generateKeyframeId(layerId, propertyPath, layerEndFrame, endValueStr),
          frame: layerEndFrame,
          value: endSourceTime,
          interpolation: "linear" as const,
          controlMode: "smooth" as const,
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
        },
      ];

      data.timeRemap = data.speedMap;
    }
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Enabled SpeedMap on layer: ${layer.name}`);
}

/**
 * Disable SpeedMap (time remapping) on a video or nested comp layer
 * @param layerId - The layer ID
 */
export function disableSpeedMap(
  layerId: string,
): void {
  const projectStore = useProjectStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for disableSpeedMap:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    return;
  }

  projectStore.pushHistory();

  if (layer.data) {
    const data = layer.data as SpeedMappableData;
    data.speedMapEnabled = false;
    data.timeRemapEnabled = false;
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Disabled SpeedMap on layer: ${layer.name}`);
}

/**
 * Toggle SpeedMap on/off for a layer
 * @param layerId - The layer ID
 * @param fps - Optional fps override
 * @returns Whether SpeedMap is now enabled
 */
export function toggleSpeedMap(
  layerId: string,
  fps?: number,
): boolean {
  const projectStore = useProjectStore();
  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (
    !layer ||
    (layer.type !== "video" && layer.type !== "nestedComp")
  ) {
    return false;
  }

  type ToggleableData = { speedMapEnabled?: boolean };
  const data = layer.data as ToggleableData | null;
  // Type proof: speedMapEnabled ∈ boolean | undefined → boolean
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const speedMapEnabledValue = (data != null && typeof data === "object" && "speedMapEnabled" in data && typeof data.speedMapEnabled === "boolean") ? data.speedMapEnabled : undefined;
  const isCurrentlyEnabled = speedMapEnabledValue === true;

  if (isCurrentlyEnabled) {
    disableSpeedMap(layerId);
    return false;
  } else {
    enableSpeedMap(layerId, fps);
    return true;
  }
}
