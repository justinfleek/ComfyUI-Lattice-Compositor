/**
 * Layer Time Operations
 *
 * Time stretch, reverse, freeze frame, split, and speed map operations.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import type { AnimatableProperty, Layer, NestedCompData } from "@/types/project";
import { createAnimatableProperty, isLayerOfType } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import type { CompositorStoreAccess, TimeStretchOptions } from "./types";

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
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to stretch
 * @param options - Time stretch options
 */
export function timeStretchLayer(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  options: TimeStretchOptions,
): void {
  const layer = compositorStore
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

  compositorStore.pushHistory();

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
  compositorStore.project.meta.modified = new Date().toISOString();

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
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID to reverse
 */
export function reverseLayer(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): void {
  const layer = compositorStore
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

  compositorStore.pushHistory();

  if (isLayerOfType(layer, "video") && layer.data) {
    layer.data.speed = -(layer.data.speed ?? 1);
  } else if (layer.type === "nestedComp" && layer.data) {
    const nestedData = layer.data as NestedCompData;
    if (nestedData.timewarpEnabled && nestedData.timewarpSpeed) {
      nestedData.timewarpSpeed.value = -nestedData.timewarpSpeed.value;
    }
  }

  markLayerDirty(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Reversed layer: ${layer.name}`);
}

// ============================================================================
// FREEZE FRAME
// ============================================================================

/**
 * Create a freeze frame at the current playhead position
 * @param compositorStore - The compositor store instance (must have currentFrame, fps)
 * @param layerId - The layer ID to freeze
 */
export function freezeFrameAtPlayhead(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): void {
  const layer = compositorStore
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

  compositorStore.pushHistory();

  const currentFrame = compositorStore.currentFrame ?? 0;
  // Validate fps (nullish coalescing doesn't catch NaN)
  const fps =
    Number.isFinite(compositorStore.fps) && compositorStore.fps! > 0
      ? compositorStore.fps!
      : 16;
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

    data.speedMap.keyframes = [
      {
        id: `kf_freeze_start_${Date.now()}`,
        frame: currentFrame,
        value: sourceTime,
        interpolation: "hold" as const,
        controlMode: "smooth" as const,
        inHandle: { frame: -5, value: 0, enabled: true },
        outHandle: { frame: 5, value: 0, enabled: true },
      },
      {
        id: `kf_freeze_end_${Date.now() + 1}`,
        frame:
          (layer.endFrame ??
            compositorStore.getActiveComp()?.settings.frameCount ??
            81) - 1,
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
  compositorStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(
    `Created freeze frame on ${layer.name} at frame ${currentFrame}`,
  );
}

// ============================================================================
// SPLIT LAYER
// ============================================================================

/**
 * Split layer at the current playhead position
 * @param compositorStore - The compositor store instance (must have currentFrame, fps)
 * @param layerId - The layer ID to split
 * @returns The new layer created from the split, or null on failure
 */
export function splitLayerAtPlayhead(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): Layer | null {
  const layer = compositorStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for split:", layerId);
    return null;
  }

  const currentFrame = compositorStore.currentFrame ?? 0;
  const startFrame = layer.startFrame ?? 0;
  const endFrame =
    layer.endFrame ??
    compositorStore.getActiveComp()?.settings.frameCount ??
    81;

  if (currentFrame <= startFrame || currentFrame >= endFrame) {
    storeLogger.warn("Split point must be within layer bounds");
    return null;
  }

  compositorStore.pushHistory();

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
    // Validate fps (nullish coalescing doesn't catch NaN)
    const fps =
      Number.isFinite(compositorStore.fps) && compositorStore.fps! > 0
        ? compositorStore.fps!
        : 16;
    const originalStartTime = newLayer.data.startTime ?? 0;
    const speed = newLayer.data.speed ?? 1;
    const frameOffset = currentFrame - startFrame;
    const timeOffset = (frameOffset / fps) * speed;
    newLayer.data.startTime = originalStartTime + timeOffset;
  }

  const layers = compositorStore.getActiveCompLayers();
  const originalIndex = layers.findIndex((l: Layer) => l.id === layerId);
  layers.splice(originalIndex + 1, 0, newLayer);

  markLayerDirty(layerId);
  markLayerDirty(newLayerId);
  compositorStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Split layer ${layer.name} at frame ${currentFrame}`);

  return newLayer;
}

// ============================================================================
// SPEED MAP (TIME REMAPPING)
// ============================================================================

/**
 * Enable SpeedMap (time remapping) on a video or nested comp layer
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID
 * @param fps - Optional fps override
 */
export function enableSpeedMap(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  fps?: number,
): void {
  const layer = compositorStore
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

  compositorStore.pushHistory();

  const compositionFps = fps ?? compositorStore.fps ?? 30;
  const layerStartFrame = layer.startFrame ?? 0;
  const layerEndFrame =
    layer.endFrame ??
    compositorStore.getActiveComp()?.settings.frameCount ??
    81;

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
      data.speedMap.keyframes = [
        {
          id: `kf_speedmap_start_${Date.now()}`,
          frame: layerStartFrame,
          value: startSourceTime,
          interpolation: "linear" as const,
          controlMode: "smooth" as const,
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
        },
        {
          id: `kf_speedmap_end_${Date.now() + 1}`,
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
  compositorStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Enabled SpeedMap on layer: ${layer.name}`);
}

/**
 * Disable SpeedMap (time remapping) on a video or nested comp layer
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID
 */
export function disableSpeedMap(
  compositorStore: CompositorStoreAccess,
  layerId: string,
): void {
  const layer = compositorStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for disableSpeedMap:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    return;
  }

  compositorStore.pushHistory();

  if (layer.data) {
    const data = layer.data as SpeedMappableData;
    data.speedMapEnabled = false;
    data.timeRemapEnabled = false;
  }

  markLayerDirty(layerId);
  compositorStore.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Disabled SpeedMap on layer: ${layer.name}`);
}

/**
 * Toggle SpeedMap on/off for a layer
 * @param compositorStore - The compositor store instance
 * @param layerId - The layer ID
 * @param fps - Optional fps override
 * @returns Whether SpeedMap is now enabled
 */
export function toggleSpeedMap(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  fps?: number,
): boolean {
  const layer = compositorStore
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
  const isCurrentlyEnabled = data?.speedMapEnabled ?? false;

  if (isCurrentlyEnabled) {
    disableSpeedMap(compositorStore, layerId);
    return false;
  } else {
    enableSpeedMap(compositorStore, layerId, fps);
    return true;
  }
}
