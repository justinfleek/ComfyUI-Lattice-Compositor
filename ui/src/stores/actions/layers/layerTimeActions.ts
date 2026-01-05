/**
 * Layer Time Manipulation Actions
 *
 * Handles time stretch, reverse, freeze frame, split, and speed map operations.
 * Extracted from layerActions.ts for modularity.
 */

import { markLayerDirty } from "@/services/layerEvaluationCache";
import type {
  AnimatableProperty,
  Layer,
  NestedCompData,
} from "@/types/project";
import { createAnimatableProperty, isLayerOfType } from "@/types/project";
import { storeLogger } from "@/utils/logger";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface LayerTimeStore {
  project: {
    meta: { modified: string };
  };
  getActiveComp(): { settings: { frameCount: number }; layers: Layer[] } | null;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
  currentFrame?: number;
  fps?: number;
}

// ============================================================================
// TIME STRETCH
// ============================================================================

export interface TimeStretchOptions {
  stretchFactor: number; // 100% = normal, 200% = half speed, 50% = double speed
  holdInPlace: "in-point" | "current-frame" | "out-point";
  reverse: boolean;
  newStartFrame: number;
  newEndFrame: number;
  speed: number; // Computed speed value (100 / stretchFactor)
}

/**
 * Apply time stretch to a video or nested comp layer
 * Adjusts layer timing based on stretch factor and hold-in-place pivot
 */
export function timeStretchLayer(
  store: LayerTimeStore,
  layerId: string,
  options: TimeStretchOptions,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for time stretch:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("Time stretch only works on video/nestedComp layers");
    return;
  }

  store.pushHistory();

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
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(
    `Time stretched layer ${layer.name}: ${options.stretchFactor}% ` +
      `(speed: ${options.speed.toFixed(2)}, hold: ${options.holdInPlace})`,
  );
}

/**
 * Reverse layer playback
 */
export function reverseLayer(store: LayerTimeStore, layerId: string): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for reverse:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("Reverse only works on video/nestedComp layers");
    return;
  }

  store.pushHistory();

  if (isLayerOfType(layer, "video") && layer.data) {
    layer.data.speed = -(layer.data.speed ?? 1);
  } else if (layer.type === "nestedComp" && layer.data) {
    const nestedData = layer.data as NestedCompData;
    if (nestedData.timewarpEnabled && nestedData.timewarpSpeed) {
      nestedData.timewarpSpeed.value = -nestedData.timewarpSpeed.value;
    }
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Reversed layer: ${layer.name}`);
}

// ============================================================================
// FREEZE FRAME
// ============================================================================

/**
 * Create a freeze frame at the current playhead position
 */
export function freezeFrameAtPlayhead(
  store: LayerTimeStore & { currentFrame: number; fps: number },
  layerId: string,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for freeze frame:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("Freeze frame only works on video/nestedComp layers");
    return;
  }

  store.pushHistory();

  const currentFrame = store.currentFrame ?? 0;
  // Validate fps (nullish coalescing doesn't catch NaN)
  const fps = Number.isFinite(store.fps) && store.fps > 0 ? store.fps : 16;
  const sourceTime = currentFrame / fps;

  type SpeedMappableData = {
    speedMapEnabled: boolean;
    speedMap?: AnimatableProperty<number>;
  };

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
          (layer.endFrame ?? store.getActiveComp()?.settings.frameCount ?? 81) -
          1,
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
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(
    `Created freeze frame on ${layer.name} at frame ${currentFrame}`,
  );
}

// ============================================================================
// SPLIT LAYER
// ============================================================================

/**
 * Split layer at the current playhead position
 */
export function splitLayerAtPlayhead(
  store: LayerTimeStore & { currentFrame: number; fps: number },
  layerId: string,
): Layer | null {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for split:", layerId);
    return null;
  }

  const currentFrame = store.currentFrame ?? 0;
  const startFrame = layer.startFrame ?? 0;
  const endFrame =
    layer.endFrame ?? store.getActiveComp()?.settings.frameCount ?? 81;

  if (currentFrame <= startFrame || currentFrame >= endFrame) {
    storeLogger.warn("Split point must be within layer bounds");
    return null;
  }

  store.pushHistory();

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
    const fps = Number.isFinite(store.fps) && store.fps > 0 ? store.fps : 16;
    const originalStartTime = newLayer.data.startTime ?? 0;
    const speed = newLayer.data.speed ?? 1;
    const frameOffset = currentFrame - startFrame;
    const timeOffset = (frameOffset / fps) * speed;
    newLayer.data.startTime = originalStartTime + timeOffset;
  }

  const layers = store.getActiveCompLayers();
  const originalIndex = layers.findIndex((l) => l.id === layerId);
  layers.splice(originalIndex + 1, 0, newLayer);

  markLayerDirty(layerId);
  markLayerDirty(newLayerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Split layer ${layer.name} at frame ${currentFrame}`);

  return newLayer;
}

// ============================================================================
// SPEED MAP (TIME REMAP)
// ============================================================================

/**
 * Enable SpeedMap (time remapping) on a video or nested comp layer
 */
export function enableSpeedMap(
  store: LayerTimeStore & { fps?: number },
  layerId: string,
  fps?: number,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for enableSpeedMap:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    storeLogger.warn("SpeedMap only works on video/nestedComp layers");
    return;
  }

  store.pushHistory();

  const compositionFps = fps ?? store.fps ?? 30;
  const layerStartFrame = layer.startFrame ?? 0;
  const layerEndFrame =
    layer.endFrame ?? store.getActiveComp()?.settings.frameCount ?? 81;

  type SpeedMappableData = {
    speedMapEnabled: boolean;
    speedMap?: AnimatableProperty<number>;
    timeRemapEnabled?: boolean;
    timeRemap?: AnimatableProperty<number>;
  };

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
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Enabled SpeedMap on layer: ${layer.name}`);
}

/**
 * Disable SpeedMap (time remapping) on a video or nested comp layer
 */
export function disableSpeedMap(store: LayerTimeStore, layerId: string): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("Layer not found for disableSpeedMap:", layerId);
    return;
  }

  if (layer.type !== "video" && layer.type !== "nestedComp") {
    return;
  }

  store.pushHistory();

  type SpeedMappableData = {
    speedMapEnabled: boolean;
    timeRemapEnabled?: boolean;
  };

  if (layer.data) {
    const data = layer.data as SpeedMappableData;
    data.speedMapEnabled = false;
    data.timeRemapEnabled = false;
  }

  markLayerDirty(layerId);
  store.project.meta.modified = new Date().toISOString();

  storeLogger.debug(`Disabled SpeedMap on layer: ${layer.name}`);
}

/**
 * Toggle SpeedMap on/off for a layer
 */
export function toggleSpeedMap(
  store: LayerTimeStore & { fps?: number },
  layerId: string,
  fps?: number,
): boolean {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || (layer.type !== "video" && layer.type !== "nestedComp")) {
    return false;
  }

  type SpeedMappableData = { speedMapEnabled?: boolean };
  const data = layer.data as SpeedMappableData | null;
  const isCurrentlyEnabled = data?.speedMapEnabled ?? false;

  if (isCurrentlyEnabled) {
    disableSpeedMap(store, layerId);
    return false;
  } else {
    enableSpeedMap(store, layerId, fps);
    return true;
  }
}
