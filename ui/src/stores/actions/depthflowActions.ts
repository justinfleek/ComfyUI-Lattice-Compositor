/**
 * Depthflow Actions
 *
 * Depthflow parallax layer creation and configuration.
 *
 * Extracted from compositorStore.ts for modularity.
 */

import type { DepthflowLayerData, Layer } from "@/types/project";
import { createAnimatableProperty } from "@/types/project";

/**
 * Sanitize numeric config value, returning default if invalid
 */
function sanitizeNumber(value: unknown, defaultValue: number): number {
  if (typeof value !== "number" || !Number.isFinite(value)) {
    return defaultValue;
  }
  return value;
}

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface DepthflowStore {
  project: {
    meta: { modified: string };
  };

  // Methods the actions need to call
  getActiveCompLayers(): Layer[];
  createLayer(type: Layer["type"], name?: string): Layer;
}

// ============================================================================
// DEPTHFLOW LAYER CREATION
// ============================================================================

/**
 * Create a depthflow parallax layer
 */
export function createDepthflowLayer(
  store: DepthflowStore,
  sourceLayerId: string = "",
  depthLayerId: string = "",
): Layer {
  const layer = store.createLayer("depthflow", "Depthflow");

  // Set up depthflow layer data
  const depthflowData: DepthflowLayerData = {
    sourceLayerId,
    depthLayerId,
    config: {
      preset: "zoom_in",
      zoom: 1.0,
      offsetX: 0,
      offsetY: 0,
      rotation: 0,
      depthScale: 1.0,
      focusDepth: 0.5,
      dollyZoom: 0,
      orbitRadius: 0.1,
      orbitSpeed: 360,
      swingAmplitude: 0.1,
      swingFrequency: 1,
      edgeDilation: 5,
      inpaintEdges: true,
    },
    animatedZoom: createAnimatableProperty("zoom", 1.0, "number"),
    animatedOffsetX: createAnimatableProperty("offsetX", 0, "number"),
    animatedOffsetY: createAnimatableProperty("offsetY", 0, "number"),
    animatedRotation: createAnimatableProperty("rotation", 0, "number"),
    animatedDepthScale: createAnimatableProperty("depthScale", 1.0, "number"),
  };

  layer.data = depthflowData;

  return layer;
}

// ============================================================================
// DEPTHFLOW CONFIG UPDATES
// ============================================================================

/**
 * Update depthflow config
 */
export function updateDepthflowConfig(
  store: DepthflowStore,
  layerId: string,
  updates: Partial<DepthflowLayerData["config"]>,
): void {
  const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
  if (!layer || layer.type !== "depthflow") return;

  const data = layer.data as DepthflowLayerData;

  // Sanitize numeric values to prevent NaN/Infinity corruption
  const sanitized: Partial<DepthflowLayerData["config"]> = { ...updates };
  if (sanitized.zoom !== undefined)
    sanitized.zoom = sanitizeNumber(sanitized.zoom, data.config.zoom);
  if (sanitized.offsetX !== undefined)
    sanitized.offsetX = sanitizeNumber(sanitized.offsetX, data.config.offsetX);
  if (sanitized.offsetY !== undefined)
    sanitized.offsetY = sanitizeNumber(sanitized.offsetY, data.config.offsetY);
  if (sanitized.rotation !== undefined)
    sanitized.rotation = sanitizeNumber(
      sanitized.rotation,
      data.config.rotation,
    );
  if (sanitized.depthScale !== undefined)
    sanitized.depthScale = sanitizeNumber(
      sanitized.depthScale,
      data.config.depthScale,
    );
  if (sanitized.focusDepth !== undefined)
    sanitized.focusDepth = sanitizeNumber(
      sanitized.focusDepth,
      data.config.focusDepth,
    );
  if (sanitized.dollyZoom !== undefined)
    sanitized.dollyZoom = sanitizeNumber(
      sanitized.dollyZoom,
      data.config.dollyZoom,
    );
  if (sanitized.orbitRadius !== undefined)
    sanitized.orbitRadius = sanitizeNumber(
      sanitized.orbitRadius,
      data.config.orbitRadius,
    );
  if (sanitized.orbitSpeed !== undefined)
    sanitized.orbitSpeed = sanitizeNumber(
      sanitized.orbitSpeed,
      data.config.orbitSpeed,
    );
  if (sanitized.swingAmplitude !== undefined)
    sanitized.swingAmplitude = sanitizeNumber(
      sanitized.swingAmplitude,
      data.config.swingAmplitude,
    );
  if (sanitized.swingFrequency !== undefined)
    sanitized.swingFrequency = sanitizeNumber(
      sanitized.swingFrequency,
      data.config.swingFrequency,
    );
  if (sanitized.edgeDilation !== undefined)
    sanitized.edgeDilation = sanitizeNumber(
      sanitized.edgeDilation,
      data.config.edgeDilation,
    );

  Object.assign(data.config, sanitized);
  store.project.meta.modified = new Date().toISOString();
}
