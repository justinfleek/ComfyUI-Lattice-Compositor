/**
 * Depthflow Store
 *
 * Domain store for depthflow parallax layer creation and configuration.
 * Provides 2.5D depth-based parallax effects for images with depth maps.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import type { DepthflowLayerData, Layer } from "@/types/project";
import { createAnimatableProperty } from "@/types/project";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                              // store // access // interface
// ════════════════════════════════════════════════════════════════════════════

export interface DepthflowStoreAccess {
  project: {
    meta: { modified: string };
  };
  getActiveCompLayers(): Layer[];
  createLayer(type: Layer["type"], name?: string): Layer;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // helper // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Sanitize numeric config value, returning default if invalid.
 * Prevents NaN/Infinity corruption in layer data.
 */
function sanitizeNumber(value: RuntimeValue, defaultValue: number): number {
  if (typeof value !== "number" || !Number.isFinite(value)) {
    return defaultValue;
  }
  return value;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                            // pinia // store
// ════════════════════════════════════════════════════════════════════════════

export const useDepthflowStore = defineStore("depthflow", {
  state: () => ({}),

  getters: {},

  actions: {
    /**
     * Create a depthflow parallax layer.
     *
     * @param store - Compositor store access
     * @param sourceLayerId - ID of the source image layer
     * @param depthLayerId - ID of the depth map layer
     * @returns The created depthflow layer
     */
    createDepthflowLayer(
      store: DepthflowStoreAccess,
      sourceLayerId: string = "",
      depthLayerId: string = "",
    ): Layer {
      // Use store.createLayer directly - defined in DepthflowStoreAccess interface
      const layer = store.createLayer("depthflow", "Depthflow");

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
    },

    /**
     * Update depthflow configuration with sanitized values.
     *
     * @param store - Compositor store access
     * @param layerId - ID of the depthflow layer to update
     * @param updates - Partial configuration updates
     */
    updateDepthflowConfig(
      store: DepthflowStoreAccess,
      layerId: string,
      updates: Partial<DepthflowLayerData["config"]>,
    ): void {
      const layer = store.getActiveCompLayers().find((l) => l.id === layerId);
      if (!layer || layer.type !== "depthflow") {
        return;
      }

      const data = layer.data as DepthflowLayerData;
      if (!data || !data.config) {
        return;
      }

      // Sanitize numeric values to prevent NaN/Infinity corruption
      const sanitized: Partial<DepthflowLayerData["config"]> = { ...updates };

      if (sanitized.zoom !== undefined) {
        sanitized.zoom = sanitizeNumber(sanitized.zoom, data.config.zoom);
      }
      if (sanitized.offsetX !== undefined) {
        sanitized.offsetX = sanitizeNumber(sanitized.offsetX, data.config.offsetX);
      }
      if (sanitized.offsetY !== undefined) {
        sanitized.offsetY = sanitizeNumber(sanitized.offsetY, data.config.offsetY);
      }
      if (sanitized.rotation !== undefined) {
        sanitized.rotation = sanitizeNumber(sanitized.rotation, data.config.rotation);
      }
      if (sanitized.depthScale !== undefined) {
        sanitized.depthScale = sanitizeNumber(sanitized.depthScale, data.config.depthScale);
      }
      if (sanitized.focusDepth !== undefined) {
        sanitized.focusDepth = sanitizeNumber(sanitized.focusDepth, data.config.focusDepth);
      }
      if (sanitized.dollyZoom !== undefined) {
        sanitized.dollyZoom = sanitizeNumber(sanitized.dollyZoom, data.config.dollyZoom);
      }
      if (sanitized.orbitRadius !== undefined) {
        sanitized.orbitRadius = sanitizeNumber(sanitized.orbitRadius, data.config.orbitRadius);
      }
      if (sanitized.orbitSpeed !== undefined) {
        sanitized.orbitSpeed = sanitizeNumber(sanitized.orbitSpeed, data.config.orbitSpeed);
      }
      if (sanitized.swingAmplitude !== undefined) {
        sanitized.swingAmplitude = sanitizeNumber(sanitized.swingAmplitude, data.config.swingAmplitude);
      }
      if (sanitized.swingFrequency !== undefined) {
        sanitized.swingFrequency = sanitizeNumber(sanitized.swingFrequency, data.config.swingFrequency);
      }
      if (sanitized.edgeDilation !== undefined) {
        sanitized.edgeDilation = sanitizeNumber(sanitized.edgeDilation, data.config.edgeDilation);
      }

      Object.assign(data.config, sanitized);
      store.project.meta.modified = new Date().toISOString();
    },
  },
});
