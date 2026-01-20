/**
 * Layer Batch Operations
 *
 * Batch operations for multiple layers: sequencing, exponential scale.
 * Extracted from layerStore.ts during Phase 1B modularization.
 *
 * @see docs/graphs/layerActions.md
 */

import type { Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { markLayerDirty } from "@/services/layerEvaluationCache";
import type {
  ExponentialScaleOptions,
  SequenceLayersOptions,
} from "./types";
import { useProjectStore } from "../projectStore";

// ============================================================================
// SEQUENCE LAYERS
// ============================================================================

/**
 * Sequence layers - arrange them one after another in timeline
 * @param layerIds - Array of layer IDs to sequence
 * @param options - Sequencing options
 * @returns Number of layers sequenced
 */
export function sequenceLayers(
  layerIds: string[],
  options: SequenceLayersOptions = {},
): number {
  const projectStore = useProjectStore();
  const { gapFrames = 0, startFrame = 0, reverse = false } = options;

  if (layerIds.length < 2) {
    storeLogger.warn("sequenceLayers: need at least 2 layers");
    return 0;
  }

  // Get layers in order
  const layers = layerIds
    .map((id) =>
      projectStore.getActiveCompLayers().find((l: Layer) => l.id === id),
    )
    .filter((l: Layer | undefined): l is Layer => l !== null && l !== undefined);

  if (layers.length < 2) {
    storeLogger.warn("sequenceLayers: could not find enough layers");
    return 0;
  }

  // Optionally reverse the order
  const orderedLayers = reverse ? [...layers].reverse() : layers;

  // Push history BEFORE changes for undo support
  projectStore.pushHistory();

  let currentFrame = startFrame;

  orderedLayers.forEach((layer: Layer) => {
    const duration = layer.endFrame - layer.startFrame;

    // Set new start/end frames
    layer.startFrame = currentFrame;
    layer.endFrame = currentFrame + duration;

    // Move to next position
    currentFrame = layer.endFrame + gapFrames;

    markLayerDirty(layer.id);
  });

  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.info(
    `sequenceLayers: sequenced ${orderedLayers.length} layers starting at frame ${startFrame}`,
  );
  return orderedLayers.length;
}

// ============================================================================
// EXPONENTIAL SCALE
// ============================================================================

/**
 * Create exponential scale animation on a layer
 * Uses exponential curve instead of linear for more natural zoom effect.
 * Formula: scale(t) = startScale * (endScale/startScale)^t
 *
 * @param layerId - Layer to apply exponential scale to
 * @param options - Scale animation options
 * @returns Number of keyframes created
 */
export function applyExponentialScale(
  layerId: string,
  options: ExponentialScaleOptions = {},
): number {
  const projectStore = useProjectStore();
  const {
    startScale = 100,
    endScale = 200,
    startFrame = 0,
    endFrame = 30,
    keyframeCount = 10,
    axis = "both",
  } = options;

  const layer = projectStore
    .getActiveCompLayers()
    .find((l: Layer) => l.id === layerId);
  if (!layer) {
    storeLogger.warn("applyExponentialScale: layer not found");
    return 0;
  }

  // Validate scale values (prevent division by zero)
  if (!Number.isFinite(startScale) || startScale === 0) {
    storeLogger.warn(
      "applyExponentialScale: startScale must be a non-zero finite number",
    );
    return 0;
  }
  if (!Number.isFinite(endScale)) {
    storeLogger.warn(
      "applyExponentialScale: endScale must be a finite number",
    );
    return 0;
  }

  // Push history BEFORE changes for undo support
  projectStore.pushHistory();

  // Clear existing scale keyframes
  layer.transform.scale.keyframes = [];
  layer.transform.scale.animated = true;

  const duration = endFrame - startFrame;
  const ratio = endScale / startScale;

  // Generate keyframes with exponential interpolation
  for (let i = 0; i <= keyframeCount; i++) {
    const t = i / keyframeCount; // 0 to 1
    const frame = Math.round(startFrame + t * duration);

    // Exponential formula: startScale * ratio^t
    const scaleValue = startScale * ratio ** t;

    const currentValue = layer.transform.scale.value;
    let newValue: { x: number; y: number; z?: number };

    if (axis === "x") {
      newValue = { x: scaleValue, y: currentValue.y, z: currentValue.z };
    } else if (axis === "y") {
      newValue = { x: currentValue.x, y: scaleValue, z: currentValue.z };
    } else {
      newValue = { x: scaleValue, y: scaleValue, z: currentValue.z };
    }

    layer.transform.scale.keyframes.push({
      id: `kf_expscale_${frame}_${Date.now()}_${i}`,
      frame,
      value: newValue,
      interpolation: "linear", // Linear between exponential samples gives smooth curve
      inHandle: { frame: -2, value: 0, enabled: false },
      outHandle: { frame: 2, value: 0, enabled: false },
      controlMode: "smooth",
    });
  }

  markLayerDirty(layerId);
  projectStore.project.meta.modified = new Date().toISOString();

  storeLogger.info(
    `applyExponentialScale: created ${keyframeCount + 1} keyframes for exponential scale ${startScale}% -> ${endScale}%`,
  );
  return keyframeCount + 1;
}
