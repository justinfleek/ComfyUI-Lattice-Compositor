/**
 * Physics Actions - Bake to Keyframes
 *
 * Convert physics simulation to keyframe animation.
 */

import type { PhysicsLayerData } from "@/types/physics";
import { storeLogger } from "@/utils/logger";
import { getPhysicsEngine } from "./engine";
import { disableLayerPhysics } from "./rigidBody";
import type { PhysicsStore, BakeOptions, BakeResult, BakedKeyframe } from "./types";

// ============================================================================
// BAKE SINGLE LAYER
// ============================================================================

/**
 * Bake physics simulation to keyframes
 * Creates position and rotation keyframes from simulation
 */
export async function bakePhysicsToKeyframes(
  store: PhysicsStore,
  layerId: string,
  options: BakeOptions = {},
): Promise<BakeResult> {
  const layer = store.getLayerById(layerId);
  if (!layer) {
    throw new Error(`Layer not found: ${layerId}`);
  }

  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) {
    throw new Error("No active composition");
  }

  const startFrame = options.startFrame ?? 0;
  const endFrame = options.endFrame ?? comp.settings.frameCount - 1;
  // Validate sampleInterval to prevent infinite loop (NaN causes frame += NaN = NaN)
  const sampleInterval: number =
    Number.isFinite(options.sampleInterval) && options.sampleInterval! > 0
      ? options.sampleInterval!
      : 1;

  const engine = getPhysicsEngine(store);

  // Clear cache to start fresh
  engine.clearCache();

  const positionKeyframes: BakedKeyframe<{
    x: number;
    y: number;
    z: number;
  }>[] = [];
  const rotationKeyframes: BakedKeyframe<number>[] = [];

  // Simulate and collect keyframes
  for (let frame = startFrame; frame <= endFrame; frame += sampleInterval) {
    const state = engine.evaluateFrame(frame);
    const bodyState = state.rigidBodies.find((b) => b.id === layerId);

    if (bodyState) {
      positionKeyframes.push({
        frame,
        value: {
          x: bodyState.position.x,
          y: bodyState.position.y,
          z: layer.transform?.position?.value?.z ?? 0,
        },
        interpolation: "linear",
      });

      rotationKeyframes.push({
        frame,
        value: bodyState.angle * (180 / Math.PI),
        interpolation: "linear",
      });
    }
  }

  // Apply keyframes to layer (store should handle the Keyframe type conversion)
  for (const kf of positionKeyframes) {
    store.addKeyframe(layerId, "transform.position", kf.value, kf.frame);
  }

  for (const kf of rotationKeyframes) {
    store.addKeyframe(layerId, "transform.rotation", kf.value, kf.frame);
  }

  // Disable physics after baking
  disableLayerPhysics(store, layerId);

  storeLogger.info("Physics baked to keyframes:", layerId, {
    positionKeyframes: positionKeyframes.length,
    rotationKeyframes: rotationKeyframes.length,
  });

  return {
    layerId,
    positionKeyframes,
    rotationKeyframes,
  };
}

// ============================================================================
// BAKE ALL LAYERS
// ============================================================================

/**
 * Bake all physics-enabled layers to keyframes
 */
export async function bakeAllPhysicsToKeyframes(
  store: PhysicsStore,
  options: BakeOptions = {},
): Promise<BakeResult[]> {
  const comp = store.project.compositions[store.activeCompositionId];
  if (!comp) return [];

  const results: BakeResult[] = [];

  for (const layer of comp.layers) {
    const physicsData = (layer.data as unknown as Record<string, unknown>)?.physics as
      | PhysicsLayerData
      | undefined;
    if (physicsData?.physicsEnabled) {
      const result = await bakePhysicsToKeyframes(store, layer.id, options);
      results.push(result);
    }
  }

  return results;
}
