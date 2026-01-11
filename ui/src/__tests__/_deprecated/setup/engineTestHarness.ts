/**
 * Engine Test Harness
 *
 * Creates a REAL test environment with actual engine instances.
 * This is NOT a mock - it's a real engine running in a test context.
 *
 * NOTE: This harness tests the REAL MotionEngine (pure frame evaluation)
 * with REAL store data. LatticeEngine (WebGL) requires a browser environment
 * and is tested separately in e2e tests.
 */

import { createPinia, setActivePinia } from "pinia";
import type { FrameState } from "@/engine/MotionEngine";
import { MotionEngine } from "@/engine/MotionEngine";
import { useAudioStore } from "@/stores/audioStore";
import { useCompositorStore } from "@/stores/compositorStore";

/**
 * Creates a real test environment with actual engine instances.
 *
 * Tests the REAL evaluation pipeline:
 * 1. Layer creation through REAL store actions
 * 2. REAL MotionEngine.evaluate() - pure function
 * 3. REAL FrameState output verification
 *
 * Note: WebGL rendering (LatticeEngine) requires a browser and is
 * tested in e2e tests with Playwright/Puppeteer.
 */
export function createEngineTestHarness() {
  // Create real Pinia instance
  const pinia = createPinia();
  setActivePinia(pinia);

  // Get real stores
  const store = useCompositorStore();
  const audioStore = useAudioStore();

  // Real motion engine for evaluation - this is the PURE evaluation engine
  const motionEngine = new MotionEngine();

  return {
    store,
    audioStore,
    motionEngine,
    pinia,

    /**
     * Evaluate a frame using the REAL MotionEngine.
     * This tests the entire evaluation pipeline:
     * - Property interpolation
     * - Keyframe evaluation
     * - Expression evaluation
     * - Layer transform calculation
     */
    async renderFrame(frame: number): Promise<FrameState> {
      const frameState = motionEngine.evaluate(
        frame,
        store.project,
        audioStore.audioAnalysis,
      );
      return frameState;
    },

    /**
     * Cleanup all resources
     */
    dispose() {
      // Clear store state
      store.$reset();
    },
  };
}

export type EngineTestHarness = ReturnType<typeof createEngineTestHarness>;
