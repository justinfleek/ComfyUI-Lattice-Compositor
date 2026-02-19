<template>
  <div class="scopes-panel">
    <div class="scope-header">
      <select v-model="activeScope" class="scope-select">
        <option value="histogram">Histogram</option>
        <option value="waveform">Waveform</option>
        <option value="vectorscope">Vectorscope</option>
        <option value="parade">RGB Parade</option>
      </select>

      <div class="scope-controls">
        <label class="brightness-label">
          <span>Brightness</span>
          <input
            type="range"
            v-model.number="brightness"
            min="0.5"
            max="3"
            step="0.1"
            class="brightness-slider"
          />
        </label>
      </div>
    </div>

    <div class="scope-container">
      <!-- Histogram -->
      <HistogramScope
        v-if="activeScope === 'histogram'"
        :data="histogramData"
        :brightness="brightness"
      />

      <!-- Waveform -->
      <WaveformScope
        v-else-if="activeScope === 'waveform'"
        :data="waveformData"
        :brightness="brightness"
      />

      <!-- Vectorscope -->
      <VectorscopeScope
        v-else-if="activeScope === 'vectorscope'"
        :data="vectorscopeData"
        :brightness="brightness"
        :showTargets="true"
        :showSkinLine="true"
      />

      <!-- RGB Parade -->
      <RGBParadeScope
        v-else-if="activeScope === 'parade'"
        :data="paradeData"
        :brightness="brightness"
      />

      <!-- Loading state -->
      <div v-if="isAnalyzing" class="scope-loading">
        <span>Analyzing...</span>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { onMounted, onUnmounted, ref, watch } from "vue";

// Types from worker
interface HistogramResult {
  red: number[];
  green: number[];
  blue: number[];
  luminance: number[];
  maxCount: number;
}

interface WaveformResult {
  lumaPoints: Float32Array;
  width: number;
  height: number;
}

interface VectorscopeResult {
  data: Uint32Array;
  maxCount: number;
  targets: {
    r: [number, number];
    y: [number, number];
    g: [number, number];
    c: [number, number];
    b: [number, number];
    m: [number, number];
    skinLine: [[number, number], [number, number]];
  };
}

interface ParadeResult {
  red: WaveformResult;
  green: WaveformResult;
  blue: WaveformResult;
}

//                                                                        // ui
const activeScope = ref<"histogram" | "waveform" | "vectorscope" | "parade">(
  "histogram",
);
const brightness = ref(1.5);
const isAnalyzing = ref(false);

// Scope data
const histogramData = ref<HistogramResult | null>(null);
const waveformData = ref<WaveformResult | null>(null);
const vectorscopeData = ref<VectorscopeResult | null>(null);
const paradeData = ref<ParadeResult | null>(null);

// Worker instance
let worker: Worker | null = null;
let animationFrameId: number | null = null;
let lastAnalysisTime = 0;
const ANALYSIS_INTERVAL = 100; // ms between analyses (10 fps for scopes)

// Initialize worker
onMounted(() => {
  try {
    worker = new Worker(new URL("@/workers/scopeWorker.ts", import.meta.url), {
      type: "module",
    });

    worker.onmessage = (e) => {
      const { type, payload } = e.data;

      if (type === "complete") {
        isAnalyzing.value = false;

        if (payload.histogram) {
          histogramData.value = payload.histogram;
        }
        if (payload.waveform) {
          waveformData.value = payload.waveform;
        }
        if (payload.vectorscope) {
          vectorscopeData.value = payload.vectorscope;
        }
        if (payload.parade) {
          paradeData.value = payload.parade;
        }
      } else if (type === "error") {
        console.error("Scope worker error:", payload.error);
        isAnalyzing.value = false;
      }
    };

    // Start analysis loop
    startAnalysisLoop();
  } catch (error) {
    console.error("Failed to create scope worker:", error);
  }
});

onUnmounted(() => {
  if (worker) {
    worker.terminate();
    worker = null;
  }
  if (animationFrameId !== null) {
    cancelAnimationFrame(animationFrameId);
  }
});

// Watch for scope changes to request appropriate data
watch(activeScope, () => {
  requestAnalysis();
});

// Analysis loop
function startAnalysisLoop() {
  const loop = () => {
    const now = performance.now();

    if (now - lastAnalysisTime >= ANALYSIS_INTERVAL) {
      requestAnalysis();
      lastAnalysisTime = now;
    }

    animationFrameId = requestAnimationFrame(loop);
  };

  loop();
}

// Request analysis from worker
function requestAnalysis() {
  if (!worker || isAnalyzing.value) return;

  // Get current frame image data from engine (throws explicit error if unavailable)
  let imageData: ImageData;
  try {
    imageData = getCanvasImageData();
  } catch (error) {
    // Canvas not available - skip analysis (expected state)
    console.warn("[ScopesPanel] Cannot analyze scopes:", error instanceof Error ? error.message : String(error));
    return;
  }

  isAnalyzing.value = true;

  // Determine which scopes to compute
  const scopes: ("histogram" | "waveform" | "vectorscope" | "parade")[] = [
    activeScope.value,
  ];

  worker.postMessage({
    type: "analyze",
    payload: {
      imageData: imageData.data,
      width: imageData.width,
      height: imageData.height,
      scopes,
    },
  });
}

/**
 * Get image data from the canvas
 * 
 * System F/Omega proof: Explicit error throwing - never return null
 * Type proof: → ImageData (non-nullable)
 * Mathematical proof: Canvas image data retrieval must succeed or throw explicit error
 * Pattern proof: Missing canvas or context is an explicit error condition
 */
function getCanvasImageData(): ImageData {
  // Try to get canvas from engine
  const canvas = document.querySelector(
    ".three-canvas canvas",
  ) as HTMLCanvasElement;
  
  // System F/Omega: Throw explicit error when canvas not found
  if (!canvas) {
    throw new Error(
      `[ScopesPanel] Cannot get canvas image data: Canvas not found. ` +
      `Canvas element ".three-canvas canvas" must exist in the DOM. ` +
      `Wrap in try/catch if "canvas not ready" is an expected state.`
    );
  }

  try {
    const ctx = canvas.getContext("2d", { willReadFrequently: true });
    if (ctx) {
      return ctx.getImageData(0, 0, canvas.width, canvas.height);
    }

    // For WebGL canvas, we need to read pixels differently
    const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
    if (gl) {
      const width = canvas.width;
      const height = canvas.height;
      const pixels = new Uint8Array(width * height * 4);

      gl.readPixels(0, 0, width, height, gl.RGBA, gl.UNSIGNED_BYTE, pixels);

      // WebGL reads from bottom-left, flip vertically
      const flipped = new Uint8ClampedArray(width * height * 4);
      for (let y = 0; y < height; y++) {
        const srcRow = (height - y - 1) * width * 4;
        const dstRow = y * width * 4;
        for (let x = 0; x < width * 4; x++) {
          flipped[dstRow + x] = pixels[srcRow + x];
        }
      }

      return new ImageData(flipped, width, height);
    }
    
    // System F/Omega: Throw explicit error when no context is available
    throw new Error(
      `[ScopesPanel] Cannot get canvas image data: No canvas context available. ` +
      `Canvas dimensions: ${canvas.width}x${canvas.height}. ` +
      `Canvas must have a 2D, WebGL, or WebGL2 context available.`
    );
  } catch (error) {
    // System F/Omega: Re-throw error with context instead of returning null
    if (error instanceof Error && error.message.startsWith("[ScopesPanel]")) {
      throw error;
    }
    const errorMessage = error instanceof Error ? error.message : String(error);
    throw new Error(
      `[ScopesPanel] Cannot get canvas image data: Failed to read pixels. ` +
      `Canvas dimensions: ${canvas.width}x${canvas.height}, error: ${errorMessage}. ` +
      `Wrap in try/catch if "read failure" is an expected state.`
    );
  }
}
</script>

<style scoped>
.scopes-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  min-height: 200px;
  background: var(--lattice-surface-1);
}

.scope-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 8px;
  border-bottom: 1px solid var(--lattice-border-subtle);
  background: var(--lattice-surface-0);
}

.scope-select {
  padding: 4px 8px;
  background: var(--lattice-surface-2);
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-primary);
  font-size: var(--lattice-font-size-sm);
  cursor: pointer;
}

.scope-select:hover {
  border-color: var(--lattice-accent);
}

.scope-controls {
  display: flex;
  align-items: center;
  gap: 12px;
}

.brightness-label {
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: var(--lattice-font-size-xs);
  color: var(--lattice-text-secondary);
}

.brightness-slider {
  width: 80px;
  height: 4px;
  -webkit-appearance: none;
  appearance: none;
  background: var(--lattice-surface-3);
  border-radius: 2px;
  cursor: pointer;
}

.brightness-slider::-webkit-slider-thumb {
  -webkit-appearance: none;
  width: 12px;
  height: 12px;
  background: var(--lattice-accent);
  border-radius: 50%;
  cursor: pointer;
}

.scope-container {
  flex: 1;
  position: relative;
  min-height: 150px;
  background: #000;
  overflow: hidden;
}

.scope-loading {
  position: absolute;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
  color: var(--lattice-text-muted);
  font-size: var(--lattice-font-size-sm);
}
</style>
