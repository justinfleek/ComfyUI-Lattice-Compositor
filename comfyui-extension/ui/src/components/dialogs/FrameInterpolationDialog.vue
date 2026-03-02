<template>
  <div class="frame-interpolation-dialog-overlay" @click.self="emit('close')">
    <div class="frame-interpolation-dialog">
      <div class="dialog-header">
        <h3>Frame Interpolation (RIFE)</h3>
        <button class="close-btn" @click="emit('close')">
          <i class="pi pi-times" />
        </button>
      </div>

      <div class="dialog-content">
        <!-- Backend Status -->
        <div v-if="!backendAvailable" class="status-warning">
          <i class="pi pi-exclamation-triangle" />
          <span>RIFE backend not available. Using client-side blending (lower quality).</span>
        </div>

        <!-- Mode Selection -->
        <div class="form-group">
          <label>Mode</label>
          <div class="mode-options">
            <button
              class="mode-btn"
              :class="{ active: mode === 'upscale' }"
              @click="mode = 'upscale'"
            >
              <i class="pi pi-chart-line" />
              <span>Frame Rate Upscale</span>
              <small>Increase frame rate (24 → 48/60 fps)</small>
            </button>
            <button
              class="mode-btn"
              :class="{ active: mode === 'slowmo' }"
              @click="mode = 'slowmo'"
            >
              <i class="pi pi-clock" />
              <span>Slow Motion</span>
              <small>Create smooth slow-mo effect</small>
            </button>
          </div>
        </div>

        <!-- Frame Range -->
        <div class="form-group">
          <label>Frame Range</label>
          <div class="range-inputs">
            <div class="range-input">
              <label>Start</label>
              <input
                v-model.number="startFrame"
                type="number"
                :min="0"
                :max="projectStore.getFrameCount() - 1"
              />
            </div>
            <span class="range-separator">to</span>
            <div class="range-input">
              <label>End</label>
              <input
                v-model.number="endFrame"
                type="number"
                :min="startFrame"
                :max="projectStore.getFrameCount() - 1"
              />
            </div>
          </div>
          <p class="frame-info">
            {{ frameRangeCount }} frames selected
          </p>
        </div>

        <!-- Factor Selection -->
        <div class="form-group">
          <label>{{ mode === 'upscale' ? 'Multiplication Factor' : 'Slowdown Factor' }}</label>
          <div class="factor-options">
            <button
              v-for="f in availableFactors"
              :key="f.value"
              class="factor-btn"
              :class="{ active: factor === f.value }"
              @click="factor = f.value"
            >
              {{ f.label }}
            </button>
          </div>
          <p class="factor-info">
            <template v-if="mode === 'upscale'">
              Output: ~{{ estimatedOutputFrames }} frames ({{ estimatedFps }} fps)
            </template>
            <template v-else>
              Duration: {{ slowmoDuration }}x slower
            </template>
          </p>
        </div>

        <!-- Model Selection -->
        <div class="form-group">
          <label>Model</label>
          <select v-model="selectedModel" class="model-select">
            <option v-for="m in models" :key="m.id" :value="m.id">
              {{ m.name }} {{ m.recommended ? '(Recommended)' : '' }}
            </option>
          </select>
          <p class="model-info">
            {{ currentModelDescription }}
          </p>
        </div>

        <!-- Ensemble Option -->
        <div v-if="currentModelSupportsEnsemble" class="form-group">
          <label class="checkbox-label">
            <input type="checkbox" v-model="useEnsemble" />
            <span>Use Ensemble Mode</span>
          </label>
          <p class="ensemble-info">
            Higher quality but 2x slower processing
          </p>
        </div>

        <!-- Progress -->
        <div v-if="isProcessing" class="progress-section">
          <div class="progress-bar">
            <div
              class="progress-fill"
              :style="{ width: `${progress}%` }"
            />
          </div>
          <p class="progress-text">{{ progressMessage }}</p>
        </div>

        <!-- Result Preview -->
        <div v-if="resultPreview" class="result-section">
          <label>Result Preview</label>
          <div class="result-preview">
            <img :src="resultPreview" alt="Interpolation result preview" />
          </div>
          <p class="result-info">
            Generated {{ resultFrameCount }} frames
          </p>
        </div>
      </div>

      <div class="dialog-footer">
        <div class="footer-info">
          <span v-if="backendAvailable">RIFE {{ selectedModel }}</span>
          <span v-else>Client-side blending</span>
        </div>
        <button class="cancel-btn" @click="emit('close')" :disabled="isProcessing">
          Cancel
        </button>
        <button
          class="process-btn"
          @click="startProcessing"
          :disabled="isProcessing || !canProcess"
        >
          <i class="pi pi-play" />
          {{ isProcessing ? 'Processing...' : 'Interpolate' }}
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, ref } from "vue";
import {
  type InterpolationFactor,
  type InterpolationModel,
  type RIFEModel,
  createSlowMotion,
  getInterpolationModels,
  interpolateSequence,
  isInterpolationAvailable,
} from "@/services/video/frameInterpolation";
import { useProjectStore } from "@/stores/projectStore";

const emit = defineEmits<{
  (e: "close"): void;
  (e: "complete", frames: string[]): void;
}>();

const projectStore = useProjectStore();

// State
const backendAvailable = ref(false);
const models = ref<InterpolationModel[]>([]);
const mode = ref<"upscale" | "slowmo">("upscale");
const startFrame = ref(0);
const endFrame = ref(Math.min(30, projectStore.getFrameCount() - 1));
const factor = ref<number>(2);
const selectedModel = ref<RIFEModel>("rife-v4.6");
const useEnsemble = ref(false);
const isProcessing = ref(false);
const progress = ref(0);
const progressMessage = ref("");
const resultPreview = ref<string | null>(null);
const resultFrameCount = ref(0);

// Computed
const frameRangeCount = computed(() => endFrame.value - startFrame.value + 1);

const availableFactors = computed(() => {
  if (mode.value === "upscale") {
    return [
      { value: 2, label: "2x" },
      { value: 4, label: "4x" },
      { value: 8, label: "8x" },
    ];
  } else {
    return [
      { value: 2, label: "2x Slow" },
      { value: 4, label: "4x Slow" },
      { value: 8, label: "8x Slow" },
    ];
  }
});

const estimatedOutputFrames = computed(() => {
  const count = frameRangeCount.value;
  return count * factor.value - (factor.value - 1);
});

const estimatedFps = computed(() => {
  const baseFps = projectStore.getFps();
  return baseFps * factor.value;
});

const slowmoDuration = computed(() => factor.value);

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
const currentModelDescription = computed(() => {
  const model = models.value.find((m) => m.id === selectedModel.value);
  return (model !== null && model !== undefined && typeof model === "object" && "description" in model && typeof model.description === "string") ? model.description : "Select a model";
});

const currentModelSupportsEnsemble = computed(() => {
  const model = models.value.find((m) => m.id === selectedModel.value);
  return (model !== null && model !== undefined && typeof model === "object" && "supports_ensemble" in model && typeof model.supports_ensemble === "boolean") ? model.supports_ensemble : false;
});

const canProcess = computed(() => {
  return frameRangeCount.value >= 2;
});

// Methods
async function startProcessing() {
  if (isProcessing.value || !canProcess.value) return;

  isProcessing.value = true;
  progress.value = 0;
  progressMessage.value = "Preparing frames...";

  try {
    // Collect frames from the compositor
    const frames = await collectFrames();

    if (frames.length < 2) {
      throw new Error("Need at least 2 frames for interpolation");
    }

    progressMessage.value = `Processing ${frames.length} frames...`;

    let result;

    if (mode.value === "upscale") {
      result = await interpolateSequence(frames, {
        factor: factor.value as InterpolationFactor,
        model: selectedModel.value,
        ensemble: useEnsemble.value,
      });
    } else {
      result = await createSlowMotion(
        frames,
        factor.value,
        selectedModel.value,
      );
    }

    if (result.status === "success" && result.frames) {
      resultFrameCount.value = result.frames.length;

      // Show first frame as preview
      if (result.frames.length > 0) {
        resultPreview.value = `data:image/png;base64,${result.frames[0]}`;
      }

      progressMessage.value = `Complete! Generated ${result.frames.length} frames`;
      progress.value = 100;

      emit("complete", result.frames);
    } else {
      throw new Error(result.message || "Interpolation failed");
    }
  } catch (error) {
    console.error("[FrameInterpolation] Error:", error);
    progressMessage.value = `Error: ${error instanceof Error ? error.message : "Unknown error"}`;
  } finally {
    isProcessing.value = false;
  }
}

async function collectFrames(): Promise<string[]> {
  const frames: string[] = [];
  interface LatticeEngineGlobal {
    __latticeEngine?: {
      renderFrameToCanvas?: (frame: number, width: number, height: number) => Promise<HTMLCanvasElement>;
    };
  }
  const engine = (window as LatticeEngineGlobal).__latticeEngine;

  for (let i = startFrame.value; i <= endFrame.value; i++) {
    progress.value = ((i - startFrame.value) / frameRangeCount.value) * 30;
    progressMessage.value = `Collecting frame ${i - startFrame.value + 1}/${frameRangeCount.value}`;

    let frameData: string;

    if (engine && typeof engine.renderFrameToCanvas === "function") {
      const canvas = await engine.renderFrameToCanvas(
        i,
        projectStore.getWidth(),
        projectStore.getHeight(),
      );
      frameData = canvas.toDataURL("image/png").split(",")[1];
    } else {
      // Fallback: create a placeholder
      const canvas = document.createElement("canvas");
      canvas.width = projectStore.getWidth();
      canvas.height = projectStore.getHeight();
      const ctx = canvas.getContext("2d")!;
      ctx.fillStyle = "#333";
      ctx.fillRect(0, 0, canvas.width, canvas.height);
      ctx.fillStyle = "#fff";
      ctx.font = "24px sans-serif";
      ctx.textAlign = "center";
      ctx.fillText(`Frame ${i}`, canvas.width / 2, canvas.height / 2);
      frameData = canvas.toDataURL("image/png").split(",")[1];
    }

    frames.push(frameData);
  }

  return frames;
}

// Initialize
onMounted(async () => {
  // Check backend availability
  backendAvailable.value = await isInterpolationAvailable();

  // Get available models
  models.value = await getInterpolationModels();

  // Set recommended model as default
  const recommended = models.value.find((m) => m.recommended);
  if (recommended) {
    selectedModel.value = recommended.id;
  }

  // Set initial frame range
  endFrame.value = Math.min(projectStore.getFrameCount() - 1, startFrame.value + 30);
});
</script>

<style scoped>
.frame-interpolation-dialog-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.6);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.frame-interpolation-dialog {
  width: 500px;
  max-height: 90vh;
  background: #2a2a2a;
  border-radius: 8px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.4);
  display: flex;
  flex-direction: column;
}

.dialog-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 12px 16px;
  border-bottom: 1px solid #3d3d3d;
}

.dialog-header h3 {
  margin: 0;
  font-size: 14px;
  font-weight: 500;
  color: #e0e0e0;
}

.close-btn {
  padding: 4px 8px;
  border: none;
  background: transparent;
  color: #888;
  cursor: pointer;
}

.close-btn:hover {
  color: #fff;
}

.dialog-content {
  flex: 1;
  overflow-y: auto;
  padding: 16px;
}

.status-warning {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 10px 12px;
  background: rgba(255, 193, 7, 0.1);
  border: 1px solid rgba(255, 193, 7, 0.3);
  border-radius: 4px;
  margin-bottom: 16px;
  color: #ffc107;
  font-size: 13px;
}

.form-group {
  margin-bottom: 20px;
}

.form-group > label {
  display: block;
  font-size: 12px;
  font-weight: 500;
  color: #aaa;
  margin-bottom: 8px;
}

.mode-options {
  display: flex;
  gap: 12px;
}

.mode-btn {
  flex: 1;
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 6px;
  padding: 12px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  border-radius: 6px;
  cursor: pointer;
  transition: all 0.1s;
}

.mode-btn:hover {
  background: #333;
}

.mode-btn.active {
  background: rgba(74, 144, 217, 0.2);
  border-color: #4a90d9;
}

.mode-btn i {
  font-size: 20px;
  color: #666;
}

.mode-btn.active i {
  color: #4a90d9;
}

.mode-btn span {
  font-size: 13px;
  font-weight: 500;
  color: #e0e0e0;
}

.mode-btn small {
  font-size: 11px;
  color: #666;
  text-align: center;
}

.range-inputs {
  display: flex;
  align-items: flex-end;
  gap: 12px;
}

.range-input {
  flex: 1;
}

.range-input label {
  display: block;
  font-size: 11px;
  color: #666;
  margin-bottom: 4px;
}

.range-input input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 13px;
}

.range-separator {
  color: #666;
  padding-bottom: 6px;
}

.frame-info,
.factor-info,
.model-info,
.ensemble-info,
.result-info {
  margin-top: 6px;
  font-size: 12px;
  color: #666;
}

.factor-options {
  display: flex;
  gap: 8px;
}

.factor-btn {
  flex: 1;
  padding: 8px 12px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #aaa;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
  transition: all 0.1s;
}

.factor-btn:hover {
  background: #333;
  color: #fff;
}

.factor-btn.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.model-select {
  width: 100%;
  padding: 8px 12px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 13px;
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
}

.checkbox-label input {
  accent-color: #4a90d9;
}

.checkbox-label span {
  font-size: 13px;
  color: #e0e0e0;
}

.progress-section {
  padding: 12px;
  background: #1e1e1e;
  border-radius: 4px;
  margin-top: 16px;
}

.progress-bar {
  height: 8px;
  background: #333;
  border-radius: 4px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: #4a90d9;
  transition: width 0.2s;
}

.progress-text {
  margin-top: 8px;
  font-size: 12px;
  color: #aaa;
  text-align: center;
}

.result-section {
  margin-top: 16px;
}

.result-preview {
  width: 100%;
  height: 150px;
  background: #1e1e1e;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
  overflow: hidden;
}

.result-preview img {
  max-width: 100%;
  max-height: 100%;
  object-fit: contain;
}

.dialog-footer {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 12px 16px;
  border-top: 1px solid #3d3d3d;
}

.footer-info {
  flex: 1;
  font-size: 12px;
  color: #666;
}

.cancel-btn {
  padding: 8px 16px;
  border: 1px solid #3d3d3d;
  background: transparent;
  color: #aaa;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.cancel-btn:hover:not(:disabled) {
  background: #333;
  color: #fff;
}

.cancel-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.process-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 16px;
  border: none;
  background: #4a90d9;
  color: #fff;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.process-btn:hover:not(:disabled) {
  background: #5a9fe9;
}

.process-btn:disabled {
  background: #333;
  color: #666;
  cursor: not-allowed;
}
</style>
