<!--
  @component LayerDecompositionPanel
  @description AI-powered image layer decomposition using Qwen-Image-Layered model.
  Decomposes a single image into multiple RGBA layers with automatic depth-based z-space placement.

  @features
  - Model download with progress tracking and hash verification
  - Configurable layer count (3-16)
  - LLM-based depth estimation (GPT-4o / Claude)
  - Automatic z-space positioning
  - Progress visualization
  - Layer preview grid

  @requires Qwen-Image-Layered model (28.8GB download)
-->
<template>
  <div class="layer-decomposition-panel" role="region" aria-label="AI Layer Decomposition">
    <div class="panel-header">
      <span class="panel-title">Layer Decomposition</span>
      <span class="badge" :class="modelStatusClass">{{ modelStatusText }}</span>
    </div>

    <div class="panel-content">
      <!-- Model Status Section -->
      <div class="section model-status-section">
        <div class="section-header">Model Status</div>

        <!-- Not Downloaded -->
        <div v-if="!modelStatus.downloaded" class="model-not-downloaded">
          <p class="warning-text">
            <i class="pi pi-exclamation-triangle" />
            Qwen-Image-Layered model not downloaded
          </p>
          <p class="size-info">Download size: <strong>28.8 GB</strong></p>

          <button
            class="download-btn"
            @click="startDownload"
            :disabled="isDownloading"
          >
            <i :class="isDownloading ? 'pi pi-spin pi-spinner' : 'pi pi-download'" />
            {{ isDownloading ? 'Downloading...' : 'Download Model' }}
          </button>

          <!-- Download Progress -->
          <div v-if="isDownloading" class="download-progress">
            <div class="progress-bar">
              <div class="progress-fill" :style="{ width: downloadProgress + '%' }" />
            </div>
            <div class="progress-info">
              <span>{{ downloadStage }}</span>
              <span>{{ downloadProgress.toFixed(1) }}%</span>
            </div>
          </div>
        </div>

        <!-- Downloaded -->
        <div v-else class="model-ready">
          <div class="status-row">
            <i class="pi pi-check-circle ready-icon" />
            <span>Model Ready</span>
            <span v-if="modelStatus.loaded" class="loaded-badge">Loaded</span>
          </div>
          <div v-if="modelStatus.verification" class="verification-info">
            <span :class="modelStatus.verification.verified ? 'verified' : 'unverified'">
              {{ modelStatus.verification.message }}
            </span>
          </div>
        </div>
      </div>

      <!-- Image Upload Section -->
      <div class="section upload-section" :class="{ disabled: !modelStatus.downloaded }">
        <div class="section-header">Source Image</div>

        <div class="upload-area" @click="triggerFileSelect" @drop.prevent="handleDrop" @dragover.prevent>
          <input
            type="file"
            ref="fileInput"
            accept="image/*"
            @change="handleFileSelect"
            style="display: none"
          />

          <div v-if="!previewUrl" class="upload-placeholder">
            <i class="pi pi-image" />
            <span>Click or drop image</span>
          </div>

          <img v-else :src="previewUrl" class="preview-image" alt="Source image" />
        </div>

        <div v-if="previewUrl" class="image-actions">
          <button class="clear-btn" @click="clearImage">
            <i class="pi pi-times" /> Clear
          </button>
        </div>
      </div>

      <!-- Options Section -->
      <div class="section options-section" :class="{ disabled: !previewUrl }">
        <div class="section-header">Options</div>

        <div class="option-row">
          <label>Number of Layers</label>
          <input
            type="range"
            v-model.number="numLayers"
            min="3"
            max="10"
            step="1"
          />
          <span class="value">{{ numLayers }}</span>
        </div>

        <div class="option-row checkbox">
          <input type="checkbox" v-model="autoDepth" id="autoDepth" />
          <label for="autoDepth">AI Depth Estimation</label>
        </div>

        <div v-if="autoDepth" class="option-row">
          <label>AI Provider</label>
          <select v-model="depthProvider">
            <option value="openai">GPT-4o</option>
            <option value="anthropic">Claude</option>
          </select>
        </div>

        <div class="option-row">
          <label>Z-Space Scale</label>
          <input
            type="number"
            v-model.number="zScale"
            min="100"
            max="2000"
            step="100"
          />
          <span class="unit">units</span>
        </div>

        <div class="option-row checkbox">
          <input type="checkbox" v-model="autoUnload" id="autoUnload" />
          <label for="autoUnload">Auto-unload model after</label>
        </div>
      </div>

      <!-- Decompose Button -->
      <div class="action-section">
        <button
          class="decompose-btn"
          @click="startDecomposition"
          :disabled="!canDecompose"
        >
          <i :class="isDecomposing ? 'pi pi-spin pi-spinner' : 'pi pi-bolt'" />
          {{ isDecomposing ? 'Decomposing...' : 'Decompose Image' }}
        </button>
      </div>

      <!-- Progress Section -->
      <div v-if="isDecomposing" class="progress-section">
        <div class="progress-bar">
          <div class="progress-fill" :style="{ width: decomposeProgress + '%' }" />
        </div>
        <div class="progress-message">{{ progressMessage }}</div>
      </div>

      <!-- Results Section -->
      <div v-if="result && result.success" class="results-section">
        <div class="section-header">
          Created {{ result.layers.length }} Layers
        </div>

        <div class="layer-grid">
          <div
            v-for="layer in result.layers"
            :key="layer.id"
            class="layer-card"
            @click="selectLayer(layer.id)"
          >
            <div class="layer-name">{{ layer.name }}</div>
            <div class="layer-depth">
              Z: {{ getLayerZ(layer).toFixed(0) }}
            </div>
          </div>
        </div>

        <div v-if="result.depthEstimation" class="depth-info">
          <p>{{ result.depthEstimation.sceneDescription }}</p>
          <p class="depth-range">
            Depth range: {{ result.depthEstimation.depthRange.near.toFixed(0) }} -
            {{ result.depthEstimation.depthRange.far.toFixed(0) }}
          </p>
        </div>
      </div>

      <!-- Error Section -->
      <div v-if="errorMessage" class="error-section">
        <i class="pi pi-exclamation-circle" />
        <span>{{ errorMessage }}</span>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref } from "vue";
import type { LLMProvider } from "@/services/ai/depthEstimation";
import {
  type DecompositionModelStatus,
  getLayerDecompositionService,
} from "@/services/layerDecomposition";
import {
  type DecompositionResult,
  useDecompositionStore,
} from "@/stores/decompositionStore";
import { useLayerStore } from "@/stores/layerStore";
import type { Layer } from "@/types/project";

const layerStore = useLayerStore();
const service = getLayerDecompositionService();

// State
const modelStatus = ref<Partial<DecompositionModelStatus>>({
  downloaded: false,
  loaded: false,
  loading: false,
});
const isDownloading = ref(false);
const downloadProgress = ref(0);
const downloadStage = ref("");

const fileInput = ref<HTMLInputElement | null>(null);
const selectedFile = ref<File | null>(null);
const previewUrl = ref<string | null>(null);

const numLayers = ref(5);
const autoDepth = ref(true);
const depthProvider = ref<LLMProvider>("openai");
const zScale = ref(500);
const autoUnload = ref(true);

const isDecomposing = ref(false);
const decomposeProgress = ref(0);
const progressMessage = ref("");
const result = ref<DecompositionResult | null>(null);
const errorMessage = ref<string | null>(null);

// Computed
const modelStatusClass = computed(() => {
  if (modelStatus.value.loaded) return "loaded";
  if (modelStatus.value.downloaded) return "ready";
  return "not-ready";
});

const modelStatusText = computed(() => {
  if (modelStatus.value.loaded) return "Loaded";
  if (modelStatus.value.downloaded) return "Ready";
  return "Not Downloaded";
});

const canDecompose = computed(() => {
  return (
    modelStatus.value.downloaded && previewUrl.value && !isDecomposing.value
  );
});

// Methods
async function checkStatus() {
  try {
    const status = await service.getStatus();
    modelStatus.value = status;
  } catch (error) {
    console.warn("Failed to check model status:", error);
  }
}

async function startDownload() {
  isDownloading.value = true;
  downloadProgress.value = 0;
  downloadStage.value = "Starting...";
  errorMessage.value = null;

  const decompositionStore = useDecompositionStore();
  try {
    await decompositionStore.downloadDecompositionModel((progress) => {
      downloadProgress.value = progress.percent;
      downloadStage.value = progress.stage;
    });

    await checkStatus();
  } catch (error) {
    errorMessage.value =
      error instanceof Error ? error.message : "Download failed";
  } finally {
    isDownloading.value = false;
  }
}

function triggerFileSelect() {
  if (!modelStatus.value.downloaded) return;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const fileInputVal = fileInput.value;
  if (fileInputVal != null && typeof fileInputVal === "object" && typeof fileInputVal.click === "function") {
    fileInputVal.click();
  }
}

function handleFileSelect(event: Event) {
  const input = event.target as HTMLInputElement;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const files = (input != null && typeof input === "object" && "files" in input && input.files != null && input.files.length > 0) ? input.files : null;
  const file = (files != null && files.length > 0) ? files[0] : undefined;
  if (file) {
    selectedFile.value = file;
    previewUrl.value = URL.createObjectURL(file);
    result.value = null;
    errorMessage.value = null;
  }
}

function handleDrop(event: DragEvent) {
  if (!modelStatus.value.downloaded) return;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  const files = (dataTransfer != null && typeof dataTransfer === "object" && "files" in dataTransfer && dataTransfer.files != null && dataTransfer.files.length > 0) ? dataTransfer.files : null;
  const file = (files != null && files.length > 0) ? files[0] : undefined;
  const fileType = (file != null && typeof file === "object" && "type" in file && typeof file.type === "string") ? file.type : undefined;
  if (fileType != null && fileType.startsWith("image/")) {
    selectedFile.value = file;
    previewUrl.value = URL.createObjectURL(file);
    result.value = null;
    errorMessage.value = null;
  }
}

function clearImage() {
  if (previewUrl.value) {
    URL.revokeObjectURL(previewUrl.value);
  }
  selectedFile.value = null;
  previewUrl.value = null;
  result.value = null;
}

async function startDecomposition() {
  if (!previewUrl.value || !selectedFile.value) return;

  isDecomposing.value = true;
  decomposeProgress.value = 0;
  progressMessage.value = "Starting...";
  errorMessage.value = null;
  result.value = null;

  try {
    // Convert file to data URL
    const imageDataUrl = await fileToDataUrl(selectedFile.value);

    // Run decomposition
    const decompositionStore = useDecompositionStore();
    const decompositionResult = await decompositionStore.decomposeImageToLayers(
      store,
      imageDataUrl,
      {
        numLayers: numLayers.value,
        autoDepthEstimation: autoDepth.value,
        depthProvider: depthProvider.value,
        zSpaceScale: zScale.value,
        autoUnload: autoUnload.value,
        onProgress: (_stage, message, progress) => {
          progressMessage.value = message;
          if (progress !== undefined) {
            decomposeProgress.value = progress;
          }
        },
        groupLayers: true,
        groupName: `Decomposed: ${selectedFile.value.name}`,
      },
    );

    result.value = decompositionResult;

    if (!decompositionResult.success) {
      errorMessage.value = decompositionResult.error || "Decomposition failed";
    }
  } catch (error) {
    errorMessage.value =
      error instanceof Error ? error.message : "Decomposition failed";
  } finally {
    isDecomposing.value = false;
  }
}

function fileToDataUrl(file: File): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(reader.result as string);
    reader.onerror = reject;
    reader.readAsDataURL(file);
  });
}

function selectLayer(layerId: string) {
  layerStore.selectLayer(layerId, false);
}

function getLayerZ(layer: Layer): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const transform = (layer != null && typeof layer === "object" && "transform" in layer && layer.transform != null && typeof layer.transform === "object") ? layer.transform : undefined;
  const position = (transform != null && typeof transform === "object" && "position" in transform && transform.position != null && typeof transform.position === "object") ? transform.position : undefined;
  const positionValue = (position != null && typeof position === "object" && "value" in position && position.value != null && typeof position.value === "object") ? position.value : undefined;
  const zValue = (positionValue != null && typeof positionValue === "object" && "z" in positionValue && typeof positionValue.z === "number") ? positionValue.z : undefined;
  if (zValue != null) return zValue;
  const positionDefaultValue = (position != null && typeof position === "object" && "defaultValue" in position && position.defaultValue != null && typeof position.defaultValue === "object") ? position.defaultValue : undefined;
  const zDefaultValue = (positionDefaultValue != null && typeof positionDefaultValue === "object" && "z" in positionDefaultValue && typeof positionDefaultValue.z === "number") ? positionDefaultValue.z : undefined;
  if (zDefaultValue != null) return zDefaultValue;
  return 0;
}

// Lifecycle
onMounted(() => {
  checkStatus();
});

onUnmounted(() => {
  if (previewUrl.value) {
    URL.revokeObjectURL(previewUrl.value);
  }
});
</script>

<style scoped>
.layer-decomposition-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1);
  color: var(--lattice-text-primary);
  font-size: 0.875rem;
}

.panel-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 8px 12px;
  border-bottom: 1px solid var(--lattice-border-subtle);
  background: var(--lattice-surface-2);
}

.panel-title {
  font-weight: 600;
}

.badge {
  padding: 2px 8px;
  border-radius: var(--lattice-radius-pill);
  font-size: 0.75rem;
  font-weight: 500;
}

.badge.loaded {
  background: rgba(16, 185, 129, 0.2);
  color: #10B981;
}

.badge.ready {
  background: rgba(139, 92, 246, 0.2);
  color: var(--lattice-accent);
}

.badge.not-ready {
  background: rgba(239, 68, 68, 0.2);
  color: #EF4444;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  padding: 12px;
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.section {
  background: var(--lattice-surface-2);
  border-radius: var(--lattice-radius-md);
  padding: 12px;
}

.section.disabled {
  opacity: 0.5;
  pointer-events: none;
}

.section-header {
  font-weight: 600;
  margin-bottom: 8px;
  color: var(--lattice-text-secondary);
  font-size: 0.75rem;
  text-transform: uppercase;
  letter-spacing: 0.05em;
}

/* Model Status */
.model-not-downloaded {
  text-align: center;
}

.warning-text {
  color: #F59E0B;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
  margin-bottom: 8px;
}

.size-info {
  color: var(--lattice-text-secondary);
  margin-bottom: 12px;
}

.download-btn {
  width: 100%;
  padding: 10px 16px;
  background: var(--lattice-accent);
  color: white;
  border: none;
  border-radius: var(--lattice-radius-md);
  font-weight: 500;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
  transition: background 0.2s;
}

.download-btn:hover:not(:disabled) {
  background: var(--lattice-accent-hover);
}

.download-btn:disabled {
  opacity: 0.7;
  cursor: not-allowed;
}

.download-progress {
  margin-top: 12px;
}

.progress-bar {
  height: 6px;
  background: var(--lattice-surface-3);
  border-radius: 3px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: var(--lattice-accent-gradient);
  transition: width 0.3s ease;
}

.progress-info {
  display: flex;
  justify-content: space-between;
  font-size: 0.75rem;
  color: var(--lattice-text-secondary);
  margin-top: 4px;
}

.model-ready .status-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.ready-icon {
  color: #10B981;
}

.loaded-badge {
  font-size: 0.7rem;
  padding: 2px 6px;
  background: rgba(16, 185, 129, 0.2);
  color: #10B981;
  border-radius: var(--lattice-radius-pill);
}

.verification-info {
  margin-top: 4px;
  font-size: 0.75rem;
}

.verified {
  color: #10B981;
}

.unverified {
  color: #F59E0B;
}

/* Upload Area */
.upload-area {
  border: 2px dashed var(--lattice-border-default);
  border-radius: var(--lattice-radius-md);
  padding: 24px;
  text-align: center;
  cursor: pointer;
  transition: border-color 0.2s, background 0.2s;
  min-height: 150px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.upload-area:hover {
  border-color: var(--lattice-accent);
  background: var(--lattice-surface-3);
}

.upload-placeholder {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 8px;
  color: var(--lattice-text-muted);
}

.upload-placeholder i {
  font-size: 2rem;
}

.preview-image {
  max-width: 100%;
  max-height: 200px;
  object-fit: contain;
  border-radius: var(--lattice-radius-sm);
}

.image-actions {
  margin-top: 8px;
  text-align: center;
}

.clear-btn {
  padding: 4px 12px;
  background: transparent;
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-secondary);
  cursor: pointer;
  font-size: 0.75rem;
}

.clear-btn:hover {
  background: var(--lattice-surface-3);
}

/* Options */
.option-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.option-row label {
  flex: 1;
  color: var(--lattice-text-secondary);
}

.option-row.checkbox {
  justify-content: flex-start;
}

.option-row.checkbox label {
  flex: none;
}

.option-row input[type="range"] {
  flex: 1;
  max-width: 120px;
}

.option-row input[type="number"] {
  width: 80px;
  padding: 4px 8px;
  background: var(--lattice-surface-3);
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-primary);
}

.option-row select {
  flex: 1;
  max-width: 150px;
  padding: 4px 8px;
  background: var(--lattice-surface-3);
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-primary);
}

.option-row .value,
.option-row .unit {
  font-size: 0.75rem;
  color: var(--lattice-text-muted);
  min-width: 40px;
}

/* Action Button */
.action-section {
  padding: 0 12px;
}

.decompose-btn {
  width: 100%;
  padding: 12px 16px;
  background: var(--lattice-accent-gradient);
  color: white;
  border: none;
  border-radius: var(--lattice-radius-md);
  font-weight: 600;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
  transition: opacity 0.2s, transform 0.1s;
}

.decompose-btn:hover:not(:disabled) {
  opacity: 0.9;
}

.decompose-btn:active:not(:disabled) {
  transform: scale(0.98);
}

.decompose-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

/* Progress */
.progress-section {
  background: var(--lattice-surface-2);
  border-radius: var(--lattice-radius-md);
  padding: 12px;
}

.progress-message {
  font-size: 0.75rem;
  color: var(--lattice-text-secondary);
  margin-top: 8px;
  text-align: center;
}

/* Results */
.results-section {
  background: var(--lattice-surface-2);
  border-radius: var(--lattice-radius-md);
  padding: 12px;
}

.layer-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(100px, 1fr));
  gap: 8px;
  margin-top: 8px;
}

.layer-card {
  background: var(--lattice-surface-3);
  border-radius: var(--lattice-radius-sm);
  padding: 8px;
  cursor: pointer;
  transition: background 0.2s;
}

.layer-card:hover {
  background: var(--lattice-surface-4);
}

.layer-name {
  font-weight: 500;
  font-size: 0.8rem;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.layer-depth {
  font-size: 0.7rem;
  color: var(--lattice-text-muted);
}

.depth-info {
  margin-top: 12px;
  padding-top: 8px;
  border-top: 1px solid var(--lattice-border-subtle);
  font-size: 0.75rem;
  color: var(--lattice-text-secondary);
}

.depth-range {
  color: var(--lattice-text-muted);
}

/* Error */
.error-section {
  background: rgba(239, 68, 68, 0.1);
  border: 1px solid rgba(239, 68, 68, 0.3);
  border-radius: var(--lattice-radius-md);
  padding: 12px;
  color: #EF4444;
  display: flex;
  align-items: center;
  gap: 8px;
}
</style>
