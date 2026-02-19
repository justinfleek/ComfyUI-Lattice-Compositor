<!--
  @component AIGeneratePanel
  @description AI-powered generation tools for depth maps, normal maps, and segmentation.
  Uses ComfyUI backend models for processing.

  @features
  - Depth estimation (Depth Anything, MiDaS)
  - Normal map generation
  - Segmentation (SAM)
  - Layer selection for input
  - Live preview of results

  @requires ComfyUI backend with AI models installed
-->
<template>
  <div class="ai-generate-panel" role="region" aria-label="AI Generation Tools">
    <div class="panel-header">
      <span class="panel-title">AI Generate</span>
      <button class="refresh-btn" @click="refreshModels" title="Refresh model status">
        <i class="pi pi-refresh" />
      </button>
    </div>

    <div class="panel-content">
      <!-- Source Selection -->
      <div class="section">
        <div class="section-header">Source</div>
        <div class="source-options">
          <button
            :class="{ active: sourceType === 'layer' }"
            @click="sourceType = 'layer'"
          >
            Selected Layer
          </button>
          <button
            :class="{ active: sourceType === 'canvas' }"
            @click="sourceType = 'canvas'"
          >
            Canvas Frame
          </button>
          <button
            :class="{ active: sourceType === 'file' }"
            @click="sourceType = 'file'"
          >
            Upload File
          </button>
        </div>

        <div v-if="sourceType === 'layer'" class="layer-info">
          <span v-if="selectedLayerName">{{ selectedLayerName }}</span>
          <span v-else class="no-selection">No layer selected</span>
        </div>

        <div v-if="sourceType === 'file'" class="file-upload">
          <input
            type="file"
            ref="fileInput"
            accept="image/*"
            @change="handleFileSelect"
            style="display: none"
          />
          <button class="upload-btn" @click="handleFileInputClick()">
            Select Image...
          </button>
          <span v-if="uploadedFileName" class="file-name">{{ uploadedFileName }}</span>
        </div>
      </div>

      <!-- Generation Type -->
      <div class="section">
        <div class="section-header">Generation Type</div>
        <div class="generation-types">
          <button
            v-for="type in generationTypes"
            :key="type.id"
            :class="{ active: selectedType === type.id }"
            @click="selectedType = type.id"
            :title="type.description"
          >
            <span class="type-icon">{{ type.icon }}</span>
            <span class="type-label">{{ type.label }}</span>
          </button>
        </div>
      </div>

      <!-- Model Selection -->
      <div class="section">
        <div class="section-header">Model</div>
        <select v-model="selectedModel" class="model-select">
          <option v-for="model in availableModels" :key="model.type" :value="model.type">
            {{ model.name }}
          </option>
        </select>
        <div class="model-info" v-if="selectedModelInfo">
          <span class="memory-badge">{{ selectedModelInfo.memoryRequired }}MB</span>
          <span class="status-badge" :class="selectedModelInfo.status">
            {{ selectedModelInfo.status }}
          </span>
        </div>
      </div>

      <!-- Options -->
      <div class="section">
        <div class="section-header">Options</div>

        <!-- Depth-specific options -->
        <div v-if="selectedType === 'depth'" class="options-group">
          <label class="option-row">
            <span>Color Map</span>
            <select v-model="depthOptions.colorMap">
              <option value="grayscale">Grayscale</option>
              <option value="viridis">Viridis</option>
              <option value="plasma">Plasma</option>
              <option value="magma">Magma</option>
            </select>
          </label>
          <label class="option-row">
            <input type="checkbox" v-model="depthOptions.normalize" />
            <span>Normalize output</span>
          </label>
        </div>

        <!-- Normal-specific options -->
        <div v-if="selectedType === 'normal'" class="options-group">
          <label class="option-row">
            <span>Strength</span>
            <input
              type="range"
              min="0"
              max="100"
              v-model.number="normalOptions.strength"
            />
            <span class="value">{{ normalOptions.strength }}%</span>
          </label>
          <label class="option-row">
            <span>Smoothing</span>
            <input
              type="range"
              min="0"
              max="100"
              v-model.number="normalOptions.smoothing"
            />
            <span class="value">{{ normalOptions.smoothing }}%</span>
          </label>
        </div>

        <!-- Segment-specific options -->
        <div v-if="selectedType === 'segment'" class="options-group">
          <div class="option-row">
            <span>Click on canvas to set point</span>
          </div>
          <label class="option-row">
            <input type="checkbox" v-model="segmentOptions.autoMask" />
            <span>Auto-mask to layer</span>
          </label>
        </div>
      </div>

      <!-- Output -->
      <div class="section">
        <div class="section-header">Output</div>
        <div class="output-options">
          <label class="option-row">
            <input type="radio" v-model="outputTarget" value="layer" />
            <span>Create new layer</span>
          </label>
          <label class="option-row">
            <input type="radio" v-model="outputTarget" value="mask" />
            <span>Apply as layer mask</span>
          </label>
          <label class="option-row">
            <input type="radio" v-model="outputTarget" value="download" />
            <span>Download file</span>
          </label>
        </div>
      </div>

      <!-- Generate Button -->
      <div class="section">
        <button
          class="generate-btn"
          :disabled="!canGenerate || isGenerating"
          @click="generate"
        >
          <span v-if="isGenerating" class="spinner"></span>
          <span v-else>{{ generateButtonText }}</span>
        </button>
      </div>

      <!-- Status Messages -->
      <div v-if="statusMessage" class="status-message" :class="statusType">
        {{ statusMessage }}
      </div>

      <!-- Preview -->
      <div v-if="previewUrl" class="preview-section">
        <div class="section-header">Preview</div>
        <img :src="previewUrl" class="preview-image" alt="Generation preview" />
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, ref } from "vue";
import {
  type AIModelType,
  aiGeneration,
  type ModelInfo,
} from "@/services/aiGeneration";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";

const projectStore = useProjectStore();
const selectionStore = useSelectionStore();

// Source selection
const sourceType = ref<"layer" | "canvas" | "file">("layer");
const uploadedFile = ref<File | null>(null);
const uploadedFileName = ref<string>("");
const fileInput = ref<HTMLInputElement | null>(null);

// Generation type
const selectedType = ref<"depth" | "normal" | "segment">("depth");

// Model
const selectedModel = ref<AIModelType>("depth-anything");
const models = ref<ModelInfo[]>([]);

// Options
const depthOptions = ref({
  colorMap: "grayscale" as "grayscale" | "viridis" | "plasma" | "magma",
  normalize: true,
});
const normalOptions = ref({
  strength: 100,
  smoothing: 0,
});
const segmentOptions = ref({
  autoMask: true,
});

// Output
const outputTarget = ref<"layer" | "mask" | "download">("layer");

// State
const isGenerating = ref(false);
const statusMessage = ref("");
const statusType = ref<"info" | "success" | "error">("info");
const previewUrl = ref<string | null>(null);

// Generation types
const generationTypes = [
  {
    id: "depth",
    label: "Depth",
    icon: "⬛",
    description: "Estimate depth from image",
  },
  {
    id: "normal",
    label: "Normal",
    icon: "🔮",
    description: "Generate normal map",
  },
  {
    id: "segment",
    label: "Segment",
    icon: "✂️",
    description: "Segment objects",
  },
] as const;

// Computed
const selectedLayerName = computed(() => {
  const layerId = selectionStore.selectedLayerIds[0];
  if (!layerId) return null;
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === layerId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layerName = (layer != null && typeof layer === "object" && "name" in layer && typeof layer.name === "string") ? layer.name : undefined;
  return layerName != null ? layerName : null;
});

const availableModels = computed(() => {
  switch (selectedType.value) {
    case "depth":
      return models.value.filter(
        (m) => m.type === "depth-anything" || m.type === "depth-anything-v2",
      );
    case "normal":
      return models.value.filter((m) => m.type === "normal-crafter");
    case "segment":
      return models.value.filter(
        (m) => m.type === "segment-anything" || m.type === "segment-anything-2",
      );
    default:
      return models.value;
  }
});

const selectedModelInfo = computed(() => {
  return models.value.find((m) => m.type === selectedModel.value);
});

const canGenerate = computed(() => {
  if (sourceType.value === "layer" && !selectedLayerName.value) return false;
  if (sourceType.value === "file" && !uploadedFile.value) return false;
  return true;
});

const generateButtonText = computed(() => {
  if (isGenerating.value) return "Generating...";
  switch (selectedType.value) {
    case "depth":
      return "Generate Depth Map";
    case "normal":
      return "Generate Normal Map";
    case "segment":
      return "Segment Image";
    default:
      return "Generate";
  }
});

// Methods
function handleFileInputClick() {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const fileInputValue = fileInput.value;
  if (fileInputValue != null && typeof fileInputValue === "object" && typeof fileInputValue.click === "function") {
    fileInputValue.click();
  }
}

function handleFileSelect(event: Event) {
  const input = event.target as HTMLInputElement;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const files = (input != null && typeof input === "object" && "files" in input && input.files != null && input.files instanceof FileList && input.files.length > 0) ? input.files : null;
  const file = files != null ? files[0] : undefined;
  if (file != null) {
    uploadedFile.value = file;
    uploadedFileName.value = file.name;
  }
}

async function refreshModels() {
  try {
    models.value = aiGeneration.getAllModels();
    statusMessage.value = "Model status refreshed";
    statusType.value = "info";
  } catch (_error) {
    statusMessage.value = "Failed to refresh models";
    statusType.value = "error";
  }
}

async function generate() {
  if (!canGenerate.value || isGenerating.value) return;

  isGenerating.value = true;
  statusMessage.value = "Starting generation...";
  statusType.value = "info";
  previewUrl.value = null;

  try {
    // Get source image
    let sourceImage: ImageData | Blob | null = null;

    if (sourceType.value === "file" && uploadedFile.value) {
      sourceImage = uploadedFile.value;
    } else if (sourceType.value === "canvas") {
      // Capture from canvas
      statusMessage.value = "Canvas capture not yet implemented";
      statusType.value = "error";
      return;
    } else if (sourceType.value === "layer") {
      // Get layer content
      statusMessage.value = "Layer capture not yet implemented";
      statusType.value = "error";
      return;
    }

    if (!sourceImage) {
      statusMessage.value = "No source image available";
      statusType.value = "error";
      return;
    }

    statusMessage.value = `Running ${selectedType.value} estimation...`;

    let result;
    switch (selectedType.value) {
      case "depth":
        result = await aiGeneration.estimateDepth(sourceImage, {
          model: selectedModel.value as "depth-anything" | "depth-anything-v2",
          normalize: depthOptions.value.normalize,
          colorMap: depthOptions.value.colorMap,
        });
        break;
      case "normal":
        result = await aiGeneration.generateNormalMap(sourceImage, {
          model: "normal-crafter",
          strength: normalOptions.value.strength / 100,
          smoothing: normalOptions.value.smoothing / 100,
        });
        break;
      case "segment":
        result = await aiGeneration.segment(sourceImage, {
          model: selectedModel.value as
            | "segment-anything"
            | "segment-anything-2",
        });
        break;
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const resultSuccess = (result != null && typeof result === "object" && "success" in result && typeof result.success === "boolean" && result.success) ? true : false;
    const resultData = (result != null && typeof result === "object" && "data" in result && result.data != null) ? result.data : undefined;
    if (resultSuccess && resultData != null) {
      const resultProcessingTime = (result != null && typeof result === "object" && "processingTime" in result && typeof result.processingTime === "number") ? result.processingTime : 0;
      statusMessage.value = `Generation complete in ${resultProcessingTime.toFixed(0)}ms`;
      statusType.value = "success";

      // Create preview URL
      const canvas = document.createElement("canvas");
      const dataWidth = (resultData != null && typeof resultData === "object" && "width" in resultData && typeof resultData.width === "number") ? resultData.width : 0;
      const dataHeight = (resultData != null && typeof resultData === "object" && "height" in resultData && typeof resultData.height === "number") ? resultData.height : 0;
      canvas.width = dataWidth;
      canvas.height = dataHeight;
      const ctx = canvas.getContext("2d");
      if (ctx) {
        ctx.putImageData(resultData, 0, 0);
        previewUrl.value = canvas.toDataURL();
      }

      // Handle output target
      if (outputTarget.value === "download" && previewUrl.value) {
        const a = document.createElement("a");
        a.href = previewUrl.value;
        a.download = `${selectedType.value}_map.png`;
        a.click();
      } else if (outputTarget.value === "layer") {
        statusMessage.value += " - Create layer feature pending";
      }
    } else {
      const resultError = (result != null && typeof result === "object" && "error" in result && typeof result.error === "string") ? result.error : undefined;
      statusMessage.value = resultError != null ? resultError : "Generation failed";
      statusType.value = "error";
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : "Unknown error";
    statusMessage.value = `Error: ${message}`;
    statusType.value = "error";
  } finally {
    isGenerating.value = false;
  }
}

// Lifecycle
onMounted(() => {
  refreshModels();
});
</script>

<style scoped>
.ai-generate-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #121212);
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 13px;
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 10px 12px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.panel-title {
  font-weight: 600;
  font-size: 12px;
}

.refresh-btn {
  width: 24px;
  height: 24px;
  padding: 0;
  border: none;
  background: transparent;
  color: var(--lattice-text-secondary, #9ca3af);
  cursor: pointer;
  border-radius: 4px;
}

.refresh-btn:hover {
  background: var(--lattice-surface-3, #222);
  color: var(--lattice-text-primary, #e5e5e5);
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  padding: 12px;
}

.section {
  margin-bottom: 16px;
}

.section-header {
  font-size: 11px;
  font-weight: 600;
  color: var(--lattice-text-secondary, #9ca3af);
  text-transform: uppercase;
  margin-bottom: 8px;
}

.source-options,
.generation-types {
  display: flex;
  gap: 6px;
}

.source-options button,
.generation-types button {
  flex: 1;
  padding: 6px 8px;
  border: 1px solid var(--lattice-border-default, #333);
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-secondary, #9ca3af);
  border-radius: 4px;
  cursor: pointer;
  font-size: 12px;
  transition: all 0.15s ease;
}

.source-options button:hover,
.generation-types button:hover {
  background: var(--lattice-surface-3, #222);
  color: var(--lattice-text-primary, #e5e5e5);
}

.source-options button.active,
.generation-types button.active {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
  border-color: var(--lattice-accent, #8b5cf6);
  color: var(--lattice-accent, #8b5cf6);
}

.generation-types button {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 4px;
}

.type-icon {
  font-size: 18px;
}

.type-label {
  font-size: 11px;
}

.layer-info,
.file-upload {
  margin-top: 8px;
  padding: 8px;
  background: var(--lattice-surface-0, #0a0a0a);
  border-radius: 4px;
}

.no-selection {
  color: var(--lattice-text-muted, #6b7280);
  font-style: italic;
}

.upload-btn {
  padding: 6px 12px;
  border: 1px dashed var(--lattice-border-default, #333);
  background: transparent;
  color: var(--lattice-text-secondary, #9ca3af);
  border-radius: 4px;
  cursor: pointer;
}

.upload-btn:hover {
  border-color: var(--lattice-accent, #8b5cf6);
  color: var(--lattice-accent, #8b5cf6);
}

.file-name {
  display: block;
  margin-top: 6px;
  font-size: 12px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.model-select {
  width: 100%;
  padding: 8px;
  border: 1px solid var(--lattice-border-default, #333);
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-primary, #e5e5e5);
  border-radius: 4px;
  font-size: 13px;
}

.model-info {
  display: flex;
  gap: 8px;
  margin-top: 6px;
}

.memory-badge,
.status-badge {
  padding: 2px 8px;
  border-radius: 10px;
  font-size: 11px;
}

.memory-badge {
  background: var(--lattice-surface-3, #222);
  color: var(--lattice-text-secondary, #9ca3af);
}

.status-badge.ready {
  background: rgba(16, 185, 129, 0.2);
  color: #10b981;
}

.status-badge.not-loaded {
  background: var(--lattice-surface-3, #222);
  color: var(--lattice-text-muted, #6b7280);
}

.status-badge.loading {
  background: rgba(245, 158, 11, 0.2);
  color: #f59e0b;
}

.status-badge.error {
  background: rgba(239, 68, 68, 0.2);
  color: #ef4444;
}

.options-group {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.option-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.option-row input[type="range"] {
  flex: 1;
}

.option-row .value {
  min-width: 40px;
  text-align: right;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 12px;
}

.option-row select {
  flex: 1;
  padding: 4px 8px;
  border: 1px solid var(--lattice-border-default, #333);
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-primary, #e5e5e5);
  border-radius: 4px;
}

.output-options {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.generate-btn {
  width: 100%;
  padding: 12px;
  border: none;
  background: var(--lattice-accent-gradient, linear-gradient(135deg, #8b5cf6, #ec4899));
  color: white;
  font-size: 14px;
  font-weight: 600;
  border-radius: 6px;
  cursor: pointer;
  transition: opacity 0.15s ease;
}

.generate-btn:hover:not(:disabled) {
  opacity: 0.9;
}

.generate-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.spinner {
  display: inline-block;
  width: 16px;
  height: 16px;
  border: 2px solid rgba(255, 255, 255, 0.3);
  border-top-color: white;
  border-radius: 50%;
  animation: spin 0.8s linear infinite;
}

@keyframes spin {
  to { transform: rotate(360deg); }
}

.status-message {
  margin-top: 12px;
  padding: 10px;
  border-radius: 4px;
  font-size: 12px;
}

.status-message.info {
  background: rgba(59, 130, 246, 0.1);
  color: #3b82f6;
  border: 1px solid rgba(59, 130, 246, 0.3);
}

.status-message.success {
  background: rgba(16, 185, 129, 0.1);
  color: #10b981;
  border: 1px solid rgba(16, 185, 129, 0.3);
}

.status-message.error {
  background: rgba(239, 68, 68, 0.1);
  color: #ef4444;
  border: 1px solid rgba(239, 68, 68, 0.3);
}

.preview-section {
  margin-top: 16px;
}

.preview-image {
  width: 100%;
  border-radius: 4px;
  background: var(--lattice-surface-0, #0a0a0a);
}
</style>
