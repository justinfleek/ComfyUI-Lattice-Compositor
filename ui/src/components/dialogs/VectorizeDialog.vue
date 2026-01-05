<template>
  <Dialog
    :visible="visible"
    modal
    header="Vectorize Image"
    :style="{ width: '700px' }"
    :closable="!isProcessing"
    @update:visible="$emit('close')"
  >
    <div class="vectorize-dialog">
      <!-- Source Selection -->
      <div class="section">
        <h4>Source</h4>
        <div class="source-options">
          <div class="option-group">
            <label>
              <input
                type="radio"
                v-model="sourceType"
                value="layer"
                :disabled="isProcessing || !availableLayers.length"
              />
              From Layer
            </label>
            <select
              v-model="selectedLayerId"
              :disabled="sourceType !== 'layer' || isProcessing"
              class="layer-select"
            >
              <option value="">Select a layer...</option>
              <option
                v-for="layer in availableLayers"
                :key="layer.id"
                :value="layer.id"
              >
                {{ layer.name }}
              </option>
            </select>
          </div>

          <div class="option-group">
            <label>
              <input
                type="radio"
                v-model="sourceType"
                value="upload"
                :disabled="isProcessing"
              />
              Upload Image
            </label>
            <input
              ref="fileInput"
              type="file"
              accept="image/*"
              @change="onFileSelect"
              :disabled="sourceType !== 'upload' || isProcessing"
              class="file-input"
            />
          </div>
        </div>

        <!-- Preview -->
        <div v-if="previewUrl" class="preview-container">
          <img :src="previewUrl" alt="Source preview" class="preview-image" />
          <span class="preview-size">{{ previewWidth }} x {{ previewHeight }}</span>
        </div>
      </div>

      <!-- Mode Selection -->
      <div class="section">
        <h4>Vectorization Mode</h4>
        <div class="mode-options">
          <label class="mode-option" :class="{ selected: mode === 'trace' }">
            <input type="radio" v-model="mode" value="trace" :disabled="isProcessing" />
            <div class="mode-info">
              <span class="mode-title">VTracer (Fast)</span>
              <span class="mode-desc">Works with any image. Fast tracing to bezier curves.</span>
            </div>
          </label>

          <label class="mode-option" :class="{ selected: mode === 'ai' }">
            <input type="radio" v-model="mode" value="ai" :disabled="isProcessing || !starVectorAvailable" />
            <div class="mode-info">
              <span class="mode-title">StarVector AI</span>
              <span class="mode-desc">Best for icons/logos. Requires ~2.5GB VRAM.</span>
              <span v-if="!starVectorAvailable" class="mode-warning">Model not available</span>
            </div>
          </label>
        </div>
      </div>

      <!-- VTracer Options -->
      <div v-if="mode === 'trace'" class="section options-section">
        <h4>Tracing Options</h4>

        <div class="options-grid">
          <div class="option-row">
            <label>Color Mode</label>
            <select v-model="traceOptions.colorMode" :disabled="isProcessing">
              <option value="color">Color</option>
              <option value="binary">Black & White</option>
            </select>
          </div>

          <div class="option-row">
            <label>Filter Speckle</label>
            <input
              type="range"
              v-model.number="traceOptions.filterSpeckle"
              min="0"
              max="100"
              :disabled="isProcessing"
            />
            <span class="value">{{ traceOptions.filterSpeckle }}</span>
          </div>

          <div class="option-row">
            <label>Corner Threshold</label>
            <input
              type="range"
              v-model.number="traceOptions.cornerThreshold"
              min="0"
              max="180"
              :disabled="isProcessing"
            />
            <span class="value">{{ traceOptions.cornerThreshold }}°</span>
          </div>

          <div class="option-row">
            <label>Color Precision</label>
            <input
              type="range"
              v-model.number="traceOptions.colorPrecision"
              min="1"
              max="10"
              :disabled="isProcessing"
            />
            <span class="value">{{ traceOptions.colorPrecision }}</span>
          </div>

          <div class="option-row">
            <label>Layer Difference</label>
            <input
              type="range"
              v-model.number="traceOptions.layerDifference"
              min="1"
              max="256"
              :disabled="isProcessing"
            />
            <span class="value">{{ traceOptions.layerDifference }}</span>
          </div>
        </div>
      </div>

      <!-- Output Options -->
      <div class="section">
        <h4>Output Options</h4>
        <div class="output-options">
          <label>
            <input type="checkbox" v-model="createSeparateLayers" :disabled="isProcessing" />
            Create separate layer for each path
          </label>
          <label>
            <input type="checkbox" v-model="groupByPath" :disabled="isProcessing" />
            Assign group IDs to control points (for group animation)
          </label>
          <label>
            <input type="checkbox" v-model="autoGroupByRegion" :disabled="isProcessing" />
            Auto-group points by region (quadrants)
          </label>
          <label>
            <input type="checkbox" v-model="enableAnimation" :disabled="isProcessing" />
            Enable keyframe animation on created layers
          </label>
        </div>
      </div>

      <!-- Progress -->
      <div v-if="isProcessing" class="progress-section">
        <div class="progress-bar">
          <div class="progress-fill" :style="{ width: progressPercent + '%' }" />
        </div>
        <span class="progress-text">{{ progressMessage }}</span>
      </div>

      <!-- Result Preview -->
      <div v-if="result && !isProcessing" class="result-section">
        <div class="result-header">
          <span class="result-count">{{ result.pathCount }} paths found</span>
          <button class="preview-svg-btn" @click="showSvgPreview = !showSvgPreview">
            {{ showSvgPreview ? 'Hide' : 'Show' }} SVG Preview
          </button>
        </div>
        <div v-if="showSvgPreview && result.svg" class="svg-preview" v-html="sanitizedSvg" />
      </div>

      <!-- Error -->
      <div v-if="errorMessage" class="error-message">
        {{ errorMessage }}
      </div>
    </div>

    <template #footer>
      <div class="dialog-footer">
        <button class="btn-secondary" @click="$emit('close')" :disabled="isProcessing">
          Cancel
        </button>
        <button
          class="btn-primary"
          @click="startVectorize"
          :disabled="!canVectorize || isProcessing"
        >
          {{ isProcessing ? 'Processing...' : 'Vectorize' }}
        </button>
        <button
          v-if="result && !isProcessing"
          class="btn-success"
          @click="createLayers"
        >
          Create Layers ({{ result.pathCount }})
        </button>
      </div>
    </template>
  </Dialog>
</template>

<script setup lang="ts">
import DOMPurify from "dompurify";
import { computed, onMounted, ref, watch } from "vue";
import {
  autoGroupPoints,
  DEFAULT_VTRACE_OPTIONS,
  filterSmallPaths,
  getVectorizeService,
  normalizeControlPoints,
  type VectorizeResult,
  type VTraceOptions,
} from "@/services/vectorize";
import { useCompositorStore } from "@/stores/compositorStore";
import type { ControlPoint, Layer } from "@/types/project";

const _props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<{
  (e: "close"): void;
  (e: "created", layerIds: string[]): void;
}>();

const store = useCompositorStore();
const vectorizeService = getVectorizeService();

// Source selection
const sourceType = ref<"layer" | "upload">("layer");
const selectedLayerId = ref("");
const uploadedImage = ref<string | null>(null);
const _fileInput = ref<HTMLInputElement | null>(null);

// Preview
const previewUrl = ref<string | null>(null);
const previewWidth = ref(0);
const previewHeight = ref(0);

// Mode
const mode = ref<"trace" | "ai">("trace");
const starVectorAvailable = ref(false);

// Options
const traceOptions = ref<VTraceOptions>({ ...DEFAULT_VTRACE_OPTIONS });

// Output options
const createSeparateLayers = ref(true);
const groupByPath = ref(true);
const autoGroupByRegion = ref(false);
const enableAnimation = ref(true);

// Progress
const isProcessing = ref(false);
const progressPercent = ref(0);
const progressMessage = ref("");

// Result
const result = ref<VectorizeResult | null>(null);
const _showSvgPreview = ref(false);
const errorMessage = ref("");

// Available layers (image layers only)
const _availableLayers = computed(() => {
  return store.layers.filter(
    (l: Layer) =>
      l.type === "image" || l.type === "video" || l.type === "solid",
  );
});

// Can vectorize?
const _canVectorize = computed(() => {
  if (sourceType.value === "layer") {
    return !!selectedLayerId.value;
  }
  return !!uploadedImage.value;
});

// Sanitized SVG for preview using DOMPurify with SVG-specific config
const _sanitizedSvg = computed(() => {
  if (!result.value?.svg) return "";
  return DOMPurify.sanitize(result.value.svg, {
    USE_PROFILES: { svg: true, svgFilters: true },
    ADD_TAGS: ["use"],
  });
});

// Watch source changes to update preview
watch([sourceType, selectedLayerId], async () => {
  if (sourceType.value === "layer" && selectedLayerId.value) {
    await loadLayerPreview();
  }
});

// Check StarVector availability on mount
onMounted(async () => {
  try {
    const status = await vectorizeService.getStatus();
    starVectorAvailable.value =
      status.starvector.available || status.starvector.downloaded;
  } catch {
    starVectorAvailable.value = false;
  }
});

// Load preview from selected layer
async function loadLayerPreview() {
  const layer = store.layers.find((l: Layer) => l.id === selectedLayerId.value);
  if (!layer) return;

  try {
    // Get the layer's image data
    const layerData = layer.data as any;
    if (layerData?.source) {
      previewUrl.value = layerData.source;
    } else if (layerData?.assetId) {
      const asset = store.project?.assets[layerData.assetId];
      if (asset?.data) {
        previewUrl.value = asset.data;
      }
    }

    // Get dimensions
    if (previewUrl.value) {
      const img = new Image();
      img.onload = () => {
        previewWidth.value = img.naturalWidth;
        previewHeight.value = img.naturalHeight;
      };
      img.src = previewUrl.value;
    }
  } catch (error) {
    console.error("Failed to load layer preview:", error);
  }
}

// Handle file upload
function _onFileSelect(event: Event) {
  const input = event.target as HTMLInputElement;
  const file = input.files?.[0];
  if (!file) return;

  const reader = new FileReader();
  reader.onload = (e) => {
    uploadedImage.value = e.target?.result as string;
    previewUrl.value = uploadedImage.value;

    // Get dimensions
    const img = new Image();
    img.onload = () => {
      previewWidth.value = img.naturalWidth;
      previewHeight.value = img.naturalHeight;
    };
    img.src = uploadedImage.value;
  };
  reader.readAsDataURL(file);
}

// Start vectorization
async function _startVectorize() {
  errorMessage.value = "";
  result.value = null;
  isProcessing.value = true;
  progressPercent.value = 0;

  try {
    // Get image data URL
    let imageDataUrl: string;

    if (sourceType.value === "layer") {
      const layer = store.layers.find(
        (l: Layer) => l.id === selectedLayerId.value,
      );
      if (!layer) throw new Error("Layer not found");

      const layerData = layer.data as any;
      if (layerData?.source) {
        imageDataUrl = layerData.source;
      } else if (layerData?.assetId) {
        const asset = store.project?.assets[layerData.assetId];
        if (!asset?.data) throw new Error("Asset data not found");
        imageDataUrl = asset.data;
      } else {
        throw new Error("Could not get image data from layer");
      }
    } else {
      if (!uploadedImage.value) throw new Error("No image uploaded");
      imageDataUrl = uploadedImage.value;
    }

    progressMessage.value = "Vectorizing image...";
    progressPercent.value = 30;

    // Run vectorization
    result.value = await vectorizeService.vectorize(
      imageDataUrl,
      {
        mode: mode.value,
        traceOptions: traceOptions.value,
      },
      (stage, message) => {
        progressMessage.value = message;
        if (stage === "downloading") progressPercent.value = 20;
        else if (stage === "tracing" || stage === "vectorizing")
          progressPercent.value = 60;
        else if (stage === "complete") progressPercent.value = 100;
      },
    );

    progressPercent.value = 100;
    progressMessage.value = `Found ${result.value.pathCount} paths`;
  } catch (error) {
    errorMessage.value =
      error instanceof Error ? error.message : "Vectorization failed";
  } finally {
    isProcessing.value = false;
  }
}

// Create layers from result
function _createLayers() {
  if (!result.value) return;

  const createdLayerIds: string[] = [];

  // Filter small paths
  let paths = filterSmallPaths(result.value.paths, 2);

  // Normalize control points
  paths = normalizeControlPoints(paths, {
    groupByPath: groupByPath.value,
    prefix: "vec",
  });

  if (createSeparateLayers.value) {
    // Create a separate spline layer for each path
    for (let i = 0; i < paths.length; i++) {
      const path = paths[i];

      // Auto-group by region if requested
      let controlPoints = path.controlPoints;
      if (autoGroupByRegion.value) {
        controlPoints = autoGroupPoints(controlPoints, { method: "quadrant" });
      }

      // Create the spline layer
      const layer = store.createSplineLayer();
      store.renameLayer(layer.id, `Vector Path ${i + 1}`);

      // Update with control points
      store.updateLayerData(layer.id, {
        controlPoints,
        closed: path.closed,
        stroke: path.stroke || "#00ff00",
        strokeWidth: 2,
        fill: path.fill || "",
        animated: enableAnimation.value,
      });

      createdLayerIds.push(layer.id);
    }
  } else {
    // Create a single layer with all paths merged
    // Each path becomes a group
    const allPoints: ControlPoint[] = [];
    let pointIdx = 0;

    for (let pathIdx = 0; pathIdx < paths.length; pathIdx++) {
      const path = paths[pathIdx];
      for (const cp of path.controlPoints) {
        allPoints.push({
          ...cp,
          id: `vec_${pointIdx++}`,
          group: `path_${pathIdx}`,
        });
      }
    }

    // Auto-group by region if requested (overrides path grouping)
    let controlPoints = allPoints;
    if (autoGroupByRegion.value) {
      controlPoints = autoGroupPoints(allPoints, { method: "quadrant" });
    }

    const layer = store.createSplineLayer();
    store.renameLayer(layer.id, "Vectorized Paths");

    store.updateLayerData(layer.id, {
      controlPoints,
      closed: false,
      stroke: "#00ff00",
      strokeWidth: 2,
      fill: "",
      animated: enableAnimation.value,
    });

    createdLayerIds.push(layer.id);
  }

  emit("created", createdLayerIds);
  emit("close");
}
</script>

<style scoped>
.vectorize-dialog {
  display: flex;
  flex-direction: column;
  gap: 20px;
}

.section {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.section h4 {
  margin: 0;
  font-size: 13px;
  font-weight: 600;
  color: #e0e0e0;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.source-options {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.option-group {
  display: flex;
  align-items: center;
  gap: 12px;
}

.option-group label {
  display: flex;
  align-items: center;
  gap: 6px;
  min-width: 120px;
  cursor: pointer;
}

.layer-select,
.file-input {
  flex: 1;
  padding: 8px 12px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
}

.layer-select:disabled,
.file-input:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.preview-container {
  position: relative;
  display: flex;
  justify-content: center;
  align-items: center;
  background: #1a1a1a;
  border-radius: 6px;
  padding: 12px;
  max-height: 200px;
  overflow: hidden;
}

.preview-image {
  max-width: 100%;
  max-height: 180px;
  object-fit: contain;
  border-radius: 4px;
}

.preview-size {
  position: absolute;
  bottom: 8px;
  right: 8px;
  padding: 4px 8px;
  background: rgba(0, 0, 0, 0.7);
  border-radius: 4px;
  font-size: 11px;
  color: #888;
}

.mode-options {
  display: flex;
  gap: 12px;
}

.mode-option {
  flex: 1;
  display: flex;
  align-items: flex-start;
  gap: 10px;
  padding: 12px;
  background: #2a2a2a;
  border: 2px solid #444;
  border-radius: 6px;
  cursor: pointer;
  transition: all 0.2s ease;
}

.mode-option:hover {
  border-color: #666;
}

.mode-option.selected {
  border-color: #8B5CF6;
  background: rgba(139, 92, 246, 0.1);
}

.mode-option input {
  margin-top: 2px;
}

.mode-info {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.mode-title {
  font-weight: 600;
  color: #e0e0e0;
}

.mode-desc {
  font-size: 12px;
  color: #888;
}

.mode-warning {
  font-size: 11px;
  color: #f59e0b;
}

.options-section {
  padding: 16px;
  background: #1e1e1e;
  border-radius: 6px;
}

.options-grid {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.option-row {
  display: flex;
  align-items: center;
  gap: 12px;
}

.option-row label {
  min-width: 140px;
  font-size: 13px;
  color: #aaa;
}

.option-row input[type="range"] {
  flex: 1;
}

.option-row select {
  flex: 1;
  padding: 6px 10px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
}

.option-row .value {
  min-width: 50px;
  text-align: right;
  font-family: monospace;
  color: #8B5CF6;
}

.output-options {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.output-options label {
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 13px;
  color: #ccc;
  cursor: pointer;
}

.progress-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
  padding: 16px;
  background: #1e1e1e;
  border-radius: 6px;
}

.progress-bar {
  height: 6px;
  background: #333;
  border-radius: 3px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: linear-gradient(90deg, #8B5CF6, #EC4899);
  transition: width 0.3s ease;
}

.progress-text {
  font-size: 12px;
  color: #888;
  text-align: center;
}

.result-section {
  padding: 16px;
  background: #1e1e1e;
  border-radius: 6px;
}

.result-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 12px;
}

.result-count {
  font-weight: 600;
  color: #10B981;
}

.preview-svg-btn {
  padding: 6px 12px;
  background: #3d3d3d;
  border: none;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 12px;
  cursor: pointer;
}

.preview-svg-btn:hover {
  background: #4a4a4a;
}

.svg-preview {
  max-height: 300px;
  overflow: auto;
  background: #121212;
  border-radius: 4px;
  padding: 12px;
}

.svg-preview :deep(svg) {
  max-width: 100%;
  height: auto;
}

.error-message {
  padding: 12px;
  background: rgba(244, 67, 54, 0.15);
  border: 1px solid rgba(244, 67, 54, 0.3);
  border-radius: 4px;
  color: #f44336;
  font-size: 13px;
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
}

.btn-secondary,
.btn-primary,
.btn-success {
  padding: 10px 20px;
  border: none;
  border-radius: 6px;
  font-size: 13px;
  font-weight: 500;
  cursor: pointer;
  transition: all 0.2s ease;
}

.btn-secondary {
  background: #3d3d3d;
  color: #e0e0e0;
}

.btn-secondary:hover:not(:disabled) {
  background: #4a4a4a;
}

.btn-primary {
  background: #8B5CF6;
  color: white;
}

.btn-primary:hover:not(:disabled) {
  background: #7c4fe0;
}

.btn-primary:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.btn-success {
  background: #10B981;
  color: white;
}

.btn-success:hover:not(:disabled) {
  background: #0d9668;
}
</style>
