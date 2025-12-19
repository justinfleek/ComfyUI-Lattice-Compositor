<template>
  <div class="decompose-dialog-overlay" @click.self="emit('close')">
    <div class="decompose-dialog">
      <div class="dialog-header">
        <h3>AI Layer Decomposition</h3>
        <button class="close-btn" @click="emit('close')" :disabled="isProcessing">
          <i class="pi pi-times" />
        </button>
      </div>

      <div class="dialog-content">
        <!-- Model Status -->
        <div class="status-section">
          <div class="status-indicator" :class="statusClass">
            <i :class="statusIcon" />
            <span>{{ statusText }}</span>
          </div>
          <div v-if="modelStatus && !modelStatus.downloaded" class="model-info">
            <small>Model size: {{ modelStatus.model_size_gb }}GB</small>
          </div>
        </div>

        <!-- Source Selection -->
        <div class="form-group">
          <label>Source Image</label>
          <div class="source-options">
            <button
              class="source-btn"
              :class="{ active: sourceType === 'layer' }"
              @click="sourceType = 'layer'"
              :disabled="!hasImageLayers"
            >
              <i class="pi pi-images" />
              <span>From Layer</span>
            </button>
            <button
              class="source-btn"
              :class="{ active: sourceType === 'upload' }"
              @click="sourceType = 'upload'"
            >
              <i class="pi pi-upload" />
              <span>Upload</span>
            </button>
          </div>

          <!-- Layer Selection -->
          <div v-if="sourceType === 'layer'" class="layer-select">
            <select v-model="selectedLayerId" :disabled="isProcessing">
              <option value="">Select a layer...</option>
              <option v-for="layer in imageLayers" :key="layer.id" :value="layer.id">
                {{ layer.name }}
              </option>
            </select>
          </div>

          <!-- File Upload -->
          <div v-else class="upload-area" @click="triggerUpload" @drop.prevent="handleDrop" @dragover.prevent>
            <input
              ref="fileInput"
              type="file"
              accept="image/*"
              @change="handleFileSelect"
              style="display: none"
            />
            <div v-if="!uploadedImage" class="upload-placeholder">
              <i class="pi pi-cloud-upload" />
              <span>Click or drop image here</span>
            </div>
            <img v-else :src="uploadedImage" class="upload-preview" alt="Uploaded image" />
          </div>
        </div>

        <!-- Parameters -->
        <div class="form-group">
          <label>Number of Layers</label>
          <div class="slider-row">
            <input
              v-model.number="numLayers"
              type="range"
              min="3"
              max="16"
              step="1"
              :disabled="isProcessing"
            />
            <span class="slider-value">{{ numLayers }}</span>
          </div>
          <small class="param-hint">More layers = finer separation (3-16)</small>
        </div>

        <!-- Organization Options -->
        <div class="form-group options-group">
          <label>Organization</label>
          <div class="checkbox-row">
            <label class="checkbox-label">
              <input type="checkbox" v-model="groupIntoComp" :disabled="isProcessing" />
              <span>Group into nested composition</span>
            </label>
            <small>Keeps layers organized, reduces clutter</small>
          </div>
          <div class="checkbox-row">
            <label class="checkbox-label">
              <input type="checkbox" v-model="semanticLabels" :disabled="isProcessing" />
              <span>Generate semantic labels</span>
            </label>
            <small>AI-friendly names based on content analysis</small>
          </div>
          <div class="checkbox-row">
            <label class="checkbox-label">
              <input type="checkbox" v-model="autoUnload" :disabled="isProcessing" />
              <span>Free GPU memory after</span>
            </label>
            <small>Recommended for complex projects</small>
          </div>
        </div>

        <div class="form-group collapsed-params" v-if="showAdvanced">
          <label>Advanced Settings</label>
          <div class="param-row">
            <span>Guidance Scale</span>
            <input
              v-model.number="guidanceScale"
              type="number"
              min="1"
              max="10"
              step="0.5"
              :disabled="isProcessing"
            />
          </div>
          <div class="param-row">
            <span>Inference Steps</span>
            <input
              v-model.number="numInferenceSteps"
              type="number"
              min="20"
              max="100"
              step="10"
              :disabled="isProcessing"
            />
          </div>
          <div class="param-row">
            <span>Seed (optional)</span>
            <input
              v-model.number="seed"
              type="number"
              min="0"
              placeholder="Random"
              :disabled="isProcessing"
            />
          </div>
        </div>
        <button class="advanced-toggle" @click="showAdvanced = !showAdvanced">
          <i :class="showAdvanced ? 'pi pi-chevron-up' : 'pi pi-chevron-down'" />
          {{ showAdvanced ? 'Hide' : 'Show' }} Advanced Settings
        </button>

        <!-- Progress -->
        <div v-if="isProcessing" class="progress-section">
          <div class="progress-bar">
            <div class="progress-fill" :class="{ indeterminate: progressIndeterminate }" />
          </div>
          <p class="progress-text">{{ progressMessage }}</p>
        </div>

        <!-- Error -->
        <div v-if="errorMessage" class="error-section">
          <i class="pi pi-exclamation-triangle" />
          <span>{{ errorMessage }}</span>
        </div>
      </div>

      <div class="dialog-footer">
        <button class="cancel-btn" @click="emit('close')" :disabled="isProcessing">
          Cancel
        </button>
        <button
          class="decompose-btn"
          @click="startDecomposition"
          :disabled="!canDecompose || isProcessing"
        >
          <i class="pi pi-sparkles" />
          {{ buttonText }}
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import {
  getLayerDecompositionService,
  type DecompositionModelStatus,
  type DecomposedLayer,
} from '@/services/layerDecomposition';

const emit = defineEmits<{
  (e: 'close'): void;
  (e: 'decomposed', layers: DecomposedLayer[]): void;
}>();

const store = useCompositorStore();

// Model status
const modelStatus = ref<DecompositionModelStatus | null>(null);

// Source selection
const sourceType = ref<'layer' | 'upload'>('layer');
const selectedLayerId = ref('');
const uploadedImage = ref<string | null>(null);
const fileInput = ref<HTMLInputElement | null>(null);

// Parameters
const numLayers = ref(4);
const guidanceScale = ref(3.0);
const numInferenceSteps = ref(50);
const seed = ref<number | undefined>(undefined);
const showAdvanced = ref(false);

// Organization options
const groupIntoComp = ref(true); // Group decomposed layers into nested comp
const semanticLabels = ref(true); // Generate AI-friendly semantic labels
const autoUnload = ref(true); // Free GPU memory after decomposition

// Processing state
const isProcessing = ref(false);
const progressMessage = ref('');
const progressIndeterminate = ref(false);
const errorMessage = ref('');

// Get image layers from composition
const imageLayers = computed(() => {
  const layers = store.getActiveCompLayers();
  return layers.filter(l => l.type === 'image' || l.type === 'solid');
});

const hasImageLayers = computed(() => imageLayers.value.length > 0);

// Model status display
const statusClass = computed(() => {
  if (!modelStatus.value) return 'checking';
  if (modelStatus.value.error) return 'error';
  if (modelStatus.value.loading) return 'loading';
  if (modelStatus.value.loaded) return 'ready';
  if (modelStatus.value.downloaded) return 'downloaded';
  return 'not-downloaded';
});

const statusIcon = computed(() => {
  switch (statusClass.value) {
    case 'ready': return 'pi pi-check-circle';
    case 'downloaded': return 'pi pi-download';
    case 'loading': return 'pi pi-spin pi-spinner';
    case 'checking': return 'pi pi-spin pi-spinner';
    case 'error': return 'pi pi-exclamation-circle';
    default: return 'pi pi-cloud-download';
  }
});

const statusText = computed(() => {
  if (!modelStatus.value) return 'Checking model status...';
  if (modelStatus.value.error) return `Error: ${modelStatus.value.error}`;
  if (modelStatus.value.loading) return 'Loading model...';
  if (modelStatus.value.loaded) return 'Model ready';
  if (modelStatus.value.downloaded) return 'Model downloaded (not loaded)';
  return 'Model not downloaded';
});

// Can decompose?
const canDecompose = computed(() => {
  if (!modelStatus.value) return false;
  if (sourceType.value === 'layer' && !selectedLayerId.value) return false;
  if (sourceType.value === 'upload' && !uploadedImage.value) return false;
  return true;
});

// Button text based on state
const buttonText = computed(() => {
  if (!modelStatus.value) return 'Checking...';
  if (isProcessing.value) {
    if (!modelStatus.value.downloaded) return 'Downloading...';
    if (!modelStatus.value.loaded) return 'Loading...';
    return 'Decomposing...';
  }
  if (!modelStatus.value.downloaded) return 'Download & Decompose';
  if (!modelStatus.value.loaded) return 'Load & Decompose';
  return 'Decompose Image';
});

// File handling
function triggerUpload() {
  fileInput.value?.click();
}

function handleFileSelect(event: Event) {
  const input = event.target as HTMLInputElement;
  const file = input.files?.[0];
  if (file) {
    loadImageFile(file);
  }
}

function handleDrop(event: DragEvent) {
  const file = event.dataTransfer?.files[0];
  if (file && file.type.startsWith('image/')) {
    loadImageFile(file);
  }
}

function loadImageFile(file: File) {
  const reader = new FileReader();
  reader.onload = () => {
    uploadedImage.value = reader.result as string;
  };
  reader.readAsDataURL(file);
}

// Get source image as data URL
async function getSourceImage(): Promise<string | null> {
  if (sourceType.value === 'upload') {
    return uploadedImage.value;
  }

  // Get from layer
  const layer = imageLayers.value.find(l => l.id === selectedLayerId.value);
  if (!layer) return null;

  // For image layers, get the source URL (may be data URL or external URL)
  if (layer.type === 'image' && layer.data) {
    const source = layer.data.source || layer.data.url || layer.data.assetId;
    if (source) {
      // If it's already a data URL, return it directly
      if (source.startsWith('data:')) {
        return source;
      }
      // Otherwise, load and convert to data URL
      return await loadImageAsDataUrl(source);
    }
  }

  // For solid layers, create a canvas with the color
  if (layer.type === 'solid' && layer.data) {
    const canvas = document.createElement('canvas');
    canvas.width = layer.data.width || store.width;
    canvas.height = layer.data.height || store.height;
    const ctx = canvas.getContext('2d')!;
    ctx.fillStyle = layer.data.color || '#808080';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    return canvas.toDataURL('image/png');
  }

  return null;
}

// Helper to load an image URL and convert to data URL
async function loadImageAsDataUrl(url: string): Promise<string> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.crossOrigin = 'anonymous';
    img.onload = () => {
      const canvas = document.createElement('canvas');
      canvas.width = img.naturalWidth;
      canvas.height = img.naturalHeight;
      const ctx = canvas.getContext('2d')!;
      ctx.drawImage(img, 0, 0);
      resolve(canvas.toDataURL('image/png'));
    };
    img.onerror = () => reject(new Error('Failed to load image'));
    img.src = url;
  });
}

// Create layers from decomposition result
async function createLayersFromDecomposition(decomposedLayers: DecomposedLayer[]) {
  const comp = store.getActiveComp();
  if (!comp) return;

  if (groupIntoComp.value) {
    // Create a nested composition to contain all decomposed layers
    const nestedCompName = `Decomposed (${decomposedLayers.length} layers)`;
    const nestedComp = store.createComposition(nestedCompName, {
      width: comp.settings.width,
      height: comp.settings.height,
      frameCount: comp.settings.frameCount,
      fps: comp.settings.fps,
      backgroundColor: '#00000000', // Transparent
    });

    // Switch to nested comp to add layers
    const originalCompId = comp.id;
    store.setActiveComposition(nestedComp.id);

    // Create image layers for each decomposed layer (reverse order so Background is at bottom)
    for (let i = decomposedLayers.length - 1; i >= 0; i--) {
      const decomposed = decomposedLayers[i];
      const layer = store.createLayer('image', decomposed.label);
      if (layer.data) {
        (layer.data as any).source = decomposed.image;
      }
    }

    // Switch back to original comp
    store.setActiveComposition(originalCompId);

    // Add the nested comp as a layer in the original
    const nestedLayer = store.createLayer('nestedComp', nestedCompName);
    if (nestedLayer.data) {
      (nestedLayer.data as any).compositionId = nestedComp.id;
    }
  } else {
    // Create layers directly in current composition (original behavior)
    for (let i = decomposedLayers.length - 1; i >= 0; i--) {
      const decomposed = decomposedLayers[i];
      const layer = store.createLayer('image', decomposed.label);
      if (layer.data) {
        (layer.data as any).source = decomposed.image;
      }
    }
  }

  store.pushHistory();
}

// Main decomposition function
async function startDecomposition() {
  if (!canDecompose.value || isProcessing.value) return;

  isProcessing.value = true;
  errorMessage.value = '';
  progressIndeterminate.value = true;

  try {
    const service = getLayerDecompositionService();

    // Get source image
    progressMessage.value = 'Preparing source image...';
    const sourceImage = await getSourceImage();
    if (!sourceImage) {
      throw new Error('Failed to get source image');
    }

    // Run decomposition with auto-setup
    const layers = await service.decomposeWithAutoSetup(
      sourceImage,
      {
        numLayers: numLayers.value,
        guidanceScale: guidanceScale.value,
        numInferenceSteps: numInferenceSteps.value,
        seed: seed.value,
        autoUnload: autoUnload.value,
        generateSemanticLabels: semanticLabels.value,
      },
      (stage, message) => {
        progressMessage.value = message;
        progressIndeterminate.value = stage !== 'decomposing';

        // Refresh model status during setup
        if (stage === 'downloading' || stage === 'loading' || stage === 'cleanup') {
          checkModelStatus();
        }
      }
    );

    // Create layers from result
    progressMessage.value = 'Creating layers...';
    await createLayersFromDecomposition(layers);

    // Emit success
    emit('decomposed', layers);
    emit('close');

  } catch (err) {
    errorMessage.value = err instanceof Error ? err.message : 'Decomposition failed';
    console.error('[DecomposeDialog] Error:', err);
  } finally {
    isProcessing.value = false;
    progressIndeterminate.value = false;
  }
}

// Check model status
async function checkModelStatus() {
  try {
    const service = getLayerDecompositionService();
    modelStatus.value = await service.getStatus();
  } catch (err) {
    console.error('[DecomposeDialog] Failed to get model status:', err);
    modelStatus.value = {
      downloaded: false,
      loaded: false,
      loading: false,
      error: 'Failed to connect to backend',
      model_path: '',
      model_size_gb: 28.8,
    };
  }
}

// Auto-select first image layer if available
watch(hasImageLayers, (has) => {
  if (has && !selectedLayerId.value) {
    selectedLayerId.value = imageLayers.value[0]?.id || '';
  }
}, { immediate: true });

// Initialize
onMounted(() => {
  checkModelStatus();

  // If no image layers, default to upload
  if (!hasImageLayers.value) {
    sourceType.value = 'upload';
  }
});
</script>

<style scoped>
.decompose-dialog-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.6);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.decompose-dialog {
  width: 480px;
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

.close-btn:hover:not(:disabled) {
  color: #fff;
}

.close-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.dialog-content {
  flex: 1;
  overflow-y: auto;
  padding: 16px;
}

/* Status Section */
.status-section {
  margin-bottom: 16px;
  padding: 12px;
  background: #1e1e1e;
  border-radius: 6px;
}

.status-indicator {
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 13px;
}

.status-indicator.ready {
  color: #4caf50;
}

.status-indicator.downloaded {
  color: #ffc107;
}

.status-indicator.loading,
.status-indicator.checking {
  color: #2196f3;
}

.status-indicator.error {
  color: #f44336;
}

.status-indicator.not-downloaded {
  color: #9e9e9e;
}

.model-info {
  margin-top: 8px;
  color: #666;
}

/* Form Groups */
.form-group {
  margin-bottom: 16px;
}

.form-group > label {
  display: block;
  font-size: 12px;
  font-weight: 500;
  color: #aaa;
  margin-bottom: 8px;
}

/* Source Options */
.source-options {
  display: flex;
  gap: 8px;
  margin-bottom: 12px;
}

.source-btn {
  flex: 1;
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 4px;
  padding: 12px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  border-radius: 6px;
  color: #aaa;
  cursor: pointer;
  transition: all 0.1s;
}

.source-btn:hover:not(:disabled) {
  background: #333;
  color: #fff;
}

.source-btn.active {
  background: rgba(74, 144, 217, 0.2);
  border-color: #4a90d9;
  color: #fff;
}

.source-btn:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.source-btn i {
  font-size: 18px;
}

.source-btn span {
  font-size: 12px;
}

/* Layer Select */
.layer-select select {
  width: 100%;
  padding: 8px 12px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 13px;
}

.layer-select select:focus {
  outline: none;
  border-color: #4a90d9;
}

/* Upload Area */
.upload-area {
  height: 120px;
  border: 2px dashed #3d3d3d;
  border-radius: 6px;
  display: flex;
  align-items: center;
  justify-content: center;
  cursor: pointer;
  transition: all 0.1s;
  overflow: hidden;
}

.upload-area:hover {
  border-color: #4a90d9;
  background: rgba(74, 144, 217, 0.1);
}

.upload-placeholder {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 8px;
  color: #666;
}

.upload-placeholder i {
  font-size: 32px;
}

.upload-placeholder span {
  font-size: 12px;
}

.upload-preview {
  max-width: 100%;
  max-height: 100%;
  object-fit: contain;
}

/* Slider */
.slider-row {
  display: flex;
  align-items: center;
  gap: 12px;
}

.slider-row input[type="range"] {
  flex: 1;
  height: 4px;
  -webkit-appearance: none;
  background: #3d3d3d;
  border-radius: 2px;
}

.slider-row input[type="range"]::-webkit-slider-thumb {
  -webkit-appearance: none;
  width: 16px;
  height: 16px;
  border-radius: 50%;
  background: #4a90d9;
  cursor: pointer;
}

.slider-value {
  min-width: 24px;
  text-align: center;
  font-size: 14px;
  font-weight: 500;
  color: #e0e0e0;
}

.param-hint {
  display: block;
  margin-top: 4px;
  color: #666;
  font-size: 11px;
}

/* Organization Options */
.options-group {
  padding: 12px;
  background: #1e1e1e;
  border-radius: 6px;
}

.checkbox-row {
  margin-bottom: 10px;
}

.checkbox-row:last-child {
  margin-bottom: 0;
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  font-size: 13px;
  color: #e0e0e0;
}

.checkbox-label input[type="checkbox"] {
  width: 16px;
  height: 16px;
  accent-color: #4a90d9;
  cursor: pointer;
}

.checkbox-row small {
  display: block;
  margin-left: 24px;
  margin-top: 2px;
  color: #666;
  font-size: 11px;
}

/* Advanced Settings */
.collapsed-params {
  padding: 12px;
  background: #1e1e1e;
  border-radius: 6px;
  margin-bottom: 8px;
}

.param-row {
  display: flex;
  align-items: center;
  justify-content: space-between;
  margin-bottom: 8px;
}

.param-row:last-child {
  margin-bottom: 0;
}

.param-row span {
  font-size: 12px;
  color: #aaa;
}

.param-row input {
  width: 80px;
  padding: 4px 8px;
  border: 1px solid #3d3d3d;
  background: #2a2a2a;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 13px;
  text-align: right;
}

.param-row input:focus {
  outline: none;
  border-color: #4a90d9;
}

.advanced-toggle {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  width: 100%;
  padding: 8px;
  border: none;
  background: transparent;
  color: #666;
  font-size: 12px;
  cursor: pointer;
}

.advanced-toggle:hover {
  color: #aaa;
}

/* Progress */
.progress-section {
  margin-top: 16px;
  padding: 12px;
  background: #1e1e1e;
  border-radius: 4px;
}

.progress-bar {
  height: 4px;
  background: #333;
  border-radius: 2px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: #4a90d9;
  transition: width 0.2s;
}

.progress-fill.indeterminate {
  width: 30%;
  animation: indeterminate 1.5s infinite ease-in-out;
}

@keyframes indeterminate {
  0% { transform: translateX(-100%); }
  100% { transform: translateX(400%); }
}

.progress-text {
  margin-top: 8px;
  font-size: 12px;
  color: #aaa;
  text-align: center;
}

/* Error */
.error-section {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-top: 16px;
  padding: 12px;
  background: rgba(244, 67, 54, 0.1);
  border: 1px solid rgba(244, 67, 54, 0.3);
  border-radius: 4px;
  color: #f44336;
  font-size: 13px;
}

/* Footer */
.dialog-footer {
  display: flex;
  align-items: center;
  justify-content: flex-end;
  gap: 8px;
  padding: 12px 16px;
  border-top: 1px solid #3d3d3d;
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

.decompose-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 16px;
  border: none;
  background: linear-gradient(135deg, #9c27b0, #4a90d9);
  color: #fff;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.decompose-btn:hover:not(:disabled) {
  filter: brightness(1.1);
}

.decompose-btn:disabled {
  background: #333;
  color: #666;
  cursor: not-allowed;
}
</style>
