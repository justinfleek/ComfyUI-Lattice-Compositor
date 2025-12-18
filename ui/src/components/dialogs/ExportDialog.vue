<template>
  <div class="export-dialog-overlay" @click.self="emit('close')">
    <div class="export-dialog">
      <div class="dialog-header">
        <h3>Export Matte Sequence</h3>
        <button class="close-btn" @click="emit('close')">
          <i class="pi pi-times" />
        </button>
      </div>

      <div class="dialog-content">
        <!-- Resolution Selection -->
        <div class="form-group">
          <label>Resolution</label>
          <div class="resolution-presets">
            <button
              v-for="preset in resolutionPresets"
              :key="preset.label"
              class="preset-btn"
              :class="{ active: selectedPreset === preset.label }"
              @click="selectPreset(preset)"
            >
              {{ preset.label }}
            </button>
          </div>
          <div class="custom-resolution">
            <div class="dimension-input">
              <label>Width</label>
              <input
                v-model.number="customWidth"
                type="number"
                min="256"
                step="8"
                @change="validateCustomDimensions"
              />
            </div>
            <span class="dimension-x">×</span>
            <div class="dimension-input">
              <label>Height</label>
              <input
                v-model.number="customHeight"
                type="number"
                min="256"
                step="8"
                @change="validateCustomDimensions"
              />
            </div>
          </div>
          <p v-if="dimensionWarning" class="dimension-warning">
            <i class="pi pi-info-circle" />
            {{ dimensionWarning }}
          </p>
        </div>

        <!-- Matte Mode -->
        <div class="form-group">
          <label>Matte Mode</label>
          <div class="matte-mode-options">
            <button
              class="mode-btn"
              :class="{ active: matteMode === 'exclude_text' }"
              @click="matteMode = 'exclude_text'"
            >
              <i class="pi pi-ban" />
              <span>Exclude Text</span>
              <small>Text regions are BLACK (excluded from generation)</small>
            </button>
            <button
              class="mode-btn"
              :class="{ active: matteMode === 'include_all' }"
              @click="matteMode = 'include_all'"
            >
              <i class="pi pi-check-circle" />
              <span>Include All</span>
              <small>Entire frame is WHITE (generate everything)</small>
            </button>
          </div>
        </div>

        <!-- Preview -->
        <div class="form-group">
          <label>Preview (Frame 0)</label>
          <div class="preview-container">
            <img
              v-if="previewUrl"
              :src="previewUrl"
              alt="Matte preview"
              class="preview-image"
            />
            <div v-else class="preview-placeholder">
              <i class="pi pi-image" />
              <span>Generating preview...</span>
            </div>
          </div>
          <p class="preview-info">
            White = Keep original / generate content<br />
            Black = Exclude from generation
          </p>
        </div>

        <!-- Export Progress -->
        <div v-if="isExporting" class="progress-section">
          <div class="progress-bar">
            <div
              class="progress-fill"
              :style="{ width: `${exportProgress}%` }"
            />
          </div>
          <p class="progress-text">
            {{ progressMessage }}
          </p>
        </div>
      </div>

      <div class="dialog-footer">
        <div class="export-info">
          <span>{{ store.frameCount }} frames @ {{ exportWidth }}×{{ exportHeight }}</span>
        </div>
        <button class="cancel-btn" @click="emit('close')" :disabled="isExporting">
          Cancel
        </button>
        <button
          class="export-btn"
          @click="startExport"
          :disabled="isExporting || !store.hasProject"
        >
          <i class="pi pi-download" />
          {{ isExporting ? 'Exporting...' : 'Export ZIP' }}
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { matteExporter, type ExportOptions } from '@/services/matteExporter';

const emit = defineEmits<{
  (e: 'close'): void;
  (e: 'exported'): void;
}>();

const store = useCompositorStore();

// Resolution presets
const resolutionPresets = matteExporter.getResolutionPresets();

// State
const selectedPreset = ref('720p (1280x720)');
const customWidth = ref(1280);
const customHeight = ref(720);
const dimensionWarning = ref<string | undefined>();
const matteMode = ref<'exclude_text' | 'include_all'>('exclude_text');
const previewUrl = ref<string | null>(null);
const isExporting = ref(false);
const exportProgress = ref(0);
const progressMessage = ref('');

// Computed export dimensions
const exportWidth = computed(() => customWidth.value);
const exportHeight = computed(() => customHeight.value);

// Select a preset
function selectPreset(preset: { label: string; width: number; height: number }): void {
  selectedPreset.value = preset.label;
  customWidth.value = preset.width;
  customHeight.value = preset.height;
  dimensionWarning.value = undefined;
}

// Validate custom dimensions
function validateCustomDimensions(): void {
  const validation = matteExporter.validateDimensions(customWidth.value, customHeight.value);

  if (!validation.valid) {
    customWidth.value = validation.correctedWidth;
    customHeight.value = validation.correctedHeight;
    dimensionWarning.value = validation.message;
    selectedPreset.value = '';
  } else {
    dimensionWarning.value = undefined;
    // Check if matches a preset
    const matchingPreset = resolutionPresets.find(
      p => p.width === customWidth.value && p.height === customHeight.value
    );
    selectedPreset.value = matchingPreset?.label || '';
  }
}

// Generate preview
async function generatePreview(): Promise<void> {
  if (!store.hasProject) return;

  // Revoke old preview URL
  if (previewUrl.value) {
    URL.revokeObjectURL(previewUrl.value);
    previewUrl.value = null;
  }

  const options: ExportOptions = {
    width: exportWidth.value,
    height: exportHeight.value,
    matteMode: matteMode.value
  };

  previewUrl.value = await matteExporter.generatePreviewFrame(
    store.project,
    0,
    options
  );
}

// Start export
async function startExport(): Promise<void> {
  if (isExporting.value || !store.hasProject) return;

  isExporting.value = true;
  exportProgress.value = 0;
  progressMessage.value = 'Generating frames...';

  const options: ExportOptions = {
    width: exportWidth.value,
    height: exportHeight.value,
    matteMode: matteMode.value
  };

  try {
    // Generate all frames
    const frames = await matteExporter.generateMatteSequence(
      store.project,
      options,
      (progress) => {
        exportProgress.value = progress.percent;
        progressMessage.value = `Generating frame ${progress.frame + 1} of ${progress.total}...`;
      }
    );

    // Package as ZIP
    progressMessage.value = 'Creating ZIP archive...';
    await matteExporter.downloadAsZip(
      frames,
      `matte_${Date.now()}`,
      (percent) => {
        progressMessage.value = `Compressing... ${percent}%`;
      }
    );

    progressMessage.value = 'Export complete!';
    emit('exported');

    // Close after brief delay
    setTimeout(() => {
      emit('close');
    }, 1000);

  } catch (err) {
    console.error('[ExportDialog] Export failed:', err);
    progressMessage.value = `Export failed: ${err instanceof Error ? err.message : 'Unknown error'}`;
  } finally {
    isExporting.value = false;
  }
}

// Watch for changes that affect preview
watch(
  [exportWidth, exportHeight, matteMode],
  () => {
    generatePreview();
  },
  { immediate: false }
);

// Initialize
onMounted(() => {
  // Set initial dimensions from composition
  if (store.hasProject) {
    const validation = matteExporter.validateDimensions(store.width, store.height);
    customWidth.value = validation.correctedWidth;
    customHeight.value = validation.correctedHeight;

    // Check if matches a preset
    const matchingPreset = resolutionPresets.find(
      p => p.width === customWidth.value && p.height === customHeight.value
    );
    selectedPreset.value = matchingPreset?.label || '';

    if (!validation.valid) {
      dimensionWarning.value = validation.message;
    }
  }

  generatePreview();
});

// Cleanup
onUnmounted(() => {
  if (previewUrl.value) {
    URL.revokeObjectURL(previewUrl.value);
  }
  matteExporter.dispose();
});
</script>

<style scoped>
.export-dialog-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.6);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.export-dialog {
  width: 520px;
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

.resolution-presets {
  display: flex;
  gap: 8px;
  margin-bottom: 12px;
}

.preset-btn {
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

.preset-btn:hover {
  background: #333;
  color: #fff;
}

.preset-btn.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.custom-resolution {
  display: flex;
  align-items: flex-end;
  gap: 8px;
}

.dimension-input {
  flex: 1;
}

.dimension-input label {
  display: block;
  font-size: 12px;
  color: #666;
  margin-bottom: 4px;
}

.dimension-input input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 13px;
}

.dimension-input input:focus {
  outline: none;
  border-color: #4a90d9;
}

.dimension-x {
  color: #666;
  font-size: 14px;
  padding-bottom: 6px;
}

.dimension-warning {
  display: flex;
  align-items: center;
  gap: 6px;
  margin-top: 8px;
  padding: 6px 10px;
  background: rgba(255, 193, 7, 0.1);
  border: 1px solid rgba(255, 193, 7, 0.3);
  border-radius: 4px;
  font-size: 13px;
  color: #ffc107;
}

.matte-mode-options {
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
  font-size: 12px;
  font-weight: 500;
  color: #e0e0e0;
}

.mode-btn small {
  font-size: 12px;
  color: #666;
  text-align: center;
}

.preview-container {
  width: 100%;
  height: 200px;
  background: #1e1e1e;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
  overflow: hidden;
}

.preview-image {
  max-width: 100%;
  max-height: 100%;
  object-fit: contain;
}

.preview-placeholder {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 8px;
  color: #666;
}

.preview-placeholder i {
  font-size: 32px;
}

.preview-placeholder span {
  font-size: 12px;
}

.preview-info {
  margin-top: 8px;
  font-size: 12px;
  color: #666;
  text-align: center;
}

.progress-section {
  margin-top: 16px;
  padding: 12px;
  background: #1e1e1e;
  border-radius: 4px;
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
  font-size: 13px;
  color: #aaa;
  text-align: center;
}

.dialog-footer {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 12px 16px;
  border-top: 1px solid #3d3d3d;
}

.export-info {
  flex: 1;
  font-size: 13px;
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

.export-btn {
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

.export-btn:hover:not(:disabled) {
  background: #5a9fe9;
}

.export-btn:disabled {
  background: #333;
  color: #666;
  cursor: not-allowed;
}
</style>
