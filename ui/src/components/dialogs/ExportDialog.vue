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

        <!-- Additional Export Options -->
        <div class="form-group">
          <label>Additional Outputs</label>
          <div class="export-options">
            <label class="checkbox-option">
              <input
                type="checkbox"
                v-model="exportDepthMaps"
              />
              <span class="checkbox-label">
                <i class="pi pi-box" />
                Export Depth Maps
              </span>
              <small>Include grayscale depth frames (for depth-aware AI models)</small>
            </label>
            <label class="checkbox-option">
              <input
                type="checkbox"
                v-model="exportNormalMaps"
              />
              <span class="checkbox-label">
                <i class="pi pi-compass" />
                Export Normal Maps
              </span>
              <small>Include surface normal frames (RGB encoded)</small>
            </label>
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
        <button
          class="collect-btn"
          @click="collectProject"
          :disabled="isExporting || isCollecting || !store.hasProject"
          title="Download project with all assets as ZIP"
        >
          <i class="pi pi-folder" />
          {{ isCollecting ? `Collecting ${collectProgress}%` : 'Collect Files' }}
        </button>
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
import { computed, onMounted, onUnmounted, ref, watch } from "vue";
import { type ExportOptions, matteExporter } from "@/services/matteExporter";
import { projectCollectionService } from "@/services/projectCollection";
import { useCompositorStore } from "@/stores/compositorStore";

const emit = defineEmits<{
  (e: "close"): void;
  (e: "exported"): void;
}>();

const store = useCompositorStore();

// Resolution presets
const resolutionPresets = matteExporter.getResolutionPresets();

// Project collection state
const isCollecting = ref(false);
const collectProgress = ref(0);

// Collect project as ZIP
async function _collectProject() {
  if (isCollecting.value || !store.project) return;

  isCollecting.value = true;
  collectProgress.value = 0;

  try {
    // Convert Record<string, AssetReference> to Map for collection service
    const assetsMap = new Map(Object.entries(store.project.assets || {}));
    const blob = await projectCollectionService.collectProject(
      store.project,
      assetsMap,
      {
        includeProject: true,
        includeAssets: true,
        includeRenderedFrames: false,
        flatStructure: false,
      },
      (progress) => {
        collectProgress.value = progress.percent;
      },
    );

    // Download the ZIP
    const projectName = store.project.meta?.name || "lattice-project";
    projectCollectionService.downloadZip(blob, `${projectName}-collection.zip`);

    console.log("[ExportDialog] Project collected successfully");
  } catch (error) {
    console.error("[ExportDialog] Collection failed:", error);
    alert(
      `Collection failed: ${error instanceof Error ? error.message : "Unknown error"}`,
    );
  } finally {
    isCollecting.value = false;
    collectProgress.value = 0;
  }
}

// State
const selectedPreset = ref("720p (1280x720)");
const customWidth = ref(1280);
const customHeight = ref(720);
const dimensionWarning = ref<string | undefined>();
const matteMode = ref<"exclude_text" | "include_all">("exclude_text");
const previewUrl = ref<string | null>(null);
const isExporting = ref(false);
const exportProgress = ref(0);
const progressMessage = ref("");

// Additional export options
const exportDepthMaps = ref(false);
const exportNormalMaps = ref(false);

// Computed export dimensions
const exportWidth = computed(() => customWidth.value);
const exportHeight = computed(() => customHeight.value);

// Select a preset
function _selectPreset(preset: {
  label: string;
  width: number;
  height: number;
}): void {
  selectedPreset.value = preset.label;
  customWidth.value = preset.width;
  customHeight.value = preset.height;
  dimensionWarning.value = undefined;
}

// Validate custom dimensions
function _validateCustomDimensions(): void {
  const validation = matteExporter.validateDimensions(
    customWidth.value,
    customHeight.value,
  );

  if (!validation.valid) {
    customWidth.value = validation.correctedWidth;
    customHeight.value = validation.correctedHeight;
    dimensionWarning.value = validation.message;
    selectedPreset.value = "";
  } else {
    dimensionWarning.value = undefined;
    // Check if matches a preset
    const matchingPreset = resolutionPresets.find(
      (p) => p.width === customWidth.value && p.height === customHeight.value,
    );
    selectedPreset.value = matchingPreset?.label || "";
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
    matteMode: matteMode.value,
  };

  previewUrl.value = await matteExporter.generatePreviewFrame(
    store.project,
    0,
    options,
  );
}

// Start export
async function _startExport(): Promise<void> {
  if (isExporting.value || !store.hasProject) return;

  isExporting.value = true;
  exportProgress.value = 0;
  progressMessage.value = "Generating matte frames...";

  const options: ExportOptions = {
    width: exportWidth.value,
    height: exportHeight.value,
    matteMode: matteMode.value,
  };

  try {
    // Dynamic import JSZip
    const JSZip = (await import("jszip")).default;
    const zip = new JSZip();

    // Generate matte frames
    const matteFrames = await matteExporter.generateMatteSequence(
      store.project,
      options,
      (progress) => {
        const baseProgress = 0;
        const matteWeight =
          exportDepthMaps.value || exportNormalMaps.value ? 0.5 : 1;
        exportProgress.value = baseProgress + progress.percent * matteWeight;
        progressMessage.value = `Generating matte frame ${progress.frame + 1} of ${progress.total}...`;
      },
    );

    // Add matte frames to ZIP
    matteFrames.forEach((blob, index) => {
      const frameName = `matte_${String(index).padStart(4, "0")}.png`;
      zip.file(frameName, blob);
    });

    // Generate depth maps if enabled
    if (exportDepthMaps.value) {
      progressMessage.value = "Generating depth maps...";
      const depthFrames = await generateDepthFrames(
        store.frameCount,
        exportWidth.value,
        exportHeight.value,
        (frame, total) => {
          const baseProgress = exportNormalMaps.value ? 50 : 75;
          const weight = exportNormalMaps.value ? 25 : 25;
          exportProgress.value = baseProgress + (frame / total) * weight;
          progressMessage.value = `Generating depth frame ${frame + 1} of ${total}...`;
        },
      );
      depthFrames.forEach((blob, index) => {
        const frameName = `depth_${String(index).padStart(4, "0")}.png`;
        zip.file(frameName, blob);
      });
    }

    // Generate normal maps if enabled
    if (exportNormalMaps.value) {
      progressMessage.value = "Generating normal maps...";
      const normalFrames = await generateNormalFrames(
        store.frameCount,
        exportWidth.value,
        exportHeight.value,
        (frame, total) => {
          const baseProgress = exportDepthMaps.value ? 75 : 75;
          exportProgress.value = baseProgress + (frame / total) * 25;
          progressMessage.value = `Generating normal frame ${frame + 1} of ${total}...`;
        },
      );
      normalFrames.forEach((blob, index) => {
        const frameName = `normal_${String(index).padStart(4, "0")}.png`;
        zip.file(frameName, blob);
      });
    }

    // Package and download ZIP
    progressMessage.value = "Creating ZIP archive...";
    const content = await zip.generateAsync({ type: "blob" }, (metadata) => {
      progressMessage.value = `Compressing... ${Math.round(metadata.percent)}%`;
    });

    // Download
    const url = URL.createObjectURL(content);
    const link = document.createElement("a");
    link.href = url;
    link.download = `export_${Date.now()}.zip`;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    URL.revokeObjectURL(url);

    progressMessage.value = "Export complete!";
    emit("exported");

    // Close after brief delay
    setTimeout(() => {
      emit("close");
    }, 1000);
  } catch (err) {
    console.error("[ExportDialog] Export failed:", err);
    progressMessage.value = `Export failed: ${err instanceof Error ? err.message : "Unknown error"}`;
  } finally {
    isExporting.value = false;
  }
}

// Generate depth map frames from current composition
async function generateDepthFrames(
  frameCount: number,
  width: number,
  height: number,
  onProgress?: (frame: number, total: number) => void,
): Promise<Blob[]> {
  const frames: Blob[] = [];
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext("2d")!;

  for (let frame = 0; frame < frameCount; frame++) {
    if (onProgress) onProgress(frame, frameCount);

    // Render depth as grayscale gradient (simulated depth based on layer order)
    // In a full implementation, this would use Three.js depth buffer
    ctx.fillStyle = "#000000";
    ctx.fillRect(0, 0, width, height);

    // Get layers sorted by z-index/depth
    const layers = store.activeComposition?.layers || [];
    const visibleLayers = layers.filter((layer) => {
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      return layer.visible && frame >= start && frame <= end;
    });

    // Render each layer as a depth value (farther = darker, closer = brighter)
    for (let i = 0; i < visibleLayers.length; i++) {
      const depth = Math.round(
        (i / Math.max(visibleLayers.length - 1, 1)) * 255,
      );
      const gray = 255 - depth; // Invert: closer layers are brighter
      ctx.fillStyle = `rgb(${gray}, ${gray}, ${gray})`;

      // Simple rectangular representation (actual impl would render layer shapes)
      const layer = visibleLayers[i];
      const pos = layer.transform?.position?.value || {
        x: width / 2,
        y: height / 2,
      };
      const scale = layer.transform?.scale?.value || { x: 1, y: 1 };
      const w = 200 * scale.x;
      const h = 150 * scale.y;
      ctx.fillRect(pos.x - w / 2, pos.y - h / 2, w, h);
    }

    const blob = await canvas.convertToBlob({ type: "image/png" });
    frames.push(blob);
  }

  return frames;
}

// Generate normal map frames from current composition
async function generateNormalFrames(
  frameCount: number,
  width: number,
  height: number,
  onProgress?: (frame: number, total: number) => void,
): Promise<Blob[]> {
  const frames: Blob[] = [];
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext("2d")!;

  for (let frame = 0; frame < frameCount; frame++) {
    if (onProgress) onProgress(frame, frameCount);

    // Default normal map: flat surface pointing toward camera (RGB 128, 128, 255)
    ctx.fillStyle = "rgb(128, 128, 255)";
    ctx.fillRect(0, 0, width, height);

    // In a full implementation, this would calculate actual surface normals
    // For now, generate a simple normal map with slight variation per layer
    const layers = store.activeComposition?.layers || [];
    const visibleLayers = layers.filter((layer) => {
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      return layer.visible && frame >= start && frame <= end;
    });

    for (const layer of visibleLayers) {
      const pos = layer.transform?.position?.value || {
        x: width / 2,
        y: height / 2,
      };
      const scale = layer.transform?.scale?.value || { x: 1, y: 1 };
      const w = 200 * scale.x;
      const h = 150 * scale.y;

      // Slight normal variation based on layer type
      const r = 128 + Math.random() * 10 - 5;
      const g = 128 + Math.random() * 10 - 5;
      ctx.fillStyle = `rgb(${r}, ${g}, 255)`;
      ctx.fillRect(pos.x - w / 2, pos.y - h / 2, w, h);
    }

    const blob = await canvas.convertToBlob({ type: "image/png" });
    frames.push(blob);
  }

  return frames;
}

// Watch for changes that affect preview
watch(
  [exportWidth, exportHeight, matteMode],
  () => {
    generatePreview();
  },
  { immediate: false },
);

// Initialize
onMounted(() => {
  // Set initial dimensions from composition
  if (store.hasProject) {
    const validation = matteExporter.validateDimensions(
      store.width,
      store.height,
    );
    customWidth.value = validation.correctedWidth;
    customHeight.value = validation.correctedHeight;

    // Check if matches a preset
    const matchingPreset = resolutionPresets.find(
      (p) => p.width === customWidth.value && p.height === customHeight.value,
    );
    selectedPreset.value = matchingPreset?.label || "";

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

.collect-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 16px;
  border: 1px solid #6b5b95;
  background: transparent;
  color: #a89cc8;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.collect-btn:hover:not(:disabled) {
  background: rgba(107, 91, 149, 0.2);
  color: #c8b8e8;
  border-color: #8b7bb5;
}

.collect-btn:disabled {
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

.export-options {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.checkbox-option {
  display: flex;
  align-items: flex-start;
  gap: 10px;
  padding: 10px 12px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.1s;
}

.checkbox-option:hover {
  background: #2a2a2a;
  border-color: #4a90d9;
}

.checkbox-option input[type="checkbox"] {
  width: 16px;
  height: 16px;
  margin-top: 2px;
  accent-color: #4a90d9;
  cursor: pointer;
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 6px;
  font-size: 13px;
  font-weight: 500;
  color: #e0e0e0;
}

.checkbox-label i {
  font-size: 14px;
  color: #888;
}

.checkbox-option:has(input:checked) .checkbox-label i {
  color: #4a90d9;
}

.checkbox-option small {
  display: block;
  font-size: 12px;
  color: #666;
  margin-top: 4px;
  margin-left: 26px;
}
</style>
