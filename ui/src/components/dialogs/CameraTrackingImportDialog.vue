<template>
  <div v-if="visible" class="dialog-overlay" @click.self="close">
    <div class="dialog-content">
      <div class="dialog-header">
        <h3>Import Camera Tracking</h3>
        <button class="close-btn" @click="close">×</button>
      </div>

      <div class="dialog-body">
        <!-- File Input Section -->
        <div class="section">
          <h4>Tracking Data</h4>
          <div class="file-drop-zone"
               :class="{ dragover: isDragging }"
               @dragover.prevent="isDragging = true"
               @dragleave="isDragging = false"
               @drop.prevent="handleDrop">
            <i class="pi pi-cloud-upload" />
            <p v-if="!selectedFile">
              Drop tracking file here or
              <label class="file-label">
                <input
                  type="file"
                  accept=".json,.txt"
                  @change="handleFileSelect"
                />
                browse
              </label>
            </p>
            <p v-else class="selected-file">
              <i class="pi pi-file" />
              {{ selectedFile.name }}
              <span class="format-badge">{{ detectedFormat.toUpperCase() }}</span>
              <button class="clear-btn" @click="clearFile">×</button>
            </p>
          </div>

          <div class="format-info">
            <p>Supported formats:</p>
            <ul>
              <li><strong>Lattice JSON</strong> - Native tracking format</li>
              <li><strong>COLMAP</strong> - cameras.txt, images.txt, points3D.txt</li>
              <li><strong>Blender</strong> - Motion tracking JSON export</li>
            </ul>
          </div>
        </div>

        <!-- Parse Result -->
        <div v-if="parseResult" class="section">
          <h4>Tracking Data Preview</h4>
          <div class="preview-stats">
            <div class="stat">
              <span class="label">Source</span>
              <span class="value">{{ parseResult.source }}</span>
            </div>
            <div class="stat">
              <span class="label">Frames</span>
              <span class="value">{{ parseResult.cameraPath.length }}</span>
            </div>
            <div class="stat">
              <span class="label">Resolution</span>
              <span class="value">{{ parseResult.metadata.sourceWidth }}×{{ parseResult.metadata.sourceHeight }}</span>
            </div>
            <div class="stat" v-if="parseResult.trackPoints3D">
              <span class="label">3D Points</span>
              <span class="value">{{ parseResult.trackPoints3D.length }}</span>
            </div>
          </div>
        </div>

        <!-- Import Options -->
        <div v-if="parseResult" class="section">
          <h4>Import Options</h4>

          <div class="option-row">
            <label>
              <input type="checkbox" v-model="options.createCamera" />
              Create camera layer
            </label>
          </div>

          <div class="option-row">
            <label>
              <input type="checkbox" v-model="options.createNulls" />
              Create null objects at track points
            </label>
            <small v-if="options.createNulls">(Limited to 100 points)</small>
          </div>

          <div class="option-row">
            <label>
              <input type="checkbox" v-model="options.pointCloud.create" />
              Create point cloud layer
            </label>
          </div>

          <div class="option-group">
            <label>Scale</label>
            <input
              type="number"
              v-model.number="options.scale"
              min="0.001"
              step="0.1"
            />
          </div>

          <div class="option-group offset-group">
            <label>Position Offset</label>
            <div class="xyz-inputs">
              <input type="number" v-model.number="options.offset.x" placeholder="X" />
              <input type="number" v-model.number="options.offset.y" placeholder="Y" />
              <input type="number" v-model.number="options.offset.z" placeholder="Z" />
            </div>
          </div>

          <div class="option-row">
            <label>
              <input type="checkbox" v-model="options.flipY" />
              Flip Y axis (common for Blender/OpenGL)
            </label>
          </div>

          <div class="option-row">
            <label>
              <input type="checkbox" v-model="options.flipZ" />
              Flip Z axis
            </label>
          </div>

          <div class="option-group">
            <label>Frame Offset</label>
            <input
              type="number"
              v-model.number="options.frameOffset"
              step="1"
            />
          </div>
        </div>

        <!-- Error Display -->
        <div v-if="error" class="error-message">
          <i class="pi pi-exclamation-triangle" />
          {{ error }}
        </div>
      </div>

      <div class="dialog-footer">
        <button class="btn secondary" @click="close">Cancel</button>
        <button
          class="btn primary"
          @click="importTracking"
          :disabled="!parseResult || importing"
        >
          <i v-if="importing" class="pi pi-spin pi-spinner" />
          {{ importing ? 'Importing...' : 'Import' }}
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { reactive, ref, watch } from "vue";
import {
  detectTrackingFormat,
  importCameraTracking,
  parseBlenderTrackingJSON,
  parseLatticeTrackingJSON,
} from "@/services/cameraTrackingImport";
import type {
  CameraTrackingImportOptions,
  CameraTrackingSolve,
} from "@/types/cameraTracking";

// Local type with required properties (always initialized in this dialog)
interface DialogImportOptions extends CameraTrackingImportOptions {
  offset: { x: number; y: number; z: number };
  pointCloud: {
    create: boolean;
    maxPoints?: number;
    pointSize?: number;
  };
}

const props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<{
  (e: "close"): void;
  (
    e: "imported",
    result: { cameraLayerId?: string; warnings?: string[] },
  ): void;
}>();

const isDragging = ref(false);
const selectedFile = ref<File | null>(null);
const detectedFormat = ref<string>("unknown");
const parseResult = ref<CameraTrackingSolve | null>(null);
const error = ref<string | null>(null);
const importing = ref(false);

const options = reactive<DialogImportOptions>({
  scale: 1,
  offset: { x: 0, y: 0, z: 0 },
  frameOffset: 0,
  flipY: false,
  flipZ: false,
  createCamera: true,
  createNulls: false,
  pointCloud: {
    create: false,
    maxPoints: 50000,
    pointSize: 2,
  },
});

watch(
  () => props.visible,
  (visible) => {
    if (!visible) {
      clearFile();
    }
  },
);

function close() {
  emit("close");
}

function clearFile() {
  selectedFile.value = null;
  parseResult.value = null;
  error.value = null;
  detectedFormat.value = "unknown";
}

function _handleFileSelect(event: Event) {
  const input = event.target as HTMLInputElement;
  if (input.files?.[0]) {
    processFile(input.files[0]);
  }
}

function _handleDrop(event: DragEvent) {
  isDragging.value = false;
  const files = event.dataTransfer?.files;
  if (files?.[0]) {
    processFile(files[0]);
  }
}

async function processFile(file: File) {
  selectedFile.value = file;
  error.value = null;
  parseResult.value = null;

  try {
    const content = await file.text();
    detectedFormat.value = detectTrackingFormat(content);

    switch (detectedFormat.value) {
      case "lattice":
        parseResult.value = parseLatticeTrackingJSON(content);
        break;
      case "blender":
        parseResult.value = parseBlenderTrackingJSON(content);
        // Auto-enable flip Y for Blender
        options.flipY = true;
        break;
      case "colmap":
        error.value =
          "COLMAP format requires multiple files (cameras.txt, images.txt). Please use a combined JSON export.";
        break;
      default:
        error.value =
          "Unknown tracking format. Please use Lattice JSON or Blender export.";
    }
  } catch (err) {
    error.value = err instanceof Error ? err.message : "Failed to parse file";
  }
}

async function _importTracking() {
  if (!parseResult.value) return;

  importing.value = true;
  error.value = null;

  try {
    const result = await importCameraTracking(parseResult.value, options);

    if (result.success) {
      emit("imported", {
        cameraLayerId: result.cameraLayerId,
        warnings: result.warnings,
      });
      close();
    } else {
      error.value = result.error || "Import failed";
    }
  } catch (err) {
    error.value = err instanceof Error ? err.message : "Import failed";
  } finally {
    importing.value = false;
  }
}
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.dialog-content {
  background: var(--lattice-surface-1, #121212);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: var(--lattice-radius-lg, 8px);
  width: 520px;
  max-height: 80vh;
  display: flex;
  flex-direction: column;
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 16px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.dialog-header h3 {
  margin: 0;
  font-size: 16px;
  color: var(--lattice-text-primary, #E5E5E5);
}

.close-btn {
  background: none;
  border: none;
  color: var(--lattice-text-muted, #6B7280);
  font-size: 24px;
  cursor: pointer;
  padding: 0;
  line-height: 1;
}

.close-btn:hover {
  color: var(--lattice-text-primary, #E5E5E5);
}

.dialog-body {
  padding: 16px;
  overflow-y: auto;
  flex: 1;
}

.section {
  margin-bottom: 20px;
}

.section h4 {
  margin: 0 0 12px 0;
  font-size: 13px;
  color: var(--lattice-text-secondary, #9CA3AF);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.file-drop-zone {
  border: 2px dashed var(--lattice-border-default, #333);
  border-radius: var(--lattice-radius-md, 4px);
  padding: 32px;
  text-align: center;
  color: var(--lattice-text-muted, #6B7280);
  transition: all 0.2s;
}

.file-drop-zone.dragover {
  border-color: var(--lattice-accent, #8B5CF6);
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.1));
}

.file-drop-zone .pi-cloud-upload {
  font-size: 32px;
  margin-bottom: 12px;
  display: block;
}

.file-label {
  color: var(--lattice-accent, #8B5CF6);
  cursor: pointer;
}

.file-label:hover {
  text-decoration: underline;
}

.file-label input {
  display: none;
}

.selected-file {
  display: flex;
  align-items: center;
  gap: 8px;
  color: var(--lattice-text-primary, #E5E5E5);
}

.format-badge {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
  padding: 2px 6px;
  border-radius: 4px;
  font-size: 10px;
  font-weight: 600;
}

.clear-btn {
  background: none;
  border: none;
  color: var(--lattice-text-muted, #6B7280);
  cursor: pointer;
  font-size: 16px;
  margin-left: auto;
}

.format-info {
  margin-top: 12px;
  font-size: 12px;
  color: var(--lattice-text-muted, #6B7280);
}

.format-info ul {
  margin: 8px 0 0 0;
  padding-left: 20px;
}

.format-info li {
  margin-bottom: 4px;
}

.preview-stats {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 12px;
  background: var(--lattice-surface-2, #1a1a1a);
  padding: 12px;
  border-radius: var(--lattice-radius-md, 4px);
}

.stat {
  display: flex;
  flex-direction: column;
}

.stat .label {
  font-size: 11px;
  color: var(--lattice-text-muted, #6B7280);
  text-transform: uppercase;
}

.stat .value {
  font-size: 14px;
  color: var(--lattice-text-primary, #E5E5E5);
  font-weight: 500;
}

.option-row {
  margin-bottom: 12px;
}

.option-row label {
  display: flex;
  align-items: center;
  gap: 8px;
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: 13px;
  cursor: pointer;
}

.option-row small {
  font-size: 11px;
  color: var(--lattice-text-muted, #6B7280);
  margin-left: 24px;
}

.option-group {
  margin-bottom: 12px;
}

.option-group label {
  display: block;
  font-size: 12px;
  color: var(--lattice-text-secondary, #9CA3AF);
  margin-bottom: 4px;
}

.option-group input[type="number"] {
  width: 100px;
  padding: 6px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: var(--lattice-radius-sm, 2px);
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: 12px;
}

.xyz-inputs {
  display: flex;
  gap: 8px;
}

.xyz-inputs input {
  width: 70px;
}

.error-message {
  background: rgba(239, 68, 68, 0.1);
  border: 1px solid rgba(239, 68, 68, 0.3);
  border-radius: var(--lattice-radius-md, 4px);
  padding: 12px;
  color: #EF4444;
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 13px;
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  padding: 16px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.btn {
  padding: 8px 16px;
  border-radius: var(--lattice-radius-md, 4px);
  font-size: 13px;
  font-weight: 500;
  cursor: pointer;
  display: flex;
  align-items: center;
  gap: 6px;
  transition: all 0.2s;
}

.btn.secondary {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #333);
  color: var(--lattice-text-primary, #E5E5E5);
}

.btn.secondary:hover {
  background: var(--lattice-surface-3, #222);
}

.btn.primary {
  background: var(--lattice-accent, #8B5CF6);
  border: none;
  color: white;
}

.btn.primary:hover:not(:disabled) {
  background: var(--lattice-accent-hover, #A78BFA);
}

.btn.primary:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}
</style>
