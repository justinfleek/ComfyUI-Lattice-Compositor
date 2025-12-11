<script setup lang="ts">
/**
 * Export Dialog
 * UI for configuring and executing exports to ComfyUI
 */

import { ref, computed, watch, onMounted, onUnmounted } from 'vue';
import type {
  ExportConfig,
  ExportTarget,
  ExportProgress,
  DepthMapFormat,
  ControlType,
} from '@/types/export';
import type { Layer } from '@/types';
import { EXPORT_PRESETS, EXPORT_TARGET_INFO, RESOLUTION_PRESETS, FRAME_COUNT_PRESETS } from '@/config/exportPresets';
import { exportToComfyUI } from '@/services/export/exportPipeline';
import { getComfyUIClient } from '@/services/comfyui/comfyuiClient';
import ScrubableNumber from '@/components/controls/ScrubableNumber.vue';

// ============================================================================
// Props & Emits
// ============================================================================

interface Props {
  layers: Layer[];
  cameraKeyframes: any[];
  currentFrame: number;
  totalFrames: number;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  close: [];
  exported: [result: any];
}>();

// ============================================================================
// State
// ============================================================================

const activeTab = ref<'target' | 'output' | 'generation' | 'comfyui'>('target');

// Export target
const selectedTarget = ref<ExportTarget>('wan22-i2v');

// Output settings
const width = ref(832);
const height = ref(480);
const frameCount = ref(81);
const fps = ref(24);
const startFrame = ref(0);
const endFrame = ref(81);

// Export options
const exportDepthMap = ref(true);
const exportControlImages = ref(false);
const exportCameraData = ref(true);
const exportReferenceFrame = ref(true);
const exportLastFrame = ref(false);
const depthFormat = ref<DepthMapFormat>('midas');
const controlType = ref<ControlType>('depth');

// Generation settings
const prompt = ref('');
const negativePrompt = ref('blurry, low quality, distorted');
const seed = ref<number | undefined>(undefined);
const steps = ref(30);
const cfgScale = ref(5);

// ComfyUI settings
const comfyuiServer = ref('127.0.0.1:8188');
const autoQueueWorkflow = ref(false);
const connectionStatus = ref<'disconnected' | 'connecting' | 'connected' | 'error'>('disconnected');

// Export state
const isExporting = ref(false);
const exportProgress = ref<ExportProgress | null>(null);
const exportError = ref<string | null>(null);
const abortController = ref<AbortController | null>(null);

// ============================================================================
// Computed
// ============================================================================

const targetInfo = computed(() => EXPORT_TARGET_INFO[selectedTarget.value]);

const targetCategories = computed(() => ({
  'Wan 2.2': ['wan22-i2v', 'wan22-t2v', 'wan22-fun-camera', 'wan22-first-last'] as ExportTarget[],
  'Uni3C': ['uni3c-camera', 'uni3c-motion'] as ExportTarget[],
  'MotionCtrl': ['motionctrl', 'motionctrl-svd'] as ExportTarget[],
  'Other': ['cogvideox', 'animatediff-cameractrl'] as ExportTarget[],
  'ControlNet': ['controlnet-depth', 'controlnet-canny', 'controlnet-lineart'] as ExportTarget[],
  'Custom': ['custom-workflow'] as ExportTarget[],
}));

const targetDisplayName = computed(() => {
  const names: Record<ExportTarget, string> = {
    'wan22-i2v': 'Image to Video',
    'wan22-t2v': 'Text to Video',
    'wan22-fun-camera': 'Fun Camera',
    'wan22-first-last': 'First + Last Frame',
    'uni3c-camera': 'Camera Control',
    'uni3c-motion': 'Motion + Camera',
    'motionctrl': 'MotionCtrl',
    'motionctrl-svd': 'MotionCtrl SVD',
    'cogvideox': 'CogVideoX I2V',
    'animatediff-cameractrl': 'CameraCtrl',
    'controlnet-depth': 'Depth',
    'controlnet-canny': 'Canny Edge',
    'controlnet-lineart': 'Line Art',
    'custom-workflow': 'Custom Workflow',
  };
  return names;
});

const depthFormats: { value: DepthMapFormat; label: string }[] = [
  { value: 'midas', label: 'MiDaS (8-bit inverted)' },
  { value: 'zoe', label: 'Zoe (16-bit linear)' },
  { value: 'depth-pro', label: 'Depth-Pro (metric)' },
  { value: 'normalized', label: 'Normalized (0-1)' },
];

const controlTypes: { value: ControlType; label: string }[] = [
  { value: 'depth', label: 'Depth' },
  { value: 'canny', label: 'Canny Edge' },
  { value: 'lineart', label: 'Line Art' },
  { value: 'softedge', label: 'Soft Edge' },
  { value: 'normal', label: 'Normal Map' },
];

// ============================================================================
// Methods
// ============================================================================

function selectTarget(target: ExportTarget) {
  selectedTarget.value = target;

  // Apply preset settings
  const preset = EXPORT_PRESETS[target];
  if (preset) {
    width.value = preset.defaultWidth;
    height.value = preset.defaultHeight;
    frameCount.value = preset.defaultFrameCount;
    fps.value = preset.defaultFPS;
    endFrame.value = frameCount.value;
  }

  // Update export options based on target
  const info = EXPORT_TARGET_INFO[target];
  if (info) {
    exportDepthMap.value = info.requiresInputs.includes('depth_sequence');
    exportCameraData.value = info.requiresInputs.includes('camera_data');
    exportReferenceFrame.value = info.requiresInputs.includes('reference_image');
    exportLastFrame.value = info.requiresInputs.includes('last_frame');
    exportControlImages.value = target.startsWith('controlnet-');
  }
}

async function checkConnection() {
  connectionStatus.value = 'connecting';

  try {
    const client = getComfyUIClient(comfyuiServer.value);
    const connected = await client.checkConnection();
    connectionStatus.value = connected ? 'connected' : 'error';
  } catch {
    connectionStatus.value = 'error';
  }
}

function applyResolutionPreset(preset: { width: number; height: number }) {
  width.value = preset.width;
  height.value = preset.height;
}

function applyFrameCountPreset(count: number) {
  frameCount.value = count;
  endFrame.value = Math.min(endFrame.value, count);
}

function randomizeSeed() {
  seed.value = Math.floor(Math.random() * 2147483647);
}

async function startExport() {
  isExporting.value = true;
  exportError.value = null;
  abortController.value = new AbortController();

  const config: ExportConfig = {
    target: selectedTarget.value,
    width: width.value,
    height: height.value,
    frameCount: frameCount.value,
    fps: fps.value,
    startFrame: startFrame.value,
    endFrame: endFrame.value,
    outputDir: '',
    filenamePrefix: `weyl_${selectedTarget.value}_${Date.now()}`,
    exportDepthMap: exportDepthMap.value,
    exportControlImages: exportControlImages.value,
    exportCameraData: exportCameraData.value,
    exportReferenceFrame: exportReferenceFrame.value,
    exportLastFrame: exportLastFrame.value,
    depthFormat: depthFormat.value,
    controlType: controlType.value,
    prompt: prompt.value,
    negativePrompt: negativePrompt.value,
    seed: seed.value,
    steps: steps.value,
    cfgScale: cfgScale.value,
    comfyuiServer: comfyuiServer.value,
    autoQueueWorkflow: autoQueueWorkflow.value,
  };

  try {
    const result = await exportToComfyUI(
      props.layers,
      props.cameraKeyframes,
      config,
      (progress) => {
        exportProgress.value = progress;
      }
    );

    if (result.success) {
      emit('exported', result);
    } else {
      exportError.value = result.errors.join('\n');
    }
  } catch (error) {
    exportError.value = error instanceof Error ? error.message : 'Export failed';
  } finally {
    isExporting.value = false;
    abortController.value = null;
  }
}

function cancelExport() {
  if (abortController.value) {
    abortController.value.abort();
  }
}

function close() {
  if (isExporting.value) {
    cancelExport();
  }
  emit('close');
}

// ============================================================================
// Lifecycle
// ============================================================================

onMounted(() => {
  // Initialize with current timeline range
  endFrame.value = Math.min(frameCount.value, props.totalFrames);

  // Check ComfyUI connection
  checkConnection();
});

watch(selectedTarget, () => {
  selectTarget(selectedTarget.value);
});
</script>

<template>
  <div class="export-dialog-overlay" @click.self="close">
    <div class="export-dialog">
      <!-- Header -->
      <header class="dialog-header">
        <h2>Export to ComfyUI</h2>
        <button class="close-btn" @click="close">&times;</button>
      </header>

      <!-- Tabs -->
      <nav class="dialog-tabs">
        <button
          :class="{ active: activeTab === 'target' }"
          @click="activeTab = 'target'"
        >
          Target
        </button>
        <button
          :class="{ active: activeTab === 'output' }"
          @click="activeTab = 'output'"
        >
          Output
        </button>
        <button
          :class="{ active: activeTab === 'generation' }"
          @click="activeTab = 'generation'"
        >
          Generation
        </button>
        <button
          :class="{ active: activeTab === 'comfyui' }"
          @click="activeTab = 'comfyui'"
        >
          ComfyUI
        </button>
      </nav>

      <!-- Content -->
      <div class="dialog-content">
        <!-- Target Selection Tab -->
        <div v-if="activeTab === 'target'" class="tab-content">
          <div class="target-grid">
            <div
              v-for="(targets, category) in targetCategories"
              :key="category"
              class="target-category"
            >
              <h3>{{ category }}</h3>
              <div class="target-buttons">
                <button
                  v-for="target in targets"
                  :key="target"
                  :class="{ selected: selectedTarget === target }"
                  @click="selectTarget(target)"
                >
                  {{ targetDisplayName[target] }}
                </button>
              </div>
            </div>
          </div>

          <!-- Target Info -->
          <div v-if="targetInfo" class="target-info">
            <h4>{{ targetDisplayName[selectedTarget] }}</h4>
            <div class="info-row">
              <span class="label">Required:</span>
              <span>{{ targetInfo.requiresInputs.join(', ') || 'None' }}</span>
            </div>
            <div class="info-row">
              <span class="label">Optional:</span>
              <span>{{ targetInfo.optionalInputs.join(', ') || 'None' }}</span>
            </div>
            <div class="info-row">
              <span class="label">Outputs:</span>
              <span>{{ targetInfo.outputTypes.join(', ') }}</span>
            </div>
          </div>
        </div>

        <!-- Output Settings Tab -->
        <div v-if="activeTab === 'output'" class="tab-content">
          <div class="settings-section">
            <h3>Resolution</h3>
            <div class="preset-buttons">
              <button
                v-for="preset in RESOLUTION_PRESETS"
                :key="preset.label"
                @click="applyResolutionPreset(preset)"
              >
                {{ preset.label }}
              </button>
            </div>
            <div class="input-row">
              <ScrubableNumber
                v-model="width"
                label="Width"
                :min="64"
                :max="4096"
                :step="8"
              />
              <ScrubableNumber
                v-model="height"
                label="Height"
                :min="64"
                :max="4096"
                :step="8"
              />
            </div>
          </div>

          <div class="settings-section">
            <h3>Frames</h3>
            <div class="preset-buttons">
              <button
                v-for="count in FRAME_COUNT_PRESETS"
                :key="count"
                @click="applyFrameCountPreset(count)"
              >
                {{ count }}f
              </button>
            </div>
            <div class="input-row">
              <ScrubableNumber
                v-model="frameCount"
                label="Total Frames"
                :min="1"
                :max="1000"
              />
              <ScrubableNumber
                v-model="fps"
                label="FPS"
                :min="1"
                :max="120"
              />
            </div>
            <div class="input-row">
              <ScrubableNumber
                v-model="startFrame"
                label="Start"
                :min="0"
                :max="endFrame - 1"
              />
              <ScrubableNumber
                v-model="endFrame"
                label="End"
                :min="startFrame + 1"
                :max="frameCount"
              />
            </div>
          </div>

          <div class="settings-section">
            <h3>Export Options</h3>
            <div class="checkbox-grid">
              <label>
                <input type="checkbox" v-model="exportReferenceFrame" />
                Reference Frame
              </label>
              <label>
                <input type="checkbox" v-model="exportLastFrame" />
                Last Frame
              </label>
              <label>
                <input type="checkbox" v-model="exportDepthMap" />
                Depth Maps
              </label>
              <label>
                <input type="checkbox" v-model="exportControlImages" />
                Control Images
              </label>
              <label>
                <input type="checkbox" v-model="exportCameraData" />
                Camera Data
              </label>
            </div>
          </div>

          <div v-if="exportDepthMap" class="settings-section">
            <h3>Depth Format</h3>
            <select v-model="depthFormat">
              <option v-for="fmt in depthFormats" :key="fmt.value" :value="fmt.value">
                {{ fmt.label }}
              </option>
            </select>
          </div>

          <div v-if="exportControlImages" class="settings-section">
            <h3>Control Type</h3>
            <select v-model="controlType">
              <option v-for="ct in controlTypes" :key="ct.value" :value="ct.value">
                {{ ct.label }}
              </option>
            </select>
          </div>
        </div>

        <!-- Generation Settings Tab -->
        <div v-if="activeTab === 'generation'" class="tab-content">
          <div class="settings-section">
            <h3>Prompt</h3>
            <textarea
              v-model="prompt"
              placeholder="Describe the video you want to generate..."
              rows="4"
            />
          </div>

          <div class="settings-section">
            <h3>Negative Prompt</h3>
            <textarea
              v-model="negativePrompt"
              placeholder="What to avoid..."
              rows="2"
            />
          </div>

          <div class="settings-section">
            <h3>Parameters</h3>
            <div class="input-row">
              <ScrubableNumber
                v-model="steps"
                label="Steps"
                :min="1"
                :max="100"
              />
              <ScrubableNumber
                v-model="cfgScale"
                label="CFG Scale"
                :min="1"
                :max="20"
                :step="0.5"
              />
            </div>
            <div class="input-row seed-row">
              <ScrubableNumber
                v-model="seed"
                label="Seed"
                :min="0"
                :max="2147483647"
              />
              <button class="randomize-btn" @click="randomizeSeed">Random</button>
            </div>
          </div>
        </div>

        <!-- ComfyUI Settings Tab -->
        <div v-if="activeTab === 'comfyui'" class="tab-content">
          <div class="settings-section">
            <h3>Server</h3>
            <div class="server-row">
              <input
                type="text"
                v-model="comfyuiServer"
                placeholder="127.0.0.1:8188"
              />
              <button @click="checkConnection">
                {{ connectionStatus === 'connecting' ? 'Connecting...' : 'Test' }}
              </button>
            </div>
            <div :class="['connection-status', connectionStatus]">
              <span v-if="connectionStatus === 'connected'">Connected</span>
              <span v-else-if="connectionStatus === 'error'">Connection failed</span>
              <span v-else-if="connectionStatus === 'connecting'">Connecting...</span>
              <span v-else>Not connected</span>
            </div>
          </div>

          <div class="settings-section">
            <h3>Workflow</h3>
            <label class="checkbox-large">
              <input type="checkbox" v-model="autoQueueWorkflow" />
              <span>
                <strong>Auto-queue workflow</strong>
                <small>Automatically send workflow to ComfyUI after export</small>
              </span>
            </label>
          </div>
        </div>
      </div>

      <!-- Progress -->
      <div v-if="isExporting" class="export-progress">
        <div class="progress-header">
          <span>{{ exportProgress?.message || 'Exporting...' }}</span>
          <button @click="cancelExport">Cancel</button>
        </div>
        <div class="progress-bar">
          <div
            class="progress-fill"
            :style="{ width: `${exportProgress?.overallProgress || 0}%` }"
          />
        </div>
        <div v-if="exportProgress?.currentFrame" class="progress-details">
          Frame {{ exportProgress.currentFrame }} / {{ exportProgress.totalFrames }}
        </div>
      </div>

      <!-- Error -->
      <div v-if="exportError" class="export-error">
        {{ exportError }}
      </div>

      <!-- Footer -->
      <footer class="dialog-footer">
        <button class="secondary" @click="close">Cancel</button>
        <button
          class="primary"
          :disabled="isExporting"
          @click="startExport"
        >
          {{ isExporting ? 'Exporting...' : 'Export' }}
        </button>
      </footer>
    </div>
  </div>
</template>

<style scoped>
.export-dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.export-dialog {
  background: var(--panel-bg, #1e1e1e);
  border: 1px solid var(--border-color, #333);
  border-radius: 8px;
  width: 600px;
  max-height: 80vh;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 16px 20px;
  border-bottom: 1px solid var(--border-color, #333);
}

.dialog-header h2 {
  margin: 0;
  font-size: 18px;
  font-weight: 500;
}

.close-btn {
  background: none;
  border: none;
  color: var(--text-secondary, #888);
  font-size: 24px;
  cursor: pointer;
  padding: 0;
  line-height: 1;
}

.close-btn:hover {
  color: var(--text-primary, #fff);
}

.dialog-tabs {
  display: flex;
  border-bottom: 1px solid var(--border-color, #333);
}

.dialog-tabs button {
  flex: 1;
  padding: 12px;
  background: none;
  border: none;
  color: var(--text-secondary, #888);
  cursor: pointer;
  font-size: 13px;
  transition: all 0.15s;
}

.dialog-tabs button:hover {
  color: var(--text-primary, #fff);
  background: rgba(255, 255, 255, 0.05);
}

.dialog-tabs button.active {
  color: var(--accent-color, #4a9eff);
  border-bottom: 2px solid var(--accent-color, #4a9eff);
}

.dialog-content {
  flex: 1;
  overflow-y: auto;
  padding: 16px 20px;
}

.tab-content {
  display: flex;
  flex-direction: column;
  gap: 20px;
}

/* Target Selection */
.target-grid {
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.target-category h3 {
  font-size: 12px;
  font-weight: 500;
  color: var(--text-secondary, #888);
  margin: 0 0 8px 0;
  text-transform: uppercase;
}

.target-buttons {
  display: flex;
  flex-wrap: wrap;
  gap: 8px;
}

.target-buttons button {
  padding: 8px 16px;
  background: var(--input-bg, #2a2a2a);
  border: 1px solid var(--border-color, #333);
  border-radius: 4px;
  color: var(--text-primary, #fff);
  font-size: 13px;
  cursor: pointer;
  transition: all 0.15s;
}

.target-buttons button:hover {
  border-color: var(--accent-color, #4a9eff);
}

.target-buttons button.selected {
  background: var(--accent-color, #4a9eff);
  border-color: var(--accent-color, #4a9eff);
}

.target-info {
  background: var(--input-bg, #2a2a2a);
  border-radius: 4px;
  padding: 12px;
}

.target-info h4 {
  margin: 0 0 8px 0;
  font-size: 14px;
}

.info-row {
  display: flex;
  gap: 8px;
  font-size: 12px;
  margin-top: 4px;
}

.info-row .label {
  color: var(--text-secondary, #888);
  min-width: 70px;
}

/* Settings */
.settings-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.settings-section h3 {
  font-size: 13px;
  font-weight: 500;
  color: var(--text-secondary, #888);
  margin: 0;
}

.preset-buttons {
  display: flex;
  gap: 6px;
  flex-wrap: wrap;
}

.preset-buttons button {
  padding: 4px 10px;
  background: var(--input-bg, #2a2a2a);
  border: 1px solid var(--border-color, #333);
  border-radius: 3px;
  color: var(--text-primary, #fff);
  font-size: 11px;
  cursor: pointer;
}

.preset-buttons button:hover {
  border-color: var(--accent-color, #4a9eff);
}

.input-row {
  display: flex;
  gap: 12px;
}

.input-row > * {
  flex: 1;
}

.checkbox-grid {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 8px;
}

.checkbox-grid label {
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 13px;
  cursor: pointer;
}

.settings-section select {
  padding: 8px;
  background: var(--input-bg, #2a2a2a);
  border: 1px solid var(--border-color, #333);
  border-radius: 4px;
  color: var(--text-primary, #fff);
  font-size: 13px;
}

.settings-section textarea {
  padding: 8px;
  background: var(--input-bg, #2a2a2a);
  border: 1px solid var(--border-color, #333);
  border-radius: 4px;
  color: var(--text-primary, #fff);
  font-size: 13px;
  resize: vertical;
  font-family: inherit;
}

.seed-row {
  align-items: flex-end;
}

.randomize-btn {
  padding: 8px 16px;
  background: var(--input-bg, #2a2a2a);
  border: 1px solid var(--border-color, #333);
  border-radius: 4px;
  color: var(--text-primary, #fff);
  cursor: pointer;
  white-space: nowrap;
}

/* ComfyUI Tab */
.server-row {
  display: flex;
  gap: 8px;
}

.server-row input {
  flex: 1;
  padding: 8px;
  background: var(--input-bg, #2a2a2a);
  border: 1px solid var(--border-color, #333);
  border-radius: 4px;
  color: var(--text-primary, #fff);
  font-size: 13px;
}

.server-row button {
  padding: 8px 16px;
  background: var(--input-bg, #2a2a2a);
  border: 1px solid var(--border-color, #333);
  border-radius: 4px;
  color: var(--text-primary, #fff);
  cursor: pointer;
}

.connection-status {
  font-size: 12px;
  padding: 4px 0;
}

.connection-status.connected {
  color: #4caf50;
}

.connection-status.error {
  color: #f44336;
}

.connection-status.connecting {
  color: #ff9800;
}

.checkbox-large {
  display: flex;
  align-items: flex-start;
  gap: 12px;
  cursor: pointer;
}

.checkbox-large input {
  margin-top: 2px;
}

.checkbox-large span {
  display: flex;
  flex-direction: column;
}

.checkbox-large strong {
  font-size: 13px;
}

.checkbox-large small {
  font-size: 11px;
  color: var(--text-secondary, #888);
}

/* Progress */
.export-progress {
  padding: 12px 20px;
  border-top: 1px solid var(--border-color, #333);
  background: var(--input-bg, #2a2a2a);
}

.progress-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 8px;
  font-size: 13px;
}

.progress-header button {
  padding: 4px 12px;
  background: none;
  border: 1px solid var(--border-color, #333);
  border-radius: 3px;
  color: var(--text-secondary, #888);
  cursor: pointer;
  font-size: 11px;
}

.progress-bar {
  height: 4px;
  background: var(--border-color, #333);
  border-radius: 2px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: var(--accent-color, #4a9eff);
  transition: width 0.2s;
}

.progress-details {
  font-size: 11px;
  color: var(--text-secondary, #888);
  margin-top: 4px;
}

/* Error */
.export-error {
  padding: 12px 20px;
  background: rgba(244, 67, 54, 0.1);
  border-top: 1px solid #f44336;
  color: #f44336;
  font-size: 13px;
}

/* Footer */
.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  padding: 16px 20px;
  border-top: 1px solid var(--border-color, #333);
}

.dialog-footer button {
  padding: 10px 24px;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
  transition: all 0.15s;
}

.dialog-footer button.secondary {
  background: none;
  border: 1px solid var(--border-color, #333);
  color: var(--text-primary, #fff);
}

.dialog-footer button.primary {
  background: var(--accent-color, #4a9eff);
  border: none;
  color: #fff;
}

.dialog-footer button.primary:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.dialog-footer button:hover:not(:disabled) {
  filter: brightness(1.1);
}
</style>
