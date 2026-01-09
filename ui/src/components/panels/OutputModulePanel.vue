<!--
  @component OutputModulePanel
  @description Configures output settings for rendered content.
  Separated from Render Settings for clear workflow separation.

  Settings include:
  - Format (PNG sequence, JPEG sequence, MP4, WebM)
  - Color profile (sRGB, Display P3, ProPhoto RGB)
  - Color depth (8-bit, 16-bit)
  - Alpha channel (straight, premultiplied, none)
  - Naming pattern (comp name, custom pattern)
  - Destination (download, ComfyUI output folder)

  @props
  - settings: Current output module settings object
  @emits
  - update:settings: Settings changed
-->
<template>
  <div class="output-module-panel">
    <div class="panel-section">
      <h4 class="section-title">Output Module</h4>

      <!-- Format -->
      <div class="form-row">
        <label>Format</label>
        <select v-model="localSettings.format" @change="handleFormatChange">
          <option value="png-sequence">PNG Sequence</option>
          <option value="jpeg-sequence">JPEG Sequence</option>
          <option value="webp-sequence">WebP Sequence</option>
          <option value="mp4">MP4 Video (H.264)</option>
          <option value="webm">WebM Video (VP9)</option>
          <option value="gif">Animated GIF</option>
        </select>
      </div>

      <!-- Quality (for lossy formats) -->
      <div v-if="showQualitySlider" class="form-row sub-row">
        <label>Quality</label>
        <div class="slider-row">
          <input
            type="range"
            v-model.number="localSettings.quality"
            min="1"
            max="100"
            @input="emitUpdate"
          />
          <span class="slider-value">{{ localSettings.quality }}%</span>
        </div>
      </div>

      <!-- Video Bitrate (for video formats) -->
      <div v-if="isVideoFormat" class="form-row sub-row">
        <label>Bitrate</label>
        <select v-model="localSettings.videoBitrate" @change="emitUpdate">
          <option value="low">Low (2 Mbps)</option>
          <option value="medium">Medium (5 Mbps)</option>
          <option value="high">High (10 Mbps)</option>
          <option value="ultra">Ultra (20 Mbps)</option>
        </select>
      </div>
    </div>

    <!-- Color Section -->
    <div class="panel-section">
      <h4 class="section-title">Color</h4>

      <!-- Color Depth -->
      <div class="form-row">
        <label>Depth</label>
        <select v-model="localSettings.colorDepth" @change="emitUpdate">
          <option value="8">8-bit (Standard)</option>
          <option value="16">16-bit (HDR)</option>
        </select>
      </div>

      <!-- Color Profile -->
      <div class="form-row">
        <label>Profile</label>
        <select v-model="localSettings.colorProfile" @change="emitUpdate">
          <option value="srgb">sRGB (Web)</option>
          <option value="display-p3">Display P3 (Wide Gamut)</option>
          <option value="prophoto-rgb">ProPhoto RGB</option>
          <option value="none">Unmanaged</option>
        </select>
      </div>

      <!-- Alpha Channel -->
      <div v-if="supportsAlpha" class="form-row">
        <label>Alpha</label>
        <select v-model="localSettings.alpha" @change="emitUpdate">
          <option value="none">No Alpha</option>
          <option value="straight">Straight (Unmatted)</option>
          <option value="premultiplied">Premultiplied</option>
        </select>
      </div>
    </div>

    <!-- Output Section -->
    <div class="panel-section">
      <h4 class="section-title">Output</h4>

      <!-- Naming Pattern -->
      <div class="form-row">
        <label>Naming</label>
        <select v-model="localSettings.namingPattern" @change="emitUpdate">
          <option value="comp">Composition Name</option>
          <option value="comp-frame">Comp_[frame]</option>
          <option value="frame-only">[frame]</option>
          <option value="custom">Custom Pattern</option>
        </select>
      </div>

      <!-- Custom Pattern -->
      <div v-if="localSettings.namingPattern === 'custom'" class="form-row sub-row">
        <label>Pattern</label>
        <input
          v-model="localSettings.customPattern"
          type="text"
          placeholder="frame_[####]"
          @change="emitUpdate"
        />
      </div>

      <!-- Frame Padding -->
      <div v-if="isSequenceFormat" class="form-row">
        <label>Padding</label>
        <select v-model.number="localSettings.framePadding" @change="emitUpdate">
          <option :value="0">No padding (1, 2, 10)</option>
          <option :value="2">2 digits (01, 02, 10)</option>
          <option :value="4">4 digits (0001, 0002)</option>
          <option :value="5">5 digits (00001, 00002)</option>
        </select>
      </div>

      <!-- Destination -->
      <div class="form-row">
        <label>Destination</label>
        <select v-model="localSettings.destination" @change="emitUpdate">
          <option value="download">Download (Browser)</option>
          <option value="comfyui">ComfyUI Output</option>
          <option value="custom">Custom Path</option>
        </select>
      </div>

      <!-- Custom Path -->
      <div v-if="localSettings.destination === 'custom'" class="form-row sub-row">
        <label>Path</label>
        <div class="path-input">
          <input
            v-model="localSettings.customPath"
            type="text"
            placeholder="/path/to/output"
            @change="emitUpdate"
          />
          <button class="browse-btn" title="Browse">
            <i class="pi pi-folder" />
          </button>
        </div>
      </div>

      <!-- Subfolder per Render -->
      <div class="form-row">
        <label class="checkbox-label">
          <input
            type="checkbox"
            v-model="localSettings.createSubfolder"
            @change="emitUpdate"
          />
          Create Subfolder per Render
        </label>
      </div>
    </div>

    <!-- Post-Render Section -->
    <div class="panel-section">
      <h4 class="section-title">Post-Render</h4>

      <div class="form-row">
        <label class="checkbox-label">
          <input
            type="checkbox"
            v-model="localSettings.openOnComplete"
            @change="emitUpdate"
          />
          Open Output on Complete
        </label>
      </div>

      <div class="form-row">
        <label class="checkbox-label">
          <input
            type="checkbox"
            v-model="localSettings.notifyOnComplete"
            @change="emitUpdate"
          />
          Notify When Done
        </label>
      </div>

      <!-- Post-render action -->
      <div class="form-row">
        <label>Action</label>
        <select v-model="localSettings.postAction" @change="emitUpdate">
          <option value="none">None</option>
          <option value="import">Import to Project</option>
          <option value="comfyui-queue">Send to ComfyUI Queue</option>
        </select>
      </div>
    </div>

    <!-- Preview Footer -->
    <div class="preview-footer">
      <div class="output-preview">
        <span class="preview-label">Output:</span>
        <span class="preview-value">{{ outputPreview }}</span>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, ref, watch } from "vue";

export interface OutputModuleSettings {
  format:
    | "png-sequence"
    | "jpeg-sequence"
    | "webp-sequence"
    | "mp4"
    | "webm"
    | "gif";
  quality: number;
  videoBitrate: "low" | "medium" | "high" | "ultra";
  colorDepth: "8" | "16";
  colorProfile: "srgb" | "display-p3" | "prophoto-rgb" | "none";
  alpha: "none" | "straight" | "premultiplied";
  namingPattern: "comp" | "comp-frame" | "frame-only" | "custom";
  customPattern?: string;
  framePadding: number;
  destination: "download" | "comfyui" | "custom";
  customPath?: string;
  createSubfolder: boolean;
  openOnComplete: boolean;
  notifyOnComplete: boolean;
  postAction: "none" | "import" | "comfyui-queue";
}

const props = defineProps<{
  settings: OutputModuleSettings;
  compositionName?: string;
}>();

const emit =
  defineEmits<(e: "update:settings", settings: OutputModuleSettings) => void>();

// Local copy of settings for editing
const localSettings = ref<OutputModuleSettings>({
  ...getDefaultSettings(),
  ...props.settings,
});

function getDefaultSettings(): OutputModuleSettings {
  return {
    format: "png-sequence",
    quality: 90,
    videoBitrate: "medium",
    colorDepth: "8",
    colorProfile: "srgb",
    alpha: "none",
    namingPattern: "comp-frame",
    customPattern: "frame_[####]",
    framePadding: 4,
    destination: "download",
    customPath: "",
    createSubfolder: true,
    openOnComplete: false,
    notifyOnComplete: true,
    postAction: "none",
  };
}

// Computed properties for conditional UI
const showQualitySlider = computed(() =>
  ["jpeg-sequence", "webp-sequence", "mp4", "webm"].includes(
    localSettings.value.format,
  ),
);

const isVideoFormat = computed(() =>
  ["mp4", "webm"].includes(localSettings.value.format),
);

const isSequenceFormat = computed(() =>
  ["png-sequence", "jpeg-sequence", "webp-sequence"].includes(
    localSettings.value.format,
  ),
);

const supportsAlpha = computed(() =>
  ["png-sequence", "webp-sequence", "webm"].includes(
    localSettings.value.format,
  ),
);

// Output preview
const outputPreview = computed(() => {
  const compName = props.compositionName || "Composition";
  const ext = getExtension(localSettings.value.format);
  let name = "";

  switch (localSettings.value.namingPattern) {
    case "comp":
      name = compName;
      break;
    case "comp-frame":
      name = `${compName}_${"0".repeat(localSettings.value.framePadding || 4)}`;
      break;
    case "frame-only":
      name = "0".repeat(localSettings.value.framePadding || 4);
      break;
    case "custom":
      name = (localSettings.value.customPattern || "frame_[####]").replace(
        "[####]",
        "0".repeat(localSettings.value.framePadding || 4),
      );
      break;
  }

  return `${name}.${ext}`;
});

function getExtension(format: string): string {
  switch (format) {
    case "png-sequence":
      return "png";
    case "jpeg-sequence":
      return "jpg";
    case "webp-sequence":
      return "webp";
    case "mp4":
      return "mp4";
    case "webm":
      return "webm";
    case "gif":
      return "gif";
    default:
      return "png";
  }
}

// Sync with prop changes
watch(
  () => props.settings,
  (newSettings) => {
    localSettings.value = { ...getDefaultSettings(), ...newSettings };
  },
  { deep: true },
);

// Emit updates
function emitUpdate() {
  emit("update:settings", { ...localSettings.value });
}

function handleFormatChange() {
  // Adjust settings when format changes
  if (!supportsAlpha.value) {
    localSettings.value.alpha = "none";
  }
  emitUpdate();
}

onMounted(() => {
  // Ensure defaults are set
  localSettings.value = { ...getDefaultSettings(), ...props.settings };
});
</script>

<style scoped>
.output-module-panel {
  display: flex;
  flex-direction: column;
  gap: 16px;
  padding: 12px;
  font-size: 12px;
  color: var(--lattice-text-primary, #E5E5E5);
}

.panel-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
  padding-bottom: 12px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2A2A2A);
}

.panel-section:last-child {
  border-bottom: none;
  padding-bottom: 0;
}

.section-title {
  margin: 0;
  font-size: 11px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--lattice-text-secondary, #9CA3AF);
}

.form-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.form-row > label:first-child {
  flex: 0 0 80px;
  color: var(--lattice-text-secondary, #9CA3AF);
}

.form-row.sub-row {
  margin-left: 20px;
}

.form-row select,
.form-row input[type="text"],
.form-row input[type="number"] {
  flex: 1;
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1A1A1A);
  border: 1px solid var(--lattice-border-default, #333333);
  border-radius: 4px;
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: 12px;
}

.form-row select:focus,
.form-row input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  color: var(--lattice-text-primary, #E5E5E5);
}

.checkbox-label input[type="checkbox"] {
  width: 14px;
  height: 14px;
  accent-color: var(--lattice-accent, #8B5CF6);
}

.slider-row {
  display: flex;
  align-items: center;
  gap: 8px;
  flex: 1;
}

.slider-row input[type="range"] {
  flex: 1;
  height: 4px;
  appearance: none;
  background: var(--lattice-surface-3, #222222);
  border-radius: 2px;
}

.slider-row input[type="range"]::-webkit-slider-thumb {
  appearance: none;
  width: 14px;
  height: 14px;
  border-radius: 50%;
  background: var(--lattice-accent, #8B5CF6);
  cursor: pointer;
}

.slider-value {
  min-width: 45px;
  text-align: right;
  color: var(--lattice-text-secondary, #9CA3AF);
  font-family: monospace;
}

.path-input {
  display: flex;
  flex: 1;
  gap: 4px;
}

.path-input input {
  flex: 1;
}

.browse-btn {
  padding: 4px 8px;
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-default, #333333);
  border-radius: 4px;
  color: var(--lattice-text-secondary, #9CA3AF);
  cursor: pointer;
}

.browse-btn:hover {
  background: var(--lattice-surface-4, #2A2A2A);
  color: var(--lattice-text-primary, #E5E5E5);
}

.preview-footer {
  padding-top: 12px;
  border-top: 1px solid var(--lattice-border-subtle, #2A2A2A);
}

.output-preview {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px;
  background: var(--lattice-surface-2, #1A1A1A);
  border-radius: 4px;
}

.preview-label {
  color: var(--lattice-text-secondary, #9CA3AF);
}

.preview-value {
  font-family: monospace;
  color: var(--lattice-accent, #8B5CF6);
}
</style>
