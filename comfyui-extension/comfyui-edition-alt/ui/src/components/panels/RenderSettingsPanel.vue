<!--
  @component RenderSettingsPanel
  @description Configures render settings for a composition or render queue job.
  Separated from Output Module for clear workflow separation.

  Settings include:
  - Resolution (full, half, third, quarter, custom)
  - Frame rate (inherit, 16, 24, 30, 60 fps)
  - Quality (draft, standard, best)
  - Motion blur (on/off, samples, shutter angle)
  - Field rendering (none, upper first, lower first)
  - Time span (work area, comp duration, custom)

  @props
  - settings: Current render settings object
  @emits
  - update:settings: Settings changed
-->
<template>
  <div class="render-settings-panel">
    <div class="panel-section">
      <h4 class="section-title">Render Settings</h4>

      <!-- Quality -->
      <div class="form-row">
        <label>Quality</label>
        <select v-model="localSettings.quality" @change="emitUpdate">
          <option value="draft">Draft (fast)</option>
          <option value="standard">Standard</option>
          <option value="best">Best (slow)</option>
        </select>
      </div>

      <!-- Resolution -->
      <div class="form-row">
        <label>Resolution</label>
        <select v-model="localSettings.resolution" @change="handleResolutionChange">
          <option value="full">Full</option>
          <option value="half">Half</option>
          <option value="third">Third</option>
          <option value="quarter">Quarter</option>
          <option value="custom">Custom</option>
        </select>
      </div>

      <!-- Custom Resolution -->
      <div v-if="localSettings.resolution === 'custom'" class="form-row sub-row">
        <label>Size</label>
        <div class="dimension-inputs">
          <input
            v-model.number="localSettings.customWidth"
            type="number"
            min="8"
            step="8"
            @change="emitUpdate"
          />
          <span>x</span>
          <input
            v-model.number="localSettings.customHeight"
            type="number"
            min="8"
            step="8"
            @change="emitUpdate"
          />
        </div>
      </div>

      <!-- Frame Rate -->
      <div class="form-row">
        <label>Frame Rate</label>
        <select v-model="localSettings.frameRate" @change="emitUpdate">
          <option value="inherit">Use Comp Settings</option>
          <option value="16">16 fps (Wan 2.1)</option>
          <option value="24">24 fps (Film)</option>
          <option value="30">30 fps (Video)</option>
          <option value="60">60 fps (High)</option>
          <option value="custom">Custom</option>
        </select>
      </div>

      <!-- Custom Frame Rate -->
      <div v-if="localSettings.frameRate === 'custom'" class="form-row sub-row">
        <label>FPS</label>
        <input
          v-model.number="localSettings.customFps"
          type="number"
          min="1"
          max="120"
          @change="emitUpdate"
        />
      </div>
    </div>

    <!-- Time Span Section -->
    <div class="panel-section">
      <h4 class="section-title">Time Span</h4>

      <div class="form-row">
        <label>Render</label>
        <select v-model="localSettings.timeSpan" @change="emitUpdate">
          <option value="workArea">Work Area Only</option>
          <option value="full">Entire Composition</option>
          <option value="custom">Custom</option>
        </select>
      </div>

      <!-- Custom Time Span -->
      <div v-if="localSettings.timeSpan === 'custom'" class="form-row sub-row">
        <label>Frames</label>
        <div class="range-inputs">
          <input
            v-model.number="localSettings.startFrame"
            type="number"
            min="0"
            @change="emitUpdate"
          />
          <span>to</span>
          <input
            v-model.number="localSettings.endFrame"
            type="number"
            min="0"
            @change="emitUpdate"
          />
        </div>
      </div>
    </div>

    <!-- Motion Blur Section -->
    <div class="panel-section">
      <h4 class="section-title">Motion Blur</h4>

      <div class="form-row">
        <label class="checkbox-label">
          <input
            type="checkbox"
            v-model="localSettings.motionBlur"
            @change="emitUpdate"
          />
          Enable Motion Blur
        </label>
      </div>

      <template v-if="localSettings.motionBlur">
        <div class="form-row sub-row">
          <label>Samples</label>
          <select v-model.number="localSettings.motionBlurSamples" @change="emitUpdate">
            <option :value="4">4 (Fast)</option>
            <option :value="8">8 (Standard)</option>
            <option :value="16">16 (Best)</option>
            <option :value="32">32 (Extreme)</option>
          </select>
        </div>

        <div class="form-row sub-row">
          <label>Shutter Angle</label>
          <div class="slider-row">
            <input
              type="range"
              v-model.number="localSettings.shutterAngle"
              min="0"
              max="360"
              @input="emitUpdate"
            />
            <span class="slider-value">{{ localSettings.shutterAngle }}°</span>
          </div>
        </div>

        <div class="form-row sub-row">
          <label>Shutter Phase</label>
          <div class="slider-row">
            <input
              type="range"
              v-model.number="localSettings.shutterPhase"
              min="-180"
              max="180"
              @input="emitUpdate"
            />
            <span class="slider-value">{{ localSettings.shutterPhase }}°</span>
          </div>
        </div>
      </template>
    </div>

    <!-- Advanced Section -->
    <div class="panel-section">
      <h4 class="section-title">Advanced</h4>

      <div class="form-row">
        <label class="checkbox-label">
          <input
            type="checkbox"
            v-model="localSettings.skipExisting"
            @change="emitUpdate"
          />
          Skip Existing Frames
        </label>
      </div>

      <div class="form-row">
        <label class="checkbox-label">
          <input
            type="checkbox"
            v-model="localSettings.useCache"
            @change="emitUpdate"
          />
          Use Frame Cache
        </label>
      </div>

      <div class="form-row">
        <label class="checkbox-label">
          <input
            type="checkbox"
            v-model="localSettings.useMultiProcessing"
            @change="emitUpdate"
          />
          Multi-Frame Rendering
        </label>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { onMounted, ref, watch } from "vue";

export interface RenderSettings {
  quality: "draft" | "standard" | "best";
  resolution: "full" | "half" | "third" | "quarter" | "custom";
  customWidth?: number;
  customHeight?: number;
  frameRate: "inherit" | "16" | "24" | "30" | "60" | "custom";
  customFps?: number;
  timeSpan: "workArea" | "full" | "custom";
  startFrame?: number;
  endFrame?: number;
  motionBlur: boolean;
  motionBlurSamples: number;
  shutterAngle: number;
  shutterPhase: number;
  skipExisting: boolean;
  useCache: boolean;
  useMultiProcessing: boolean;
}

const props = defineProps<{
  settings: RenderSettings;
}>();

const emit =
  defineEmits<(e: "update:settings", settings: RenderSettings) => void>();

// Local copy of settings for editing
const localSettings = ref<RenderSettings>({
  ...getDefaultSettings(),
  ...props.settings,
});

function getDefaultSettings(): RenderSettings {
  return {
    quality: "standard",
    resolution: "full",
    customWidth: 832,
    customHeight: 480,
    frameRate: "inherit",
    customFps: 16,
    timeSpan: "workArea",
    startFrame: 0,
    endFrame: 80,
    motionBlur: false,
    motionBlurSamples: 8,
    shutterAngle: 180,
    shutterPhase: -90,
    skipExisting: false,
    useCache: true,
    useMultiProcessing: false,
  };
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

function handleResolutionChange() {
  // Set default custom size when switching to custom
  if (localSettings.value.resolution === "custom") {
    if (!localSettings.value.customWidth) localSettings.value.customWidth = 832;
    if (!localSettings.value.customHeight)
      localSettings.value.customHeight = 480;
  }
  emitUpdate();
}

onMounted(() => {
  // Ensure defaults are set
  localSettings.value = { ...getDefaultSettings(), ...props.settings };
});
</script>

<style scoped>
.render-settings-panel {
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
  flex: 0 0 100px;
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

.dimension-inputs,
.range-inputs {
  display: flex;
  align-items: center;
  gap: 8px;
  flex: 1;
}

.dimension-inputs input,
.range-inputs input[type="number"] {
  width: 70px;
  flex: 0 0 auto;
}

.dimension-inputs span,
.range-inputs span {
  color: var(--lattice-text-muted, #6B7280);
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
</style>
