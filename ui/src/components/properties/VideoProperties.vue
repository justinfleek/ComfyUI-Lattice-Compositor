<template>
  <div class="video-properties">
    <!-- Video Info -->
    <div class="property-section" v-if="assetInfo">
      <div class="section-header">Video Info</div>
      <div class="section-content info-grid">
        <div class="info-row">
          <span class="info-label">Dimensions</span>
          <span class="info-value">{{ assetInfo.width }} × {{ assetInfo.height }}</span>
        </div>
        <div class="info-row">
          <span class="info-label">Duration</span>
          <span class="info-value">{{ formatDuration(assetInfo.duration) }}</span>
        </div>
        <div class="info-row">
          <span class="info-label">Frame Rate</span>
          <span class="info-value">{{ assetInfo.fps?.toFixed(2) || '?' }} fps</span>
        </div>
        <div class="info-row">
          <span class="info-label">Has Audio</span>
          <span class="info-value">{{ assetInfo.hasAudio ? 'Yes' : 'No' }}</span>
        </div>
      </div>
    </div>

    <!-- Playback Options -->
    <div class="property-section">
      <div class="section-header">Playback</div>
      <div class="section-content">
        <div class="property-row">
          <label>Speed</label>
          <ScrubableNumber
            :modelValue="videoData.speed"
            @update:modelValue="updateSpeed"
            :min="0.1" :max="10" :step="0.1" :precision="2" unit="x"
          />
        </div>
        <div class="property-row">
          <label>Start Time</label>
          <ScrubableNumber
            :modelValue="videoData.startTime"
            @update:modelValue="updateStartTime"
            :min="0" :step="0.1" :precision="2" unit="s"
          />
        </div>
        <div class="property-row">
          <label>End Time</label>
          <ScrubableNumber
            :modelValue="videoData.endTime || assetInfo?.duration || 0"
            @update:modelValue="updateEndTime"
            :min="0" :step="0.1" :precision="2" unit="s"
          />
        </div>
        <div class="checkbox-group">
          <label class="checkbox-row">
            <input type="checkbox" :checked="videoData.loop" @change="updateLoop" />
            <span>Loop</span>
          </label>
          <label class="checkbox-row">
            <input type="checkbox" :checked="videoData.pingPong" @change="updatePingPong" />
            <span>Ping-Pong</span>
          </label>
        </div>
      </div>
    </div>

    <!-- Time Remapping -->
    <div class="property-section">
      <div class="section-header">
        <span>Speed Map</span>
        <label class="header-toggle">
          <input type="checkbox" :checked="speedMapEnabled" @change="toggleSpeedMap" />
        </label>
      </div>
      <div class="section-content" v-if="speedMapEnabled">
        <div class="property-row">
          <label>Map Time</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              :modelValue="speedMapValue"
              @update:modelValue="updateSpeedMap"
              :min="0" :step="0.01" :precision="3" unit="s"
            />
            <KeyframeToggle
              v-if="speedMapProperty"
              :property="speedMapProperty"
              :layerId="layer.id"
              propertyPath="data.speedMap"
              @keyframeAdded="onKeyframeChange"
              @keyframeRemoved="onKeyframeChange"
              @animationToggled="onAnimationToggled"
            />
          </div>
        </div>
        <p class="hint">Animate speed map to control video playback independently of composition time.</p>
      </div>
    </div>

    <!-- Frame Blending -->
    <div class="property-section">
      <div class="section-header">Frame Blending</div>
      <div class="section-content">
        <div class="property-row">
          <label>Mode</label>
          <select :value="videoData.frameBlending" @change="updateFrameBlending" class="select-input">
            <option value="none">None</option>
            <option value="frame-mix">Frame Mix</option>
            <option value="pixel-motion">Pixel Motion</option>
          </select>
        </div>
      </div>
    </div>

    <!-- Timewarp -->
    <div class="property-section">
      <div class="section-header">
        <span>Timewarp</span>
        <label class="header-toggle">
          <input type="checkbox" :checked="timewarpEnabled" @change="toggleTimewarp" />
        </label>
      </div>
      <div class="section-content" v-if="timewarpEnabled">
        <div class="property-row">
          <label>Speed</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              :modelValue="timewarpSpeedValue"
              @update:modelValue="updateTimewarpSpeed"
              unit="%"
              :min="1"
              :max="400"
              :precision="1"
            />
            <KeyframeToggle
              v-if="timewarpSpeedProperty"
              :property="timewarpSpeedProperty"
              :layerId="layer.id"
              propertyPath="data.timewarpSpeed"
              @keyframeAdded="onKeyframeChange"
              @keyframeRemoved="onKeyframeChange"
              @animationToggled="onAnimationToggled"
            />
          </div>
        </div>
        <div class="property-row">
          <label>Method</label>
          <select :value="videoData.timewarpMethod || 'frame-mix'" @change="updateTimewarpMethod" class="select-input">
            <option value="whole-frames">Whole Frames</option>
            <option value="frame-mix">Frame Mix</option>
            <option value="pixel-motion">Pixel Motion</option>
          </select>
        </div>
        <div class="preset-buttons">
          <button class="preset-btn" @click="applyTimewarpPreset('slow-fast')" title="Start slow, end fast">Slow→Fast</button>
          <button class="preset-btn" @click="applyTimewarpPreset('fast-slow')" title="Start fast, end slow">Fast→Slow</button>
          <button class="preset-btn" @click="applyTimewarpPreset('impact')" title="Slow motion at impact point">Impact</button>
          <button class="preset-btn" @click="applyTimewarpPreset('rewind')" title="Normal→Reverse→Normal">Rewind</button>
        </div>
        <p class="hint">Keyframe Speed % for smooth speed ramps. Uses curve editor easing.</p>
      </div>
    </div>

    <!-- Audio -->
    <div class="property-section" v-if="assetInfo?.hasAudio !== false">
      <div class="section-header">Audio</div>
      <div class="section-content">
        <div class="checkbox-group">
          <label class="checkbox-row">
            <input type="checkbox" :checked="videoData.audioEnabled" @change="updateAudioEnabled" />
            <span>Audio Enabled</span>
          </label>
        </div>
        <div class="property-row" v-if="videoData.audioEnabled">
          <label>Level</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              v-if="audioLevel"
              :modelValue="audioLevel.value"
              @update:modelValue="updateLevel"
              unit="dB"
              :min="-48"
              :max="12"
              :precision="1"
            />
            <KeyframeToggle
              v-if="audioLevel"
              :property="audioLevel"
              :layerId="layer.id"
              propertyPath="audio.level"
              @keyframeAdded="onKeyframeChange"
              @keyframeRemoved="onKeyframeChange"
              @animationToggled="onAnimationToggled"
            />
          </div>
        </div>
        <div class="property-row" v-if="videoData.audioEnabled">
          <label>Volume</label>
          <ScrubableNumber
            :modelValue="videoData.audioLevel"
            @update:modelValue="updateAudioLevel"
            :min="0" :max="200" :step="1" :precision="0" unit="%"
          />
        </div>
        <div class="waveform-container" v-if="videoData.audioEnabled">
          <div class="waveform-placeholder">Audio Waveform</div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { useProjectStore } from "@/stores/projectStore";
import { useLayerStore } from "@/stores/layerStore";
import type {
  AnimatableProperty,
  AssetReference,
  Layer,
  VideoData,
} from "@/types/project";

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();
const projectStore = useProjectStore();

const videoData = computed<VideoData>(() => {
  return (
    (props.layer.data as VideoData) || {
      assetId: null,
      loop: false,
      pingPong: false,
      startTime: 0,
      endTime: undefined,
      speed: 1,
      speedMapEnabled: false,
      speedMap: undefined,
      // Backwards compatibility
      timeRemapEnabled: false,
      timeRemap: undefined,
      frameBlending: "none",
      audioEnabled: true,
      audioLevel: 100,
      posterFrame: 0,
    }
  );
});

const assetInfo = computed<AssetReference | null>(() => {
  const assetId = videoData.value.assetId;
  if (!assetId) return null;
  return store.assets[assetId] || null;
});

const audioLevel = computed<AnimatableProperty<number> | undefined>(() => {
  return props.layer.audio?.level;
});

// Speed map computed properties (with backwards compatibility)
const speedMapEnabled = computed(() => {
  return (
    videoData.value.speedMapEnabled ?? videoData.value.timeRemapEnabled ?? false
  );
});

const speedMapProperty = computed(() => {
  return videoData.value.speedMap ?? videoData.value.timeRemap;
});

const speedMapValue = computed(() => {
  const prop = speedMapProperty.value;
  if (!prop) return 0;
  return prop.value;
});

function formatDuration(seconds: number | undefined): string {
  if (!seconds) return "0:00";
  const mins = Math.floor(seconds / 60);
  const secs = Math.floor(seconds % 60);
  const frames = Math.floor((seconds % 1) * (assetInfo.value?.fps || 30));
  return `${mins}:${secs.toString().padStart(2, "0")}:${frames.toString().padStart(2, "0")}`;
}

function updateSpeed(val: number) {
  store.updateVideoLayerData(props.layer.id, { speed: val });
  emit("update");
}

function updateStartTime(val: number) {
  store.updateVideoLayerData(props.layer.id, { startTime: val });
  emit("update");
}

function updateEndTime(val: number) {
  store.updateVideoLayerData(props.layer.id, { endTime: val });
  emit("update");
}

function updateLoop(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, { loop: target.checked });
  emit("update");
}

function updatePingPong(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, { pingPong: target.checked });
  emit("update");
}

function toggleSpeedMap(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, {
    speedMapEnabled: target.checked,
    timeRemapEnabled: target.checked, // Backwards compatibility
  });
  emit("update");
}

function updateSpeedMap(val: number) {
  // Use store method to ensure history tracking
  const data = props.layer.data as VideoData;
  const updates: Partial<VideoData> = {};

  // Update both new and legacy properties via store
  if (data.speedMap) {
    updates.speedMap = { ...data.speedMap, value: val };
  }
  if (data.timeRemap) {
    updates.timeRemap = { ...data.timeRemap, value: val };
  }

  store.updateVideoLayerData(props.layer.id, updates);
  emit("update");
}

function updateFrameBlending(e: Event) {
  const target = e.target as HTMLSelectElement;
  store.updateVideoLayerData(props.layer.id, {
    frameBlending: target.value as VideoData["frameBlending"],
  });
  emit("update");
}

// Timewarp computed properties
const timewarpEnabled = computed(() => {
  return videoData.value.timewarpEnabled ?? false;
});

const timewarpSpeedProperty = computed(() => {
  return videoData.value.timewarpSpeed;
});

const timewarpSpeedValue = computed(() => {
  const prop = timewarpSpeedProperty.value;
  if (!prop) return 100;
  return prop.value;
});

function toggleTimewarp(e: Event) {
  const target = e.target as HTMLInputElement;
  const updates: Partial<VideoData> = {
    timewarpEnabled: target.checked,
  };

  // Initialize timewarpSpeed property if enabling and not set
  if (target.checked && !videoData.value.timewarpSpeed) {
    updates.timewarpSpeed = {
      id: `timewarpSpeed_${Date.now()}`,
      name: "Timewarp Speed",
      value: 100,
      type: "number",
      animated: false,
      keyframes: [],
    };
    updates.timewarpMethod = "frame-mix";
  }

  store.updateVideoLayerData(props.layer.id, updates);
  emit("update");
}

function updateTimewarpSpeed(val: number) {
  // Use store method to ensure history tracking
  const data = props.layer.data as VideoData;
  if (data.timewarpSpeed) {
    store.updateVideoLayerData(props.layer.id, {
      timewarpSpeed: { ...data.timewarpSpeed, value: val },
    });
  }
  emit("update");
}

function updateTimewarpMethod(e: Event) {
  const target = e.target as HTMLSelectElement;
  store.updateVideoLayerData(props.layer.id, {
    timewarpMethod: target.value as
      | "whole-frames"
      | "frame-mix"
      | "pixel-motion",
  });
  emit("update");
}

function applyTimewarpPreset(
  preset: "slow-fast" | "fast-slow" | "impact" | "rewind",
) {
  // Import the preset creator
  import("@/services/timewarp").then(({ createSpeedRampPreset }) => {
    const layerStart = props.layer.startFrame ?? 0;
    const layerEnd = props.layer.endFrame ?? projectStore.getFrameCount(store);
    const duration = layerEnd - layerStart;
    const fps = projectStore.getFps(store) || 30;

    const presetProperty = createSpeedRampPreset(
      preset,
      layerStart,
      duration,
      fps,
    );

    store.updateVideoLayerData(props.layer.id, {
      timewarpEnabled: true,
      timewarpSpeed: presetProperty,
      timewarpMethod: "pixel-motion",
    });
    emit("update");
  });
}

function updateAudioEnabled(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, { audioEnabled: target.checked });
  emit("update");
}

function updateAudioLevel(val: number) {
  store.updateVideoLayerData(props.layer.id, { audioLevel: val });
  emit("update");
}

function updateLevel(val: number) {
  // Use store method to ensure history tracking
  if (props.layer.audio?.level) {
    layerStore.updateLayer(store, props.layer.id, {
      audio: {
        ...props.layer.audio,
        level: { ...props.layer.audio.level, value: val },
      },
    });
    emit("update");
  }
}

// Keyframe event handlers
function onKeyframeChange() {
  // Keyframe was added or removed - trigger update
  emit("update");
}

function onAnimationToggled(animated: boolean) {
  // Animation was enabled or disabled
  console.log("[VideoProperties] Animation toggled:", animated);
  emit("update");
}
</script>

<style scoped>
.video-properties { padding: 0; }
.property-section { border-bottom: 1px solid #2a2a2a; }

.section-header {
  padding: 8px 10px;
  background: #252525;
  font-weight: 600;
  font-size: 12px;
  color: #aaa;
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.header-toggle {
  cursor: pointer;
}

.header-toggle input {
  cursor: pointer;
}

.section-content {
  padding: 10px;
  background: #1e1e1e;
  display: flex;
  flex-direction: column;
  gap: 8px;
}

/* Info Grid */
.info-grid {
  gap: 4px;
}

.info-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  font-size: 13px;
}

.info-label {
  color: #666;
}

.info-value {
  color: #ccc;
  font-family: monospace;
}

/* Property Rows */
.property-row {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 8px;
}

.property-row > label {
  width: 80px;
  color: #888;
  font-size: 13px;
  flex-shrink: 0;
}

.control-with-keyframe {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 4px;
}

/* Checkboxes */
.checkbox-group {
  display: flex;
  gap: 16px;
}

.checkbox-row {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  color: #ccc;
  font-size: 13px;
}

.checkbox-row input {
  cursor: pointer;
}

/* Select Input */
.select-input {
  flex: 1;
  padding: 4px 8px;
  background: #2a2a2a;
  border: 1px solid #3a3a3a;
  border-radius: 3px;
  color: #ccc;
  font-size: 13px;
  cursor: pointer;
}

.select-input:focus {
  outline: none;
  border-color: #4a90d9;
}

/* Hint Text */
.hint {
  font-size: 12px;
  color: #666;
  margin: 4px 0 0 0;
  font-style: italic;
}

/* Preset Buttons */
.preset-buttons {
  display: flex;
  gap: 6px;
  flex-wrap: wrap;
  margin-top: 4px;
}

.preset-btn {
  padding: 4px 10px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-pill, 999px);
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 11px;
  cursor: pointer;
  transition: all 0.15s ease;
}

.preset-btn:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
  border-color: var(--lattice-accent, #8b5cf6);
}

/* Waveform */
.waveform-container {
  margin-top: 8px;
}

.waveform-placeholder {
  height: 50px;
  background: #111;
  border: 1px solid #333;
  border-radius: 3px;
  display: flex;
  align-items: center;
  justify-content: center;
  color: #444;
  font-size: 12px;
}
</style>
