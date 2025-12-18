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
        <span>Time Remap</span>
        <label class="header-toggle">
          <input type="checkbox" :checked="videoData.timeRemapEnabled" @change="toggleTimeRemap" />
        </label>
      </div>
      <div class="section-content" v-if="videoData.timeRemapEnabled">
        <div class="property-row">
          <label>Remap Time</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              :modelValue="timeRemapValue"
              @update:modelValue="updateTimeRemap"
              :min="0" :step="0.01" :precision="3" unit="s"
            />
            <KeyframeToggle
              v-if="videoData.timeRemap"
              :property="videoData.timeRemap"
              :layerId="layer.id"
              propertyPath="data.timeRemap"
            />
          </div>
        </div>
        <p class="hint">Animate time remap to control video playback independently of composition time.</p>
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
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from './KeyframeToggle.vue';
import type { Layer, VideoData, AnimatableProperty, AssetReference } from '@/types/project';

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

const videoData = computed<VideoData>(() => {
  return props.layer.data as VideoData || {
    assetId: null,
    loop: false,
    pingPong: false,
    startTime: 0,
    endTime: undefined,
    speed: 1,
    timeRemapEnabled: false,
    timeRemap: undefined,
    frameBlending: 'none',
    audioEnabled: true,
    audioLevel: 100,
    posterFrame: 0
  };
});

const assetInfo = computed<AssetReference | null>(() => {
  const assetId = videoData.value.assetId;
  if (!assetId) return null;
  return store.assets[assetId] || null;
});

const audioLevel = computed<AnimatableProperty<number> | undefined>(() => {
  return props.layer.audio?.level;
});

const timeRemapValue = computed(() => {
  if (!videoData.value.timeRemap) return 0;
  return videoData.value.timeRemap.value;
});

function formatDuration(seconds: number | undefined): string {
  if (!seconds) return '0:00';
  const mins = Math.floor(seconds / 60);
  const secs = Math.floor(seconds % 60);
  const frames = Math.floor((seconds % 1) * (assetInfo.value?.fps || 30));
  return `${mins}:${secs.toString().padStart(2, '0')}:${frames.toString().padStart(2, '0')}`;
}

function updateSpeed(val: number) {
  store.updateVideoLayerData(props.layer.id, { speed: val });
  emit('update');
}

function updateStartTime(val: number) {
  store.updateVideoLayerData(props.layer.id, { startTime: val });
  emit('update');
}

function updateEndTime(val: number) {
  store.updateVideoLayerData(props.layer.id, { endTime: val });
  emit('update');
}

function updateLoop(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, { loop: target.checked });
  emit('update');
}

function updatePingPong(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, { pingPong: target.checked });
  emit('update');
}

function toggleTimeRemap(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, { timeRemapEnabled: target.checked });
  emit('update');
}

function updateTimeRemap(val: number) {
  const data = props.layer.data as VideoData;
  if (data.timeRemap) {
    data.timeRemap.value = val;
  }
  emit('update');
}

function updateFrameBlending(e: Event) {
  const target = e.target as HTMLSelectElement;
  store.updateVideoLayerData(props.layer.id, { frameBlending: target.value as VideoData['frameBlending'] });
  emit('update');
}

function updateAudioEnabled(e: Event) {
  const target = e.target as HTMLInputElement;
  store.updateVideoLayerData(props.layer.id, { audioEnabled: target.checked });
  emit('update');
}

function updateAudioLevel(val: number) {
  store.updateVideoLayerData(props.layer.id, { audioLevel: val });
  emit('update');
}

function updateLevel(val: number) {
  if (props.layer.audio?.level) {
    props.layer.audio.level.value = val;
    emit('update');
  }
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
