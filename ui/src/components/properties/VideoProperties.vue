<template>
  <div class="video-properties">
    <div class="property-section">
      <div class="section-header">Audio</div>
      <div class="section-content">
        <div class="property-row">
          <label>Audio Levels</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              v-if="audioLevel"
              :modelValue="audioLevel.value"
              @update:modelValue="updateLevel"
              unit="dB"
              :min="-48"
              :max="12"
              :precision="2"
            />
            <KeyframeToggle
              v-if="audioLevel"
              :property="audioLevel"
              :layerId="layer.id"
            />
          </div>
        </div>
        <div class="waveform-container">
          <div class="waveform-placeholder">Waveform Visual</div>
        </div>
      </div>
    </div>

    <div class="property-section">
      <div class="section-header">Video Options</div>
      <div class="section-content">
        <div class="property-row checkbox-row">
          <label>
            <input type="checkbox" :checked="videoData.loop" @change="updateLoop" />
            Loop Video
          </label>
        </div>
        <div class="property-row">
          <label>Speed</label>
          <ScrubableNumber
            :modelValue="videoData.speed"
            @update:modelValue="updateSpeed"
            :min="0.1" :max="10" :step="0.1" :precision="1" unit="x"
          />
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from './KeyframeToggle.vue';
import type { Layer, VideoData, AnimatableProperty } from '@/types/project';

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(['update']);

const videoData = computed<VideoData>(() => {
  return props.layer.data as VideoData || {
    assetId: null,
    loop: false,
    startTime: 0,
    speed: 1.0
  };
});

const audioLevel = computed<AnimatableProperty<number> | undefined>(() => {
  return props.layer.audio?.level;
});

function updateLevel(val: number) {
  if (props.layer.audio?.level) {
    props.layer.audio.level.value = val;
    emit('update');
  }
}

function updateLoop(e: Event) {
  const target = e.target as HTMLInputElement;
  (props.layer.data as VideoData).loop = target.checked;
  emit('update');
}

function updateSpeed(val: number) {
  (props.layer.data as VideoData).speed = val;
  emit('update');
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
}
.section-content { padding: 10px; background: #1e1e1e; display: flex; flex-direction: column; gap: 8px; }

.property-row { display: flex; align-items: center; justify-content: space-between; gap: 8px; }
.property-row > label { width: 80px; color: #888; font-size: 11px; flex-shrink: 0; }

.control-with-keyframe { flex: 1; display: flex; align-items: center; gap: 4px; }

.waveform-container { margin-top: 8px; }
.waveform-placeholder {
  height: 60px;
  background: #111;
  border: 1px solid #333;
  border-radius: 3px;
  display: flex;
  align-items: center;
  justify-content: center;
  color: #555;
  font-size: 11px;
}

.checkbox-row label { display: flex; align-items: center; gap: 6px; cursor: pointer; color: #ccc; font-size: 11px; }
</style>
