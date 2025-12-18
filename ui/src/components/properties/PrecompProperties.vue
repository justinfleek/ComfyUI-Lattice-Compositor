<template>
  <div class="precomp-properties">
    <!-- Composition Info -->
    <div class="property-section" v-if="compInfo">
      <div class="section-header">Composition Info</div>
      <div class="section-content info-grid">
        <div class="info-row">
          <span class="info-label">Name</span>
          <span class="info-value">{{ compInfo.name }}</span>
        </div>
        <div class="info-row">
          <span class="info-label">Dimensions</span>
          <span class="info-value">{{ compInfo.width }} x {{ compInfo.height }}</span>
        </div>
        <div class="info-row">
          <span class="info-label">Duration</span>
          <span class="info-value">{{ compInfo.frameCount }} frames ({{ formatDuration(compInfo.duration) }})</span>
        </div>
        <div class="info-row">
          <span class="info-label">Frame Rate</span>
          <span class="info-value">{{ compInfo.fps }} fps</span>
        </div>
      </div>
    </div>

    <!-- Quick Actions -->
    <div class="property-section">
      <div class="section-header">Actions</div>
      <div class="section-content">
        <button class="action-btn" @click="enterPrecomp">
          Enter Composition
        </button>
      </div>
    </div>

    <!-- Time Remapping -->
    <div class="property-section">
      <div class="section-header">
        <span>Time Remap</span>
        <label class="header-toggle">
          <input type="checkbox" :checked="precompData.timeRemapEnabled" @change="toggleTimeRemap" />
        </label>
      </div>
      <div class="section-content" v-if="precompData.timeRemapEnabled">
        <div class="property-row">
          <label>Remap Time</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              :modelValue="timeRemapValue"
              @update:modelValue="updateTimeRemap"
              :min="0" :step="0.01" :precision="3" unit="s"
            />
            <KeyframeToggle
              v-if="precompData.timeRemap"
              :property="precompData.timeRemap"
              :layerId="layer.id"
              propertyPath="data.timeRemap"
            />
          </div>
        </div>
        <p class="hint">Animate to control precomp playback independently of composition time.</p>
      </div>
    </div>

    <!-- Frame Rate Override -->
    <div class="property-section">
      <div class="section-header">
        <span>Frame Rate Override</span>
        <label class="header-toggle">
          <input type="checkbox" :checked="precompData.overrideFrameRate" @change="toggleFrameRateOverride" />
        </label>
      </div>
      <div class="section-content" v-if="precompData.overrideFrameRate">
        <div class="property-row">
          <label>Frame Rate</label>
          <ScrubableNumber
            :modelValue="precompData.frameRate || compInfo?.fps || 30"
            @update:modelValue="updateFrameRate"
            :min="1" :max="120" :step="1" :precision="0" unit="fps"
          />
        </div>
      </div>
    </div>

    <!-- Collapse Transformations -->
    <div class="property-section">
      <div class="section-header">Options</div>
      <div class="section-content">
        <div class="checkbox-group">
          <label class="checkbox-row">
            <input
              type="checkbox"
              :checked="precompData.collapseTransformations"
              @change="updateCollapseTransform"
            />
            <span>Collapse Transformations</span>
          </label>
        </div>
        <p class="hint" v-if="precompData.collapseTransformations">
          3D layers render in parent's 3D space. Effects are rasterized.
        </p>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from './KeyframeToggle.vue';
import type { Layer, PrecompData, AnimatableProperty } from '@/types/project';
import { createAnimatableProperty } from '@/types/project';

const props = defineProps<{
  layer: Layer;
}>();

const emit = defineEmits<{
  (e: 'update', data: Partial<PrecompData>): void;
}>();

const store = useCompositorStore();

// Get precomp data from layer
const precompData = computed<PrecompData>(() => {
  const data = props.layer.data as PrecompData | null;
  return {
    compositionId: data?.compositionId ?? '',
    timeRemapEnabled: data?.timeRemapEnabled ?? false,
    timeRemap: data?.timeRemap,
    collapseTransformations: data?.collapseTransformations ?? false,
    overrideFrameRate: data?.overrideFrameRate ?? false,
    frameRate: data?.frameRate,
  };
});

// Get referenced composition info
const compInfo = computed(() => {
  if (!precompData.value.compositionId) return null;
  const comp = store.project.compositions[precompData.value.compositionId];
  if (!comp) return null;
  return {
    name: comp.name,
    width: comp.settings.width,
    height: comp.settings.height,
    frameCount: comp.settings.frameCount,
    fps: comp.settings.fps,
    duration: comp.settings.duration,
  };
});

// Time remap value
const timeRemapValue = computed(() => {
  if (!precompData.value.timeRemap) return 0;
  return precompData.value.timeRemap.value;
});

// Format duration as MM:SS.ms
function formatDuration(seconds: number | undefined): string {
  if (seconds === undefined) return '0:00';
  const mins = Math.floor(seconds / 60);
  const secs = (seconds % 60).toFixed(2);
  return `${mins}:${secs.padStart(5, '0')}`;
}

// Enter the precomp composition
function enterPrecomp() {
  if (precompData.value.compositionId) {
    store.enterPrecomp(precompData.value.compositionId);
  }
}

// Time remap
function toggleTimeRemap(e: Event) {
  const enabled = (e.target as HTMLInputElement).checked;
  const updates: Partial<PrecompData> = { timeRemapEnabled: enabled };

  // Create time remap property if enabling
  if (enabled && !precompData.value.timeRemap) {
    updates.timeRemap = createAnimatableProperty(0);
  }

  store.updateLayerData(props.layer.id, updates);
  emit('update', updates);
}

function updateTimeRemap(value: number) {
  if (precompData.value.timeRemap) {
    const timeRemap: AnimatableProperty<number> = {
      ...precompData.value.timeRemap,
      value,
    };
    store.updateLayerData(props.layer.id, { timeRemap });
    emit('update', { timeRemap });
  }
}

// Frame rate override
function toggleFrameRateOverride(e: Event) {
  const enabled = (e.target as HTMLInputElement).checked;
  const updates: Partial<PrecompData> = {
    overrideFrameRate: enabled,
    frameRate: enabled ? (compInfo.value?.fps || 30) : undefined,
  };
  store.updateLayerData(props.layer.id, updates);
  emit('update', updates);
}

function updateFrameRate(value: number) {
  store.updateLayerData(props.layer.id, { frameRate: value });
  emit('update', { frameRate: value });
}

// Collapse transformations
function updateCollapseTransform(e: Event) {
  const enabled = (e.target as HTMLInputElement).checked;
  store.updateLayerData(props.layer.id, { collapseTransformations: enabled });
  // Also update the layer-level flag
  store.updateLayer(props.layer.id, { collapseTransform: enabled });
  emit('update', { collapseTransformations: enabled });
}
</script>

<style scoped>
.precomp-properties {
  padding: 0;
}

.property-section {
  margin-bottom: 8px;
  background: #1e1e1e;
  border-radius: 4px;
  overflow: hidden;
}

.section-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 6px 8px;
  background: #252525;
  font-size: 13px;
  font-weight: 500;
  color: #aaa;
  cursor: pointer;
}

.header-toggle {
  display: flex;
  align-items: center;
  cursor: pointer;
}

.header-toggle input {
  margin: 0;
}

.section-content {
  padding: 8px;
}

.info-grid {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.info-row {
  display: flex;
  justify-content: space-between;
  font-size: 12px;
}

.info-label {
  color: #888;
}

.info-value {
  color: #ccc;
}

.property-row {
  display: flex;
  align-items: center;
  justify-content: space-between;
  margin-bottom: 6px;
  gap: 8px;
}

.property-row label {
  font-size: 12px;
  color: #aaa;
  min-width: 60px;
}

.control-with-keyframe {
  display: flex;
  align-items: center;
  gap: 4px;
  flex: 1;
}

.checkbox-group {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.checkbox-row {
  display: flex;
  align-items: center;
  gap: 6px;
  font-size: 12px;
  color: #ccc;
  cursor: pointer;
}

.checkbox-row input {
  margin: 0;
}

.hint {
  font-size: 11px;
  color: #666;
  margin: 4px 0 0 0;
  font-style: italic;
}

.action-btn {
  width: 100%;
  padding: 6px 12px;
  background: #3a5070;
  border: none;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
  cursor: pointer;
}

.action-btn:hover {
  background: #4a6090;
}

.select-input {
  flex: 1;
  padding: 4px 8px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 12px;
}
</style>
