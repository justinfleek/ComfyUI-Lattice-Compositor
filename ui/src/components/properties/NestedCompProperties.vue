<template>
  <div class="nested-comp-properties">
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
        <button class="action-btn" @click="enterNestedComp">
          Enter Composition
        </button>
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
        <p class="hint">Animate to control nested comp playback independently of composition time.</p>
      </div>
    </div>

    <!-- Frame Rate Override -->
    <div class="property-section">
      <div class="section-header">
        <span>Frame Rate Override</span>
        <label class="header-toggle">
          <input type="checkbox" :checked="nestedCompData.overrideFrameRate" @change="toggleFrameRateOverride" />
        </label>
      </div>
      <div class="section-content" v-if="nestedCompData.overrideFrameRate">
        <div class="property-row">
          <label>Frame Rate</label>
          <ScrubableNumber
            :modelValue="nestedCompData.frameRate || compInfo?.fps || 30"
            @update:modelValue="updateFrameRate"
            :min="1" :max="120" :step="1" :precision="0" unit="fps"
          />
        </div>
      </div>
    </div>

    <!-- Flatten Transform -->
    <div class="property-section">
      <div class="section-header">Options</div>
      <div class="section-content">
        <div class="checkbox-group">
          <label class="checkbox-row">
            <input
              type="checkbox"
              :checked="nestedCompData.flattenTransform"
              @change="updateFlattenTransform"
            />
            <span>Flatten Transform</span>
          </label>
        </div>
        <p class="hint" v-if="nestedCompData.flattenTransform">
          3D layers render in parent's 3D space. Effects are rasterized.
        </p>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import type {
  AnimatableProperty,
  Layer,
  NestedCompData,
} from "@/types/project";
import { createAnimatableProperty } from "@/types/project";

const props = defineProps<{
  layer: Layer;
}>();

const emit =
  defineEmits<(e: "update", data: Partial<NestedCompData>) => void>();

const store = useCompositorStore();

// Get nested comp data from layer
const nestedCompData = computed<NestedCompData>(() => {
  const data = props.layer.data as NestedCompData | null;
  return {
    compositionId: data?.compositionId ?? "",
    // New naming with backwards compatibility
    speedMapEnabled: data?.speedMapEnabled ?? data?.timeRemapEnabled ?? false,
    speedMap: data?.speedMap ?? data?.timeRemap,
    // Legacy (deprecated)
    timeRemapEnabled: data?.timeRemapEnabled ?? false,
    timeRemap: data?.timeRemap,
    flattenTransform: data?.flattenTransform ?? false,
    overrideFrameRate: data?.overrideFrameRate ?? false,
    frameRate: data?.frameRate,
  };
});

// Get referenced composition info
const compInfo = computed(() => {
  if (!nestedCompData.value.compositionId) return null;
  const comp = store.project.compositions[nestedCompData.value.compositionId];
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

// Speed map computed properties (with backwards compatibility)
const _speedMapEnabled = computed(() => {
  return (
    nestedCompData.value.speedMapEnabled ??
    nestedCompData.value.timeRemapEnabled ??
    false
  );
});

const speedMapProperty = computed(() => {
  return nestedCompData.value.speedMap ?? nestedCompData.value.timeRemap;
});

const _speedMapValue = computed(() => {
  const prop = speedMapProperty.value;
  if (!prop) return 0;
  return prop.value;
});

// Format duration as MM:SS.ms
function _formatDuration(seconds: number | undefined): string {
  if (seconds === undefined) return "0:00";
  const mins = Math.floor(seconds / 60);
  const secs = (seconds % 60).toFixed(2);
  return `${mins}:${secs.padStart(5, "0")}`;
}

// Enter the nested comp composition
function _enterNestedComp() {
  if (nestedCompData.value.compositionId) {
    store.enterNestedComp(nestedCompData.value.compositionId);
  }
}

// Speed map functions (with backwards compatibility)
function _toggleSpeedMap(e: Event) {
  const enabled = (e.target as HTMLInputElement).checked;
  const updates: Partial<NestedCompData> = {
    speedMapEnabled: enabled,
    timeRemapEnabled: enabled, // Backwards compatibility
  };

  // Create speed map property if enabling
  if (enabled && !nestedCompData.value.speedMap) {
    const newProp = createAnimatableProperty("Speed Map", 0, "number");
    updates.speedMap = newProp;
    updates.timeRemap = newProp; // Backwards compatibility
  }

  store.updateLayerData(props.layer.id, updates);
  emit("update", updates);
}

function _updateSpeedMap(value: number) {
  const prop = speedMapProperty.value;
  if (prop) {
    const speedMap: AnimatableProperty<number> = {
      ...prop,
      value,
    };
    store.updateLayerData(props.layer.id, {
      speedMap,
      timeRemap: speedMap, // Backwards compatibility
    });
    emit("update", { speedMap });
  }
}

// Frame rate override
function _toggleFrameRateOverride(e: Event) {
  const enabled = (e.target as HTMLInputElement).checked;
  const updates: Partial<NestedCompData> = {
    overrideFrameRate: enabled,
    frameRate: enabled ? compInfo.value?.fps || 30 : undefined,
  };
  store.updateLayerData(props.layer.id, updates);
  emit("update", updates);
}

function _updateFrameRate(value: number) {
  store.updateLayerData(props.layer.id, { frameRate: value });
  emit("update", { frameRate: value });
}

// Flatten transform
function _updateFlattenTransform(e: Event) {
  const enabled = (e.target as HTMLInputElement).checked;
  store.updateLayerData(props.layer.id, { flattenTransform: enabled });
  // Also update the layer-level flag
  store.updateLayer(props.layer.id, { flattenTransform: enabled });
  emit("update", { flattenTransform: enabled });
}

// Keyframe event handlers
function _onKeyframeChange() {
  // Keyframe was added or removed - trigger update
  emit("update", {});
}

function _onAnimationToggled(animated: boolean) {
  // Animation was enabled or disabled
  console.log("[NestedCompProperties] Animation toggled:", animated);
  emit("update", {});
}
</script>

<style scoped>
.nested-comp-properties {
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
