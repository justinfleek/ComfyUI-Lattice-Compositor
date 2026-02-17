<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Depth of Field</span>
    </div>
    <div v-if="expanded" class="section-content">
      <p class="help-text">
        Blur particles based on their distance from the focus point.
      </p>

      <div class="property-row checkbox-row">
        <label title="Enable depth of field blur effect">
          <input
            type="checkbox"
            :checked="config.enabled"
            @change="update('enabled', ($event.target as HTMLInputElement).checked)"
          />
          Enable DoF
        </label>
      </div>

      <template v-if="config.enabled">
        <div class="property-row">
          <label title="Distance from camera to the focus plane (in pixels)">Focus Distance</label>
          <input
            type="range"
            :value="config.focusDistance"
            min="50"
            max="2000"
            step="25"
            @input="update('focusDistance', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ config.focusDistance }}px</span>
        </div>

        <div class="property-row">
          <label title="Range around focus distance that remains sharp">Focus Range</label>
          <input
            type="range"
            :value="config.focusRange"
            min="10"
            max="500"
            step="10"
            @input="update('focusRange', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ config.focusRange }}px</span>
        </div>

        <div class="property-row">
          <label title="Maximum blur amount (0 = no blur, 1 = fully transparent)">Max Blur</label>
          <input
            type="range"
            :value="config.maxBlur"
            min="0"
            max="1"
            step="0.05"
            @input="update('maxBlur', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ Math.round(config.maxBlur * 100) }}%</span>
        </div>

        <div class="dof-preview">
          <div class="focus-diagram">
            <div class="blur-zone near" :style="{ width: `${nearBlurWidth}%` }">
              <span>Blur</span>
            </div>
            <div class="focus-zone" :style="{ width: `${focusWidth}%`, left: `${focusLeft}%` }">
              <span>In Focus</span>
            </div>
            <div class="blur-zone far" :style="{ width: `${farBlurWidth}%` }">
              <span>Blur</span>
            </div>
          </div>
          <div class="distance-markers">
            <span>Near</span>
            <span>{{ config.focusDistance }}px</span>
            <span>Far</span>
          </div>
        </div>
      </template>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";

export interface DOFConfig {
  enabled: boolean;
  focusDistance: number;
  focusRange: number;
  maxBlur: number;
}

const props = defineProps<{
  config: DOFConfig;
  expanded: boolean;
}>();

const emit = defineEmits<{
  toggle: [];
  update: [key: keyof DOFConfig, value: number | boolean];
}>();

function update(key: keyof DOFConfig, value: number | boolean) {
  emit("update", key, value);
}

// Calculate diagram dimensions
const focusLeft = computed(() => {
  const totalRange = 2000; // Assume 2000px max view depth
  return Math.max(0, ((props.config.focusDistance - props.config.focusRange / 2) / totalRange) * 100);
});

const focusWidth = computed(() => {
  const totalRange = 2000;
  return Math.min(100 - focusLeft.value, (props.config.focusRange / totalRange) * 100);
});

const nearBlurWidth = computed(() => focusLeft.value);
const farBlurWidth = computed(() => 100 - focusLeft.value - focusWidth.value);
</script>

<style scoped>
.property-section {
  border-bottom: 1px solid #333;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 10px 12px;
  cursor: pointer;
  user-select: none;
  background: #1e1e1e;
}

.section-header:hover {
  background: #252525;
}

.section-content {
  padding: 12px;
  background: #181818;
}

.help-text {
  color: #888;
  font-size: 12px;
  margin: 0 0 12px 0;
  line-height: 1.4;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.property-row label {
  flex: 0 0 100px;
  font-size: 12px;
  color: #ccc;
}

.property-row input[type="range"] {
  flex: 1;
}

.value-display {
  flex: 0 0 60px;
  text-align: right;
  font-size: 11px;
  color: #888;
}

.checkbox-row label {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
}

.dof-preview {
  margin-top: 16px;
  padding: 12px;
  background: #1a1a1a;
  border-radius: 6px;
}

.focus-diagram {
  position: relative;
  height: 30px;
  background: #333;
  border-radius: 4px;
  overflow: hidden;
  display: flex;
}

.blur-zone {
  background: linear-gradient(90deg, rgba(100, 100, 100, 0.5), rgba(100, 100, 100, 0.3));
  display: flex;
  align-items: center;
  justify-content: center;
}

.blur-zone span {
  font-size: 10px;
  color: #666;
}

.focus-zone {
  position: absolute;
  height: 100%;
  background: linear-gradient(90deg, #4a9eff, #6ab4ff, #4a9eff);
  display: flex;
  align-items: center;
  justify-content: center;
}

.focus-zone span {
  font-size: 10px;
  color: #fff;
  font-weight: 500;
  text-shadow: 0 1px 2px rgba(0,0,0,0.5);
}

.distance-markers {
  display: flex;
  justify-content: space-between;
  margin-top: 6px;
  font-size: 10px;
  color: #666;
}
</style>
