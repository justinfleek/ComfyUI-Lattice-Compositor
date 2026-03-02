<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Level of Detail (LOD)</span>
    </div>
    <div v-if="expanded" class="section-content">
      <p class="help-text">
        Reduce particle detail at distance for better performance.
      </p>

      <div class="property-row checkbox-row">
        <label title="Enable level-of-detail based on camera distance">
          <input
            type="checkbox"
            :checked="config.enabled"
            @change="update('enabled', ($event.target as HTMLInputElement).checked)"
          />
          Enable LOD
        </label>
      </div>

      <template v-if="config.enabled">
        <div class="lod-level">
          <h4>Near Distance (Full Detail)</h4>
          <div class="property-row">
            <label title="Particles closer than this distance render at full size">Distance</label>
            <input
              type="range"
              :value="config.nearDistance"
              min="10"
              max="500"
              step="10"
              @input="update('nearDistance', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ config.nearDistance }}</span>
          </div>
          <div class="property-row">
            <label title="Size multiplier for near particles (1 = full size)">Size</label>
            <input
              type="range"
              :value="config.nearSizeMultiplier"
              min="0.1"
              max="2"
              step="0.1"
              @input="update('nearSizeMultiplier', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ config.nearSizeMultiplier.toFixed(1) }}x</span>
          </div>
        </div>

        <div class="lod-level">
          <h4>Mid Distance</h4>
          <div class="property-row">
            <label title="Distance threshold for mid-range particles">Distance</label>
            <input
              type="range"
              :value="config.midDistance"
              min="100"
              max="2000"
              step="50"
              @input="update('midDistance', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ config.midDistance }}</span>
          </div>
          <div class="property-row">
            <label title="Size multiplier for mid-range particles">Size</label>
            <input
              type="range"
              :value="config.midSizeMultiplier"
              min="0.1"
              max="1.5"
              step="0.1"
              @input="update('midSizeMultiplier', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ config.midSizeMultiplier.toFixed(1) }}x</span>
          </div>
        </div>

        <div class="lod-level">
          <h4>Far Distance (Minimum Detail)</h4>
          <div class="property-row">
            <label title="Particles beyond this distance render at minimum size">Distance</label>
            <input
              type="range"
              :value="config.farDistance"
              min="500"
              max="5000"
              step="100"
              @input="update('farDistance', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ config.farDistance }}</span>
          </div>
          <div class="property-row">
            <label title="Size multiplier for far particles (smaller = better performance)">Size</label>
            <input
              type="range"
              :value="config.farSizeMultiplier"
              min="0"
              max="1"
              step="0.05"
              @input="update('farSizeMultiplier', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ config.farSizeMultiplier.toFixed(2) }}x</span>
          </div>
        </div>
      </template>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";

export interface LODConfig {
  enabled: boolean;
  nearDistance: number;
  midDistance: number;
  farDistance: number;
  nearSizeMultiplier: number;
  midSizeMultiplier: number;
  farSizeMultiplier: number;
}

const props = defineProps<{
  config: LODConfig;
  expanded: boolean;
}>();

const emit = defineEmits<{
  toggle: [];
  update: [key: keyof LODConfig, value: number | boolean];
}>();

function update(key: keyof LODConfig, value: number | boolean) {
  emit("update", key, value);
}
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

.property-row input[type="number"] {
  width: 70px;
  padding: 4px 8px;
  background: #2a2a2a;
  border: 1px solid #444;
  color: #fff;
  border-radius: 4px;
}

.value-display {
  flex: 0 0 50px;
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

.checkbox-row input[type="checkbox"] {
  cursor: pointer;
}

.lod-level {
  background: #1a1a1a;
  border-radius: 6px;
  padding: 10px;
  margin-bottom: 10px;
}

.lod-level h4 {
  margin: 0 0 8px 0;
  font-size: 12px;
  color: #aaa;
  font-weight: 500;
}
</style>
