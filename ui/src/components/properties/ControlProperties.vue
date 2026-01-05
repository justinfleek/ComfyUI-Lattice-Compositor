<template>
  <div class="control-properties">
    <!-- Visual Settings -->
    <div class="prop-section">
      <div class="section-title">Visual Settings</div>

      <div class="row">
        <label>Icon Size</label>
        <ScrubableNumber
          :modelValue="controlData.size"
          @update:modelValue="v => updateData('size', v)"
          :min="10"
          :max="200"
          :precision="0"
        />
      </div>

      <div class="row">
        <label>Icon Shape</label>
        <select :value="controlData.iconShape" @change="updateData('iconShape', ($event.target as HTMLSelectElement).value as ControlLayerData['iconShape'])">
          <option value="crosshair">Crosshair</option>
          <option value="diamond">Diamond</option>
          <option value="circle">Circle</option>
          <option value="square">Square</option>
        </select>
      </div>

      <div class="row color-row">
        <label>Icon Color</label>
        <div class="color-picker-wrapper">
          <input
            type="color"
            :value="controlData.iconColor"
            @input="updateData('iconColor', ($event.target as HTMLInputElement).value)"
          />
          <span class="color-hex">{{ controlData.iconColor }}</span>
        </div>
      </div>
    </div>

    <!-- Display Options -->
    <div class="prop-section">
      <div class="section-title">Display Options</div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="controlData.showIcon" @change="updateData('showIcon', !controlData.showIcon)" />
          Show Icon
        </label>
        <span class="hint-icon" title="Display the control icon in the viewport">?</span>
      </div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="controlData.showAxes" @change="updateData('showAxes', !controlData.showAxes)" />
          Show Axes
        </label>
        <span class="hint-icon" title="Display XYZ axis indicators">?</span>
      </div>
    </div>

    <!-- Quick Color Presets -->
    <div class="prop-section">
      <div class="section-title">Color Presets</div>
      <div class="color-presets">
        <button
          v-for="preset in colorPresets"
          :key="preset.color"
          class="preset-btn"
          :style="{ backgroundColor: preset.color }"
          :title="preset.name"
          @click="updateData('iconColor', preset.color)"
        />
      </div>
    </div>

    <!-- Info -->
    <div class="prop-section">
      <div class="info-note">
        Control layers are invisible in renders. Use them as parent objects to control groups of layers.
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import type { ControlLayerData, Layer } from "@/types/project";

const props = defineProps<{
  layer: Layer;
}>();

const emit =
  defineEmits<(e: "update", data: Partial<ControlLayerData>) => void>();

const _controlData = computed(() => props.layer.data as ControlLayerData);

const _colorPresets = [
  { name: "Yellow", color: "#ffcc00" },
  { name: "Red", color: "#e74c3c" },
  { name: "Orange", color: "#e67e22" },
  { name: "Green", color: "#2ecc71" },
  { name: "Cyan", color: "#1abc9c" },
  { name: "Blue", color: "#3498db" },
  { name: "Purple", color: "#9b59b6" },
  { name: "Pink", color: "#e91e63" },
  { name: "White", color: "#ffffff" },
];

function _updateData<K extends keyof ControlLayerData>(
  key: K,
  value: ControlLayerData[K],
) {
  emit("update", { [key]: value } as Partial<ControlLayerData>);
}
</script>

<style scoped>
.control-properties {
  padding: 8px 0;
}

.prop-section {
  margin-bottom: 12px;
  padding: 0 10px;
}

.section-title {
  font-size: 12px;
  font-weight: 600;
  color: #4a90d9;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-bottom: 8px;
  padding-bottom: 4px;
  border-bottom: 1px solid #333;
}

.row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.row label {
  min-width: 80px;
  font-size: 13px;
  color: #888;
}

.row select {
  flex: 1;
  padding: 4px 8px;
  background: #1e1e1e;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
}

.row select:focus {
  outline: none;
  border-color: #4a90d9;
}

.color-row {
  display: flex;
  align-items: center;
}

.color-picker-wrapper {
  display: flex;
  align-items: center;
  gap: 8px;
  flex: 1;
}

.color-picker-wrapper input[type="color"] {
  width: 40px;
  height: 28px;
  padding: 0;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: transparent;
  cursor: pointer;
}

.color-hex {
  font-family: monospace;
  font-size: 12px;
  color: #888;
  text-transform: uppercase;
}

.checkbox-row {
  display: flex;
  align-items: center;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  min-width: auto;
  color: #e0e0e0;
  font-size: 13px;
  flex: 1;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
  accent-color: #4a90d9;
}

.hint-icon {
  width: 16px;
  height: 16px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 10px;
  color: #666;
  background: #333;
  border-radius: 50%;
  cursor: help;
}

.color-presets {
  display: flex;
  gap: 4px;
  flex-wrap: wrap;
}

.preset-btn {
  width: 24px;
  height: 24px;
  border: 2px solid #1e1e1e;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.15s;
}

.preset-btn:hover {
  transform: scale(1.1);
  border-color: #fff;
}

.info-note {
  font-size: 12px;
  color: #666;
  font-style: italic;
  padding: 8px;
  background: #252525;
  border-radius: 4px;
  border-left: 3px solid #4a90d9;
}
</style>
