<template>
  <div class="normal-properties">
    <!-- Visualization Mode -->
    <div class="prop-section">
      <div class="section-title">Visualization</div>

      <div class="row">
        <label>Mode</label>
        <select :value="normalData.visualizationMode" @change="updateData('visualizationMode', ($event.target as HTMLSelectElement).value as NormalLayerData['visualizationMode'])">
          <option value="rgb">RGB (Raw Normals)</option>
          <option value="hemisphere">Hemisphere</option>
          <option value="lit">Lit Preview</option>
        </select>
      </div>

      <div class="row">
        <label>Format</label>
        <select :value="normalData.format" @change="updateData('format', ($event.target as HTMLSelectElement).value as NormalLayerData['format'])">
          <option value="opengl">OpenGL (Y-up)</option>
          <option value="directx">DirectX (Y-down)</option>
        </select>
      </div>
    </div>

    <!-- Axis Flipping -->
    <div class="prop-section">
      <div class="section-title">Axis Adjustment</div>

      <div class="row flip-toggles">
        <label class="flip-toggle" :class="{ active: normalData.flipX }">
          <input type="checkbox" :checked="normalData.flipX" @change="updateData('flipX', !normalData.flipX)" />
          Flip X
        </label>
        <label class="flip-toggle" :class="{ active: normalData.flipY }">
          <input type="checkbox" :checked="normalData.flipY" @change="updateData('flipY', !normalData.flipY)" />
          Flip Y
        </label>
        <label class="flip-toggle" :class="{ active: normalData.flipZ }">
          <input type="checkbox" :checked="normalData.flipZ" @change="updateData('flipZ', !normalData.flipZ)" />
          Flip Z
        </label>
      </div>
    </div>

    <!-- Lighting Settings (for lit mode) -->
    <div class="prop-section" v-if="normalData.visualizationMode === 'lit'">
      <div class="section-title">Lighting</div>

      <div class="row">
        <label>Light X</label>
        <ScrubableNumber
          :modelValue="normalData.lightDirection.x"
          @update:modelValue="v => updateLightDirection('x', v)"
          :min="-1"
          :max="1"
          :precision="2"
        />
      </div>

      <div class="row">
        <label>Light Y</label>
        <ScrubableNumber
          :modelValue="normalData.lightDirection.y"
          @update:modelValue="v => updateLightDirection('y', v)"
          :min="-1"
          :max="1"
          :precision="2"
        />
      </div>

      <div class="row">
        <label>Light Z</label>
        <ScrubableNumber
          :modelValue="normalData.lightDirection.z"
          @update:modelValue="v => updateLightDirection('z', v)"
          :min="-1"
          :max="1"
          :precision="2"
        />
      </div>

      <div class="row">
        <label>Intensity</label>
        <ScrubableNumber
          :modelValue="normalData.lightIntensity"
          @update:modelValue="v => updateData('lightIntensity', v)"
          :min="0"
          :max="3"
          :precision="2"
        />
      </div>

      <div class="row">
        <label>Ambient</label>
        <ScrubableNumber
          :modelValue="normalData.ambientIntensity"
          @update:modelValue="v => updateData('ambientIntensity', v)"
          :min="0"
          :max="1"
          :precision="2"
        />
      </div>

      <div class="light-preview">
        <div
          class="light-indicator"
          :style="{
            left: `${(normalData.lightDirection.x + 1) * 50}%`,
            top: `${(1 - normalData.lightDirection.y) * 50}%`,
            opacity: Math.max(0.3, normalData.lightDirection.z)
          }"
        />
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import type { Layer, NormalLayerData } from "@/types/project";

const props = defineProps<{
  layer: Layer;
}>();

const emit =
  defineEmits<(e: "update", data: Partial<NormalLayerData>) => void>();

const normalData = computed(() => props.layer.data as NormalLayerData);

function _updateData<K extends keyof NormalLayerData>(
  key: K,
  value: NormalLayerData[K],
) {
  emit("update", { [key]: value } as Partial<NormalLayerData>);
}

function _updateLightDirection(axis: "x" | "y" | "z", value: number) {
  emit("update", {
    lightDirection: {
      ...normalData.value.lightDirection,
      [axis]: value,
    },
  });
}
</script>

<style scoped>
.normal-properties {
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
  min-width: 70px;
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

.flip-toggles {
  display: flex;
  gap: 8px;
  justify-content: space-between;
}

.flip-toggle {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 6px 12px;
  background: #252525;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  cursor: pointer;
  font-size: 12px;
  color: #888;
  transition: all 0.15s;
  min-width: auto !important;
}

.flip-toggle:hover {
  background: #2a2a2a;
}

.flip-toggle.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.flip-toggle input {
  display: none;
}

.color-row input[type="color"] {
  width: 40px;
  height: 24px;
  padding: 0;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: transparent;
  cursor: pointer;
}

.light-preview {
  position: relative;
  width: 100%;
  height: 60px;
  background: radial-gradient(circle at center, #333 0%, #1e1e1e 100%);
  border-radius: 4px;
  margin-top: 8px;
  overflow: hidden;
}

.light-indicator {
  position: absolute;
  width: 16px;
  height: 16px;
  background: #f0c040;
  border-radius: 50%;
  transform: translate(-50%, -50%);
  box-shadow: 0 0 20px rgba(240, 192, 64, 0.6);
  transition: all 0.1s;
}
</style>
