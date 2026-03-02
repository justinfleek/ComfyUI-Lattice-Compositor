<template>
  <div class="matte-properties">
    <!-- Matte Source -->
    <div class="prop-section">
      <div class="section-title">Matte Source</div>

      <div class="row">
        <label>Source Layer</label>
        <select :value="matteData.sourceLayerId || ''" @change="updateData('sourceLayerId', ($event.target as HTMLSelectElement).value || null)">
          <option value="">None (Self)</option>
          <option v-for="layer in sourceLayers" :key="layer.id" :value="layer.id">
            {{ layer.name }}
          </option>
        </select>
      </div>

      <div class="row">
        <label>Extract From</label>
        <select :value="matteData.matteType" @change="updateData('matteType', ($event.target as HTMLSelectElement).value as MatteLayerData['matteType'])">
          <option value="luminance">Luminance</option>
          <option value="alpha">Alpha Channel</option>
          <option value="red">Red Channel</option>
          <option value="green">Green Channel</option>
          <option value="blue">Blue Channel</option>
          <option value="hue">Hue</option>
          <option value="saturation">Saturation</option>
        </select>
      </div>
    </div>

    <!-- Matte Adjustments -->
    <div class="prop-section">
      <div class="section-title">Adjustments</div>

      <div class="row">
        <label>Threshold</label>
        <ScrubableNumber
          :modelValue="matteData.threshold"
          @update:modelValue="(v: number) => updateData('threshold', v)"
          :min="0"
          :max="1"
          :precision="2"
        />
      </div>

      <div class="row">
        <label>Feather</label>
        <ScrubableNumber
          :modelValue="matteData.feather"
          @update:modelValue="(v: number) => updateData('feather', v)"
          :min="0"
          :max="100"
          :precision="1"
        />
      </div>

      <div class="row">
        <label>Expansion</label>
        <ScrubableNumber
          :modelValue="matteData.expansion"
          @update:modelValue="(v: number) => updateData('expansion', v)"
          :min="-50"
          :max="50"
          :precision="1"
        />
      </div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="matteData.invert" @change="updateData('invert', !matteData.invert)" />
          Invert Matte
        </label>
      </div>
    </div>

    <!-- Preview Mode -->
    <div class="prop-section">
      <div class="section-title">Preview</div>

      <div class="preview-buttons">
        <button
          v-for="mode in previewModes"
          :key="mode.value"
          class="preview-btn"
          :class="{ active: matteData.previewMode === mode.value }"
          @click="updateData('previewMode', mode.value)"
          :title="mode.description"
        >
          {{ mode.label }}
        </button>
      </div>
    </div>

    <!-- Quick Actions -->
    <div class="prop-section">
      <div class="section-title">Quick Actions</div>

      <div class="action-buttons">
        <button class="action-btn" @click="resetToDefaults">
          Reset Defaults
        </button>
        <button class="action-btn" @click="invertMatte">
          {{ matteData.invert ? 'Un-invert' : 'Invert' }}
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useProjectStore } from "@/stores/projectStore";
import type { Layer, MatteLayerData } from "@/types/project";

const props = defineProps<{
  layer: Layer;
}>();

const emit =
  defineEmits<(e: "update", data: Partial<MatteLayerData>) => void>();

const projectStore = useProjectStore();

const matteData = computed(() => props.layer.data as MatteLayerData);

// Get layers that can be matte sources
const sourceLayers = computed(() => {
  return projectStore.getActiveCompLayers().filter(
    (l) =>
      l.id !== props.layer.id &&
      ["image", "video", "solid", "text", "shape", "spline"].includes(l.type),
  );
});

const previewModes = [
  { value: "matte", label: "Matte", description: "View matte as grayscale" },
  {
    value: "composite",
    label: "Result",
    description: "View composited result",
  },
  {
    value: "overlay",
    label: "Overlay",
    description: "View matte overlaid on source",
  },
] as const;

function updateData<K extends keyof MatteLayerData>(
  key: K,
  value: MatteLayerData[K],
) {
  emit("update", { [key]: value } as Partial<MatteLayerData>);
}

function resetToDefaults() {
  emit("update", {
    matteType: "luminance",
    invert: false,
    threshold: 0.5,
    feather: 0,
    expansion: 0,
    previewMode: "matte",
  });
}

function invertMatte() {
  updateData("invert", !matteData.value.invert);
}
</script>

<style scoped>
.matte-properties {
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

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  min-width: auto;
  color: #e0e0e0;
  font-size: 13px;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
  accent-color: #4a90d9;
}

.preview-buttons {
  display: flex;
  gap: 4px;
}

.preview-btn {
  flex: 1;
  padding: 8px 12px;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: #252525;
  color: #888;
  font-size: 12px;
  cursor: pointer;
  transition: all 0.15s;
}

.preview-btn:hover {
  background: #333;
  color: #e0e0e0;
}

.preview-btn.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.action-buttons {
  display: flex;
  gap: 8px;
}

.action-btn {
  flex: 1;
  padding: 8px 12px;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: #252525;
  color: #e0e0e0;
  font-size: 12px;
  cursor: pointer;
  transition: all 0.15s;
}

.action-btn:hover {
  background: #333;
}
</style>
