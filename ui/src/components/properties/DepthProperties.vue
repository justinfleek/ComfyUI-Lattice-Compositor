<template>
  <div class="depth-properties">
    <!-- Visualization Mode -->
    <div class="prop-section">
      <div class="section-title">Visualization</div>

      <div class="row">
        <label>Mode</label>
        <select :value="depthData.visualizationMode" @change="updateData('visualizationMode', ($event.target as HTMLSelectElement).value)">
          <option value="grayscale">Grayscale</option>
          <option value="colormap">Colormap</option>
          <option value="contour">Contour Lines</option>
          <option value="3d-mesh">3D Mesh Preview</option>
        </select>
      </div>

      <div class="row" v-if="depthData.visualizationMode === 'colormap' || depthData.visualizationMode === 'contour'">
        <label>Color Map</label>
        <select :value="depthData.colorMap" @change="updateData('colorMap', ($event.target as HTMLSelectElement).value)">
          <option value="turbo">Turbo (Rainbow)</option>
          <option value="viridis">Viridis (Blue-Green-Yellow)</option>
          <option value="plasma">Plasma (Purple-Orange)</option>
          <option value="inferno">Inferno (Black-Red-Yellow)</option>
          <option value="magma">Magma (Black-Purple-White)</option>
          <option value="grayscale">Grayscale</option>
        </select>
      </div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="depthData.invert" @change="updateData('invert', !depthData.invert)" />
          Invert Depth
        </label>
      </div>
    </div>

    <!-- Depth Range -->
    <div class="prop-section">
      <div class="section-title">Depth Range</div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="depthData.autoNormalize" @change="updateData('autoNormalize', !depthData.autoNormalize)" />
          Auto Normalize
        </label>
      </div>

      <template v-if="!depthData.autoNormalize">
        <div class="row">
          <label>Min Depth</label>
          <ScrubableNumber
            :modelValue="depthData.minDepth"
            @update:modelValue="v => updateData('minDepth', v)"
            :min="0"
            :max="1"
            :precision="3"
          />
        </div>

        <div class="row">
          <label>Max Depth</label>
          <ScrubableNumber
            :modelValue="depthData.maxDepth"
            @update:modelValue="v => updateData('maxDepth', v)"
            :min="0"
            :max="1"
            :precision="3"
          />
        </div>
      </template>
    </div>

    <!-- Contour Settings -->
    <div class="prop-section" v-if="depthData.visualizationMode === 'contour'">
      <div class="section-title">Contour Settings</div>

      <div class="row">
        <label>Levels</label>
        <ScrubableNumber
          :modelValue="depthData.contourLevels"
          @update:modelValue="v => updateData('contourLevels', v)"
          :min="2"
          :max="50"
          :precision="0"
        />
      </div>

      <div class="row">
        <label>Line Width</label>
        <ScrubableNumber
          :modelValue="depthData.contourWidth"
          @update:modelValue="v => updateData('contourWidth', v)"
          :min="0.1"
          :max="5"
          :precision="1"
        />
      </div>

      <div class="row color-row">
        <label>Line Color</label>
        <input
          type="color"
          :value="depthData.contourColor"
          @input="updateData('contourColor', ($event.target as HTMLInputElement).value)"
        />
      </div>
    </div>

    <!-- 3D Mesh Settings -->
    <div class="prop-section" v-if="depthData.visualizationMode === '3d-mesh'">
      <div class="section-title">3D Mesh Settings</div>

      <div class="row">
        <label>Displacement</label>
        <ScrubableNumber
          :modelValue="getAnimatableValue(depthData.meshDisplacement)"
          @update:modelValue="v => updateAnimatable('meshDisplacement', v)"
          :min="0"
          :max="500"
          :precision="1"
        />
        <button
          class="keyframe-btn"
          :class="{ active: isAnimated('meshDisplacement') }"
          @click="toggleKeyframe('meshDisplacement')"
          title="Add keyframe"
        >◆</button>
      </div>

      <div class="row">
        <label>Resolution</label>
        <ScrubableNumber
          :modelValue="depthData.meshResolution"
          @update:modelValue="v => updateData('meshResolution', v)"
          :min="8"
          :max="256"
          :precision="0"
        />
      </div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="depthData.wireframe" @change="updateData('wireframe', !depthData.wireframe)" />
          Wireframe
        </label>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, DepthLayerData, AnimatableProperty } from '@/types/project';
import { ScrubableNumber } from '@/components/controls';

const props = defineProps<{
  layer: Layer;
}>();

const emit = defineEmits<{
  (e: 'update', data: Partial<DepthLayerData>): void;
}>();

const store = useCompositorStore();

const depthData = computed(() => props.layer.data as DepthLayerData);

function updateData<K extends keyof DepthLayerData>(key: K, value: DepthLayerData[K]) {
  emit('update', { [key]: value } as Partial<DepthLayerData>);
}

function getAnimatableValue(prop: AnimatableProperty<number> | undefined): number {
  return prop?.value ?? 0;
}

function isAnimated(propName: string): boolean {
  const prop = depthData.value[propName as keyof DepthLayerData] as AnimatableProperty<number> | undefined;
  return prop?.animated ?? false;
}

function updateAnimatable(propName: string, value: number) {
  const prop = depthData.value[propName as keyof DepthLayerData] as AnimatableProperty<number>;
  if (prop) {
    emit('update', {
      [propName]: { ...prop, value }
    } as Partial<DepthLayerData>);
  }
}

function toggleKeyframe(propName: string) {
  const prop = depthData.value[propName as keyof DepthLayerData] as AnimatableProperty<number>;
  if (prop) {
    store.addKeyframe(props.layer.id, `data.${propName}`, store.currentFrame, prop.value);
  }
}
</script>

<style scoped>
.depth-properties {
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
  min-width: 90px;
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
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
  accent-color: #4a90d9;
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

.keyframe-btn {
  width: 20px;
  height: 20px;
  padding: 0;
  border: none;
  background: transparent;
  color: #555;
  cursor: pointer;
  font-size: 12px;
  border-radius: 2px;
}

.keyframe-btn:hover {
  color: #888;
}

.keyframe-btn.active {
  color: #f0c040;
}
</style>
