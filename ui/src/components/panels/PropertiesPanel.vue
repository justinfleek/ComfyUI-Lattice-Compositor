<template>
  <div class="properties-panel">
    <div class="panel-header">
      <span class="panel-title">Layer Properties</span>
    </div>

    <div class="panel-content" v-if="selectedLayer">
      <!-- Layer Name -->
      <div class="property-section">
        <div class="property-row">
          <input
            type="text"
            v-model="layerName"
            class="layer-name-input"
            @blur="updateLayerName"
            @keydown.enter="($event.target as HTMLInputElement).blur()"
          />
        </div>
      </div>

      <!-- Transform Section -->
      <div class="property-section">
        <div
          class="section-header"
          @click="toggleSection('transform')"
        >
          <span class="expand-icon">{{ expandedSections.includes('transform') ? '▼' : '►' }}</span>
          <span class="section-title">Transform</span>
        </div>

        <div v-if="expandedSections.includes('transform')" class="section-content">
          <div class="property-row">
            <label>Position</label>
            <div class="multi-value">
              <ScrubableNumber
                v-model="transform.position.x"
                :precision="1"
                unit="X"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.position.y"
                :precision="1"
                unit="Y"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-if="selectedLayer?.threeD"
                v-model="transform.position.z"
                :precision="1"
                unit="Z"
                @update:modelValue="updateTransform"
              />
            </div>
            <button class="keyframe-btn" :class="{ active: hasKeyframe('position') }" @click="toggleKeyframe('position')">◆</button>
          </div>

          <div class="property-row">
            <label>Scale</label>
            <div class="multi-value">
              <ScrubableNumber
                v-model="transform.scale.x"
                :min="0"
                :max="1000"
                unit="%"
                @update:modelValue="updateTransform"
              />
              <button
                class="link-btn"
                :class="{ active: scaleLocked }"
                @click="scaleLocked = !scaleLocked"
                title="Link scale values"
              >
                🔗
              </button>
              <ScrubableNumber
                v-model="transform.scale.y"
                :min="0"
                :max="1000"
                unit="%"
                @update:modelValue="updateTransform"
              />
            </div>
            <button class="keyframe-btn" :class="{ active: hasKeyframe('scale') }" @click="toggleKeyframe('scale')">◆</button>
          </div>

          <!-- 3D Rotations -->
          <template v-if="selectedLayer?.threeD">
            <div class="property-row">
              <label>Orientation</label>
              <div class="multi-value orientation-row">
                <ScrubableNumber v-model="transform.orientationX" unit="X" @update:modelValue="updateTransform" />
                <ScrubableNumber v-model="transform.orientationY" unit="Y" @update:modelValue="updateTransform" />
                <ScrubableNumber v-model="transform.orientationZ" unit="Z" @update:modelValue="updateTransform" />
              </div>
            </div>
            <div class="property-row">
              <label>X Rotation</label>
              <div class="single-value">
                <ScrubableNumber v-model="transform.rotationX" unit="°" @update:modelValue="updateTransform" />
              </div>
              <button class="keyframe-btn" :class="{ active: hasKeyframe('rotationX') }" @click="toggleKeyframe('rotationX')">◆</button>
            </div>
            <div class="property-row">
              <label>Y Rotation</label>
              <div class="single-value">
                <ScrubableNumber v-model="transform.rotationY" unit="°" @update:modelValue="updateTransform" />
              </div>
              <button class="keyframe-btn" :class="{ active: hasKeyframe('rotationY') }" @click="toggleKeyframe('rotationY')">◆</button>
            </div>
            <div class="property-row">
              <label>Z Rotation</label>
              <div class="single-value">
                <ScrubableNumber v-model="transform.rotationZ" unit="°" @update:modelValue="updateTransform" />
              </div>
              <button class="keyframe-btn" :class="{ active: hasKeyframe('rotationZ') }" @click="toggleKeyframe('rotationZ')">◆</button>
            </div>
          </template>
          <!-- 2D Rotation -->
          <template v-else>
            <div class="property-row">
              <label>Rotation</label>
              <div class="single-value">
                <ScrubableNumber
                  v-model="transform.rotation"
                  :min="-360"
                  :max="360"
                  unit="°"
                  @update:modelValue="updateTransform"
                />
              </div>
              <button class="keyframe-btn" :class="{ active: hasKeyframe('rotation') }" @click="toggleKeyframe('rotation')">◆</button>
            </div>
          </template>

          <div class="property-row">
            <label>Anchor Point</label>
            <div class="multi-value">
              <ScrubableNumber
                v-model="transform.anchorPoint.x"
                :precision="1"
                unit="X"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.anchorPoint.y"
                :precision="1"
                unit="Y"
                @update:modelValue="updateTransform"
              />
            </div>
            <button class="keyframe-btn" :class="{ active: hasKeyframe('anchorPoint') }" @click="toggleKeyframe('anchorPoint')">◆</button>
          </div>

          <div class="property-row">
            <label>Opacity</label>
            <div class="single-value">
              <SliderInput
                v-model="transform.opacity"
                :min="0"
                :max="100"
                unit="%"
                @update:modelValue="updateTransform"
              />
            </div>
            <button class="keyframe-btn" :class="{ active: hasKeyframe('opacity') }" @click="toggleKeyframe('opacity')">◆</button>
          </div>
        </div>
      </div>

      <!-- Blend Mode Section -->
      <div class="property-section">
        <div class="property-row">
          <label>Blend Mode</label>
          <select v-model="blendMode" class="blend-select" @change="updateBlendMode">
            <option v-for="mode in blendModes" :key="mode.value" :value="mode.value">
              {{ mode.label }}
            </option>
          </select>
        </div>
      </div>

      <!-- Layer-specific properties -->
      <component
        v-if="layerPropertiesComponent"
        :is="layerPropertiesComponent"
        :layer="selectedLayer"
        @update="onLayerUpdate"
      />
    </div>

    <!-- No Selection -->
    <div v-else class="empty-state">
      <p>No layer selected</p>
      <p class="hint">Select a layer to edit its properties</p>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, markRaw, type Component } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber, SliderInput } from '@/components/controls';

// Layer-specific property panels
import TextProperties from '@/components/properties/TextProperties.vue';
import ParticleProperties from '@/components/properties/ParticleProperties.vue';
import DepthflowProperties from '@/components/properties/DepthflowProperties.vue';
import LightProperties from '@/components/properties/LightProperties.vue';
import ShapeProperties from '@/components/properties/ShapeProperties.vue';
import VideoProperties from '@/components/properties/VideoProperties.vue';

const store = useCompositorStore();

// State
const expandedSections = ref<string[]>(['transform']);
const scaleLocked = ref(true);

const layerName = ref('');
const transform = ref({
  position: { x: 0, y: 0, z: 0 },
  scale: { x: 100, y: 100 },
  rotation: 0,
  anchorPoint: { x: 0, y: 0 },
  opacity: 100,
  // 3D properties
  orientationX: 0,
  orientationY: 0,
  orientationZ: 0,
  rotationX: 0,
  rotationY: 0,
  rotationZ: 0
});
const blendMode = ref('normal');
const keyframes = ref<string[]>([]);

// Blend modes
const blendModes = [
  { label: 'Normal', value: 'normal' },
  { label: 'Multiply', value: 'multiply' },
  { label: 'Screen', value: 'screen' },
  { label: 'Overlay', value: 'overlay' },
  { label: 'Soft Light', value: 'soft-light' },
  { label: 'Hard Light', value: 'hard-light' },
  { label: 'Color Dodge', value: 'color-dodge' },
  { label: 'Color Burn', value: 'color-burn' },
  { label: 'Darken', value: 'darken' },
  { label: 'Lighten', value: 'lighten' },
  { label: 'Difference', value: 'difference' },
  { label: 'Exclusion', value: 'exclusion' },
  { label: 'Hue', value: 'hue' },
  { label: 'Saturation', value: 'saturation' },
  { label: 'Color', value: 'color' },
  { label: 'Luminosity', value: 'luminosity' },
  { label: 'Add', value: 'add' }
];

// Computed
const selectedLayer = computed(() => store.selectedLayer);

const layerPropertiesComponent = computed<Component | null>(() => {
  if (!selectedLayer.value) return null;

  switch (selectedLayer.value.type) {
    case 'text':
      return markRaw(TextProperties);
    case 'particles':
      return markRaw(ParticleProperties);
    case 'depthflow':
      return markRaw(DepthflowProperties);
    case 'light':
      return markRaw(LightProperties);
    case 'spline':
      return markRaw(ShapeProperties);
    case 'video':
      return markRaw(VideoProperties);
    default:
      return null;
  }
});

// Watch selected layer
watch(selectedLayer, (layer) => {
  if (layer) {
    layerName.value = layer.name;
    const t = layer.transform;
    transform.value = {
      position: {
        x: t?.position?.value?.x || 0,
        y: t?.position?.value?.y || 0,
        z: t?.position?.value?.z || 0
      },
      scale: { x: t?.scale?.value?.x || 100, y: t?.scale?.value?.y || 100 },
      rotation: t?.rotation?.value || 0,
      anchorPoint: { x: t?.anchorPoint?.value?.x || 0, y: t?.anchorPoint?.value?.y || 0 },
      opacity: layer.opacity?.value || 100,
      // 3D properties
      orientationX: t?.orientation?.value?.x || 0,
      orientationY: t?.orientation?.value?.y || 0,
      orientationZ: t?.orientation?.value?.z || 0,
      rotationX: t?.rotationX?.value || 0,
      rotationY: t?.rotationY?.value || 0,
      rotationZ: t?.rotationZ?.value || 0
    };
    blendMode.value = layer.blendMode || 'normal';
  }
}, { immediate: true });

// Watch scale lock
watch(() => transform.value.scale.x, (newX, oldX) => {
  if (scaleLocked.value && newX !== oldX) {
    const ratio = newX / oldX;
    transform.value.scale.y = Math.round(transform.value.scale.y * ratio * 10) / 10;
  }
});

// Methods
function toggleSection(section: string) {
  const index = expandedSections.value.indexOf(section);
  if (index >= 0) {
    expandedSections.value.splice(index, 1);
  } else {
    expandedSections.value.push(section);
  }
}

function updateLayerName() {
  if (selectedLayer.value && layerName.value) {
    selectedLayer.value.name = layerName.value;
  }
}

function updateTransform() {
  if (!selectedLayer.value) return;
  const t = selectedLayer.value.transform;
  const v = transform.value;

  if (t?.position) {
    t.position.value = { x: v.position.x, y: v.position.y, z: v.position.z };
  }
  if (t?.scale) {
    t.scale.value = { x: v.scale.x, y: v.scale.y };
  }
  if (t?.rotation) {
    t.rotation.value = v.rotation;
  }
  if (t?.anchorPoint) {
    t.anchorPoint.value = { x: v.anchorPoint.x, y: v.anchorPoint.y };
  }
  if (selectedLayer.value.opacity) {
    selectedLayer.value.opacity.value = v.opacity;
  }

  // 3D properties
  if (selectedLayer.value.threeD) {
    if (t?.orientation) {
      t.orientation.value = { x: v.orientationX, y: v.orientationY, z: v.orientationZ };
    }
    if (t?.rotationX) t.rotationX.value = v.rotationX;
    if (t?.rotationY) t.rotationY.value = v.rotationY;
    if (t?.rotationZ) t.rotationZ.value = v.rotationZ;
  }

  onLayerUpdate();
}

function updateBlendMode() {
  if (selectedLayer.value) {
    selectedLayer.value.blendMode = blendMode.value;
  }
}

function hasKeyframe(property: string): boolean {
  return keyframes.value.includes(property);
}

function toggleKeyframe(property: string) {
  const index = keyframes.value.indexOf(property);
  if (index >= 0) {
    keyframes.value.splice(index, 1);
  } else {
    keyframes.value.push(property);
    console.log(`Added keyframe for ${property} at frame ${store.currentFrame}`);
  }
}

function onLayerUpdate() {
  store.project.meta.modified = new Date().toISOString();
}
</script>

<style scoped>
.properties-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 11px;
}

.panel-header {
  padding: 8px 10px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.panel-title {
  font-weight: 600;
  font-size: 12px;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  padding: 8px 0;
}

.property-section {
  border-bottom: 1px solid #2a2a2a;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 10px;
  cursor: pointer;
  user-select: none;
}

.section-header:hover {
  background: #252525;
}

.expand-icon {
  width: 10px;
  font-size: 8px;
  color: #666;
}

.section-title {
  font-weight: 500;
  flex: 1;
}

.section-content {
  padding: 4px 10px 8px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 10px;
  min-height: 26px;
}

.property-row label {
  width: 80px;
  color: #888;
  font-size: 10px;
  flex-shrink: 0;
}

.single-value {
  flex: 1;
}

.multi-value {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 4px;
}

.multi-value > * {
  flex: 1;
}

.link-btn {
  flex: 0 0 auto !important;
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: #555;
  cursor: pointer;
  border-radius: 3px;
  font-size: 10px;
}

.link-btn:hover {
  background: #333;
}

.link-btn.active {
  color: #4a90d9;
}

.keyframe-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: #444;
  cursor: pointer;
  font-size: 10px;
  border-radius: 2px;
}

.keyframe-btn:hover {
  color: #888;
}

.keyframe-btn.active {
  color: #f0c040;
}

.layer-name-input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid #3a3a3a;
  background: #1a1a1a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 12px;
  font-weight: 500;
}

.layer-name-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.blend-select {
  flex: 1;
  padding: 4px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 11px;
}

.empty-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  padding: 24px;
  text-align: center;
  color: #555;
}

.empty-state .hint {
  font-size: 10px;
  margin-top: 4px;
}
</style>
