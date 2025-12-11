<template>
  <div class="properties-panel">
    <div class="panel-header">
      <span class="panel-title">Properties</span>
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
                :min="-10000"
                :max="10000"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.position.y"
                :min="-10000"
                :max="10000"
                :precision="1"
                unit="px"
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
                :precision="1"
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
                :precision="1"
                unit="%"
                @update:modelValue="updateTransform"
              />
            </div>
            <button class="keyframe-btn" :class="{ active: hasKeyframe('scale') }" @click="toggleKeyframe('scale')">◆</button>
          </div>

          <div class="property-row">
            <label>Rotation</label>
            <div class="single-value">
              <ScrubableNumber
                v-model="transform.rotation"
                :min="-180"
                :max="180"
                :precision="1"
                :wrap="true"
                unit="°"
                @update:modelValue="updateTransform"
              />
            </div>
            <button class="keyframe-btn" :class="{ active: hasKeyframe('rotation') }" @click="toggleKeyframe('rotation')">◆</button>
          </div>

          <div class="property-row">
            <label>Anchor Point</label>
            <div class="multi-value">
              <ScrubableNumber
                v-model="transform.anchorPoint.x"
                :min="-10000"
                :max="10000"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.anchorPoint.y"
                :min="-10000"
                :max="10000"
                :precision="1"
                unit="px"
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
                :precision="0"
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

      <!-- Effects Section -->
      <div v-if="effects.length > 0" class="property-section">
        <div
          class="section-header"
          @click="toggleSection('effects')"
        >
          <span class="expand-icon">{{ expandedSections.includes('effects') ? '▼' : '►' }}</span>
          <span class="section-title">Effects</span>
          <span class="effect-count">{{ effects.length }}</span>
        </div>

        <div v-if="expandedSections.includes('effects')" class="section-content">
          <div
            v-for="(effect, index) in effects"
            :key="effect.id"
            class="effect-item"
          >
            <div class="effect-header">
              <input
                type="checkbox"
                :checked="effect.enabled"
                @change="toggleEffect(index)"
                class="effect-toggle"
              />
              <span class="effect-name">{{ effect.name }}</span>
              <button class="effect-delete" @click="removeEffect(index)">×</button>
            </div>
            <!-- Effect parameters would go here -->
          </div>
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

const store = useCompositorStore();

// State
const expandedSections = ref<string[]>(['transform']);
const scaleLocked = ref(true);

const layerName = ref('');
const transform = ref({
  position: { x: 0, y: 0 },
  scale: { x: 100, y: 100 },
  rotation: 0,
  anchorPoint: { x: 0, y: 0 },
  opacity: 100
});
const blendMode = ref('normal');
const effects = ref<any[]>([]);
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
    default:
      return null;
  }
});

// Watch selected layer
watch(selectedLayer, (layer) => {
  if (layer) {
    layerName.value = layer.name;
    transform.value = {
      position: { x: layer.position?.value?.[0] || 0, y: layer.position?.value?.[1] || 0 },
      scale: { x: layer.scale?.value?.[0] || 100, y: layer.scale?.value?.[1] || 100 },
      rotation: layer.rotation?.value || 0,
      anchorPoint: { x: layer.anchorPoint?.value?.[0] || 0, y: layer.anchorPoint?.value?.[1] || 0 },
      opacity: layer.opacity?.value || 100
    };
    blendMode.value = layer.blendMode || 'normal';
    effects.value = (layer as any).effects || [];
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

  if (selectedLayer.value.position) {
    selectedLayer.value.position.value = [transform.value.position.x, transform.value.position.y];
  }
  if (selectedLayer.value.scale) {
    selectedLayer.value.scale.value = [transform.value.scale.x, transform.value.scale.y];
  }
  if (selectedLayer.value.rotation) {
    selectedLayer.value.rotation.value = transform.value.rotation;
  }
  if (selectedLayer.value.anchorPoint) {
    selectedLayer.value.anchorPoint.value = [transform.value.anchorPoint.x, transform.value.anchorPoint.y];
  }
  if (selectedLayer.value.opacity) {
    selectedLayer.value.opacity.value = transform.value.opacity;
  }
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
    // In real implementation, this would add a keyframe at current time
    console.log(`Added keyframe for ${property} at frame ${store.currentFrame}`);
  }
}

function toggleEffect(index: number) {
  if (effects.value[index]) {
    effects.value[index].enabled = !effects.value[index].enabled;
  }
}

function removeEffect(index: number) {
  effects.value.splice(index, 1);
  if (selectedLayer.value && (selectedLayer.value as any).effects) {
    (selectedLayer.value as any).effects.splice(index, 1);
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

.effect-count {
  font-size: 9px;
  color: #666;
  background: #333;
  padding: 1px 5px;
  border-radius: 8px;
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

.effect-item {
  background: #222;
  border-radius: 4px;
  margin-bottom: 4px;
}

.effect-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
}

.effect-toggle {
  width: 14px;
  height: 14px;
}

.effect-name {
  flex: 1;
  font-size: 11px;
}

.effect-delete {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: #666;
  cursor: pointer;
  font-size: 14px;
  border-radius: 3px;
}

.effect-delete:hover {
  background: #3a3a3a;
  color: #ff6b6b;
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
