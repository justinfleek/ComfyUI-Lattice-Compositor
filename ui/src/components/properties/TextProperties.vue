<template>
  <div class="text-properties">
    <h4>Text Properties</h4>

    <!-- Text Content -->
    <div class="property-group">
      <label>Text</label>
      <textarea
        v-model="textData.text"
        class="text-input"
        rows="2"
        @input="updateTextContent"
      />
    </div>

    <!-- Font Family -->
    <div class="property-group">
      <label>Font Family</label>
      <div class="font-select-row">
        <select
          v-model="textData.fontFamily"
          class="font-select"
          @change="updateFont"
        >
          <optgroup label="Web Safe">
            <option v-for="font in webSafeFonts" :key="font" :value="font">
              {{ font }}
            </option>
          </optgroup>
          <optgroup label="Google Fonts">
            <option v-for="font in googleFonts" :key="font" :value="font">
              {{ font }}
            </option>
          </optgroup>
        </select>
        <button class="picker-btn" @click="showFontPicker = true" title="Browse fonts">
          <i class="pi pi-search" />
        </button>
      </div>
    </div>

    <!-- Font Size (Animatable) -->
    <div class="property-group">
      <div class="property-header">
        <label>Font Size</label>
        <KeyframeToggle
          v-if="fontSizeProperty"
          :property="fontSizeProperty"
          :layerId="layer.id"
        />
      </div>
      <div class="slider-row">
        <input
          type="range"
          v-model.number="textData.fontSize"
          :min="8"
          :max="200"
          class="slider"
          @input="updateFontSize"
        />
        <input
          type="number"
          v-model.number="textData.fontSize"
          :min="8"
          :max="200"
          class="number-input"
          @change="updateFontSize"
        />
      </div>
    </div>

    <!-- Text Color -->
    <div class="property-group">
      <label>Fill Color</label>
      <div class="color-row">
        <input
          type="color"
          v-model="textData.fill"
          class="color-input"
          @input="updateFill"
        />
        <input
          type="text"
          v-model="textData.fill"
          class="color-text"
          @change="updateFill"
        />
      </div>
    </div>

    <!-- Path Attachment -->
    <div class="property-group">
      <label>Attach to Path</label>
      <select
        v-model="textData.pathLayerId"
        class="path-select"
        @change="updatePathAttachment"
      >
        <option :value="null">None</option>
        <option v-for="path in splineLayers" :key="path.id" :value="path.id">
          {{ path.name }}
        </option>
      </select>
    </div>

    <!-- Path Offset (Animatable) - only shown when attached to path -->
    <div class="property-group" v-if="textData.pathLayerId">
      <div class="property-header">
        <label>Path Offset</label>
        <KeyframeToggle
          v-if="pathOffsetProperty"
          :property="pathOffsetProperty"
          :layerId="layer.id"
        />
      </div>
      <div class="slider-row">
        <input
          type="range"
          v-model.number="pathOffsetValue"
          :min="0"
          :max="100"
          class="slider"
          @input="updatePathOffset"
        />
        <span class="value-display">{{ Math.round(pathOffsetValue) }}%</span>
      </div>
    </div>

    <!-- Letter Spacing -->
    <div class="property-group">
      <label>Letter Spacing</label>
      <div class="slider-row">
        <input
          type="range"
          v-model.number="textData.letterSpacing"
          :min="-20"
          :max="50"
          class="slider"
          @input="updateLetterSpacing"
        />
        <input
          type="number"
          v-model.number="textData.letterSpacing"
          class="number-input"
          @change="updateLetterSpacing"
        />
      </div>
    </div>

    <!-- Font Picker Dialog -->
    <FontPicker
      v-if="showFontPicker"
      :current-font="textData.fontFamily"
      @select="selectFont"
      @close="showFontPicker = false"
    />
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { fontService } from '@/services/fontService';
import KeyframeToggle from './KeyframeToggle.vue';
import FontPicker from '../dialogs/FontPicker.vue';
import type { Layer, TextData, AnimatableProperty } from '@/types/project';

interface Props {
  layer: Layer;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: 'update'): void;
}>();

const store = useCompositorStore();

// Font picker visibility
const showFontPicker = ref(false);

// Font lists
const webSafeFonts = ref<string[]>([]);
const googleFonts = ref<string[]>([]);

// Get text data from layer
const textData = computed<TextData>(() => {
  return (props.layer.data as TextData) || {
    text: 'Text',
    fontFamily: 'Arial',
    fontSize: 48,
    fontWeight: '400',
    fontStyle: 'normal',
    fill: '#ffffff',
    stroke: '',
    strokeWidth: 0,
    letterSpacing: 0,
    lineHeight: 1.2,
    textAlign: 'left',
    pathLayerId: null,
    pathOffset: 0,
    pathAlign: 'left'
  };
});

// Get spline layers for path attachment
const splineLayers = computed(() => {
  return store.layers.filter(l => l.type === 'spline' && l.id !== props.layer.id);
});

// Find animatable properties
const fontSizeProperty = computed((): AnimatableProperty<number> | undefined => {
  return props.layer.properties.find(p => p.name === 'fontSize') as AnimatableProperty<number> | undefined;
});

const pathOffsetProperty = computed((): AnimatableProperty<number> | undefined => {
  return props.layer.properties.find(p => p.name === 'pathOffset') as AnimatableProperty<number> | undefined;
});

// Path offset as percentage (0-100)
const pathOffsetValue = computed({
  get: () => (textData.value.pathOffset || 0) * 100,
  set: (v: number) => {
    textData.value.pathOffset = v / 100;
  }
});

// Initialize font service
onMounted(async () => {
  await fontService.initialize();
  webSafeFonts.value = fontService.getWebSafeFonts().map(f => f.family);
  googleFonts.value = fontService.getGoogleFonts();
});

// Update handlers
function updateTextContent(): void {
  emit('update');
}

function updateFont(): void {
  // Ensure font is loaded
  fontService.ensureFont(textData.value.fontFamily);
  emit('update');
}

function updateFontSize(): void {
  // Also update the animatable property if exists
  if (fontSizeProperty.value) {
    fontSizeProperty.value.value = textData.value.fontSize;
  }
  emit('update');
}

function updateFill(): void {
  emit('update');
}

function updatePathAttachment(): void {
  // Reset path offset when changing path
  if (!textData.value.pathLayerId) {
    textData.value.pathOffset = 0;
  }
  emit('update');
}

function updatePathOffset(): void {
  // Also update the animatable property if exists
  if (pathOffsetProperty.value) {
    pathOffsetProperty.value.value = textData.value.pathOffset;
  }
  emit('update');
}

function updateLetterSpacing(): void {
  emit('update');
}

function selectFont(fontFamily: string): void {
  textData.value.fontFamily = fontFamily;
  showFontPicker.value = false;
  updateFont();
}

// Ensure animatable properties exist for fontSize and pathOffset
watch(() => props.layer, (layer) => {
  if (layer.type !== 'text') return;

  // Ensure fontSize property exists
  if (!layer.properties.find(p => p.name === 'fontSize')) {
    layer.properties.push({
      id: `prop_fontSize_${Date.now()}`,
      name: 'fontSize',
      type: 'number',
      value: textData.value.fontSize,
      animated: false,
      keyframes: []
    });
  }

  // Ensure pathOffset property exists
  if (!layer.properties.find(p => p.name === 'pathOffset')) {
    layer.properties.push({
      id: `prop_pathOffset_${Date.now()}`,
      name: 'pathOffset',
      type: 'number',
      value: 0,
      animated: false,
      keyframes: []
    });
  }
}, { immediate: true });
</script>

<style scoped>
.text-properties {
  padding: 0;
}

.text-properties h4 {
  margin: 0 0 12px 0;
  padding-bottom: 8px;
  border-bottom: 1px solid #3d3d3d;
  font-size: 12px;
  font-weight: 500;
  color: #aaa;
}

.property-group {
  margin-bottom: 12px;
}

.property-group label {
  display: block;
  font-size: 11px;
  color: #888;
  margin-bottom: 4px;
}

.property-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  margin-bottom: 4px;
}

.property-header label {
  margin-bottom: 0;
}

.text-input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
  resize: vertical;
  font-family: inherit;
}

.text-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.font-select-row {
  display: flex;
  gap: 4px;
}

.font-select {
  flex: 1;
  padding: 6px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
}

.picker-btn {
  padding: 6px 10px;
  border: 1px solid #3d3d3d;
  background: #2a2a2a;
  color: #aaa;
  border-radius: 4px;
  cursor: pointer;
}

.picker-btn:hover {
  background: #3a3a3a;
  color: #fff;
}

.slider-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.slider {
  flex: 1;
  height: 4px;
  cursor: pointer;
}

.number-input {
  width: 60px;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
  text-align: right;
}

.number-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.value-display {
  width: 50px;
  font-size: 11px;
  color: #aaa;
  text-align: right;
}

.color-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.color-input {
  width: 32px;
  height: 24px;
  padding: 0;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  cursor: pointer;
}

.color-text {
  flex: 1;
  padding: 4px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
  font-family: monospace;
}

.color-text:focus {
  outline: none;
  border-color: #4a90d9;
}

.path-select {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
}
</style>
