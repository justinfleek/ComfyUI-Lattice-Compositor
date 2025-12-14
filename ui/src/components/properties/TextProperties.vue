<template>
  <div class="text-properties">
    <div class="property-group">
      <label>Source Text</label>
      <textarea
        v-model="textData.text"
        class="main-text-input"
        rows="3"
        @input="e => updateData('text', (e.target as HTMLTextAreaElement).value)"
      ></textarea>
    </div>

    <div class="property-group">
      <div class="row">
        <div class="col">
          <label>Font</label>
          <select v-model="textData.fontFamily" class="select-input" @change="emit('update')">
            <option value="Arial">Arial</option>
            <option value="Helvetica">Helvetica</option>
            <option value="Times New Roman">Times New Roman</option>
            <option value="Courier New">Courier New</option>
            <option value="Georgia">Georgia</option>
            <option value="Verdana">Verdana</option>
          </select>
        </div>
        <div class="col">
          <label>Size</label>
          <ScrubableNumber :modelValue="textData.fontSize" @update:modelValue="v => updateData('fontSize', v)" :min="1" :max="500" />
        </div>
      </div>
    </div>

    <div class="property-group">
      <div class="row">
        <div class="col">
          <label>Fill Color</label>
          <ColorPicker :modelValue="textData.fill" @update:modelValue="v => updateData('fill', v)" />
        </div>
        <div class="col">
          <label>Stroke Color</label>
          <ColorPicker :modelValue="textData.stroke || '#000000'" @update:modelValue="v => updateData('stroke', v)" />
        </div>
      </div>
      <div class="row">
        <div class="col">
          <label>Stroke Width</label>
          <ScrubableNumber :modelValue="textData.strokeWidth || 0" @update:modelValue="v => updateData('strokeWidth', v)" :min="0" :max="50" />
        </div>
        <div class="col">
          <label>Alignment</label>
          <div class="align-buttons">
            <button :class="{ active: textData.textAlign === 'left' }" @click="setAlign('left')">◀</button>
            <button :class="{ active: textData.textAlign === 'center' }" @click="setAlign('center')">▬</button>
            <button :class="{ active: textData.textAlign === 'right' }" @click="setAlign('right')">▶</button>
          </div>
        </div>
      </div>
    </div>

    <div class="property-group">
      <div class="row">
        <label>Tracking</label>
        <ScrubableNumber :modelValue="textData.tracking || 0" @update:modelValue="v => updateAnimatable('Tracking', v)" />
        <KeyframeToggle :property="getProperty('Tracking')" :layerId="layer.id" />
      </div>
      <div class="row">
        <label>Line Spacing</label>
        <ScrubableNumber :modelValue="textData.lineSpacing || 0" @update:modelValue="v => updateAnimatable('Line Spacing', v)" />
        <KeyframeToggle :property="getProperty('Line Spacing')" :layerId="layer.id" />
      </div>
      <div class="row">
        <label>Character Offset</label>
        <ScrubableNumber :modelValue="textData.characterOffset || 0" @update:modelValue="v => updateAnimatable('Character Offset', v)" :precision="0" />
        <KeyframeToggle :property="getProperty('Character Offset')" :layerId="layer.id" />
      </div>
    </div>

    <div class="property-group checkbox">
      <label>
        <input type="checkbox" v-model="textData.perCharacter3D" @change="emit('update')" />
        Enable Per-Character 3D
      </label>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber, ColorPicker } from '@/components/controls';
import KeyframeToggle from './KeyframeToggle.vue';

const props = defineProps<{ layer: any }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

const textData = computed(() => props.layer.data || {
  text: 'Text',
  fontFamily: 'Arial',
  fontSize: 48,
  fill: '#ffffff',
  stroke: '#000000',
  strokeWidth: 0,
  textAlign: 'left',
  tracking: 0,
  lineSpacing: 0,
  characterOffset: 0,
  perCharacter3D: false
});

function getProperty(name: string) {
  return props.layer.properties?.find((p: any) => p.name === name);
}

function updateData(key: string, val: any) {
  // 1. Update static data (for immediate render)
  if (textData.value) {
    textData.value[key] = val;
  }

  // 2. Update Animatable Property (for Timeline/Keyframes)
  // Map internal keys to Property Names
  const keyMap: Record<string, string> = {
    'fill': 'Fill Color',
    'stroke': 'Stroke Color',
    'fontSize': 'Font Size',
    'strokeWidth': 'Stroke Width',
    'text': 'Source Text'
  };

  const propName = keyMap[key];
  if (propName) {
    const prop = getProperty(propName);
    if (prop) {
      prop.value = val;
      store.project.meta.modified = new Date().toISOString();
    }
  }

  emit('update');
}

function setAlign(align: 'left' | 'center' | 'right') {
  if (textData.value) {
    textData.value.textAlign = align;
    emit('update');
  }
}

function updateAnimatable(name: string, val: number) {
  const prop = getProperty(name);
  if (prop) {
    prop.value = val;
    store.project.meta.modified = new Date().toISOString();
  }

  // Also update static data for immediate render
  const keyMap: Record<string, string> = {
    'Tracking': 'tracking',
    'Line Spacing': 'lineSpacing',
    'Character Offset': 'characterOffset'
  };
  const dataKey = keyMap[name];
  if (dataKey && textData.value) {
    textData.value[dataKey] = val;
  }
  emit('update');
}
</script>

<style scoped>
.text-properties { padding: 12px; font-size: 14px; color: #ccc; }

.property-group {
  margin-bottom: 16px;
  border-bottom: 1px solid #333;
  padding-bottom: 12px;
}
.property-group:last-child { border-bottom: none; }

label {
  display: block;
  color: #888;
  margin-bottom: 6px;
  font-size: 12px;
  font-weight: 500;
}

.main-text-input {
  width: 100%;
  background: #111;
  color: #fff;
  border: 1px solid #444;
  padding: 10px;
  font-size: 15px;
  font-family: inherit;
  border-radius: 4px;
  resize: vertical;
  min-height: 60px;
}
.main-text-input:focus { border-color: #4a90d9; outline: none; }

.row {
  display: flex;
  align-items: center;
  gap: 12px;
  margin-bottom: 10px;
}
.row:last-child { margin-bottom: 0; }

.row > label {
  min-width: 110px;
  margin-bottom: 0;
  font-size: 13px;
}

.col { flex: 1; }

.select-input {
  width: 100%;
  background: #111;
  color: #ccc;
  border: 1px solid #444;
  padding: 6px 8px;
  font-size: 13px;
  border-radius: 3px;
}
.select-input:focus { border-color: #4a90d9; outline: none; }

.align-buttons {
  display: flex;
  background: #111;
  border: 1px solid #444;
  border-radius: 4px;
  overflow: hidden;
}
.align-buttons button {
  flex: 1;
  background: transparent;
  border: none;
  color: #666;
  padding: 6px 10px;
  cursor: pointer;
  font-size: 12px;
  border-right: 1px solid #444;
}
.align-buttons button:last-child { border-right: none; }
.align-buttons button.active { background: #4a90d9; color: #fff; }
.align-buttons button:hover:not(.active) { background: #333; color: #fff; }

.checkbox label {
  display: flex;
  align-items: center;
  gap: 10px;
  cursor: pointer;
  color: #eee;
  font-size: 13px;
}
.checkbox input[type="checkbox"] {
  width: 16px;
  height: 16px;
  cursor: pointer;
}
</style>
