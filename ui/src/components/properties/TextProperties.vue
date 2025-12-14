<template>
  <div class="text-properties">
    <!-- Text Section -->
    <div class="property-section">
      <div class="section-header">
        <span class="expand-icon">▼</span>
        <span>Text</span>
      </div>
      <div class="section-content">
        <div class="property-group">
          <label>Source Text</label>
          <textarea
            v-model="textData.text"
            class="text-input"
            rows="2"
            @input="emit('update')"
          />
        </div>

        <div class="property-group">
          <label>Font</label>
          <div class="font-row">
            <select v-model="textData.fontFamily" class="font-select" @change="updateFont">
              <option value="Arial">Arial</option>
              <option value="Helvetica">Helvetica</option>
              <option value="Times New Roman">Times New Roman</option>
              <option value="Courier New">Courier New</option>
              <option value="Georgia">Georgia</option>
              <option value="Verdana">Verdana</option>
            </select>
            <select v-model="textData.fontWeight" class="weight-select" @change="emit('update')">
              <option value="400">Regular</option>
              <option value="500">Medium</option>
              <option value="600">Semibold</option>
              <option value="700">Bold</option>
            </select>
          </div>
        </div>

        <div class="property-row">
          <label>Size</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              v-model="textData.fontSize"
              :min="1"
              :max="500"
              unit="px"
              @update:modelValue="updateAnimatable('fontSize', $event)"
            />
            <KeyframeToggle :property="getProperty('fontSize')" :layerId="layer.id" />
          </div>
        </div>

        <div class="property-row">
          <label>Fill</label>
          <ColorPicker
            :modelValue="textData.fill"
            @update:modelValue="v => { textData.fill = v; emit('update'); }"
          />
        </div>

        <div class="property-row">
          <label>Stroke</label>
          <div class="stroke-row">
            <ColorPicker
              :modelValue="textData.stroke || '#000000'"
              @update:modelValue="v => { textData.stroke = v; emit('update'); }"
            />
            <ScrubableNumber
              v-model="textData.strokeWidth"
              :min="0"
              :max="100"
              unit="px"
              @update:modelValue="emit('update')"
            />
          </div>
        </div>

        <div class="property-row">
          <label>Alignment</label>
          <div class="icon-toggle-group">
            <button :class="{ active: textData.textAlign === 'left' }" @click="setAlign('left')" title="Left">◀</button>
            <button :class="{ active: textData.textAlign === 'center' }" @click="setAlign('center')" title="Center">▬</button>
            <button :class="{ active: textData.textAlign === 'right' }" @click="setAlign('right')" title="Right">▶</button>
          </div>
        </div>
      </div>
    </div>

    <!-- Path Options Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('pathOptions')">
        <span class="expand-icon">{{ expandedSections.has('pathOptions') ? '▼' : '►' }}</span>
        <span>Path Options</span>
      </div>
      <div v-if="expandedSections.has('pathOptions')" class="section-content">
        <div class="property-row">
          <label>Path</label>
          <select v-model="textData.pathLayerId" class="full-select" @change="emit('update')">
            <option :value="null">None</option>
            <option v-for="p in splineLayers" :key="p.id" :value="p.id">{{ p.name }}</option>
          </select>
        </div>
        <template v-if="textData.pathLayerId">
          <div class="property-row">
            <label>Path Offset</label>
            <div class="control-with-keyframe">
              <ScrubableNumber
                :modelValue="(textData.pathOffset || 0) * 100"
                @update:modelValue="v => { textData.pathOffset = v / 100; updateAnimatable('pathOffset', v / 100); }"
                :min="0"
                :max="100"
                unit="%"
              />
              <KeyframeToggle :property="getProperty('pathOffset')" :layerId="layer.id" />
            </div>
          </div>
          <div class="property-row">
            <label>Path Align</label>
            <select v-model="textData.pathAlign" class="full-select" @change="emit('update')">
              <option value="left">Left</option>
              <option value="center">Center</option>
              <option value="right">Right</option>
            </select>
          </div>
        </template>
      </div>
    </div>

    <!-- More Options Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('moreOptions')">
        <span class="expand-icon">{{ expandedSections.has('moreOptions') ? '▼' : '►' }}</span>
        <span>More Options</span>
      </div>
      <div v-if="expandedSections.has('moreOptions')" class="section-content">
        <div class="property-row">
          <label>Grouping</label>
          <select v-model="textData.anchorPointGrouping" class="full-select" @change="emit('update')">
            <option value="character">Character</option>
            <option value="word">Word</option>
            <option value="line">Line</option>
            <option value="all">All</option>
          </select>
        </div>

        <div class="property-row">
          <label>Alignment</label>
          <div class="multi-value">
            <ScrubableNumber
              v-model="textData.groupingAlignment.x"
              :min="-100"
              :max="100"
              unit="X%"
              @update:modelValue="emit('update')"
            />
            <ScrubableNumber
              v-model="textData.groupingAlignment.y"
              :min="-100"
              :max="100"
              unit="Y%"
              @update:modelValue="emit('update')"
            />
          </div>
        </div>

        <div class="property-row">
          <label>Fill & Stroke</label>
          <select v-model="textData.fillAndStroke" class="full-select" @change="emit('update')">
            <option value="fill-over-stroke">Fill Over Stroke</option>
            <option value="stroke-over-fill">Stroke Over Fill</option>
          </select>
        </div>

        <div class="property-row">
          <label>Blending</label>
          <select v-model="textData.interCharacterBlending" class="full-select" @change="emit('update')">
            <option value="normal">Normal</option>
            <option value="multiply">Multiply</option>
            <option value="screen">Screen</option>
            <option value="overlay">Overlay</option>
          </select>
        </div>
      </div>
    </div>

    <!-- Advanced Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('advanced')">
        <span class="expand-icon">{{ expandedSections.has('advanced') ? '▼' : '►' }}</span>
        <span>Advanced</span>
      </div>
      <div v-if="expandedSections.has('advanced')" class="section-content">
        <div class="property-row checkbox-row">
          <label>
            <input type="checkbox" v-model="textData.perCharacter3D" @change="emit('update')" />
            Enable Per-character 3D
          </label>
        </div>

        <div class="property-row">
          <label>Tracking</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              v-model="textData.tracking"
              unit="em"
              @update:modelValue="updateAnimatable('tracking', $event)"
            />
            <KeyframeToggle :property="getProperty('tracking')" :layerId="layer.id" />
          </div>
        </div>

        <div class="property-row">
          <label>Line Spacing</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              v-model="textData.lineSpacing"
              unit="px"
              @update:modelValue="updateAnimatable('lineSpacing', $event)"
            />
            <KeyframeToggle :property="getProperty('lineSpacing')" :layerId="layer.id" />
          </div>
        </div>

        <div class="property-row">
          <label>Line Anchor</label>
          <ScrubableNumber
            v-model="textData.lineAnchor"
            :min="0"
            :max="100"
            unit="%"
            @update:modelValue="emit('update')"
          />
        </div>

        <div class="property-row">
          <label>Char Offset</label>
          <div class="control-with-keyframe">
            <ScrubableNumber
              v-model="textData.characterOffset"
              :precision="0"
              @update:modelValue="updateAnimatable('characterOffset', $event)"
            />
            <KeyframeToggle :property="getProperty('characterOffset')" :layerId="layer.id" />
          </div>
        </div>

        <div class="property-row">
          <label>Blur</label>
          <div class="multi-value">
            <ScrubableNumber v-model="textData.blur.x" unit="X" @update:modelValue="emit('update')" />
            <ScrubableNumber v-model="textData.blur.y" unit="Y" @update:modelValue="emit('update')" />
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber, ColorPicker } from '@/components/controls';
import KeyframeToggle from './KeyframeToggle.vue';
import { fontService } from '@/services/fontService';
import type { Layer, TextData } from '@/types/project';

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

const expandedSections = ref(new Set(['pathOptions', 'moreOptions', 'advanced']));

const textData = computed<TextData>(() => {
  return props.layer.data as TextData || {
    text: 'Text',
    fontFamily: 'Arial',
    fontSize: 48,
    fontWeight: '400',
    fontStyle: 'normal',
    fill: '#ffffff',
    stroke: '',
    strokeWidth: 0,
    tracking: 0,
    lineSpacing: 0,
    lineAnchor: 0,
    characterOffset: 0,
    characterValue: 0,
    blur: { x: 0, y: 0 },
    letterSpacing: 0,
    lineHeight: 1.2,
    textAlign: 'left',
    pathLayerId: null,
    pathOffset: 0,
    pathAlign: 'left',
    anchorPointGrouping: 'character',
    groupingAlignment: { x: 0, y: 0 },
    fillAndStroke: 'fill-over-stroke',
    interCharacterBlending: 'normal',
    perCharacter3D: false
  };
});

const splineLayers = computed(() => store.layers.filter(l => l.type === 'spline'));

function toggleSection(sec: string) {
  if (expandedSections.value.has(sec)) expandedSections.value.delete(sec);
  else expandedSections.value.add(sec);
}

function getProperty(name: string) {
  return props.layer.properties.find(p => p.name === name);
}

function updateAnimatable(name: string, val: number) {
  const prop = getProperty(name);
  if (prop) prop.value = val;
  emit('update');
}

function updateFont() {
  fontService.ensureFont(textData.value.fontFamily);
  emit('update');
}

function setAlign(align: 'left' | 'center' | 'right') {
  textData.value.textAlign = align;
  emit('update');
}

onMounted(async () => {
  await fontService.initialize();
});
</script>

<style scoped>
.text-properties { padding: 0; }
.property-section { border-bottom: 1px solid #2a2a2a; }
.section-header {
  padding: 8px 10px;
  background: #252525;
  cursor: pointer;
  display: flex;
  align-items: center;
  gap: 6px;
  font-weight: 600;
  font-size: 12px;
  color: #aaa;
}
.section-header:hover { background: #2a2a2a; }
.expand-icon { font-size: 8px; color: #666; width: 10px; }
.section-content { padding: 10px; background: #1e1e1e; display: flex; flex-direction: column; gap: 8px; }

.property-group { margin-bottom: 4px; }
.property-group label { display: block; color: #888; font-size: 10px; margin-bottom: 4px; }

.property-row { display: flex; align-items: center; justify-content: space-between; gap: 8px; }
.property-row > label { width: 80px; color: #888; font-size: 11px; flex-shrink: 0; }

.text-input {
  width: 100%;
  background: #111;
  border: 1px solid #333;
  color: #eee;
  padding: 6px;
  font-family: inherit;
  font-size: 12px;
  border-radius: 3px;
  resize: vertical;
}
.text-input:focus { outline: none; border-color: #4a90d9; }

.font-row { display: flex; gap: 4px; }
.font-select { flex: 2; background: #111; color: #ccc; border: 1px solid #333; padding: 4px; font-size: 11px; }
.weight-select { flex: 1; background: #111; color: #ccc; border: 1px solid #333; padding: 4px; font-size: 11px; }
.full-select { flex: 1; background: #111; color: #ccc; border: 1px solid #333; padding: 4px; font-size: 11px; }

.control-with-keyframe { flex: 1; display: flex; align-items: center; gap: 4px; }
.stroke-row { flex: 1; display: flex; align-items: center; gap: 8px; }
.multi-value { flex: 1; display: flex; gap: 4px; }

.icon-toggle-group { display: flex; background: #111; border-radius: 3px; border: 1px solid #333; }
.icon-toggle-group button {
  background: transparent; border: none; color: #666; padding: 4px 8px; cursor: pointer; font-size: 10px;
  border-right: 1px solid #333;
}
.icon-toggle-group button:last-child { border-right: none; }
.icon-toggle-group button.active { background: #4a90d9; color: #fff; }
.icon-toggle-group button:hover:not(.active) { background: #333; }

.checkbox-row label { display: flex; align-items: center; gap: 6px; cursor: pointer; color: #ccc; font-size: 11px; }
</style>
