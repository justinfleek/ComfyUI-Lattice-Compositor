<template>
  <div
    class="enhanced-layer-track"
    :class="{
      selected: isSelected,
      locked: layer.locked,
      hidden: !layer.visible,
      soloed: isSoloed,
      'dimmed-by-solo': isDimmedBySolo
    }"
    @click="selectLayer"
    :style="{ '--label-color': layer.labelColor || '#7c9cff' }"
  >
    <!-- Layer info sidebar -->
    <div class="layer-info">
      <!-- Label color indicator -->
      <div class="label-color" @click.stop="showLabelPicker = !showLabelPicker">
        <div
          v-if="showLabelPicker"
          class="label-picker"
          @click.stop
        >
          <button
            v-for="color in labelColors"
            :key="color"
            :style="{ background: color }"
            @click="setLabelColor(color)"
          />
        </div>
      </div>

      <!-- AV switches (visibility + audio) -->
      <div class="av-switches">
        <button
          class="icon-btn"
          :class="{ active: layer.visible }"
          @click.stop="toggleVisibility"
          :title="layer.visible ? 'Hide (V)' : 'Show (V)'"
        >
          <span class="icon">{{ layer.visible ? 'V' : '-' }}</span>
        </button>
        <button
          v-if="hasAudio"
          class="icon-btn"
          :class="{ active: layer.audioEnabled }"
          @click.stop="toggleAudio"
          title="Toggle Audio"
        >
          <span class="icon">A</span>
        </button>
      </div>

      <!-- Solo -->
      <button
        class="icon-btn solo-btn"
        :class="{ active: isSoloed }"
        @click.stop="toggleSolo"
        title="Solo (S)"
      >
        <span class="icon">S</span>
      </button>

      <!-- Lock -->
      <button
        class="icon-btn lock-btn"
        :class="{ active: layer.locked }"
        @click.stop="toggleLock"
        :title="layer.locked ? 'Unlock (L)' : 'Lock (L)'"
      >
        <span class="icon">{{ layer.locked ? 'L' : 'u' }}</span>
      </button>

      <!-- Layer name with type icon -->
      <div class="layer-name-container">
        <span class="layer-type-icon" :title="layer.type">
          {{ getTypeIcon(layer.type) }}
        </span>
        <span
          class="layer-name"
          :title="layer.name"
          @dblclick.stop="startRename"
        >
          <input
            v-if="isRenaming"
            v-model="renameValue"
            @blur="finishRename"
            @keyup.enter="finishRename"
            @keyup.escape="cancelRename"
            class="rename-input"
            ref="renameInput"
          />
          <template v-else>{{ layer.name }}</template>
        </span>
      </div>

      <!-- Parent picker -->
      <div class="parent-picker">
        <select
          :value="layer.parentId || ''"
          @change="setParent"
          :disabled="layer.locked"
          class="parent-select"
          title="Parent & Link"
        >
          <option value="">None</option>
          <option
            v-for="parentLayer in availableParents"
            :key="parentLayer.id"
            :value="parentLayer.id"
          >
            {{ parentLayer.name }}
          </option>
        </select>
      </div>

      <!-- Layer switches (when expanded) -->
      <div v-if="showSwitches" class="layer-switches">
        <button
          class="switch-btn"
          :class="{ active: layer.shy }"
          @click.stop="toggleSwitch('shy')"
          title="Shy"
        >
          Sh
        </button>
        <button
          class="switch-btn"
          :class="{ active: layer.collapse }"
          @click.stop="toggleSwitch('collapse')"
          title="Collapse Transformations"
        >
          Ct
        </button>
        <button
          class="switch-btn"
          :class="{ active: layer.quality === 'best' }"
          @click.stop="toggleQuality"
          title="Quality"
        >
          {{ layer.quality === 'best' ? 'B' : 'D' }}
        </button>
        <button
          class="switch-btn"
          :class="{ active: layer.is3D }"
          @click.stop="toggleSwitch('is3D')"
          title="3D Layer"
        >
          3D
        </button>
        <button
          class="switch-btn"
          :class="{ active: layer.motionBlur }"
          @click.stop="toggleSwitch('motionBlur')"
          title="Motion Blur"
        >
          MB
        </button>
      </div>
    </div>

    <!-- Timeline track area -->
    <div class="track-area" ref="trackAreaRef">
      <!-- Layer duration bar -->
      <div
        class="duration-bar"
        :style="durationBarStyle"
        :class="{ 'has-keyframes': hasKeyframes }"
        @mousedown="startDrag"
      >
        <!-- In/Out handles for trimming -->
        <div
          class="trim-handle trim-in"
          @mousedown.stop="startTrimIn"
        />
        <div
          class="trim-handle trim-out"
          @mousedown.stop="startTrimOut"
        />

        <!-- Effect indicators -->
        <div v-if="layer.effects && layer.effects.length > 0" class="effect-indicator" title="Has Effects">
          fx
        </div>
      </div>

      <!-- Keyframe diamonds -->
      <div
        v-for="keyframe in allKeyframes"
        :key="keyframe.id"
        class="keyframe-diamond"
        :style="{ left: `${getKeyframePosition(keyframe.frame)}%` }"
        :class="{
          selected: selectedKeyframeIds.includes(keyframe.id),
          [keyframe.interpolation]: true
        }"
        :title="`${keyframe.propertyName} @ Frame ${keyframe.frame}`"
        @click.stop="selectKeyframe(keyframe.id)"
        @dblclick.stop="goToKeyframe(keyframe.frame)"
      />

      <!-- Expression indicator -->
      <div
        v-for="expr in expressionIndicators"
        :key="expr.propertyId"
        class="expression-indicator"
        :style="{ left: `${getKeyframePosition(expr.startFrame)}%` }"
        title="Expression"
      >
        =
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, nextTick } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, Keyframe } from '@/types/project';

interface Props {
  layer: Layer;
  frameCount: number;
  allLayers: Layer[];
  soloedLayerIds: string[];
  showSwitches: boolean;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: 'select', layerId: string): void;
  (e: 'updateLayer', layerId: string, updates: Partial<Layer>): void;
  (e: 'selectKeyframe', keyframeId: string): void;
  (e: 'setParent', childId: string, parentId: string | null): void;
  (e: 'toggleSolo', layerId: string): void;
}>();

const store = useCompositorStore();

const trackAreaRef = ref<HTMLDivElement | null>(null);
const renameInput = ref<HTMLInputElement | null>(null);
const showLabelPicker = ref(false);
const isRenaming = ref(false);
const renameValue = ref('');

// Label colors
const labelColors = [
  '#ff6b6b', '#ffc107', '#4ecdc4', '#45b7d1',
  '#96ceb4', '#7c9cff', '#bb8fce', '#ff8a65',
  '#a1887f', '#90a4ae', '#e0e0e0', '#333333'
];

// Selection state
const isSelected = computed(() => store.selectedLayerIds.includes(props.layer.id));
const selectedKeyframeIds = computed(() => store.selectedKeyframeIds);
const isSoloed = computed(() => props.soloedLayerIds.includes(props.layer.id));
const isDimmedBySolo = computed(() =>
  props.soloedLayerIds.length > 0 && !isSoloed.value
);

// Check if layer has audio
const hasAudio = computed(() =>
  props.layer.type === 'audio' || props.layer.type === 'video'
);

// Available parent layers (exclude self and children)
const availableParents = computed(() => {
  return props.allLayers.filter(l => {
    if (l.id === props.layer.id) return false;
    // Don't allow circular parenting
    let current = l;
    while (current.parentId) {
      if (current.parentId === props.layer.id) return false;
      current = props.allLayers.find(p => p.id === current.parentId) || current;
      if (!current.parentId) break;
    }
    return true;
  });
});

// Calculate duration bar style
const durationBarStyle = computed(() => {
  const inPercent = (props.layer.inPoint / props.frameCount) * 100;
  const outPercent = ((props.layer.outPoint + 1) / props.frameCount) * 100;
  const width = outPercent - inPercent;

  return {
    left: `${inPercent}%`,
    width: `${width}%`
  };
});

// Collect all keyframes from all animated properties
const allKeyframes = computed(() => {
  const keyframes: Array<Keyframe<any> & { propertyName: string }> = [];

  // From opacity
  if (props.layer.opacity.animated) {
    props.layer.opacity.keyframes.forEach(kf => {
      keyframes.push({ ...kf, propertyName: 'Opacity' });
    });
  }

  // From transform properties
  ['position', 'scale', 'rotation'].forEach(propName => {
    const prop = (props.layer.transform as any)[propName];
    if (prop?.animated) {
      prop.keyframes.forEach((kf: Keyframe<any>) => {
        keyframes.push({ ...kf, propertyName: propName.charAt(0).toUpperCase() + propName.slice(1) });
      });
    }
  });

  // From custom properties
  props.layer.properties.forEach(prop => {
    if (prop.animated) {
      prop.keyframes.forEach(kf => {
        keyframes.push({ ...kf, propertyName: prop.name });
      });
    }
  });

  return keyframes;
});

const hasKeyframes = computed(() => allKeyframes.value.length > 0);

// Expression indicators
const expressionIndicators = computed(() => {
  const exprs: Array<{ propertyId: string; startFrame: number }> = [];
  // Check for expressions on properties
  props.layer.properties.forEach(prop => {
    if ((prop as any).expression) {
      exprs.push({
        propertyId: prop.id,
        startFrame: props.layer.inPoint
      });
    }
  });
  return exprs;
});

// Get keyframe position as percentage
function getKeyframePosition(frame: number): number {
  return (frame / props.frameCount) * 100;
}

// Get type icon
function getTypeIcon(type: string): string {
  const icons: Record<string, string> = {
    'spline': '~',
    'text': 'T',
    'solid': '[]',
    'null': 'N',
    'camera': 'C',
    'light': '*',
    'audio': 'A',
    'video': 'V',
    'image': 'I',
    'shape': 'S',
    'adjustment': 'Ad'
  };
  return icons[type] || '?';
}

// Actions
function selectLayer() {
  emit('select', props.layer.id);
}

function toggleVisibility() {
  emit('updateLayer', props.layer.id, { visible: !props.layer.visible });
}

function toggleAudio() {
  emit('updateLayer', props.layer.id, { audioEnabled: !(props.layer as any).audioEnabled });
}

function toggleLock() {
  emit('updateLayer', props.layer.id, { locked: !props.layer.locked });
}

function toggleSolo() {
  emit('toggleSolo', props.layer.id);
}

function toggleSwitch(switchName: string) {
  emit('updateLayer', props.layer.id, { [switchName]: !(props.layer as any)[switchName] });
}

function toggleQuality() {
  const newQuality = (props.layer as any).quality === 'best' ? 'draft' : 'best';
  emit('updateLayer', props.layer.id, { quality: newQuality });
}

function setLabelColor(color: string) {
  emit('updateLayer', props.layer.id, { labelColor: color });
  showLabelPicker.value = false;
}

function setParent(event: Event) {
  const select = event.target as HTMLSelectElement;
  const parentId = select.value || null;
  emit('setParent', props.layer.id, parentId);
}

function selectKeyframe(keyframeId: string) {
  emit('selectKeyframe', keyframeId);
}

function goToKeyframe(frame: number) {
  store.setFrame(frame);
}

// Renaming
function startRename() {
  if (props.layer.locked) return;
  isRenaming.value = true;
  renameValue.value = props.layer.name;
  nextTick(() => {
    renameInput.value?.focus();
    renameInput.value?.select();
  });
}

function finishRename() {
  if (renameValue.value.trim()) {
    emit('updateLayer', props.layer.id, { name: renameValue.value.trim() });
  }
  isRenaming.value = false;
}

function cancelRename() {
  isRenaming.value = false;
}

// Dragging layer duration
let dragType: 'move' | 'trimIn' | 'trimOut' | null = null;
let dragStartX = 0;
let dragStartIn = 0;
let dragStartOut = 0;

function startDrag(event: MouseEvent) {
  if (props.layer.locked) return;
  dragType = 'move';
  dragStartX = event.clientX;
  dragStartIn = props.layer.inPoint;
  dragStartOut = props.layer.outPoint;
  document.addEventListener('mousemove', handleDrag);
  document.addEventListener('mouseup', stopDrag);
}

function startTrimIn(event: MouseEvent) {
  if (props.layer.locked) return;
  dragType = 'trimIn';
  document.addEventListener('mousemove', handleDrag);
  document.addEventListener('mouseup', stopDrag);
}

function startTrimOut(event: MouseEvent) {
  if (props.layer.locked) return;
  dragType = 'trimOut';
  document.addEventListener('mousemove', handleDrag);
  document.addEventListener('mouseup', stopDrag);
}

function handleDrag(event: MouseEvent) {
  if (!trackAreaRef.value || !dragType) return;

  const rect = trackAreaRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const frame = Math.round((x / rect.width) * props.frameCount);

  if (dragType === 'trimIn') {
    const newInPoint = Math.min(frame, props.layer.outPoint - 1);
    emit('updateLayer', props.layer.id, { inPoint: Math.max(0, newInPoint) });
  } else if (dragType === 'trimOut') {
    const newOutPoint = Math.max(frame, props.layer.inPoint + 1);
    emit('updateLayer', props.layer.id, { outPoint: Math.min(props.frameCount - 1, newOutPoint) });
  } else if (dragType === 'move') {
    const dx = event.clientX - dragStartX;
    const frameShift = Math.round((dx / rect.width) * props.frameCount);

    let newIn = dragStartIn + frameShift;
    let newOut = dragStartOut + frameShift;

    // Clamp to valid range
    if (newIn < 0) {
      newOut -= newIn;
      newIn = 0;
    }
    if (newOut > props.frameCount - 1) {
      newIn -= (newOut - (props.frameCount - 1));
      newOut = props.frameCount - 1;
    }

    emit('updateLayer', props.layer.id, { inPoint: newIn, outPoint: newOut });
  }
}

function stopDrag() {
  dragType = null;
  document.removeEventListener('mousemove', handleDrag);
  document.removeEventListener('mouseup', stopDrag);
}
</script>

<style scoped>
.enhanced-layer-track {
  display: flex;
  height: 28px;
  border-bottom: 1px solid #2a2a2a;
  background: #1e1e1e;
  transition: background 0.1s;
}

.enhanced-layer-track:hover {
  background: #232323;
}

.enhanced-layer-track.selected {
  background: rgba(124, 156, 255, 0.1);
}

.enhanced-layer-track.hidden {
  opacity: 0.4;
}

.enhanced-layer-track.dimmed-by-solo {
  opacity: 0.3;
}

.enhanced-layer-track.soloed {
  background: rgba(255, 193, 7, 0.1);
}

.layer-info {
  width: 220px;
  min-width: 220px;
  display: flex;
  align-items: center;
  gap: 2px;
  padding: 0 4px;
  border-right: 1px solid #333;
  background: #222;
}

.label-color {
  width: 14px;
  height: 20px;
  background: var(--label-color);
  border-radius: 2px;
  cursor: pointer;
  position: relative;
}

.label-picker {
  position: absolute;
  top: 100%;
  left: 0;
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  gap: 2px;
  padding: 4px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  z-index: 100;
}

.label-picker button {
  width: 16px;
  height: 16px;
  border: 1px solid transparent;
  border-radius: 2px;
  cursor: pointer;
}

.label-picker button:hover {
  border-color: #fff;
}

.av-switches {
  display: flex;
}

.icon-btn {
  width: 16px;
  height: 20px;
  padding: 0;
  border: none;
  background: transparent;
  color: #555;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 10px;
}

.icon-btn:hover {
  color: #aaa;
}

.icon-btn.active {
  color: #7c9cff;
}

.solo-btn.active {
  color: #ffc107;
}

.lock-btn.active {
  color: #ff6b6b;
}

.layer-name-container {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 4px;
  min-width: 0;
  overflow: hidden;
}

.layer-type-icon {
  font-size: 9px;
  color: #666;
  background: #333;
  padding: 2px 4px;
  border-radius: 2px;
  font-family: monospace;
}

.layer-name {
  flex: 1;
  font-size: 11px;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  color: #e0e0e0;
}

.rename-input {
  width: 100%;
  padding: 2px 4px;
  border: 1px solid #7c9cff;
  background: #1a1a1a;
  color: #e0e0e0;
  font-size: 11px;
  border-radius: 2px;
  outline: none;
}

.parent-picker {
  width: 30px;
}

.parent-select {
  width: 100%;
  padding: 2px;
  background: #1a1a1a;
  border: 1px solid #333;
  color: #888;
  font-size: 9px;
  border-radius: 2px;
  cursor: pointer;
}

.parent-select:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.layer-switches {
  display: flex;
  gap: 1px;
}

.switch-btn {
  width: 18px;
  height: 16px;
  padding: 0;
  border: 1px solid #333;
  background: #1a1a1a;
  color: #555;
  font-size: 8px;
  cursor: pointer;
  border-radius: 2px;
}

.switch-btn:hover {
  background: #2a2a2a;
  color: #aaa;
}

.switch-btn.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}

.track-area {
  flex: 1;
  position: relative;
  min-width: 0;
}

.duration-bar {
  position: absolute;
  top: 4px;
  bottom: 4px;
  background: var(--label-color);
  border-radius: 3px;
  opacity: 0.6;
  cursor: move;
  transition: opacity 0.1s;
}

.duration-bar:hover {
  opacity: 0.8;
}

.duration-bar.has-keyframes {
  background: linear-gradient(
    to right,
    var(--label-color),
    color-mix(in srgb, var(--label-color), white 20%)
  );
}

.trim-handle {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 6px;
  cursor: ew-resize;
  background: transparent;
}

.trim-handle:hover {
  background: rgba(255, 255, 255, 0.2);
}

.trim-in {
  left: 0;
  border-radius: 3px 0 0 3px;
}

.trim-out {
  right: 0;
  border-radius: 0 3px 3px 0;
}

.effect-indicator {
  position: absolute;
  top: 2px;
  right: 4px;
  font-size: 8px;
  color: #fff;
  background: rgba(0, 0, 0, 0.5);
  padding: 1px 3px;
  border-radius: 2px;
}

.keyframe-diamond {
  position: absolute;
  top: 50%;
  width: 8px;
  height: 8px;
  background: #ffc107;
  transform: translate(-50%, -50%) rotate(45deg);
  cursor: pointer;
  z-index: 2;
  transition: transform 0.1s, background 0.1s;
  border: 1px solid transparent;
}

.keyframe-diamond:hover {
  transform: translate(-50%, -50%) rotate(45deg) scale(1.2);
}

.keyframe-diamond.selected {
  background: #ffffff;
  border-color: #7c9cff;
}

.keyframe-diamond.hold {
  background: #888;
}

.keyframe-diamond.linear {
  border-radius: 0;
}

.keyframe-diamond.bezier {
  border-radius: 1px;
}

.expression-indicator {
  position: absolute;
  top: 2px;
  width: 12px;
  height: 12px;
  background: #ff6b6b;
  border-radius: 50%;
  color: #fff;
  font-size: 10px;
  font-weight: bold;
  display: flex;
  align-items: center;
  justify-content: center;
  transform: translateX(-50%);
  z-index: 3;
}

.icon {
  font-family: monospace;
  font-weight: bold;
}
</style>
