<template>
  <div class="layer-track-wrapper">
    <!-- ═══════════════════════════════════════════════════════════════ -->
    <!-- MODE: SIDEBAR (Left Panel - Layer Info Only) -->
    <!-- ═══════════════════════════════════════════════════════════════ -->
    <div
      v-if="layoutMode === 'sidebar'"
      class="enhanced-layer-track sidebar-mode"
      :class="{
        selected: isSelected,
        locked: layer.locked,
        hidden: !layer.visible,
        soloed: isSoloed,
        'dimmed-by-solo': isDimmedBySolo
      }"
      @click="selectLayer"
      :style="{ '--label-color': effectiveLabelColor }"
    >
      <!-- Twirl down for property expansion -->
      <div
        class="twirl-down"
        @click.stop="toggleExpand"
        :class="{ expanded: isExpandedState }"
      >
        <span class="twirl-arrow">{{ isExpandedState ? '▼' : '▶' }}</span>
      </div>

      <!-- Layer info content -->
      <div class="layer-info">
        <!-- Label color indicator -->
        <div class="label-color" @click.stop="showLabelPicker = !showLabelPicker" title="Click to change label color">
          <div v-if="showLabelPicker" class="label-picker" @click.stop>
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
            <span class="icon">{{ layer.visible ? '👁' : '−' }}</span>
          </button>
          <button
            v-if="hasAudio"
            class="icon-btn"
            :class="{ active: layer.audioEnabled }"
            @click.stop="toggleAudio"
            title="Toggle Audio"
          >
            <span class="icon">🔊</span>
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
          <span class="icon">{{ layer.locked ? '🔒' : '🔓' }}</span>
        </button>

        <!-- Layer name with type icon -->
        <div class="layer-name-container">
          <span class="layer-type-icon" :title="`Layer type: ${layer.type}`">
            {{ getTypeIcon(layer.type) }}
          </span>
          <span
            class="layer-name"
            :title="`${layer.name} (double-click to rename)`"
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

        <!-- Parent picker (compact) -->
        <div class="parent-picker" v-if="showSwitches">
          <select
            :value="layer.parentId || ''"
            @change="setParent"
            :disabled="layer.locked"
            class="parent-select"
            title="Parent & Link"
          >
            <option value="">−</option>
            <option
              v-for="parentLayer in availableParents"
              :key="parentLayer.id"
              :value="parentLayer.id"
            >
              {{ parentLayer.name }}
            </option>
          </select>
        </div>
      </div>
    </div>

    <!-- Expanded property names in sidebar mode -->
    <template v-if="layoutMode === 'sidebar' && isExpandedState">
      <div
        v-for="prop in animatableProperties"
        :key="prop.path"
        class="property-row-sidebar"
        :class="{ selected: selectedPropertyIds.includes(getPropertyId(prop.path)) }"
        @click.stop="handlePropertyClick(prop.path, $event)"
      >
        <span class="prop-indent"></span>
        <span class="prop-stopwatch" :class="{ animated: prop.property.animated }">⦿</span>
        <span class="prop-name">{{ prop.name }}</span>
      </div>
    </template>

    <!-- ═══════════════════════════════════════════════════════════════ -->
    <!-- MODE: TRACK (Right Panel - Duration Bar + Keyframes) -->
    <!-- ═══════════════════════════════════════════════════════════════ -->
    <template v-if="layoutMode === 'track'">
      <!-- Main Layer Bar Row -->
      <div class="track-row" :style="{ '--label-color': effectiveLabelColor }">
        <div class="track-area" ref="trackAreaRef">
          <!-- Duration bar -->
          <div
            class="duration-bar"
            :style="durationBarStyle"
            :class="{ 'has-keyframes': hasKeyframes }"
            @mousedown="startDrag"
          >
            <div class="trim-handle trim-in" @mousedown.stop="startTrimIn" />
            <div class="trim-handle trim-out" @mousedown.stop="startTrimOut" />
            <div v-if="layer.effects && layer.effects.length > 0" class="effect-indicator">fx</div>
          </div>

          <!-- Keyframe diamonds (layer level - all properties combined) -->
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
            @click.stop="handleSelectKeyframe(keyframe.id, $event)"
            @dblclick.stop="goToKeyframe(keyframe.frame)"
          />

          <!-- Playhead line -->
          <div class="playhead-line" :style="{ left: `${playheadPercent}%` }"></div>
        </div>
      </div>

      <!-- Expanded Property Tracks -->
      <template v-if="isExpandedState">
        <PropertyTrack
          v-for="prop in animatableProperties"
          :key="prop.path"
          :layerId="layer.id"
          :propertyPath="prop.path"
          :name="prop.name"
          :property="prop.property"
          :frameCount="frameCount"
          :selectedKeyframeIds="selectedKeyframeIds"
          :viewMode="viewMode"
          @selectKeyframe="(id, add) => $emit('selectKeyframe', id, add)"
          @selectProperty="(id, add) => $emit('selectProperty', id, add)"
        />
      </template>
    </template>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, nextTick, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, Keyframe, AnimatableProperty } from '@/types/project';
import PropertyTrack from './PropertyTrack.vue';

// ═══════════════════════════════════════════════════════════════════
// PROPS & EMITS
// ═══════════════════════════════════════════════════════════════════

interface Props {
  layer: Layer;
  frameCount: number;
  currentFrame: number;
  allLayers: Layer[];
  soloedLayerIds: string[];
  showSwitches: boolean;
  viewMode: 'keyframes' | 'graph';
  layoutMode: 'sidebar' | 'track';
  isExpandedExternal?: boolean;
  selectedPropertyIds?: string[];
}

const props = withDefaults(defineProps<Props>(), {
  isExpandedExternal: undefined,
  selectedPropertyIds: () => []
});

const emit = defineEmits<{
  (e: 'select', layerId: string): void;
  (e: 'updateLayer', layerId: string, updates: Partial<Layer>): void;
  (e: 'selectKeyframe', keyframeId: string, addToSelection?: boolean): void;
  (e: 'setParent', childId: string, parentId: string | null): void;
  (e: 'toggleSolo', layerId: string): void;
  (e: 'selectProperty', propertyId: string, addToSelection: boolean): void;
  (e: 'toggleExpand', layerId: string, expanded: boolean): void;
}>();

const store = useCompositorStore();

// ═══════════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════════

const LAYER_TYPE_COLORS: Record<string, string> = {
  spline: '#4ecdc4',
  text: '#ffc107',
  solid: '#7c9cff',
  null: '#ff9800',
  camera: '#e91e63',
  light: '#ffeb3b',
  audio: '#9c27b0',
  video: '#2196f3',
  image: '#8bc34a',
  shape: '#00bcd4',
  adjustment: '#607d8b',
  particles: '#ff5722',
  depthflow: '#673ab7',
};

const labelColors = [
  '#ff6b6b', '#ffc107', '#4ecdc4', '#45b7d1',
  '#96ceb4', '#7c9cff', '#bb8fce', '#ff8a65',
  '#a1887f', '#90a4ae', '#e0e0e0', '#333333'
];

// ═══════════════════════════════════════════════════════════════════
// REFS
// ═══════════════════════════════════════════════════════════════════

const trackAreaRef = ref<HTMLDivElement | null>(null);
const renameInput = ref<HTMLInputElement | null>(null);
const showLabelPicker = ref(false);
const isRenaming = ref(false);
const renameValue = ref('');
const localExpanded = ref(false);

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Expansion State (synced with parent if provided)
// ═══════════════════════════════════════════════════════════════════

const isExpandedState = computed(() => {
  if (props.isExpandedExternal !== undefined) {
    return props.isExpandedExternal;
  }
  return localExpanded.value;
});

function toggleExpand() {
  const newState = !isExpandedState.value;
  localExpanded.value = newState;
  emit('toggleExpand', props.layer.id, newState);
}

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Selection & Solo State
// ═══════════════════════════════════════════════════════════════════

const isSelected = computed(() => store.selectedLayerIds.includes(props.layer.id));
const selectedKeyframeIds = computed(() => store.selectedKeyframeIds);
const isSoloed = computed(() => props.soloedLayerIds.includes(props.layer.id));
const isDimmedBySolo = computed(() => props.soloedLayerIds.length > 0 && !isSoloed.value);

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Layer Properties
// ═══════════════════════════════════════════════════════════════════

const effectiveLabelColor = computed(() => {
  return props.layer.labelColor || LAYER_TYPE_COLORS[props.layer.type] || '#7c9cff';
});

const hasAudio = computed(() => props.layer.type === 'audio' || props.layer.type === 'video');

const availableParents = computed(() => {
  return props.allLayers.filter(l => {
    if (l.id === props.layer.id) return false;
    let current = l;
    while (current.parentId) {
      if (current.parentId === props.layer.id) return false;
      const found = props.allLayers.find(p => p.id === current.parentId);
      if (!found) break;
      current = found;
    }
    return true;
  });
});

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Timeline Positioning
// ═══════════════════════════════════════════════════════════════════

const playheadPercent = computed(() => {
  return (props.currentFrame / props.frameCount) * 100;
});

const durationBarStyle = computed(() => {
  const inPercent = (props.layer.inPoint / props.frameCount) * 100;
  const outPercent = ((props.layer.outPoint + 1) / props.frameCount) * 100;
  return {
    left: `${inPercent}%`,
    width: `${outPercent - inPercent}%`
  };
});

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Keyframes
// ═══════════════════════════════════════════════════════════════════

const allKeyframes = computed(() => {
  const keyframes: Array<Keyframe<any> & { propertyName: string }> = [];

  if (props.layer.opacity?.animated && props.layer.opacity.keyframes) {
    props.layer.opacity.keyframes.forEach(kf => {
      keyframes.push({ ...kf, propertyName: 'Opacity' });
    });
  }

  ['position', 'scale', 'rotation'].forEach(propName => {
    const prop = (props.layer.transform as any)?.[propName];
    if (prop?.animated && prop.keyframes) {
      prop.keyframes.forEach((kf: Keyframe<any>) => {
        keyframes.push({ ...kf, propertyName: propName.charAt(0).toUpperCase() + propName.slice(1) });
      });
    }
  });

  if (props.layer.properties) {
    props.layer.properties.forEach(prop => {
      if (prop.animated && prop.keyframes) {
        prop.keyframes.forEach(kf => {
          keyframes.push({ ...kf, propertyName: prop.name });
        });
      }
    });
  }

  return keyframes;
});

const hasKeyframes = computed(() => allKeyframes.value.length > 0);

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Animatable Properties for Expansion
// ═══════════════════════════════════════════════════════════════════

const animatableProperties = computed(() => {
  const result: { path: string; name: string; property: AnimatableProperty<any> }[] = [];

  if (props.layer.transform) {
    if (props.layer.transform.position) {
      result.push({ path: 'transform.position', name: 'Position', property: props.layer.transform.position });
    }
    if (props.layer.transform.scale) {
      result.push({ path: 'transform.scale', name: 'Scale', property: props.layer.transform.scale });
    }
    if (props.layer.transform.rotation) {
      result.push({ path: 'transform.rotation', name: 'Rotation', property: props.layer.transform.rotation });
    }
    if (props.layer.transform.anchorPoint) {
      result.push({ path: 'transform.anchorPoint', name: 'Anchor Point', property: props.layer.transform.anchorPoint });
    }
  }

  if (props.layer.opacity) {
    result.push({ path: 'opacity', name: 'Opacity', property: props.layer.opacity });
  }

  return result;
});

// ═══════════════════════════════════════════════════════════════════
// HELPERS
// ═══════════════════════════════════════════════════════════════════

function getKeyframePosition(frame: number): number {
  return (frame / props.frameCount) * 100;
}

function getTypeIcon(type: string): string {
  const icons: Record<string, string> = {
    'spline': '⌇',
    'text': 'T',
    'solid': '□',
    'null': '◇',
    'camera': '📷',
    'light': '☀',
    'audio': '♪',
    'video': '▶',
    'image': '🖼',
    'shape': '⬡',
    'adjustment': '◐',
    'particles': '✦',
    'depthflow': '◈'
  };
  return icons[type] || '?';
}

function getPropertyId(path: string): string {
  return `${props.layer.id}-${path.replace(/\./g, '-')}`;
}

// ═══════════════════════════════════════════════════════════════════
// ACTIONS
// ═══════════════════════════════════════════════════════════════════

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

function setLabelColor(color: string) {
  emit('updateLayer', props.layer.id, { labelColor: color });
  showLabelPicker.value = false;
}

function setParent(event: Event) {
  const select = event.target as HTMLSelectElement;
  emit('setParent', props.layer.id, select.value || null);
}

function handleSelectKeyframe(keyframeId: string, event: MouseEvent) {
  emit('selectKeyframe', keyframeId, event.shiftKey);
}

function goToKeyframe(frame: number) {
  store.setFrame(frame);
}

function handlePropertyClick(path: string, event: MouseEvent) {
  const propId = getPropertyId(path);
  emit('selectProperty', propId, event.shiftKey);
}

// ═══════════════════════════════════════════════════════════════════
// RENAMING
// ═══════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════
// DRAGGING (Track mode only)
// ═══════════════════════════════════════════════════════════════════

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

// Sync with external expansion state
watch(() => props.isExpandedExternal, (val) => {
  if (val !== undefined) {
    localExpanded.value = val;
  }
});
</script>

<style scoped>
.layer-track-wrapper {
  display: flex;
  flex-direction: column;
  width: 100%;
}

/* ═══════════════════════════════════════════════════════════════════ */
/* SIDEBAR MODE */
/* ═══════════════════════════════════════════════════════════════════ */

.sidebar-mode {
  display: flex;
  align-items: center;
  min-height: 28px;
  height: 28px;
  border-bottom: 1px solid #2a2a2a;
  background: #1e1e1e;
  transition: background 0.15s ease;
  padding-right: 4px;
}

.sidebar-mode:hover {
  background: #232323;
}

.sidebar-mode.selected {
  background: rgba(124, 156, 255, 0.15);
}

.sidebar-mode.hidden {
  opacity: 0.4;
}

.sidebar-mode.dimmed-by-solo {
  opacity: 0.3;
}

.sidebar-mode.soloed {
  background: rgba(255, 193, 7, 0.1);
}

.layer-info {
  display: flex;
  align-items: center;
  gap: 2px;
  flex: 1;
  min-width: 0;
  overflow: hidden;
}

/* ═══════════════════════════════════════════════════════════════════ */
/* TRACK MODE */
/* ═══════════════════════════════════════════════════════════════════ */

.track-row {
  height: 28px;
  border-bottom: 1px solid #2a2a2a;
  position: relative;
  width: 100%;
  background: #1e1e1e;
}

.track-area {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
}

/* ═══════════════════════════════════════════════════════════════════ */
/* SHARED ELEMENTS */
/* ═══════════════════════════════════════════════════════════════════ */

.twirl-down {
  width: 16px;
  height: 28px;
  display: flex;
  align-items: center;
  justify-content: center;
  cursor: pointer;
  color: #666;
  flex-shrink: 0;
}

.twirl-down:hover {
  color: #aaa;
}

.twirl-arrow {
  font-size: 8px;
  transition: color 0.15s;
}

.twirl-down.expanded .twirl-arrow {
  color: #7c9cff;
}

.label-color {
  width: 4px;
  height: 20px;
  background: var(--label-color);
  border-radius: 2px;
  cursor: pointer;
  position: relative;
  flex-shrink: 0;
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
  width: 14px;
  height: 14px;
  border: 1px solid transparent;
  border-radius: 2px;
  cursor: pointer;
  padding: 0;
}

.label-picker button:hover {
  border-color: #fff;
}

.av-switches {
  display: flex;
  flex-shrink: 0;
}

.icon-btn {
  width: 20px;
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
  border-radius: 3px;
  transition: all 0.1s ease;
}

.icon-btn:hover {
  color: #ccc;
  background: #333;
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
  font-size: 10px;
  flex-shrink: 0;
  opacity: 0.7;
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
  width: 24px;
  flex-shrink: 0;
}

.parent-select {
  width: 100%;
  padding: 1px;
  background: #1a1a1a;
  border: 1px solid #333;
  color: #666;
  font-size: 8px;
  border-radius: 2px;
  cursor: pointer;
}

/* Property rows in sidebar */
.property-row-sidebar {
  display: flex;
  align-items: center;
  height: 22px;
  padding-left: 16px;
  border-bottom: 1px solid #252525;
  cursor: pointer;
  color: #888;
  font-size: 11px;
  background: #1a1a1a;
}

.property-row-sidebar:hover {
  background: #252525;
  color: #ccc;
}

.property-row-sidebar.selected {
  background: rgba(124, 156, 255, 0.15);
  color: #fff;
}

.prop-indent {
  width: 8px;
}

.prop-stopwatch {
  width: 14px;
  font-size: 10px;
  color: #555;
}

.prop-stopwatch.animated {
  color: #7c9cff;
}

.prop-name {
  flex: 1;
}

/* Duration bar */
.duration-bar {
  position: absolute;
  top: 4px;
  bottom: 4px;
  background: var(--label-color, #7c9cff);
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
    var(--label-color, #7c9cff),
    color-mix(in srgb, var(--label-color, #7c9cff), white 20%)
  );
}

.trim-handle {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 8px;
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

/* Keyframes */
.keyframe-diamond {
  position: absolute;
  top: 50%;
  width: 10px;
  height: 10px;
  background: #f5c542;
  transform: translate(-50%, -50%) rotate(45deg);
  cursor: pointer;
  z-index: 2;
  transition: transform 0.15s ease, background 0.15s ease;
  border: 1px solid rgba(0, 0, 0, 0.3);
}

.keyframe-diamond:hover {
  transform: translate(-50%, -50%) rotate(45deg) scale(1.3);
}

.keyframe-diamond.selected {
  background: #ffffff;
  border-color: #7c9cff;
  box-shadow: 0 0 0 2px rgba(124, 156, 255, 0.4);
}

.keyframe-diamond.hold {
  background: #888;
}

/* Playhead */
.playhead-line {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  background: #ff4444;
  pointer-events: none;
  z-index: 10;
}

.icon {
  font-family: system-ui, -apple-system, sans-serif;
}
</style>
