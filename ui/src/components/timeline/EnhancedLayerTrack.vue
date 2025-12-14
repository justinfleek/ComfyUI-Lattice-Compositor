<template>
  <div class="layer-track-wrapper">
    <!-- MODE: SIDEBAR (Left Panel - Layer Info Only) -->
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
        :class="{ expanded: isExpanded }"
      >
        <span class="twirl-arrow">{{ isExpanded ? '▼' : '▶' }}</span>
      </div>

      <!-- Layer info content -->
      <div class="layer-info">
        <!-- Label color indicator -->
        <div class="label-color" @click.stop="showLabelPicker = !showLabelPicker">
          <div v-if="showLabelPicker" class="label-picker" @click.stop>
            <button
              v-for="color in labelColors"
              :key="color"
              :style="{ background: color }"
              @click="setLabelColor(color)"
            />
          </div>
        </div>

        <!-- AV switches -->
        <div class="av-switches">
          <button class="icon-btn" :class="{ active: layer.visible }" @click.stop="toggleVisibility">
            <span class="icon">{{ layer.visible ? '👁' : '−' }}</span>
          </button>
          <button v-if="hasAudio" class="icon-btn" :class="{ active: layer.audioEnabled }" @click.stop="toggleAudio">
            <span class="icon">🔊</span>
          </button>
        </div>

        <button class="icon-btn solo-btn" :class="{ active: isSoloed }" @click.stop="toggleSolo"><span class="icon">S</span></button>
        <button class="icon-btn lock-btn" :class="{ active: layer.locked }" @click.stop="toggleLock"><span class="icon">{{ layer.locked ? '🔒' : '🔓' }}</span></button>

        <!-- Layer name -->
        <div class="layer-name-container">
          <span class="layer-type-icon">{{ getTypeIcon(layer.type) }}</span>
          <span class="layer-name" @dblclick.stop="startRename">
            <input v-if="isRenaming" v-model="renameValue" @blur="finishRename" @keyup.enter="finishRename" class="rename-input" ref="renameInput" />
            <template v-else>{{ layer.name }}</template>
          </span>
        </div>

        <!-- Parent picker -->
        <div class="parent-picker" v-if="showSwitches">
          <select :value="layer.parentId || ''" @change="setParent" :disabled="layer.locked" class="parent-select">
            <option value="">−</option>
            <option v-for="p in availableParents" :key="p.id" :value="p.id">{{ p.name }}</option>
          </select>
        </div>
      </div>

      <!-- Expanded properties in sidebar (Name/Value) -->
      <template v-if="isExpanded">
        <PropertyTrack
          v-for="prop in animatableProperties"
          :key="prop.path"
          :layerId="layer.id"
          :propertyPath="prop.path"
          :name="prop.name"
          :property="prop.property"
          :frameCount="frameCount"
          :selectedKeyframeIds="selectedKeyframeIds"
          :selectedPropertyIds="selectedPropertyIds"
          :viewMode="viewMode"
          layoutMode="sidebar"
          @selectKeyframe="(id, add) => $emit('selectKeyframe', id, add)"
          @selectProperty="(id, add) => $emit('selectProperty', id, add)"
        />
      </template>
    </div>

    <!-- MODE: TRACK (Right Panel - Duration Bar + Keyframes) -->
    <div v-else-if="layoutMode === 'track'" class="track-area-container" :style="{ '--label-color': effectiveLabelColor }">
      <div class="track-row">
        <div class="track-area" ref="trackAreaRef">
          <div class="duration-bar" :style="durationBarStyle" :class="{ 'has-keyframes': hasKeyframes }" @mousedown="startDrag">
            <div class="trim-handle trim-in" @mousedown.stop="startTrimIn" />
            <div class="trim-handle trim-out" @mousedown.stop="startTrimOut" />
            <div v-if="layer.effects && layer.effects.length > 0" class="effect-indicator">fx</div>
          </div>

          <!-- Layer Level Keyframes -->
          <div v-for="kf in allKeyframes" :key="kf.id" class="keyframe-diamond"
            :style="{ left: `${getKeyframePosition(kf.frame)}%` }"
            :class="{ selected: selectedKeyframeIds.includes(kf.id) }"
            @click.stop="selectKeyframe(kf.id)" />
        </div>
      </div>

      <!-- Expanded Property Tracks (Keyframes only) -->
      <template v-if="isExpanded">
        <PropertyTrack
          v-for="prop in animatableProperties"
          :key="prop.path"
          :layerId="layer.id"
          :propertyPath="prop.path"
          :name="prop.name"
          :property="prop.property"
          :frameCount="frameCount"
          :selectedKeyframeIds="selectedKeyframeIds"
          :selectedPropertyIds="selectedPropertyIds"
          :viewMode="viewMode"
          layoutMode="track"
          @selectKeyframe="(id, add) => $emit('selectKeyframe', id, add)"
          @selectProperty="(id, add) => $emit('selectProperty', id, add)"
        />
      </template>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, nextTick, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, Keyframe, AnimatableProperty } from '@/types/project';
import PropertyTrack from './PropertyTrack.vue';

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
  isExpandedExternal: false,
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
const trackAreaRef = ref<HTMLDivElement | null>(null);
const renameInput = ref<HTMLInputElement | null>(null);
const showLabelPicker = ref(false);
const isRenaming = ref(false);
const renameValue = ref('');
const localExpanded = ref(false);

// Constants
const LAYER_TYPE_COLORS: Record<string, string> = {
  spline: '#4ecdc4', text: '#ffc107', solid: '#7c9cff', null: '#ff9800',
  camera: '#e91e63', light: '#ffeb3b', audio: '#9c27b0', video: '#2196f3',
  image: '#8bc34a', shape: '#00bcd4', adjustment: '#607d8b', particles: '#ff5722',
  depthflow: '#673ab7',
};
const labelColors = ['#ff6b6b', '#ffc107', '#4ecdc4', '#45b7d1', '#96ceb4', '#7c9cff', '#bb8fce', '#ff8a65', '#a1887f', '#90a4ae', '#e0e0e0', '#333333'];

// Expansion
const isExpanded = computed(() => props.isExpandedExternal !== undefined ? props.isExpandedExternal : localExpanded.value);
function toggleExpand() {
  console.log('[TWIRL] toggleExpand called for layer:', props.layer.name, 'current isExpanded:', isExpanded.value);
  const newState = !isExpanded.value;
  localExpanded.value = newState;
  emit('toggleExpand', props.layer.id, newState);
}

// State
const isSelected = computed(() => store.selectedLayerIds.includes(props.layer.id));
const selectedKeyframeIds = computed(() => store.selectedKeyframeIds);
const isSoloed = computed(() => props.soloedLayerIds.includes(props.layer.id));
const isDimmedBySolo = computed(() => props.soloedLayerIds.length > 0 && !isSoloed.value);
const effectiveLabelColor = computed(() => props.layer.labelColor || LAYER_TYPE_COLORS[props.layer.type] || '#7c9cff');
const hasAudio = computed(() => props.layer.type === 'audio' || props.layer.type === 'video');
const availableParents = computed(() => props.allLayers.filter(l => l.id !== props.layer.id));

// Keyframes & Timeline
const playheadPercent = computed(() => (props.currentFrame / props.frameCount) * 100);
const durationBarStyle = computed(() => {
  const inP = (props.layer.inPoint / props.frameCount) * 100;
  const outP = ((props.layer.outPoint + 1) / props.frameCount) * 100;
  return { left: `${inP}%`, width: `${outP - inP}%` };
});

const allKeyframes = computed(() => {
  const kfs: Array<Keyframe<any> & { propertyName: string }> = [];
  ['position', 'scale', 'rotation'].forEach(p => {
    const prop = (props.layer.transform as any)?.[p];
    if (prop?.animated && prop.keyframes) prop.keyframes.forEach((k: any) => kfs.push({...k, propertyName: p}));
  });
  if (props.layer.opacity?.animated && props.layer.opacity.keyframes) {
    props.layer.opacity.keyframes.forEach(k => kfs.push({...k, propertyName: 'Opacity'}));
  }
  return kfs;
});
const hasKeyframes = computed(() => allKeyframes.value.length > 0);

const animatableProperties = computed(() => {
  const result: { path: string; name: string; property: AnimatableProperty<any> }[] = [];
  if (props.layer.transform?.position) result.push({ path: 'transform.position', name: 'Position', property: props.layer.transform.position });
  if (props.layer.transform?.scale) result.push({ path: 'transform.scale', name: 'Scale', property: props.layer.transform.scale });
  if (props.layer.transform?.rotation) result.push({ path: 'transform.rotation', name: 'Rotation', property: props.layer.transform.rotation });
  if (props.layer.opacity) result.push({ path: 'opacity', name: 'Opacity', property: props.layer.opacity });
  if (props.layer.transform?.anchorPoint) result.push({ path: 'transform.anchorPoint', name: 'Anchor Point', property: props.layer.transform.anchorPoint });
  return result;
});

// Helpers
function getKeyframePosition(f: number) { return (f / props.frameCount) * 100; }
function getTypeIcon(t: string) { return t.charAt(0).toUpperCase(); }
function getPropertyId(path: string) { return `${props.layer.id}-${path.replace('.', '-')}`; }

// Actions
function selectLayer() { emit('select', props.layer.id); }
function toggleVisibility() { emit('updateLayer', props.layer.id, { visible: !props.layer.visible }); }
function toggleAudio() { emit('updateLayer', props.layer.id, { audioEnabled: !(props.layer as any).audioEnabled }); }
function toggleLock() { emit('updateLayer', props.layer.id, { locked: !props.layer.locked }); }
function toggleSolo() { emit('toggleSolo', props.layer.id); }
function setLabelColor(c: string) { emit('updateLayer', props.layer.id, { labelColor: c }); showLabelPicker.value = false; }
function setParent(e: Event) { emit('setParent', props.layer.id, (e.target as HTMLSelectElement).value || null); }
function selectKeyframe(id: string) { emit('selectKeyframe', id); }

// Rename
function startRename() { if(!props.layer.locked) { isRenaming.value = true; renameValue.value = props.layer.name; nextTick(() => renameInput.value?.focus()); } }
function finishRename() { if(renameValue.value.trim()) emit('updateLayer', props.layer.id, { name: renameValue.value.trim() }); isRenaming.value = false; }

// Dragging
let dragType: string | null = null;
let dragStartX = 0; let dragStartIn = 0; let dragStartOut = 0;
function startDrag(e: MouseEvent) { if(!props.layer.locked) { dragType = 'move'; dragStartX = e.clientX; dragStartIn = props.layer.inPoint; dragStartOut = props.layer.outPoint; window.addEventListener('mousemove', handleDrag); window.addEventListener('mouseup', stopDrag); } }
function startTrimIn(e: MouseEvent) { if(!props.layer.locked) { dragType = 'trimIn'; window.addEventListener('mousemove', handleDrag); window.addEventListener('mouseup', stopDrag); } }
function startTrimOut(e: MouseEvent) { if(!props.layer.locked) { dragType = 'trimOut'; window.addEventListener('mousemove', handleDrag); window.addEventListener('mouseup', stopDrag); } }
function handleDrag(e: MouseEvent) {
  if (!trackAreaRef.value) return;
  const rect = trackAreaRef.value.getBoundingClientRect();
  const x = e.clientX - rect.left;
  const f = Math.round((x / rect.width) * props.frameCount);

  if (dragType === 'trimIn') emit('updateLayer', props.layer.id, { inPoint: Math.max(0, Math.min(f, props.layer.outPoint - 1)) });
  else if (dragType === 'trimOut') emit('updateLayer', props.layer.id, { outPoint: Math.min(props.frameCount - 1, Math.max(f, props.layer.inPoint + 1)) });
  else if (dragType === 'move') {
    const dx = e.clientX - dragStartX;
    const shift = Math.round((dx / rect.width) * props.frameCount);
    const w = dragStartOut - dragStartIn;
    let nIn = dragStartIn + shift;
    if (nIn < 0) nIn = 0;
    if (nIn + w >= props.frameCount) nIn = props.frameCount - 1 - w;
    emit('updateLayer', props.layer.id, { inPoint: nIn, outPoint: nIn + w });
  }
}
function stopDrag() { window.removeEventListener('mousemove', handleDrag); window.removeEventListener('mouseup', stopDrag); }

watch(() => props.isExpandedExternal, (v) => { if(v !== undefined) localExpanded.value = v; });
</script>

<style scoped>
.layer-track-wrapper { display: flex; flex-direction: column; width: 100%; }

/* Sidebar Mode */
.sidebar-mode { display: flex; flex-direction: column; }
.sidebar-mode:hover { background: #232323; }
.sidebar-mode.selected { background: rgba(124, 156, 255, 0.15); }
.sidebar-mode.hidden { opacity: 0.4; }
.sidebar-mode.dimmed-by-solo { opacity: 0.3; }
.sidebar-mode .layer-info { display: flex; align-items: center; gap: 2px; padding: 0 4px; height: 36px; min-height: 36px; border-bottom: 1px solid #2a2a2a; background: #1e1e1e; }

/* Track Mode */
.track-area-container { width: 100%; }
.track-row { height: 36px; min-height: 36px; border-bottom: 1px solid #2a2a2a; position: relative; width: 100%; background: #1e1e1e; }
.track-area { position: absolute; inset: 0; }

/* Shared */
.twirl-down { width: 16px; height: 28px; display: flex; align-items: center; justify-content: center; cursor: pointer; color: #666; }
.twirl-arrow { font-size: 8px; }
.twirl-down.expanded .twirl-arrow { color: #7c9cff; }
.label-color { width: 4px; height: 20px; border-radius: 2px; cursor: pointer; position: relative; background: var(--label-color); }
.label-picker { position: absolute; top: 100%; left: 0; display: grid; grid-template-columns: repeat(4, 1fr); gap: 2px; padding: 4px; background: #2a2a2a; border: 1px solid #444; z-index: 100; }
.label-picker button { width: 14px; height: 14px; border: 1px solid transparent; cursor: pointer; padding: 0; }
.av-switches { display: flex; }
.icon-btn { width: 28px; height: 28px; border: none; background: transparent; color: #555; cursor: pointer; font-size: 18px; display: flex; align-items: center; justify-content: center; }
.icon-btn.active { color: #7c9cff; }
.solo-btn.active { color: #ffc107; }
.lock-btn.active { color: #ff6b6b; }
.layer-name-container { flex: 1; display: flex; align-items: center; gap: 4px; overflow: hidden; }
.layer-type-icon { font-size: 16px; opacity: 0.7; }
.layer-name { font-size: 18px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; color: #e0e0e0; }
.rename-input { width: 100%; background: #1a1a1a; border: 1px solid #7c9cff; color: #fff; font-size: 11px; }
.parent-picker { width: 24px; }
.parent-select { width: 100%; background: #1a1a1a; border: 1px solid #333; color: #666; font-size: 8px; }

/* Timeline Elements */
.duration-bar { position: absolute; top: 4px; bottom: 4px; background: var(--label-color); border-radius: 3px; opacity: 0.6; cursor: move; }
.duration-bar.has-keyframes { background: linear-gradient(to right, var(--label-color), color-mix(in srgb, var(--label-color), white 20%)); }
.trim-handle { position: absolute; top: 0; bottom: 0; width: 8px; cursor: ew-resize; }
.trim-handle:hover { background: rgba(255,255,255,0.2); }
.trim-in { left: 0; border-radius: 3px 0 0 3px; }
.trim-out { right: 0; border-radius: 0 3px 3px 0; }
.effect-indicator { position: absolute; top: 2px; right: 4px; font-size: 8px; color: #fff; background: rgba(0,0,0,0.5); padding: 1px 3px; border-radius: 2px; }
.keyframe-diamond { position: absolute; top: 50%; width: 10px; height: 10px; background: #f5c542; transform: translate(-50%, -50%) rotate(45deg); cursor: pointer; z-index: 2; border: 1px solid rgba(0,0,0,0.3); }
.keyframe-diamond:hover { transform: translate(-50%, -50%) rotate(45deg) scale(1.2); }
.keyframe-diamond.selected { background: #fff; border-color: #7c9cff; box-shadow: 0 0 0 2px rgba(124,156,255,0.4); }
</style>
