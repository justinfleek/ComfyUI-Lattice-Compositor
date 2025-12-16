<template>
  <div class="prop-wrapper">
    <div v-if="layoutMode === 'sidebar'" class="prop-sidebar" :class="{ selected: isSelected }" :style="gridStyle" @click="selectProp">
      <div class="indent-spacer"></div>

      <div class="icon-box" @click.stop="addKeyframeAtCurrent">
        <span class="kf-btn" :class="{ active: hasKeyframeAtCurrent }">◇</span>
      </div>

      <div class="icon-box" @click.stop="toggleAnim">
        <span class="stopwatch" :class="{ active: property.animated }">⏱</span>
      </div>

      <div class="prop-content">
        <span class="prop-name">{{ name }}</span>

        <div class="prop-inputs">
          <!-- Z Position only (special case for 3D layers) -->
          <template v-if="name === 'Z Position'">
            <div class="vec-item">
              <span class="label z-label">Z</span>
              <ScrubableNumber
                :modelValue="property.value?.z ?? 0"
                @update:modelValue="v => updateValByIndex('z', v)"
              />
            </div>
          </template>

          <!-- Color input -->
          <template v-else-if="property.type === 'color'">
            <div class="color-input-wrapper">
              <input type="color" :value="property.value" @input="e => updateValDirect((e.target as HTMLInputElement).value)" />
              <span class="color-hex">{{ property.value }}</span>
            </div>
          </template>

          <!-- Vector (X/Y or X/Y/Z) -->
          <template v-else-if="typeof property.value === 'object'">
            <div class="vec-item">
              <span class="label x-label">X</span>
              <ScrubableNumber :modelValue="property.value.x" @update:modelValue="v => updateValByIndex('x', v)" />
            </div>
            <div class="vec-item">
              <span class="label y-label">Y</span>
              <ScrubableNumber :modelValue="property.value.y" @update:modelValue="v => updateValByIndex('y', v)" />
            </div>
          </template>

          <!-- Single number -->
          <template v-else-if="typeof property.value === 'number'">
            <ScrubableNumber :modelValue="property.value" @update:modelValue="updateValDirect" :precision="1" />
          </template>
        </div>
      </div>
    </div>

    <div v-else class="prop-track" @mousedown="handleTrackMouseDown" ref="trackRef">
       <!-- Selection box for marquee select -->
       <div v-if="isBoxSelecting" class="selection-box" :style="selectionBoxStyle"></div>

       <div v-for="kf in property.keyframes" :key="kf.id"
            class="keyframe"
            :class="{ selected: selectedKeyframeIds.has(kf.id), [kf.interpolation || 'linear']: true }"
            :style="{ left: `${kf.frame * pixelsPerFrame}px` }"
            @mousedown.stop="startKeyframeDrag($event, kf)"
            @dblclick.stop="deleteKeyframe(kf.id)"
            @contextmenu.prevent.stop="showContextMenu($event, kf)"
       >
       </div>

       <!-- Context Menu -->
       <div v-if="contextMenu.visible" class="keyframe-context-menu" :style="contextMenuStyle">
         <div class="menu-header">Interpolation</div>
         <div class="menu-item" :class="{ active: contextMenu.keyframe?.interpolation === 'linear' }" @click="setInterpolation('linear')">
           <span class="icon">📈</span> Linear
         </div>
         <div class="menu-item" :class="{ active: contextMenu.keyframe?.interpolation === 'bezier' }" @click="setInterpolation('bezier')">
           <span class="icon">〰️</span> Bezier
         </div>
         <div class="menu-item" :class="{ active: contextMenu.keyframe?.interpolation === 'hold' }" @click="setInterpolation('hold')">
           <span class="icon">⏸️</span> Hold
         </div>
         <div class="menu-divider"></div>
         <div class="menu-item" @click="goToKeyframe">
           <span class="icon">➡️</span> Go to Frame
         </div>
         <div class="menu-item delete" @click="deleteSelectedKeyframes">
           <span class="icon">🗑️</span> Delete
         </div>
       </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import ScrubableNumber from '@/components/controls/ScrubableNumber.vue';
import type { Keyframe } from '@/types/project';
import { findNearestSnap } from '@/services/timelineSnap';

const props = defineProps(['name', 'property', 'layerId', 'propertyPath', 'layoutMode', 'pixelsPerFrame', 'gridStyle']);
const emit = defineEmits(['selectKeyframe', 'deleteKeyframe', 'moveKeyframe']);
const store = useCompositorStore();

const selectedKeyframeIds = ref<Set<string>>(new Set());
const trackRef = ref<HTMLElement | null>(null);

// Box selection state
const isBoxSelecting = ref(false);
const boxStartX = ref(0);
const boxCurrentX = ref(0);

// Context menu state
const contextMenu = ref<{
  visible: boolean;
  x: number;
  y: number;
  keyframe: Keyframe<any> | null;
}>({
  visible: false,
  x: 0,
  y: 0,
  keyframe: null
});

const contextMenuStyle = computed(() => ({
  left: `${contextMenu.value.x}px`,
  top: `${contextMenu.value.y}px`
}));

const selectionBoxStyle = computed(() => {
  const left = Math.min(boxStartX.value, boxCurrentX.value);
  const width = Math.abs(boxCurrentX.value - boxStartX.value);
  return {
    left: `${left}px`,
    width: `${width}px`
  };
});

const hasKeyframeAtCurrent = computed(() => props.property.keyframes?.some((k:any) => k.frame === store.currentFrame));
const isSelected = computed(() => store.selectedPropertyPath === props.propertyPath);

function toggleAnim() { store.setPropertyAnimated(props.layerId, props.propertyPath, !props.property.animated); }
function addKeyframeAtCurrent() { store.addKeyframe(props.layerId, props.propertyPath, props.property.value); }
function updateValDirect(v: any) { store.setPropertyValue(props.layerId, props.propertyPath, v); }
function updateValByIndex(axis: string, v: number) {
  const newVal = { ...props.property.value, [axis]: v };
  store.setPropertyValue(props.layerId, props.propertyPath, newVal);
}
function selectProp() { store.selectProperty(props.propertyPath); }

// Handle mouse down on track - start box selection or navigate
function handleTrackMouseDown(e: MouseEvent) {
  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect();
  const x = e.clientX - rect.left;

  // Start box selection
  isBoxSelecting.value = true;
  boxStartX.value = x;
  boxCurrentX.value = x;

  // Clear selection unless Shift is held
  if (!e.shiftKey) {
    selectedKeyframeIds.value.clear();
  }

  const onMove = (ev: MouseEvent) => {
    const currentX = ev.clientX - rect.left;
    boxCurrentX.value = Math.max(0, currentX);

    // Select keyframes within the box
    const minFrame = Math.min(boxStartX.value, boxCurrentX.value) / props.pixelsPerFrame;
    const maxFrame = Math.max(boxStartX.value, boxCurrentX.value) / props.pixelsPerFrame;

    if (!ev.shiftKey) {
      selectedKeyframeIds.value.clear();
    }

    for (const kf of props.property.keyframes || []) {
      if (kf.frame >= minFrame && kf.frame <= maxFrame) {
        selectedKeyframeIds.value.add(kf.id);
      }
    }
  };

  const onUp = (ev: MouseEvent) => {
    isBoxSelecting.value = false;

    // If it was just a click (no drag), navigate to that frame
    const dragDistance = Math.abs(boxCurrentX.value - boxStartX.value);
    if (dragDistance < 5) {
      const frame = Math.round(boxStartX.value / props.pixelsPerFrame);
      store.setFrame(Math.max(0, Math.min(store.frameCount - 1, frame)));
    }

    window.removeEventListener('mousemove', onMove);
    window.removeEventListener('mouseup', onUp);
  };

  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', onUp);
}

// Keyframe selection and dragging
function startKeyframeDrag(e: MouseEvent, kf: Keyframe<any>) {
  // Toggle selection with Shift, otherwise single select
  if (e.shiftKey) {
    if (selectedKeyframeIds.value.has(kf.id)) {
      selectedKeyframeIds.value.delete(kf.id);
    } else {
      selectedKeyframeIds.value.add(kf.id);
    }
  } else {
    selectedKeyframeIds.value.clear();
    selectedKeyframeIds.value.add(kf.id);
  }

  // Set up drag
  const startX = e.clientX;
  const startFrame = kf.frame;

  const onMove = (ev: MouseEvent) => {
    const dx = ev.clientX - startX;
    const frameDelta = Math.round(dx / props.pixelsPerFrame);
    let newFrame = Math.max(0, Math.min(store.frameCount - 1, startFrame + frameDelta));

    // Apply snapping if enabled (hold Alt/Option to disable temporarily)
    if (!ev.altKey && store.snapConfig.enabled) {
      const snap = findNearestSnap(newFrame, store.snapConfig, props.pixelsPerFrame, {
        layers: store.layers,
        selectedLayerId: props.layerId,
        currentFrame: store.currentFrame,
        audioAnalysis: store.audioAnalysis,
        peakData: store.peakData
      });
      if (snap) {
        newFrame = snap.frame;
      }
    }

    if (newFrame !== kf.frame) {
      store.moveKeyframe(props.layerId, props.propertyPath, kf.id, newFrame);
    }
  };

  const onUp = () => {
    window.removeEventListener('mousemove', onMove);
    window.removeEventListener('mouseup', onUp);
  };

  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', onUp);
}

// Delete keyframe
function deleteKeyframe(kfId: string) {
  store.removeKeyframe(props.layerId, props.propertyPath, kfId);
  selectedKeyframeIds.value.delete(kfId);
}

// Context menu functions
function showContextMenu(e: MouseEvent, kf: Keyframe<any>) {
  // Select the keyframe if not already selected
  if (!selectedKeyframeIds.value.has(kf.id)) {
    selectedKeyframeIds.value.clear();
    selectedKeyframeIds.value.add(kf.id);
  }

  // Position relative to track
  const trackRect = trackRef.value?.getBoundingClientRect();
  if (trackRect) {
    contextMenu.value = {
      visible: true,
      x: e.clientX - trackRect.left,
      y: e.clientY - trackRect.top,
      keyframe: kf
    };
  }
}

function hideContextMenu() {
  contextMenu.value.visible = false;
  contextMenu.value.keyframe = null;
}

function setInterpolation(type: 'linear' | 'bezier' | 'hold') {
  // Apply to all selected keyframes
  for (const kfId of selectedKeyframeIds.value) {
    store.setKeyframeInterpolation(props.layerId, props.propertyPath, kfId, type);
  }
  hideContextMenu();
}

function goToKeyframe() {
  if (contextMenu.value.keyframe) {
    store.setFrame(contextMenu.value.keyframe.frame);
  }
  hideContextMenu();
}

function deleteSelectedKeyframes() {
  for (const kfId of selectedKeyframeIds.value) {
    store.removeKeyframe(props.layerId, props.propertyPath, kfId);
  }
  selectedKeyframeIds.value.clear();
  hideContextMenu();
}

// Close context menu on click outside
function handleGlobalClick(e: MouseEvent) {
  if (contextMenu.value.visible) {
    hideContextMenu();
  }
}

onMounted(() => {
  document.addEventListener('click', handleGlobalClick);
});

onUnmounted(() => {
  document.removeEventListener('click', handleGlobalClick);
});
</script>

<style scoped>
.prop-wrapper { width: 100%; display: flex; flex-direction: column; }
.prop-sidebar {
  display: grid;
  /* Must match parent grid. Columns: 24 24 30 24 24 24 1fr 70 70 */
  grid-template-columns: 24px 24px 30px 24px 24px 24px 1fr 70px 70px;
  align-items: center;
  height: 32px;
  border-bottom: 1px solid #2a2a2a;
  background: #1a1a1a;
  font-size: 13px;
  color: #ccc;
}
.indent-spacer { grid-column: span 3; }
.icon-box { display: flex; justify-content: center; cursor: pointer; }
.kf-btn.active { color: #f1c40f; }
.stopwatch.active { color: #3498db; }

/* Content spans from column 7 (Name) to the end */
.prop-content {
  grid-column: 7 / -1;
  display: flex;
  align-items: center;
  padding-right: 10px;
  overflow: hidden;
}
.prop-name { min-width: 100px; color: #999; font-size: 13px; }
.prop-inputs { display: flex; gap: 8px; flex: 1; align-items: center; }

.vec-item { display: flex; align-items: center; gap: 4px; }
.label { font-size: 10px; font-weight: bold; }
.x-label { color: #e74c3c; } .y-label { color: #2ecc71; } .z-label { color: #3498db; }

.color-input-wrapper { display: flex; align-items: center; gap: 8px; }
.color-hex { font-family: monospace; font-size: 11px; color: #aaa; }

.prop-track { height: 32px; background: #151515; border-bottom: 1px solid #2a2a2a; position: relative; cursor: pointer; }
.keyframe {
  position: absolute;
  width: 10px;
  height: 10px;
  background: #f1c40f;
  transform: rotate(45deg);
  top: 11px;
  border: 1px solid #000;
  cursor: ew-resize;
  transition: transform 0.1s;
}
.keyframe:hover {
  transform: rotate(45deg) scale(1.2);
}
.keyframe.selected {
  background: #fff;
  border-color: #4a90d9;
  box-shadow: 0 0 4px #4a90d9;
}

/* Selection box for marquee select */
.selection-box {
  position: absolute;
  top: 2px;
  bottom: 2px;
  background: rgba(74, 144, 217, 0.2);
  border: 1px solid rgba(74, 144, 217, 0.6);
  pointer-events: none;
  z-index: 5;
}

/* Context Menu */
.keyframe-context-menu {
  position: absolute;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
  min-width: 140px;
  z-index: 100;
  padding: 4px 0;
  font-size: 12px;
}

.menu-header {
  padding: 4px 12px;
  color: #888;
  font-size: 10px;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  border-bottom: 1px solid #333;
  margin-bottom: 4px;
}

.menu-item {
  padding: 6px 12px;
  cursor: pointer;
  display: flex;
  align-items: center;
  gap: 8px;
  color: #ddd;
  transition: background 0.1s;
}

.menu-item:hover {
  background: #3a3a3a;
}

.menu-item.active {
  background: #4a90d9;
  color: #fff;
}

.menu-item.delete {
  color: #e74c3c;
}

.menu-item.delete:hover {
  background: rgba(231, 76, 60, 0.2);
}

.menu-item .icon {
  font-size: 14px;
}

.menu-divider {
  height: 1px;
  background: #333;
  margin: 4px 0;
}

/* Keyframe interpolation visual styles */
.keyframe.bezier {
  border-radius: 2px;
}

.keyframe.hold {
  background: #e74c3c;
}
</style>
