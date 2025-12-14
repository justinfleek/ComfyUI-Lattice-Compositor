<template>
  <div class="track-wrapper" v-if="layer">

    <!-- SIDEBAR MODE -->
    <template v-if="layoutMode === 'sidebar'">
      <div class="sidebar-row" :class="{ selected: isSelected }" :style="gridStyle" @click="selectLayer">

        <!-- 1. Twirl Arrow (LEFTMOST) -->
        <div class="arrow-col" @click.stop="toggleExpand">
          <span class="arrow">{{ isExpanded ? '▼' : '▶' }}</span>
        </div>

        <!-- 2. Color Strip -->
        <div class="label-box" @click.stop="toggleColorPicker" :style="{ background: layer.labelColor || '#999' }"></div>

        <!-- 3. ID -->
        <div class="layer-id">{{ layerIndex }}</div>

        <!-- 4. Icons -->
        <div class="icon-col" @click.stop="toggleVis">
          <span v-if="layer.visible">👁</span><span v-else class="dim">●</span>
        </div>
        <div class="icon-col" @click.stop="toggleLock">
          <span v-if="layer.locked">🔒</span><span v-else class="dim">🔓</span>
        </div>
        <div
          class="icon-col cube-icon"
          :class="{ active: layer.threeD }"
          @click.stop="toggle3D"
          title="3D Layer"
        >
          <span>⬡</span>
        </div>

        <!-- 5. Layer Name -->
        <div class="layer-name-col" @dblclick.stop="startRename">
          <span class="type-icon" :style="{ color: getLayerColor(layer.type) }">{{ getLayerIcon(layer.type) }}</span>
          <span v-if="!isRenaming" class="name-text">{{ layer.name }}</span>
          <input v-else v-model="renameVal" @blur="saveRename" @keydown.enter="saveRename" class="rename-input" ref="renameInput" />
        </div>

        <!-- 6. Mode Dropdown -->
        <div class="col-mode">
          <select class="mini-select" :value="layer.blendMode || 'normal'" @change="setBlendMode">
            <option value="normal">Normal</option>
            <option value="add">Add</option>
            <option value="multiply">Multiply</option>
            <option value="screen">Screen</option>
          </select>
        </div>

        <!-- 7. Parent Dropdown -->
        <div class="col-parent">
          <span class="pickwhip-icon">@</span>
          <select :value="layer.parentId || ''" @change="setParent" class="mini-select">
            <option value="">None</option>
            <option v-for="p in availableParents" :key="p.id" :value="p.id">{{ p.name }}</option>
          </select>
        </div>
      </div>

      <!-- Expanded Children (Sidebar) -->
      <div v-if="isExpanded" class="children-container">
        <PropertyTrack
          v-for="prop in properties" :key="prop.path"
          :layerId="layer.id" :propertyPath="prop.path" :name="prop.name" :property="prop.property"
          layoutMode="sidebar"
          :gridStyle="gridStyle"
          :selectedPropertyIds="selectedPropertyIds"
          @selectProperty="(id, add) => $emit('selectProperty', id, add)"
        />
      </div>
    </template>

    <!-- TRACK MODE -->
    <div v-else-if="layoutMode === 'track'" class="track-row-container">
      <div class="track-row">
        <!-- Duration Bar using pixelsPerFrame -->
        <div class="duration-bar" :style="barStyle" @mousedown.stop="startDrag" @click.stop="selectLayer">
          <div class="bar-fill" :style="{ background: layer.labelColor || '#777', opacity: isSelected ? 0.8 : 0.5 }"></div>
          <div class="trim-handle trim-in" @mousedown.stop="startTrimIn"></div>
          <div class="trim-handle trim-out" @mousedown.stop="startTrimOut"></div>
        </div>

        <!-- Keyframe Markers (Summary) -->
        <div v-for="kf in allKeyframes" :key="kf.id"
             class="keyframe-marker"
             :style="{ left: `${kf.frame * pixelsPerFrame}px` }">◆</div>
      </div>

      <!-- Expanded Children (Track) -->
      <div v-if="isExpanded" class="children-container">
        <PropertyTrack
          v-for="prop in properties" :key="prop.path"
          :layerId="layer.id" :propertyPath="prop.path" :name="prop.name" :property="prop.property"
          layoutMode="track" :viewMode="viewMode" :frameCount="frameCount" :pixelsPerFrame="pixelsPerFrame"
          :selectedKeyframeIds="[]"
          @selectKeyframe="(id, add) => $emit('selectKeyframe', id, add)"
        />
      </div>
    </div>

  </div>
</template>

<script setup lang="ts">
import { computed, ref, watch, nextTick } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import PropertyTrack from './PropertyTrack.vue';

const props = defineProps(['layer', 'index', 'layoutMode', 'isExpandedExternal', 'selectedPropertyIds', 'frameCount', 'viewMode', 'allLayers', 'soloedLayerIds', 'pixelsPerFrame', 'gridStyle']);
const emit = defineEmits(['toggleExpand', 'select', 'updateLayer', 'selectProperty', 'selectKeyframe', 'toggleSolo', 'setParent']);
const store = useCompositorStore();

const localExpanded = ref(false);
const isExpanded = computed(() => props.isExpandedExternal ?? localExpanded.value);
const isSelected = computed(() => store.selectedLayerIds.includes(props.layer.id));

const isRenaming = ref(false);
const renameVal = ref('');
const renameInput = ref<HTMLInputElement | null>(null);

// Layer index for display (use passed index prop or compute from allLayers)
const layerIndex = computed(() => {
  if (props.index !== undefined) return props.index;
  const idx = props.allLayers?.findIndex((l: any) => l.id === props.layer.id);
  return idx !== undefined && idx >= 0 ? idx + 1 : 1;
});

const properties = computed(() => {
  const list: { path: string; name: string; property: any }[] = [];
  const t = props.layer.transform;

  // 1. Position (always present)
  if (t.position) {
    list.push({ path: 'transform.position', name: 'Position', property: t.position });
  }

  // 2. Scale (always present)
  if (t.scale) {
    list.push({ path: 'transform.scale', name: 'Scale', property: t.scale });
  }

  // 3. Rotation logic (2D vs 3D)
  if (props.layer.threeD) {
    // 3D mode: show Orientation and X/Y/Z Rotations
    if (t.orientation) {
      list.push({ path: 'transform.orientation', name: 'Orientation', property: t.orientation });
    }
    if (t.rotationX) {
      list.push({ path: 'transform.rotationX', name: 'X Rotation', property: t.rotationX });
    }
    if (t.rotationY) {
      list.push({ path: 'transform.rotationY', name: 'Y Rotation', property: t.rotationY });
    }
    if (t.rotationZ) {
      list.push({ path: 'transform.rotationZ', name: 'Z Rotation', property: t.rotationZ });
    }
  } else {
    // 2D mode: show standard Rotation
    if (t.rotation) {
      list.push({ path: 'transform.rotation', name: 'Rotation', property: t.rotation });
    }
  }

  // 4. Opacity (always present)
  if (props.layer.opacity) {
    list.push({ path: 'opacity', name: 'Opacity', property: props.layer.opacity });
  }

  // 5. Camera-specific: Point of Interest
  if (props.layer.type === 'camera' && t.anchorPoint) {
    list.push({ path: 'transform.anchorPoint', name: 'Point of Interest', property: t.anchorPoint });
  }

  return list;
});

const allKeyframes = computed(() => {
  const kfs: any[] = [];
  properties.value.forEach(p => { if (p.property?.animated) kfs.push(...(p.property.keyframes || [])); });
  return kfs;
});

// Bar style using pixelsPerFrame for pixel-accurate positioning
const barStyle = computed(() => {
  const ppf = props.pixelsPerFrame || 5;
  const startPx = props.layer.inPoint * ppf;
  const endPx = (props.layer.outPoint || props.frameCount) * ppf;
  return { left: `${startPx}px`, width: `${endPx - startPx}px` };
});

const availableParents = computed(() => props.allLayers?.filter((l: any) => l.id !== props.layer.id) || []);

function toggleExpand() { emit('toggleExpand', props.layer.id, !isExpanded.value); }
function selectLayer() { emit('select', props.layer.id); }
function toggleVis() { emit('updateLayer', props.layer.id, { visible: !props.layer.visible }); }
function toggleLock() { emit('updateLayer', props.layer.id, { locked: !props.layer.locked }); }
function toggle3D() { store.toggleLayer3D(props.layer.id); }
function setParent(e: Event) { emit('updateLayer', props.layer.id, { parentId: (e.target as HTMLSelectElement).value || null }); }
function setBlendMode(e: Event) { emit('updateLayer', props.layer.id, { blendMode: (e.target as HTMLSelectElement).value }); }

function getLayerColor(t: string) {
  const colors: Record<string, string> = {
    solid: '#e74c3c',
    text: '#f1c40f',
    spline: '#2ecc71',
    null: '#9b59b6',
    camera: '#3498db',
    light: '#f39c12',
    particles: '#e91e63',
    depthflow: '#00bcd4',
    image: '#95a5a6'
  };
  return colors[t] || '#95a5a6';
}

function getLayerIcon(t: string) {
  const icons: Record<string, string> = {
    solid: '■',
    text: 'T',
    spline: '~',
    null: '□',
    camera: '📷',
    light: '💡',
    particles: '✦',
    depthflow: '◐',
    image: '🖼'
  };
  return icons[t] || '■';
}

function startRename() { isRenaming.value = true; renameVal.value = props.layer.name; nextTick(() => renameInput.value?.focus()); }
function saveRename() { emit('updateLayer', props.layer.id, { name: renameVal.value }); isRenaming.value = false; }

function startDrag(e: MouseEvent) {
  const ppf = props.pixelsPerFrame || 5;
  const startX = e.clientX;
  const startIn = props.layer.inPoint;
  const startOut = props.layer.outPoint || props.frameCount;
  const duration = startOut - startIn;

  const onMove = (ev: MouseEvent) => {
    const dx = ev.clientX - startX;
    const dFrames = Math.round(dx / ppf);
    const newIn = Math.max(0, Math.min(props.frameCount - duration, startIn + dFrames));
    const newOut = newIn + duration;
    emit('updateLayer', props.layer.id, { inPoint: newIn, outPoint: newOut });
  };

  const onUp = () => {
    window.removeEventListener('mousemove', onMove);
    window.removeEventListener('mouseup', onUp);
  };

  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', onUp);
}

function startTrimIn(e: MouseEvent) {
  e.stopPropagation();
  const ppf = props.pixelsPerFrame || 5;
  const startX = e.clientX;
  const startIn = props.layer.inPoint;

  const onMove = (ev: MouseEvent) => {
    const dx = ev.clientX - startX;
    const dFrames = Math.round(dx / ppf);
    const newIn = Math.max(0, Math.min((props.layer.outPoint || props.frameCount) - 1, startIn + dFrames));
    emit('updateLayer', props.layer.id, { inPoint: newIn });
  };

  const onUp = () => {
    window.removeEventListener('mousemove', onMove);
    window.removeEventListener('mouseup', onUp);
  };

  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', onUp);
}

function startTrimOut(e: MouseEvent) {
  e.stopPropagation();
  const ppf = props.pixelsPerFrame || 5;
  const startX = e.clientX;
  const startOut = props.layer.outPoint || props.frameCount;

  const onMove = (ev: MouseEvent) => {
    const dx = ev.clientX - startX;
    const dFrames = Math.round(dx / ppf);
    const newOut = Math.max(props.layer.inPoint + 1, Math.min(props.frameCount, startOut + dFrames));
    emit('updateLayer', props.layer.id, { outPoint: newOut });
  };

  const onUp = () => {
    window.removeEventListener('mousemove', onMove);
    window.removeEventListener('mouseup', onUp);
  };

  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', onUp);
}

function toggleColorPicker() {
  // Simple color cycle for now
  const colors = ['#e74c3c', '#f39c12', '#f1c40f', '#2ecc71', '#3498db', '#9b59b6', '#95a5a6'];
  const current = props.layer.labelColor || '#999';
  const idx = colors.indexOf(current);
  const next = colors[(idx + 1) % colors.length];
  emit('updateLayer', props.layer.id, { labelColor: next });
}

watch(() => props.isExpandedExternal, v => localExpanded.value = v);
</script>

<style scoped>
.track-wrapper { display: flex; flex-direction: column; width: 100%; }

/* SIDEBAR LAYOUT */
.sidebar-row {
  border-bottom: 1px solid #2a2a2a;
  background: #1e1e1e;
  color: #ccc;
  font-size: 13px;
  min-height: 28px;
  /* Support both flex and grid layout */
  display: grid;
  align-items: center;
}
.sidebar-row.selected { background: #333; color: #fff; }

/* Arrow column FIRST */
.arrow-col { width: 20px; text-align: center; cursor: pointer; font-size: 9px; color: #888; flex-shrink: 0; }
.arrow-col:hover { color: #fff; }

.label-box { width: 12px; height: 12px; margin: 0 4px; border-radius: 2px; cursor: pointer; border: 1px solid #000; flex-shrink: 0; }
.layer-id { width: 24px; text-align: center; font-size: 10px; color: #666; flex-shrink: 0; }
.icon-col { width: 24px; text-align: center; cursor: pointer; color: #aaa; font-size: 12px; flex-shrink: 0; }
.icon-col .dim { color: #444; }
.icon-col:hover { color: #fff; }
.icon-col.cube-icon { color: #555; }
.icon-col.cube-icon.active { color: #4a90d9; }
.icon-col.cube-icon:hover { color: #fff; }

.layer-name-col { flex: 1; display: flex; align-items: center; padding: 0 5px; overflow: hidden; min-width: 100px; }
.type-icon { font-size: 10px; margin-right: 6px; }
.name-text { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 14px; }
.rename-input { background: #000; border: 1px solid #4a90d9; color: #fff; width: 100%; font-size: 13px; padding: 2px; }

/* Columns */
.col-mode, .col-parent { border-left: 1px solid #333; padding: 0 4px; height: 100%; display: flex; align-items: center; flex-shrink: 0; }
.col-mode { width: 70px; }
.col-parent { width: 80px; gap: 4px; }

.mini-select {
  width: 100%; background: transparent; border: none; color: #aaa;
  font-size: 11px; -webkit-appearance: none; cursor: pointer;
}
.mini-select:hover { color: #fff; }
.pickwhip-icon { font-family: serif; font-weight: bold; color: #666; cursor: crosshair; }

.children-container { display: flex; flex-direction: column; }

/* TRACK LAYOUT */
.track-row-container { width: 100%; }
.track-row { height: 28px; border-bottom: 1px solid #333; position: relative; background: #191919; }
.duration-bar { position: absolute; height: 18px; top: 5px; border-radius: 2px; cursor: move; }
.bar-fill { width: 100%; height: 100%; border: 1px solid rgba(0,0,0,0.4); border-radius: 2px; }
.trim-handle { position: absolute; top: 0; bottom: 0; width: 6px; cursor: ew-resize; background: rgba(255,255,255,0.1); }
.trim-handle:hover { background: rgba(255,255,255,0.3); }
.trim-in { left: 0; border-radius: 2px 0 0 2px; }
.trim-out { right: 0; border-radius: 0 2px 2px 0; }
.keyframe-marker { position: absolute; top: 10px; font-size: 8px; color: #ebcb8b; transform: translateX(-50%); z-index: 5; pointer-events: none; }
</style>
