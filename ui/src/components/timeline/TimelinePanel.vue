<template>
  <div class="timeline-panel" @mouseup="stopResize" @mouseleave="stopResize" @mousemove="handleResize">
    <!-- HEADER -->
    <div class="timeline-header">
      <div class="header-left">
        <span class="timeline-title">Timeline</span>
        <div class="frame-display">
           <input type="number" :value="store.currentFrame" @change="setFrame" class="frame-input" />
           <span class="fps-label">{{ store.fps }} fps</span>
        </div>
      </div>

      <div class="header-center">
        <!-- Main Controls moved here as requested -->
        <button class="add-layer-btn" @click="showAddLayerMenu = !showAddLayerMenu">
          <span class="icon">+</span> Layer
        </button>
        <button class="graph-toggle" :class="{ active: viewMode === 'graph' }" @click="toggleViewMode">
          {{ viewMode === 'graph' ? 'Graphs' : 'Layers' }}
        </button>
        <button class="delete-btn" @click="deleteSelectedLayers" :disabled="store.selectedLayerIds.length === 0" title="Delete">
          🗑️
        </button>

        <!-- Dropdown Menu -->
        <div v-if="showAddLayerMenu" class="add-layer-menu">
          <button @click="addLayer('solid')"><span class="icon">■</span> Solid</button>
          <button @click="addLayer('text')"><span class="icon">T</span> Text</button>
          <button @click="addLayer('spline')"><span class="icon">~</span> Shape</button>
          <button @click="addLayer('null')"><span class="icon">□</span> Null</button>
          <button @click="addLayer('camera')"><span class="icon">📷</span> Camera</button>
          <button @click="addLayer('light')"><span class="icon">💡</span> Light</button>
        </div>
      </div>

      <div class="header-right">
        <!-- Playback -->
        <div class="playback-controls">
          <button @click="goToStart">|&lt;</button>
          <button @click="togglePlayback" :class="{ active: isPlaying }">{{ isPlaying ? '||' : '▶' }}</button>
          <button @click="goToEnd">&gt;|</button>
        </div>
        <!-- Zoom Slider -->
        <input type="range" min="1" max="50" v-model.number="pixelsPerFrame" class="zoom-slider" title="Zoom" />
      </div>
    </div>

    <!-- MAIN CONTENT (Unified Scroll) -->
    <div class="timeline-content" ref="timelineContentRef">

      <!-- STICKY RULER -->
      <div class="time-ruler-container">
        <!-- Sidebar Header (Resizes) -->
        <div class="ruler-sidebar-spacer" :style="{ width: sidebarWidth + 'px' }">
          <div class="column-headers">
            <span class="col-header col-arrow"></span>
            <span class="col-header col-color">#</span>
            <span class="col-header col-name">Layer Name</span>
            <span class="col-header col-mode">Mode</span>
            <span class="col-header col-parent">Parent</span>
          </div>
        </div>

        <!-- Track Ruler (Scrolls horizontally with content) -->
        <div class="ruler-track-window" ref="rulerTrackRef" @scroll="syncScrollX">
          <div class="ruler-track-content" :style="{ width: totalTrackWidth + 'px' }" @mousedown="startRulerScrub">
            <!-- Time Marks -->
            <div v-for="mark in rulerMarks" :key="mark" class="ruler-mark"
                 :style="{ left: `${mark * pixelsPerFrame}px` }">
              {{ formatTime(mark) }}
            </div>
            <!-- Playhead Head -->
            <div class="playhead-head" :style="{ left: `${playheadPosition}px` }">
              <div class="playhead-tri"></div>
              <div class="playhead-line-top"></div>
            </div>
          </div>
        </div>
      </div>

      <!-- SPLIT LAYOUT -->
      <div class="timeline-split-layout">

        <!-- LEFT: SIDEBAR -->
        <div class="property-tree-sidebar" :style="{ width: sidebarWidth + 'px' }">
          <template v-for="layer in filteredLayers" :key="'sidebar-' + layer.id">
            <EnhancedLayerTrack
              :layer="layer"
              layoutMode="sidebar"
              :viewMode="viewMode"
              :isExpandedExternal="expandedLayers[layer.id]"
              :selectedPropertyIds="Array.from(selectedPropertyIds)"
              :allLayers="store.layers"
              :soloedLayerIds="soloedLayerIds"
              @select="selectLayer"
              @updateLayer="updateLayer"
              @toggleExpand="handleToggleExpand"
              @selectProperty="handlePropertySelect"
            />
          </template>
        </div>

        <!-- RESIZE HANDLE -->
        <div class="resize-handle" @mousedown="startResize"></div>

        <!-- RIGHT: TRACKS -->
        <div class="track-viewport" ref="trackViewportRef" @scroll="syncScrollX">
          <div class="track-scroll-content" :style="{ width: totalTrackWidth + 'px' }">

            <!-- Global Playhead Line -->
            <div class="playhead-line" :style="{ left: `${playheadPosition}px` }"></div>

            <!-- Keyframe Mode -->
            <template v-if="viewMode === 'keyframes'">
              <div class="layer-bars-container">
                <template v-for="layer in filteredLayers" :key="'track-' + layer.id">
                  <EnhancedLayerTrack
                    :layer="layer"
                    layoutMode="track"
                    :viewMode="viewMode"
                    :frameCount="store.frameCount"
                    :pixelsPerFrame="pixelsPerFrame"
                    :isExpandedExternal="expandedLayers[layer.id]"
                    :selectedPropertyIds="Array.from(selectedPropertyIds)"
                    @selectKeyframe="selectKeyframe"
                    @updateLayer="updateLayer"
                  />
                </template>
              </div>
            </template>

            <!-- Graph Mode -->
            <GraphEditorCanvas
              v-else-if="viewMode === 'graph'"
              :frameCount="store.frameCount"
              :currentFrame="store.currentFrame"
              :selectedPropertyIds="Array.from(selectedPropertyIds)"
              :graphMode="'value'"
            />
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, reactive, nextTick, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import EnhancedLayerTrack from './EnhancedLayerTrack.vue';
import GraphEditorCanvas from './GraphEditorCanvas.vue';

const store = useCompositorStore();
const viewMode = ref<'keyframes' | 'graph'>('keyframes');
const expandedLayers = ref<Record<string, boolean>>({});
const selectedPropertyIds = ref<Set<string>>(new Set());
const showAddLayerMenu = ref(false);
const rulerTrackRef = ref<HTMLDivElement | null>(null);
const trackViewportRef = ref<HTMLDivElement | null>(null);
const soloedLayerIds = ref<string[]>([]);

// VIEWPORT STATE
const sidebarWidth = ref(400);
const pixelsPerFrame = ref(5); // ZOOM LEVEL
const isResizing = ref(false);

// Logic
const filteredLayers = computed(() => store.layers || []);
const totalTrackWidth = computed(() => (store.frameCount + 50) * pixelsPerFrame.value); // Add buffer
const playheadPosition = computed(() => store.currentFrame * pixelsPerFrame.value);

// Ruler Marks
const rulerMarks = computed(() => {
  const marks = [];
  const step = pixelsPerFrame.value > 10 ? 5 : 10; // Dynamic density
  for (let i = 0; i <= store.frameCount; i += step) marks.push(i);
  return marks;
});

// Scroll Sync (Horizontal)
function syncScrollX(e: Event) {
  const target = e.target as HTMLElement;
  const isRuler = target === rulerTrackRef.value;
  const other = isRuler ? trackViewportRef.value : rulerTrackRef.value;
  if(other) other.scrollLeft = target.scrollLeft;
}

// Resize Logic
function startResize() { isResizing.value = true; document.body.style.cursor = 'col-resize'; }
function stopResize() { isResizing.value = false; document.body.style.cursor = 'default'; }
function handleResize(e: MouseEvent) {
  if (isResizing.value) sidebarWidth.value = Math.max(250, Math.min(800, e.clientX));
}

// Actions
function handleToggleExpand(layerId: string, expanded: boolean) { expandedLayers.value[layerId] = expanded; }
function handlePropertySelect(propId: string, add: boolean) {
  if (add) { if (selectedPropertyIds.value.has(propId)) selectedPropertyIds.value.delete(propId); else selectedPropertyIds.value.add(propId); }
  else { selectedPropertyIds.value.clear(); selectedPropertyIds.value.add(propId); }
  selectedPropertyIds.value = new Set(selectedPropertyIds.value);
}
function addLayer(type: string) { store.createLayer(type as any); showAddLayerMenu.value = false; }
function selectLayer(id: string) { store.selectLayer(id); }
function updateLayer(id: string, u: any) { store.updateLayer(id, u); }
function deleteSelectedLayers() { store.selectedLayerIds.forEach(id => store.deleteLayer(id)); }
function toggleViewMode() { viewMode.value = viewMode.value === 'keyframes' ? 'graph' : 'keyframes'; }
function selectKeyframe(id: string) {}

// Playback
const isPlaying = ref(false);
function togglePlayback() { isPlaying.value = !isPlaying.value; }
function goToStart() { store.setFrame(0); }
function goToEnd() { store.setFrame(store.frameCount - 1); }
function setFrame(e: Event) { store.setFrame(parseInt((e.target as HTMLInputElement).value) || 0); }

// Scrubbing
function startRulerScrub(e: MouseEvent) {
  const update = (ev: MouseEvent) => {
    // Calculate frame based on scroll offset + mouse X
    const rect = rulerTrackRef.value!.getBoundingClientRect();
    const scrollX = rulerTrackRef.value!.scrollLeft;
    const relX = (ev.clientX - rect.left) + scrollX;
    const f = Math.max(0, Math.min(store.frameCount - 1, relX / pixelsPerFrame.value));
    store.setFrame(Math.round(f));
  };
  update(e);
  window.addEventListener('mousemove', update);
  window.addEventListener('mouseup', () => window.removeEventListener('mousemove', update), { once: true });
}

function formatTime(f: number) {
  const s = Math.floor(f / store.fps);
  const fr = f % store.fps;
  return `${s}:${fr.toString().padStart(2, '0')}`;
}

function handleKeydown(e: KeyboardEvent) {
  if (e.target instanceof HTMLInputElement) return;
  if (e.key === 'Delete') deleteSelectedLayers();
  if (e.key === ' ') { e.preventDefault(); togglePlayback(); }
}

onMounted(() => window.addEventListener('keydown', handleKeydown));
onUnmounted(() => window.removeEventListener('keydown', handleKeydown));
</script>

<style scoped>
.timeline-panel { display: flex; flex-direction: column; height: 100%; background: #161616; color: #ccc; font-family: 'Segoe UI', sans-serif; user-select: none; }
.timeline-header { height: 40px; background: #222; border-bottom: 1px solid #000; display: flex; justify-content: space-between; padding: 0 10px; align-items: center; }
.header-left, .header-center, .header-right { display: flex; gap: 12px; align-items: center; }
.timeline-title { font-weight: 600; color: #ddd; }

/* Main Scroll Area - Vertical Only */
.timeline-content { flex: 1; overflow-y: auto; overflow-x: hidden; display: flex; flex-direction: column; position: relative; }

/* Sticky Ruler */
.time-ruler-container { display: flex; height: 30px; background: #222; position: sticky; top: 0; z-index: 20; border-bottom: 1px solid #444; }
.ruler-sidebar-spacer { flex-shrink: 0; border-right: 1px solid #444; background: #222; z-index: 21; }
.column-headers { display: flex; height: 100%; align-items: center; font-size: 11px; color: #888; background: #222; }
.col-header { padding: 0 5px; border-right: 1px solid #333; height: 100%; display: flex; align-items: center; }
.col-arrow { width: 24px; } .col-color { width: 24px; } .col-name { flex: 1; padding-left: 5px; } .col-mode { width: 60px; } .col-parent { width: 60px; }

/* Horizontal Scroll Window for Ruler */
.ruler-track-window { flex: 1; position: relative; overflow-x: auto; background: #222; }
.ruler-track-content { height: 100%; position: relative; }
.ruler-mark { position: absolute; font-size: 9px; color: #666; top: 2px; border-left: 1px solid #444; padding-left: 2px; height: 100%; }

/* Playhead */
.playhead-head { position: absolute; top: 0; height: 30px; transform: translateX(-50%); pointer-events: none; z-index: 25; }
.playhead-tri { width: 0; height: 0; border-left: 7px solid transparent; border-right: 7px solid transparent; border-top: 10px solid #3ea6ff; }
.playhead-line-top { width: 2px; height: 100%; background: #3ea6ff; margin: 0 auto; }

/* Split Layout */
.timeline-split-layout { display: flex; flex: 1; min-height: 0; }

.property-tree-sidebar {
  background: #1e1e1e; border-right: 1px solid #333;
  display: flex; flex-direction: column; flex-shrink: 0;
}

.resize-handle { width: 4px; background: #111; cursor: col-resize; border-left: 1px solid #333; border-right: 1px solid #333; z-index: 10; flex-shrink: 0; }
.resize-handle:hover { background: #4a90d9; }

/* Horizontal Scroll Window for Tracks */
.track-viewport {
  flex: 1; position: relative; background: #1a1a1a;
  overflow-x: auto; /* Horizontal scrolling happens here */
  min-width: 0;
}
.track-scroll-content { position: relative; min-height: 100%; }

.playhead-line { position: absolute; top: 0; bottom: 0; width: 2px; background: #3ea6ff; pointer-events: none; z-index: 100; }

/* Controls */
button { background: #333; border: 1px solid #444; color: #eee; cursor: pointer; padding: 4px 10px; border-radius: 3px; font-size: 13px; }
button:hover { background: #444; }
button.active { background: #4a90d9; border-color: #4a90d9; }
.frame-input { width: 50px; background: #111; border: 1px solid #444; color: #3ea6ff; padding: 2px; text-align: center; }
.zoom-slider { width: 80px; }

/* Add Layer Menu */
.add-layer-wrapper { position: relative; }
.add-layer-menu {
  position: absolute; top: 100%; left: 0;
  background: #252525; border: 1px solid #000;
  display: flex; flex-direction: column;
  z-index: 1000; width: 140px; margin-top: 4px;
}
.add-layer-menu button { text-align: left; border: none; padding: 8px 12px; border-bottom: 1px solid #333; }
.add-layer-menu button:hover { background: #4a90d9; color: #fff; }
.empty-state { padding: 40px; text-align: center; color: #555; }
</style>
