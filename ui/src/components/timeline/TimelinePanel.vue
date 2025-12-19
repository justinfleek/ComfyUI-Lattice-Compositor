<template>
  <div class="timeline-panel" tabindex="0" @keydown="handleKeydown" role="region" aria-label="Timeline">
    <!-- Composition Tabs -->
    <CompositionTabs
      @newComposition="emit('openCompositionSettings')"
      @openCompositionSettings="emit('openCompositionSettings')"
    />

    <div class="timeline-header">
      <div class="header-left">
        <span class="timecode">{{ formatTimecode(store.currentFrame) }}</span>
        <div class="frame-display">
           <input type="number" :value="store.currentFrame" @change="setFrame" class="frame-input" />
           <span class="fps-label">{{ store.fps }} fps</span>
        </div>
      </div>

      <div class="header-center">
        <div class="tool-group add-layer-wrapper" ref="addLayerContainer">
          <button
            class="add-layer-btn"
            :class="{ active: showAddLayerMenu }"
            @mousedown.stop.prevent="toggleAddLayerMenu"
            aria-label="Add Layer"
            aria-haspopup="menu"
            :aria-expanded="showAddLayerMenu"
          >
            <span class="icon" aria-hidden="true">+</span> Layer
          </button>

          <div v-if="showAddLayerMenu" class="add-layer-menu" role="menu" aria-label="Layer types">
            <button @mousedown="addLayer('solid')" role="menuitem"><span class="icon" aria-hidden="true">■</span> Solid</button>
            <button @mousedown="addLayer('text')" role="menuitem"><span class="icon" aria-hidden="true">T</span> Text</button>
            <button @mousedown="addLayer('shape')" role="menuitem"><span class="icon" aria-hidden="true">◇</span> Shape</button>
            <button @mousedown="addLayer('spline')" role="menuitem"><span class="icon" aria-hidden="true">〰</span> Spline/Path</button>
            <button @mousedown="addLayer('particles')" role="menuitem"><span class="icon" aria-hidden="true">✨</span> Particles</button>
            <button @mousedown="addLayer('control')" role="menuitem"><span class="icon" aria-hidden="true">□</span> Control</button>
            <button @mousedown="addLayer('camera')" role="menuitem"><span class="icon" aria-hidden="true">📷</span> Camera</button>
            <button @mousedown="addLayer('light')" role="menuitem"><span class="icon" aria-hidden="true">💡</span> Light</button>
            <button @mousedown="addLayer('video')" role="menuitem"><span class="icon" aria-hidden="true">🎞️</span> Video</button>
          </div>
        </div>

        <div class="tool-group">
           <button class="delete-btn" @click="deleteSelectedLayers" :disabled="store.selectedLayerIds.length === 0" aria-label="Delete selected layers">🗑️</button>
        </div>

        <div class="tool-group">
          <button class="comp-settings-btn" @click="emit('openCompositionSettings')" title="Composition Settings (Ctrl+K)">
            ⚙️ Comp Settings
          </button>
          <button class="ai-btn" @click="emit('openPathSuggestion')" title="AI Path Suggestion">
            ✨ AI
          </button>
        </div>
      </div>

      <div class="header-right">
        <input type="range" min="0" max="100" step="1" v-model.number="zoomPercent" class="zoom-slider" title="Zoom Timeline" aria-label="Timeline zoom level" />
      </div>
    </div>

    <div class="timeline-content">
      <div class="timeline-sidebar" :style="{ width: sidebarWidth + 'px' }">
        <div class="sidebar-header-row">
          <!-- AV Features (visibility, audio, isolate, lock) -->
          <div class="col-header col-av-features">
            <span class="header-icon" title="Video">👁</span>
            <span class="header-icon" title="Audio">🔊</span>
            <span class="header-icon" title="Isolate">●</span>
            <span class="header-icon" title="Lock">🔒</span>
          </div>
          <!-- Layer info -->
          <div class="col-header col-number">#</div>
          <div class="col-header col-name">Source Name</div>
          <!-- Switches -->
          <div class="col-header col-switches">
            <span
              class="header-icon clickable"
              :class="{ active: store.hideMinimizedLayers }"
              title="Hide Minimized Layers"
              @click="store.toggleHideMinimizedLayers()"
            >🙈</span>
            <span class="header-icon" title="Flatten Transform">☀</span>
            <span class="header-icon" title="Quality">◐</span>
            <span class="header-icon" title="Effects">fx</span>
            <span class="header-icon" title="Frame Blending">⊞</span>
            <span class="header-icon" title="Motion Blur">◔</span>
            <span class="header-icon" title="Adjustment Layer">◐</span>
            <span class="header-icon" title="3D Layer">⬡</span>
          </div>
          <div class="col-header col-parent">Parent & Link</div>
        </div>
        <div class="sidebar-scroll-area" ref="sidebarScrollRef" @scroll="syncSidebarScroll">
          <EnhancedLayerTrack
            v-for="(layer, idx) in filteredLayers"
            :key="layer.id"
            :layer="layer"
            :index="idx + 1"
            layoutMode="sidebar"
            :isExpandedExternal="expandedLayers[layer.id]"
            :allLayers="store.layers"
            :gridStyle="sidebarGridStyle"
            @toggleExpand="handleToggleExpand"
            @select="selectLayer"
            @updateLayer="updateLayer"
          />
        </div>
      </div>

      <div class="sidebar-resizer" @mousedown="startResize"></div>

      <div class="track-viewport" ref="trackViewportRef">
        <!-- Ruler stays fixed at top, scrolls horizontally with content -->
        <div class="ruler-scroll-wrapper" @scroll="syncRulerScroll" ref="rulerScrollRef">
          <div class="time-ruler" :style="{ width: computedWidthStyle }" @mousedown="startRulerScrub">
             <canvas ref="rulerCanvas" height="30"></canvas>

             <div class="playhead-head" :style="{ left: playheadPositionPct + '%' }"></div>
             <div class="playhead-hit-area"
                  :style="{ left: playheadPositionPct + '%' }"
                  @mousedown.stop="startRulerScrub"
             ></div>
          </div>
        </div>

        <!-- Layer bars scroll both horizontally and vertically -->
        <div class="track-scroll-area" ref="trackScrollRef" @scroll="handleTrackScroll">
          <div class="layer-bars-container" :style="{ width: computedWidthStyle }">
             <div class="grid-background"></div>

             <EnhancedLayerTrack
                v-for="layer in filteredLayers"
                :key="layer.id"
                :layer="layer"
                layoutMode="track"
                :frameCount="store.frameCount"
                :pixelsPerFrame="effectivePpf"
                :isExpandedExternal="expandedLayers[layer.id]"
                @select="selectLayer"
                @updateLayer="updateLayer"
              />

             <div class="playhead-line" :style="{ left: playheadPositionPct + '%' }"></div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, watch, nextTick } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import EnhancedLayerTrack from './EnhancedLayerTrack.vue';
import CompositionTabs from './CompositionTabs.vue';
import { findNearestSnap } from '@/services/timelineSnap';

const emit = defineEmits<{
  (e: 'openCompositionSettings'): void;
  (e: 'openPathSuggestion'): void;
}>();

const store = useCompositorStore();
const zoomPercent = ref(0); // 0 = fit to viewport, 100 = max zoom
const sidebarWidth = ref(450); // Increased width for better visibility of layer names
const expandedLayers = ref<Record<string, boolean>>({});
const showAddLayerMenu = ref(false);
const addLayerContainer = ref<HTMLElement | null>(null);
const trackViewportRef = ref<HTMLElement | null>(null);
const rulerCanvas = ref<HTMLCanvasElement | null>(null);
const sidebarScrollRef = ref<HTMLElement | null>(null);
const trackScrollRef = ref<HTMLElement | null>(null);
const rulerScrollRef = ref<HTMLElement | null>(null);
let isScrollingSidebar = false;
let isScrollingTrack = false;
const viewportWidth = ref(1000); // Default, updated by observer

const filteredLayers = computed(() => store.displayedLayers || []);
// Playhead position as percentage of timeline
const playheadPositionPct = computed(() => (store.currentFrame / store.frameCount) * 100);

// Zoom calculation: 0% = fit viewport exactly, 100% = max zoom (~20 frames visible)
// At 100% zoom with 1200px viewport: 1200/80 = 15 frames visible
const MAX_PPF = 80;

const effectivePpf = computed(() => {
  // minPpf ensures full composition fits viewport at 0% zoom
  const minPpf = viewportWidth.value / store.frameCount;
  // Linear interpolation from minPpf (0%) to MAX_PPF (100%)
  return minPpf + (zoomPercent.value / 100) * (MAX_PPF - minPpf);
});

// At 0% zoom: timelineWidth = frameCount * (viewportWidth/frameCount) = viewportWidth
// This guarantees the timeline fills the viewport exactly at 0%
const timelineWidth = computed(() => {
  // Ensure at 0% zoom, width is exactly viewportWidth (not less due to rounding)
  if (zoomPercent.value === 0) {
    return viewportWidth.value;
  }
  return store.frameCount * effectivePpf.value;
});

const computedWidthStyle = computed(() => timelineWidth.value + 'px');

const sidebarGridStyle = computed(() => ({
  display: 'grid',
  gridTemplateColumns: '24px 24px 30px 24px 24px 24px 1fr 70px 70px',
  alignItems: 'center',
  height: '32px',
  width: '100%',
  boxSizing: 'border-box'
}));

// Actions
function toggleAddLayerMenu() { showAddLayerMenu.value = !showAddLayerMenu.value; }

function addLayer(type: string) {
  let newLayer;

  if (type === 'text') newLayer = store.createTextLayer();
  else if (type === 'video') newLayer = store.createLayer('video');
  else if (type === 'camera') newLayer = store.createCameraLayer();
  else if (type === 'particles') newLayer = store.createParticleLayer();
  else newLayer = store.createLayer(type as any);

  showAddLayerMenu.value = false;

  // Auto-select the new layer
  if (newLayer) {
    store.selectLayer(newLayer.id);

    // Activate appropriate tool based on layer type
    if (type === 'spline' || type === 'shape') {
      store.setTool('pen');
    } else if (type === 'text') {
      store.setTool('text');
    } else {
      store.setTool('select');
    }
  }
}

function selectLayer(id: string) { store.selectLayer(id); }
function updateLayer(id: string, u: any) { store.updateLayer(id, u); }
function deleteSelectedLayers() { store.selectedLayerIds.forEach(id => store.deleteLayer(id)); }
function setFrame(e: Event) { store.setFrame(parseInt((e.target as HTMLInputElement).value) || 0); }
function togglePlayback() { store.togglePlayback(); }
function handleToggleExpand(id: string, val: boolean) { expandedLayers.value[id] = val; }

// Format frame as timecode (HH;MM;SS;FF) SMPTE format
function formatTimecode(frame: number): string {
  const fps = store.fps;
  const totalSeconds = Math.floor(frame / fps);
  const frames = Math.floor(frame % fps);
  const seconds = totalSeconds % 60;
  const minutes = Math.floor(totalSeconds / 60) % 60;
  const hours = Math.floor(totalSeconds / 3600);

  const pad = (n: number, len: number = 2) => String(n).padStart(len, '0');
  return `${pad(hours)};${pad(minutes)};${pad(seconds)};${pad(frames)}`;
}

function drawRuler() {
  const cvs = rulerCanvas.value;
  if (!cvs) return;
  const ctx = cvs.getContext('2d');
  if (!ctx) return;

  // Width fills viewport (or larger when zoomed in)
  const width = timelineWidth.value;
  cvs.width = width;
  cvs.height = 30;

  ctx.fillStyle = '#222';
  ctx.fillRect(0, 0, cvs.width, cvs.height);
  ctx.strokeStyle = '#666';
  ctx.fillStyle = '#aaa';
  ctx.font = '11px sans-serif';

  // Calculate label step based on available space, not raw ppf
  // Ensure labels have enough room and don't overlap
  const labelMinWidth = 40; // minimum pixels between labels
  const maxLabels = Math.max(1, Math.floor(width / labelMinWidth));
  const idealStep = Math.ceil(store.frameCount / maxLabels);

  // Round up to a nice number for clean ruler
  const niceSteps = [1, 2, 5, 10, 20, 25, 50, 100, 200];
  const majorStep = niceSteps.find(s => s >= idealStep) || 200;

  // Minor step is half of major, or 0 if major is 1
  const minorStep = majorStep > 1 ? Math.floor(majorStep / 2) : 0;

  // Proportional positioning: frame position = (frame / frameCount) * width
  // This ensures the ruler fills the viewport when zoomed out
  const frameCount = store.frameCount;

  for (let f = 0; f <= frameCount; f++) {
    const x = (f / frameCount) * width;

    if (f % majorStep === 0) {
      // Major Tick
      ctx.strokeStyle = '#888';
      ctx.beginPath();
      ctx.moveTo(x, 12);
      ctx.lineTo(x, 30);
      ctx.stroke();

      // Label - majorStep already accounts for spacing
      ctx.fillStyle = '#ccc';
      ctx.fillText(String(f), x + 3, 10);
    } else if (minorStep > 0 && f % minorStep === 0) {
      // Minor Tick
      ctx.strokeStyle = '#555';
      ctx.beginPath();
      ctx.moveTo(x, 22);
      ctx.lineTo(x, 30);
      ctx.stroke();
    }
  }

  // Draw bottom border line
  ctx.strokeStyle = '#444';
  ctx.beginPath();
  ctx.moveTo(0, 29.5);
  ctx.lineTo(cvs.width, 29.5);
  ctx.stroke();
}

function startRulerScrub(e: MouseEvent) {
  const rect = rulerCanvas.value!.getBoundingClientRect();
  const scrollX = rulerScrollRef.value?.scrollLeft || trackScrollRef.value?.scrollLeft || 0;

  const update = (ev: MouseEvent) => {
    const currentScrollX = rulerScrollRef.value?.scrollLeft || trackScrollRef.value?.scrollLeft || 0;
    const x = (ev.clientX - rect.left) + currentScrollX;
    // Convert x position to frame using proportional formula
    let f = Math.max(0, Math.min(store.frameCount - 1, (x / timelineWidth.value) * store.frameCount));

    // Apply snapping (hold Alt/Option to disable)
    if (!ev.altKey && store.snapConfig.enabled) {
      const snap = findNearestSnap(Math.round(f), store.snapConfig, effectivePpf.value, {
        layers: store.layers,
        audioAnalysis: store.audioAnalysis,
        peakData: store.peakData
      });
      if (snap) {
        f = snap.frame;
      }
    }

    store.setFrame(Math.round(f));
  };

  update(e);
  window.addEventListener('mousemove', update);
  window.addEventListener('mouseup', () => window.removeEventListener('mousemove', update), { once: true });
}

function startResize(e: MouseEvent) {
  const startX = e.clientX;
  const startW = sidebarWidth.value;
  const onMove = (ev: MouseEvent) => { sidebarWidth.value = Math.max(450, startW + (ev.clientX - startX)); };
  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', () => window.removeEventListener('mousemove', onMove), { once: true });
}

// Scroll synchronization between sidebar and track area
function syncSidebarScroll(e: Event) {
  if (isScrollingTrack) return;
  isScrollingSidebar = true;
  const target = e.target as HTMLElement;
  if (trackScrollRef.value) {
    trackScrollRef.value.scrollTop = target.scrollTop;
  }
  requestAnimationFrame(() => { isScrollingSidebar = false; });
}

// Handle track scroll - syncs vertical scroll to sidebar and horizontal to ruler
function handleTrackScroll(e: Event) {
  const target = e.target as HTMLElement;

  // Sync vertical scroll to sidebar
  if (!isScrollingSidebar) {
    isScrollingTrack = true;
    if (sidebarScrollRef.value) {
      sidebarScrollRef.value.scrollTop = target.scrollTop;
    }
    requestAnimationFrame(() => { isScrollingTrack = false; });
  }

  // Sync horizontal scroll to ruler
  if (rulerScrollRef.value) {
    rulerScrollRef.value.scrollLeft = target.scrollLeft;
  }
}

// Sync ruler horizontal scroll to track area
function syncRulerScroll(e: Event) {
  const target = e.target as HTMLElement;
  if (trackScrollRef.value) {
    trackScrollRef.value.scrollLeft = target.scrollLeft;
  }
}

function handleKeydown(e: KeyboardEvent) {
  if (e.target instanceof HTMLInputElement || e.target instanceof HTMLTextAreaElement) return;

  // Playback
  if (e.code === 'Space') { e.preventDefault(); togglePlayback(); }

  // Delete
  if (e.code === 'Delete' || e.code === 'Backspace') {
    e.preventDefault();
    deleteSelectedLayers();
  }

  // Copy/Cut/Paste
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyC') {
    e.preventDefault();
    store.copySelectedLayers();
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyX') {
    e.preventDefault();
    store.cutSelectedLayers();
  }
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyV') {
    e.preventDefault();
    store.pasteLayers();
  }

  // Select All
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyA') {
    e.preventDefault();
    store.selectedLayerIds = store.layers.map(l => l.id);
  }

  // Duplicate (Ctrl+D)
  if ((e.ctrlKey || e.metaKey) && e.code === 'KeyD') {
    e.preventDefault();
    for (const id of store.selectedLayerIds) {
      store.duplicateLayer(id);
    }
  }
}

let resizeObserver: ResizeObserver | null = null;

onMounted(() => {
  window.addEventListener('mousedown', (e) => {
    if (addLayerContainer.value && !addLayerContainer.value.contains(e.target as Node)) {
      showAddLayerMenu.value = false;
    }
  });

  // Track viewport size for accurate width calculation
  const elementToObserve = trackScrollRef.value || trackViewportRef.value;
  if (elementToObserve) {
    // Measure immediately on mount
    viewportWidth.value = elementToObserve.clientWidth || 1000;

    resizeObserver = new ResizeObserver((entries) => {
      for (const entry of entries) {
        viewportWidth.value = entry.contentRect.width || elementToObserve.clientWidth || 1000;
        drawRuler(); // Redraw ruler on resize
      }
    });
    resizeObserver.observe(elementToObserve);
  }

  // Draw ruler after a short delay to ensure layout is complete
  setTimeout(() => {
    if (trackScrollRef.value) {
      viewportWidth.value = trackScrollRef.value.clientWidth || viewportWidth.value;
    }
    drawRuler();
  }, 50);
});

onUnmounted(() => {
  if (resizeObserver) resizeObserver.disconnect();
});

watch(() => [computedWidthStyle.value, zoomPercent.value, store.frameCount], () => nextTick(drawRuler));
</script>

<style scoped>
.timeline-panel { display: flex; flex-direction: column; height: 100%; background: #111; color: #eee; font-family: 'Segoe UI', sans-serif; font-size: 13px; user-select: none; }
.timeline-header { height: 40px; background: #2a2a2a; border-bottom: 1px solid #000; display: flex; justify-content: space-between; padding: 0 10px; align-items: center; z-index: 20; flex-shrink: 0; }
.header-left, .header-center, .header-right { display: flex; gap: 12px; align-items: center; }
.tool-group { display: flex; gap: 8px; align-items: center; }

/* SMPTE Timecode display */
.timecode { font-family: 'Consolas', 'Courier New', monospace; font-size: 16px; color: #4a90d9; font-weight: bold; letter-spacing: 1px; }

/* Menus */
.add-layer-wrapper { position: relative; }
.add-layer-menu {
  position: absolute; top: 100%; left: 0;
  background: #333; border: 1px solid #000;
  display: flex; flex-direction: column;
  min-width: 140px; z-index: 9999;
  box-shadow: 0 4px 8px rgba(0,0,0,0.5);
}
.add-layer-menu button { text-align: left; padding: 10px; border: none; background: transparent; color: #eee; cursor: pointer; border-bottom: 1px solid #444; }
.add-layer-menu button:hover { background: #4a90d9; color: white; }
.add-layer-btn { padding: 6px 12px; background: #444; border: 1px solid #555; color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: bold; }
.add-layer-btn:hover, .add-layer-btn.active { background: #555; }

.comp-settings-btn { padding: 6px 14px; background: #3a5a8a; border: 1px solid #4a7aba; color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: 500; }
.comp-settings-btn:hover { background: #4a6a9a; border-color: #5a8aca; }
.ai-btn { padding: 6px 12px; background: linear-gradient(135deg, #6a4c93, #4a90d9); border: 1px solid #7a5ca3; color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: 500; }
.ai-btn:hover { background: linear-gradient(135deg, #7a5ca3, #5aa0e9); border-color: #8a6cb3; }

.timeline-content { flex: 1; display: flex; overflow: hidden; position: relative; min-height: 0; }
.timeline-sidebar { background: #1e1e1e; border-right: 1px solid #000; display: flex; flex-direction: column; flex-shrink: 0; z-index: 10; }
.sidebar-header-row { height: 30px; background: #252525; display: flex; align-items: center; border-bottom: 1px solid #000; }
.col-header { font-size: 12px; color: #888; display: flex; align-items: center; }
.col-header.col-av-features {
  display: flex;
  gap: 0;
  border-right: 1px solid #333;
  padding: 0 2px;
}
.col-header.col-number { width: 20px; justify-content: center; }
.col-header.col-name { flex: 1; padding-left: 8px; font-weight: 500; }
.col-header.col-switches {
  display: flex;
  gap: 0;
  border-left: 1px solid #333;
  padding: 0 2px;
}
.col-header.col-parent { min-width: 80px; border-left: 1px solid #333; padding: 0 8px; }
.header-icon { display: inline-flex; justify-content: center; align-items: center; width: 22px; height: 28px; font-size: 12px; color: #666; cursor: default; }
.header-icon.clickable { cursor: pointer; transition: color 0.15s; }
.header-icon.clickable:hover { color: #aaa; }
.header-icon.clickable.active { color: #4a90d9; }
.sidebar-scroll-area { flex: 1; overflow-y: auto; overflow-x: hidden; }

.sidebar-resizer { width: 4px; background: #111; cursor: col-resize; flex-shrink: 0; z-index: 15; }
.sidebar-resizer:hover { background: #4a90d9; }

.track-viewport {
  flex: 1;
  display: flex;
  flex-direction: column;
  overflow: hidden;
  position: relative;
  background: #151515;
}

/* Ruler wrapper - scrolls horizontally only */
.ruler-scroll-wrapper {
  height: 30px;
  overflow-x: auto;
  overflow-y: hidden;
  flex-shrink: 0;
  scrollbar-width: none; /* Firefox */
}
.ruler-scroll-wrapper::-webkit-scrollbar {
  display: none; /* Chrome/Safari */
}

.time-ruler {
  height: 30px;
  position: relative;
  background: #222;
  border-bottom: 1px solid #000;
  cursor: pointer;
  z-index: 10;
}

/* Track scroll area - scrolls both horizontally and vertically */
.track-scroll-area {
  flex: 1;
  overflow: auto;
  min-height: 0;
}

.layer-bars-container {
  position: relative;
  min-height: 100%;
}

/* Playhead Visuals */
.playhead-head {
  position: absolute; top: 0; width: 2px; height: 30px;
  background: #e74c3c; z-index: 20; pointer-events: none;
}
/* Playhead triangle at top */
.playhead-head::before {
  content: '';
  position: absolute;
  top: 0;
  left: 50%;
  transform: translateX(-50%);
  width: 0;
  height: 0;
  border-left: 8px solid transparent;
  border-right: 8px solid transparent;
  border-top: 10px solid #e74c3c;
}
/* Playhead Hit Area - Invisible but wider for easier grabbing */
.playhead-hit-area {
  position: absolute; top: 0; bottom: 0; width: 24px;
  margin-left: -12px; /* Center on position */
  background: transparent;
  z-index: 30; cursor: ew-resize;
}
.playhead-hit-area:hover {
  background: rgba(231, 76, 60, 0.15); /* Slight highlight on hover */
}

.playhead-line { position: absolute; top: 0; bottom: 0; width: 1px; background: #e74c3c; pointer-events: none; z-index: 10; }
.grid-background { position: absolute; inset: 0; pointer-events: none; background-image: linear-gradient(to right, #222 1px, transparent 1px); background-size: 100px 100%; opacity: 0.3; }
</style>
