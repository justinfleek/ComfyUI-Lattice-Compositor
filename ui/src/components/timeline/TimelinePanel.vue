<template>
  <div class="timeline-panel" tabindex="0" @keydown="handleKeydown">
    <!-- Composition Tabs -->
    <CompositionTabs @newComposition="emit('openCompositionSettings')" />

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
          >
            <span class="icon">+</span> Layer
          </button>

          <div v-if="showAddLayerMenu" class="add-layer-menu">
            <button @mousedown="addLayer('solid')"><span class="icon">■</span> Solid</button>
            <button @mousedown="addLayer('text')"><span class="icon">T</span> Text</button>
            <button @mousedown="addLayer('spline')"><span class="icon">~</span> Shape</button>
            <button @mousedown="addLayer('null')"><span class="icon">□</span> Null</button>
            <button @mousedown="addLayer('camera')"><span class="icon">📷</span> Camera</button>
            <button @mousedown="addLayer('light')"><span class="icon">💡</span> Light</button>
            <button @mousedown="addLayer('video')"><span class="icon">🎞️</span> Video</button>
          </div>
        </div>

        <div class="tool-group">
           <button class="delete-btn" @click="deleteSelectedLayers" :disabled="store.selectedLayerIds.length === 0">🗑️</button>
        </div>
      </div>

      <div class="header-right">
        <input type="range" min="0.1" max="50" step="0.1" v-model.number="pixelsPerFrame" class="zoom-slider" title="Zoom Timeline" />
      </div>
    </div>

    <div class="timeline-content">
      <div class="timeline-sidebar" :style="{ width: sidebarWidth + 'px' }">
        <div class="sidebar-header-row">
          <div class="col-header col-arrow"></div>
          <div class="col-header col-name">Layer Name</div>
          <div class="col-header col-mode">Mode</div>
          <div class="col-header col-parent">Parent</div>
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

             <div class="playhead-head" :style="{ left: playheadPosition + 'px' }"></div>
             <div class="playhead-hit-area"
                  :style="{ left: playheadPosition + 'px' }"
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
                :pixelsPerFrame="pixelsPerFrame"
                :isExpandedExternal="expandedLayers[layer.id]"
                @select="selectLayer"
                @updateLayer="updateLayer"
              />

             <div class="playhead-line" :style="{ left: playheadPosition + 'px' }"></div>
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

const emit = defineEmits<{
  (e: 'openCompositionSettings'): void;
}>();

const store = useCompositorStore();
const pixelsPerFrame = ref(10);
const sidebarWidth = ref(450);
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

const filteredLayers = computed(() => store.layers || []);
const playheadPosition = computed(() => store.currentFrame * pixelsPerFrame.value);

// Width calculation - EXACT frame count, no buffer
const computedWidthStyle = computed(() => {
  const frameWidth = store.frameCount * pixelsPerFrame.value;
  // Use max of frame width or viewport to fill screen when zoomed out
  return Math.max(frameWidth, viewportWidth.value) + 'px';
});

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
  if (type === 'text') store.createTextLayer();
  else if (type === 'video') store.createLayer('video');
  else if (type === 'camera') store.createCameraLayer();
  else store.createLayer(type as any);
  showAddLayerMenu.value = false;
}

function selectLayer(id: string) { store.selectLayer(id); }
function updateLayer(id: string, u: any) { store.updateLayer(id, u); }
function deleteSelectedLayers() { store.selectedLayerIds.forEach(id => store.deleteLayer(id)); }
function setFrame(e: Event) { store.setFrame(parseInt((e.target as HTMLInputElement).value) || 0); }
function togglePlayback() { store.togglePlayback(); }
function handleToggleExpand(id: string, val: boolean) { expandedLayers.value[id] = val; }

// Format frame as timecode (HH;MM;SS;FF) like After Effects
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

  // Width is EXACT: frameCount * pixelsPerFrame (or viewport, whichever is larger)
  const frameWidth = store.frameCount * pixelsPerFrame.value;
  const width = Math.max(frameWidth, viewportWidth.value);
  cvs.width = width;
  cvs.height = 30;

  ctx.fillStyle = '#222';
  ctx.fillRect(0, 0, cvs.width, cvs.height);
  ctx.strokeStyle = '#666';
  ctx.fillStyle = '#aaa';
  ctx.font = '11px sans-serif';

  const ppf = pixelsPerFrame.value;

  // Dynamic tick step based on zoom level - ensure labels don't overlap
  // At low ppf (zoomed out), we need larger steps
  // At high ppf (zoomed in), we can show every frame
  let majorStep: number;
  let minorStep: number;

  if (ppf >= 20) {
    // Very zoomed in: show every frame
    majorStep = 1;
    minorStep = 0; // No minor ticks needed
  } else if (ppf >= 10) {
    // Zoomed in: major every 5, minor every 1
    majorStep = 5;
    minorStep = 1;
  } else if (ppf >= 5) {
    // Medium zoom: major every 10, minor every 5
    majorStep = 10;
    minorStep = 5;
  } else if (ppf >= 2) {
    // Zoomed out: major every 20, minor every 10
    majorStep = 20;
    minorStep = 10;
  } else if (ppf >= 1) {
    // Very zoomed out: major every 50, minor every 25
    majorStep = 50;
    minorStep = 25;
  } else if (ppf >= 0.5) {
    // Extremely zoomed out: major every 100, minor every 50
    majorStep = 100;
    minorStep = 50;
  } else {
    // Ultra zoomed out: major every 200, no minor ticks
    majorStep = 200;
    minorStep = 0;
  }

  // Loop EXACTLY to frameCount - no extra frames
  for (let f = 0; f <= store.frameCount; f++) {
    const x = f * ppf;

    if (f % majorStep === 0) {
      // Major Tick
      ctx.strokeStyle = '#888';
      ctx.beginPath();
      ctx.moveTo(x, 12);
      ctx.lineTo(x, 30);
      ctx.stroke();

      // Label - ensure minimum spacing between labels
      const labelText = String(f);
      const textMetrics = ctx.measureText(labelText);
      const nextLabelX = (f + majorStep) * ppf;
      const minSpacing = textMetrics.width + 20;

      // Only draw label if there's enough space
      if (nextLabelX - x >= minSpacing || f === 0 || f >= store.frameCount - majorStep) {
        ctx.fillStyle = '#ccc';
        ctx.fillText(labelText, x + 3, 10);
      }
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
    const f = Math.max(0, Math.min(store.frameCount - 1, x / pixelsPerFrame.value));
    store.setFrame(Math.round(f));
  };

  update(e);
  window.addEventListener('mousemove', update);
  window.addEventListener('mouseup', () => window.removeEventListener('mousemove', update), { once: true });
}

function startResize(e: MouseEvent) {
  const startX = e.clientX;
  const startW = sidebarWidth.value;
  const onMove = (ev: MouseEvent) => { sidebarWidth.value = Math.max(300, startW + (ev.clientX - startX)); };
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
  if (e.code === 'Space') { e.preventDefault(); togglePlayback(); }
  if (e.code === 'Delete' || e.code === 'Backspace') {
    e.preventDefault();
    deleteSelectedLayers();
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
    resizeObserver = new ResizeObserver((entries) => {
      for (const entry of entries) {
        viewportWidth.value = entry.contentRect.width;
        drawRuler(); // Redraw ruler on resize
      }
    });
    resizeObserver.observe(elementToObserve);
  }

  setTimeout(drawRuler, 100);
});

onUnmounted(() => {
  if (resizeObserver) resizeObserver.disconnect();
});

watch(() => [computedWidthStyle.value, pixelsPerFrame.value, store.frameCount], () => nextTick(drawRuler));
</script>

<style scoped>
.timeline-panel { display: flex; flex-direction: column; height: 100%; background: #111; color: #eee; font-family: 'Segoe UI', sans-serif; font-size: 13px; user-select: none; }
.timeline-header { height: 40px; background: #2a2a2a; border-bottom: 1px solid #000; display: flex; justify-content: space-between; padding: 0 10px; align-items: center; z-index: 20; flex-shrink: 0; }
.header-left, .header-center, .header-right { display: flex; gap: 10px; align-items: center; }

/* Timecode display like After Effects */
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

.timeline-content { flex: 1; display: flex; overflow: hidden; position: relative; min-height: 0; }
.timeline-sidebar { background: #1e1e1e; border-right: 1px solid #000; display: flex; flex-direction: column; flex-shrink: 0; z-index: 10; }
.sidebar-header-row { height: 30px; background: #252525; display: flex; align-items: center; border-bottom: 1px solid #000; font-weight: bold; }
.col-header { padding: 0 4px; font-size: 12px; color: #aaa; }
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
