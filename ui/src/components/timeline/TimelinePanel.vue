<template>
  <div class="timeline-panel" tabindex="0" @keydown="handleKeydown">
    <div class="timeline-header">
      <div class="header-left">
        <span class="timeline-title">Timeline</span>
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
            title="Add New Layer"
          >
            <span class="icon">+</span> Layer
          </button>
          <div v-if="showAddLayerMenu" class="add-layer-menu">
            <button @click="addLayer('solid')"><span class="icon">■</span> Solid</button>
            <button @click="addLayer('text')"><span class="icon">T</span> Text</button>
            <button @click="addLayer('spline')"><span class="icon">~</span> Shape</button>
            <button @click="addLayer('null')"><span class="icon">□</span> Null</button>
            <button @click="addLayer('camera')"><span class="icon">📷</span> Camera</button>
            <button @click="addLayer('light')"><span class="icon">💡</span> Light</button>
            <button @click="addLayer('video')"><span class="icon">🎞️</span> Video</button>
          </div>
        </div>
        <div class="tool-group">
           <button class="delete-btn" @click="deleteSelectedLayers" :disabled="store.selectedLayerIds.length === 0">🗑️</button>
        </div>
      </div>

      <div class="header-right">
        <input type="range" min="1" max="50" v-model.number="pixelsPerFrame" class="zoom-slider" title="Zoom" />
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
        <div class="sidebar-scroll-area">
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

      <div class="track-viewport" ref="trackViewportRef" @scroll="syncScrollX">
        <div class="track-scroll-content" :style="{ width: trackContentWidth + 'px' }">
          <div class="time-ruler" @mousedown="startRulerScrub">
             <canvas ref="rulerCanvas" height="30"></canvas>
             <div class="playhead-head" :style="{ left: playheadPosition + 'px' }"></div>
          </div>

          <div class="layer-bars-container">
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

const store = useCompositorStore();
const pixelsPerFrame = ref(10);
const sidebarWidth = ref(450); // Increased default width for readability
const expandedLayers = ref<Record<string, boolean>>({});
const showAddLayerMenu = ref(false);
const addLayerContainer = ref<null | HTMLElement>(null);
const trackViewportRef = ref<HTMLElement | null>(null);
const rulerCanvas = ref<HTMLCanvasElement | null>(null);
const viewportWidth = ref(1920); // Reactive viewport width - updated by ResizeObserver

const filteredLayers = computed(() => store.layers || []);
const playheadPosition = computed(() => store.currentFrame * pixelsPerFrame.value);

// CRITICAL FIX: Width is exactly max(viewport, content) - using reactive viewportWidth
const trackContentWidth = computed(() => {
  const frameWidth = (store.frameCount + 50) * pixelsPerFrame.value;
  return Math.max(frameWidth, viewportWidth.value);
});

const sidebarGridStyle = computed(() => ({
  display: 'grid',
  gridTemplateColumns: '24px 24px 30px 24px 24px 24px 1fr 70px 70px',
  alignItems: 'center',
  height: '32px', // Taller rows
  width: '100%',
  boxSizing: 'border-box'
}));

// Actions
function toggleAddLayerMenu() { showAddLayerMenu.value = !showAddLayerMenu.value; }
function addLayer(type: string) {
  if(type === 'text') store.createTextLayer();
  else if(type === 'video') store.createLayer('video');
  else store.createLayer(type as any);
  showAddLayerMenu.value = false;
}
function handleToggleExpand(id: string, val: boolean) { expandedLayers.value[id] = val; }
function selectLayer(id: string) { store.selectLayer(id); }
function updateLayer(id: string, u: any) { store.updateLayer(id, u); }
function deleteSelectedLayers() { store.selectedLayerIds.forEach(id => store.deleteLayer(id)); }
function setFrame(e: Event) { store.setFrame(parseInt((e.target as HTMLInputElement).value) || 0); }
function togglePlayback() { store.togglePlayback(); }
function goToStart() { store.goToStart(); }
function goToEnd() { store.goToEnd(); }

// Ruler Draw
function drawRuler() {
  const cvs = rulerCanvas.value;
  if (!cvs) return;
  const ctx = cvs.getContext('2d');
  if (!ctx) return;

  cvs.width = trackContentWidth.value;
  cvs.height = 30;

  ctx.fillStyle = '#222';
  ctx.fillRect(0, 0, cvs.width, cvs.height);
  ctx.strokeStyle = '#666';
  ctx.fillStyle = '#aaa';
  ctx.font = '11px sans-serif';

  const ppf = pixelsPerFrame.value;
  const step = ppf < 5 ? 20 : 10;

  for(let f=0; f<=store.frameCount + 50; f++) {
    const x = f * ppf;
    if(f % step === 0) {
      ctx.beginPath(); ctx.moveTo(x, 15); ctx.lineTo(x, 30); ctx.stroke();
      ctx.fillText(String(f), x + 2, 12);
    } else if (f % (step/2) === 0) {
      ctx.beginPath(); ctx.moveTo(x, 22); ctx.lineTo(x, 30); ctx.stroke();
    }
  }
  ctx.beginPath(); ctx.moveTo(0, 29.5); ctx.lineTo(cvs.width, 29.5); ctx.stroke();
}

function startRulerScrub(e: MouseEvent) {
  const update = (ev: MouseEvent) => {
    const rect = rulerCanvas.value!.getBoundingClientRect();
    const x = ev.clientX - rect.left;
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

function syncScrollX(e: Event) { /* Sync logic if needed later */ }

function handleKeydown(e: KeyboardEvent) {
  if (e.target instanceof HTMLInputElement || e.target instanceof HTMLTextAreaElement) return;
  if (e.code === 'Space') { e.preventDefault(); togglePlayback(); }
}

watch(() => [trackContentWidth.value, pixelsPerFrame.value], () => nextTick(drawRuler));

// ResizeObserver to keep timeline width correct
let resizeObserver: ResizeObserver | null = null;

onMounted(() => {
  drawRuler();

  // Track window clicks to close menu
  window.addEventListener('mousedown', (e) => {
    if (addLayerContainer.value && !addLayerContainer.value.contains(e.target as Node)) {
      showAddLayerMenu.value = false;
    }
  });

  // Observe track viewport size changes
  if (trackViewportRef.value) {
    resizeObserver = new ResizeObserver((entries) => {
      for (const entry of entries) {
        viewportWidth.value = entry.contentRect.width;
      }
    });
    resizeObserver.observe(trackViewportRef.value);
  }
});

onUnmounted(() => {
  if (resizeObserver) resizeObserver.disconnect();
});
</script>

<style scoped>
.timeline-panel { display: flex; flex-direction: column; height: 100%; background: #111; color: #eee; font-family: 'Segoe UI', sans-serif; font-size: 13px; }
.timeline-header { height: 40px; background: #2a2a2a; border-bottom: 1px solid #000; display: flex; justify-content: space-between; padding: 0 10px; align-items: center; z-index: 20; position: relative; }
.header-left, .header-center, .header-right { display: flex; gap: 10px; align-items: center; }
.add-layer-wrapper { position: relative; }
.add-layer-menu { position: absolute; top: 100%; left: 0; background: #333; z-index: 9999; border: 1px solid #000; display: flex; flex-direction: column; min-width: 140px; box-shadow: 0 4px 8px rgba(0,0,0,0.5); }
.add-layer-menu button { text-align: left; padding: 10px; border: none; background: transparent; color: #eee; cursor: pointer; border-bottom: 1px solid #444; }
.add-layer-menu button:hover { background: #4a90d9; color: white; }
.add-layer-btn { padding: 6px 12px; background: #444; border: 1px solid #555; color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: bold; }
.add-layer-btn:hover, .add-layer-btn.active { background: #555; }

.timeline-content { flex: 1; display: flex; overflow: hidden; }
.timeline-sidebar { background: #1e1e1e; border-right: 1px solid #000; display: flex; flex-direction: column; flex-shrink: 0; }
.sidebar-header-row { height: 30px; background: #252525; display: flex; align-items: center; border-bottom: 1px solid #000; font-weight: bold; padding-left: 4px; }
.col-header { padding: 0 4px; font-size: 12px; color: #aaa; }
.sidebar-scroll-area { flex: 1; overflow-y: auto; overflow-x: hidden; }

.sidebar-resizer { width: 4px; background: #111; cursor: col-resize; flex-shrink: 0; }
.sidebar-resizer:hover { background: #4a90d9; }

.track-viewport { flex: 1; display: flex; flex-direction: column; overflow-x: auto; overflow-y: hidden; position: relative; background: #151515; }
.track-scroll-content { min-height: 100%; position: relative; display: flex; flex-direction: column; }
.time-ruler { height: 30px; position: relative; background: #222; border-bottom: 1px solid #000; cursor: pointer; }
.layer-bars-container { flex: 1; position: relative; }
.playhead-head { position: absolute; top: 0; width: 2px; height: 30px; background: #e74c3c; z-index: 10; pointer-events: none; }
.playhead-line { position: absolute; top: 0; bottom: 0; width: 1px; background: #e74c3c; pointer-events: none; z-index: 10; }
.grid-background { position: absolute; inset: 0; pointer-events: none; background-image: linear-gradient(to right, #222 1px, transparent 1px); background-size: 100px 100%; opacity: 0.3; }
</style>
