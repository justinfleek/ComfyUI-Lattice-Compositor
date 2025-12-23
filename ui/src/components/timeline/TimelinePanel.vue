<!--
  @component TimelinePanel
  @description Timeline and layer management panel for Weyl Compositor.
  Provides professional timeline with keyframe editing:
  - Composition tabs for multi-comp workflows
  - Playback controls (play, pause, loop, frame stepping)
  - Layer track list with visibility/lock toggles
  - Keyframe visualization on time ruler
  - Scrubbing and frame navigation
  - Layer creation menu (Solid, Text, Shape, Particles, etc.)

  @features
  - Playhead scrubbing and frame input
  - Zoom controls for timeline scale
  - Layer ordering (drag to reorder)
  - Property twirlers for keyframe access
  - Box/marquee selection for keyframes
  - Keyboard shortcuts (Space=play, Home=start, End=end)

  @emits openCompositionSettings - Open composition settings dialog
-->
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

          <div v-if="showAddLayerMenu" class="add-layer-menu" role="menu" aria-label="Layer types" :style="addLayerMenuStyle">
            <button @mousedown="addLayer('solid')" role="menuitem"><span class="icon" aria-hidden="true">■</span> Solid</button>
            <button @mousedown="addLayer('text')" role="menuitem"><span class="icon" aria-hidden="true">T</span> Text</button>
            <button @mousedown="addLayer('shape')" role="menuitem"><span class="icon" aria-hidden="true">◇</span> Shape</button>
            <button @mousedown="addLayer('spline')" role="menuitem"><span class="icon" aria-hidden="true">〰</span> Spline</button>
            <button @mousedown="addLayer('path')" role="menuitem"><span class="icon" aria-hidden="true">⤳</span> Path</button>
            <button @mousedown="addLayer('particles')" role="menuitem"><PhSparkle class="icon" aria-hidden="true" /> Particles</button>
            <button @mousedown="addLayer('control')" role="menuitem"><span class="icon" aria-hidden="true">□</span> Control</button>
            <button @mousedown="addLayer('camera')" role="menuitem"><PhCamera class="icon" aria-hidden="true" /> Camera</button>
            <button @mousedown="addLayer('light')" role="menuitem"><PhLightbulb class="icon" aria-hidden="true" /> Light</button>
            <button @mousedown="addLayer('video')" role="menuitem"><PhFilmStrip class="icon" aria-hidden="true" /> Video</button>
            <button @mousedown="addLayer('model')" role="menuitem"><PhCube class="icon" aria-hidden="true" /> 3D Model</button>
            <button @mousedown="addLayer('pointcloud')" role="menuitem"><PhCloud class="icon" aria-hidden="true" /> Point Cloud</button>
            <button @mousedown="addLayer('depth')" role="menuitem"><PhWaves class="icon" aria-hidden="true" /> Depth Map</button>
            <button @mousedown="addLayer('normal')" role="menuitem"><PhCompass class="icon" aria-hidden="true" /> Normal Map</button>
            <button @mousedown="addLayer('audio')" role="menuitem"><PhSpeakerHigh class="icon" aria-hidden="true" /> Audio</button>
            <button @mousedown="addLayer('generated')" role="menuitem"><PhRobot class="icon" aria-hidden="true" /> AI Generated</button>
            <button @mousedown="addLayer('group')" role="menuitem"><PhFolder class="icon" aria-hidden="true" /> Group</button>
          </div>
        </div>

        <div class="tool-group">
           <button class="delete-btn" @click="deleteSelectedLayers" :disabled="store.selectedLayerIds.length === 0" aria-label="Delete selected layers"><PhTrash /></button>
        </div>

        <div class="tool-group">
          <button class="comp-settings-btn" @click="emit('openCompositionSettings')" title="Composition Settings (Ctrl+K)">
            <PhGearSix /> Comp Settings
          </button>
          <button class="ai-btn" @click="emit('openPathSuggestion')" title="AI Path Suggestion">
            <PhSparkle /> AI
          </button>
        </div>

        <div class="tool-group">
          <OnionSkinControls />
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
            <span class="header-icon" title="Toggle Layer Visibility (V)"><PhEye :size="14" /></span>
            <span class="header-icon" title="Toggle Audio Mute"><PhSpeakerHigh :size="14" /></span>
            <span class="header-icon" title="Isolate Layer - Show only this layer">●</span>
            <span class="header-icon" title="Lock Layer - Prevent selection and editing (Ctrl+L)"><PhLock :size="14" /></span>
          </div>
          <!-- Layer info -->
          <div class="col-header col-number" title="Layer Number (stacking order, 1 = top)">#</div>
          <div class="col-header col-name" title="Layer Name (Enter to rename)">Source Name</div>
          <!-- Switches -->
          <div class="col-header col-switches">
            <span
              class="header-icon clickable"
              :class="{ active: store.hideMinimizedLayers }"
              title="Hide Minimized Layers - Filter view"
              @click="store.toggleHideMinimizedLayers()"
            ><PhEyeSlash :size="14" /></span>
            <span class="header-icon" title="Continuously Rasterize / Collapse Transformation"><PhSun :size="14" /></span>
            <span class="header-icon" title="Layer Quality - Draft (fast) / Full (anti-aliased)">◐</span>
            <span class="header-icon" title="Toggle Effects - Enable/disable effect stack">fx</span>
            <span class="header-icon" title="Frame Blending - Smooth slow motion playback">⊞</span>
            <span class="header-icon" title="Motion Blur - Requires composition motion blur enabled">◔</span>
            <span class="header-icon" title="Effect Layer - Apply effects to layers below">◐</span>
            <span class="header-icon" title="3D Layer - Enable depth and camera interaction">⬡</span>
          </div>
          <div class="col-header col-parent" title="Parent & Link - Link transforms to another layer">Parent & Link</div>
        </div>
        <div class="sidebar-scroll-area" ref="sidebarScrollRef" @scroll="syncSidebarScroll"
             @dragover.prevent="onDragOver"
             @dragleave="onDragLeave"
             @drop="onDrop"
             :class="{ 'drag-over': isDragOver }">
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

             <!-- Render Range Bar -->
             <div v-if="hasWorkArea" class="work-area-bar" :style="workAreaStyle"
                  @dblclick.stop="clearWorkArea"
                  title="Render Range (B/N to set, double-click to clear)">
               <div class="work-area-handle work-area-handle-left"
                    @mousedown.stop="startWorkAreaDrag('start', $event)"></div>
               <div class="work-area-handle work-area-handle-right"
                    @mousedown.stop="startWorkAreaDrag('end', $event)"></div>
             </div>

             <div class="playhead-head" :style="{ left: playheadPositionPct + '%' }"></div>
             <div class="playhead-hit-area"
                  :style="{ left: playheadPositionPct + '%' }"
                  @mousedown.stop="startRulerScrub"
             ></div>
          </div>
        </div>

        <!-- Layer bars scroll both horizontally and vertically -->
        <div class="track-scroll-area" ref="trackScrollRef" @scroll="handleTrackScroll"
             @dragover.prevent="onDragOver"
             @dragleave="onDragLeave"
             @drop="onDrop"
             :class="{ 'drag-over': isDragOver }"
        >
          <div class="layer-bars-container" :style="{ width: computedWidthStyle }"
               @dragover.prevent="onDragOver"
               @drop="onDrop">
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

             <!-- Audio Track with Waveform -->
             <AudioTrack
               v-if="audioStore.audioBuffer"
               :audioBuffer="audioStore.audioBuffer"
               :analysis="audioStore.audioAnalysis"
               :peakData="audioStore.peakData"
               :currentFrame="store.currentFrame"
               :totalFrames="store.frameCount"
               :fps="store.fps"
               :height="60"
               @seek="handleAudioSeek"
             />

             <div class="playhead-line" :style="{ left: playheadPositionPct + '%' }"></div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, watch, nextTick, inject, type Ref } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { useAudioStore } from '@/stores/audioStore';
import { usePlaybackStore } from '@/stores/playbackStore';
import EnhancedLayerTrack from './EnhancedLayerTrack.vue';
import CompositionTabs from './CompositionTabs.vue';
import OnionSkinControls from './OnionSkinControls.vue';
import AudioTrack from './AudioTrack.vue';
import { findNearestSnap } from '@/services/timelineSnap';
import {
  PhSparkle, PhCamera, PhLightbulb, PhSpeakerHigh, PhFolder, PhGearSix,
  PhTrash, PhEye, PhLock, PhSun, PhRobot, PhFilmStrip, PhCube,
  PhCloud, PhWaves, PhCompass, PhEyeSlash
} from '@phosphor-icons/vue';

// Inject work area state from WorkspaceLayout
const workAreaStart = inject<Ref<number | null>>('workAreaStart', ref(null));
const workAreaEnd = inject<Ref<number | null>>('workAreaEnd', ref(null));

const emit = defineEmits<{
  (e: 'openCompositionSettings'): void;
  (e: 'openPathSuggestion'): void;
}>();

const store = useCompositorStore();
const audioStore = useAudioStore();
const playbackStore = usePlaybackStore();
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
const isDragOver = ref(false);

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

// Work area computed properties
const hasWorkArea = computed(() => workAreaStart.value !== null && workAreaEnd.value !== null);
const workAreaLeftPct = computed(() => {
  if (workAreaStart.value === null) return 0;
  return (workAreaStart.value / store.frameCount) * 100;
});
const workAreaWidthPct = computed(() => {
  if (workAreaStart.value === null || workAreaEnd.value === null) return 100;
  const start = Math.min(workAreaStart.value, workAreaEnd.value);
  const end = Math.max(workAreaStart.value, workAreaEnd.value);
  return ((end - start) / store.frameCount) * 100;
});
const workAreaStyle = computed(() => {
  if (!hasWorkArea.value) return { display: 'none' };
  const start = Math.min(workAreaStart.value!, workAreaEnd.value!);
  const end = Math.max(workAreaStart.value!, workAreaEnd.value!);
  return {
    left: (start / store.frameCount) * 100 + '%',
    width: ((end - start) / store.frameCount) * 100 + '%'
  };
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

// Compute position for fixed dropdown menu
const addLayerMenuStyle = computed(() => {
  if (!showAddLayerMenu.value || !addLayerContainer.value) {
    return {};
  }
  const rect = addLayerContainer.value.getBoundingClientRect();
  return {
    position: 'fixed',
    left: `${rect.left}px`,
    bottom: `${window.innerHeight - rect.top + 8}px`,
  };
});

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
    if (type === 'spline' || type === 'shape' || type === 'path') {
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

// Handle audio track seek
function handleAudioSeek(frame: number) {
  store.setFrame(frame);
  // Also trigger audio scrub for feedback
  audioStore.scrubAudio(frame, store.fps);
}

// ============================================================
// DRAG & DROP FROM PROJECT PANEL
// ============================================================
function onDragOver(event: DragEvent) {
  if (event.dataTransfer?.types.includes('application/project-item')) {
    isDragOver.value = true;
  }
}

function onDragLeave() {
  isDragOver.value = false;
}

function onDrop(event: DragEvent) {
  event.preventDefault();
  event.stopPropagation();
  isDragOver.value = false;

  const data = event.dataTransfer?.getData('application/project-item');
  console.log('[TimelinePanel] onDrop called, data:', data);
  if (!data) {
    console.log('[TimelinePanel] No project-item data found');
    return;
  }

  try {
    const item = JSON.parse(data) as {
      id: string;
      name: string;
      type: 'composition' | 'footage' | 'solid' | 'audio' | 'folder';
      width?: number;
      height?: number;
    };

    console.log('[TimelinePanel] Dropped item:', item);

    // Handle different item types
    if (item.type === 'composition') {
      // Create a precomp layer
      const layer = store.createLayer('precomp', item.name);
      if (layer) {
        (layer.data as any).compositionId = item.id;
        store.selectLayer(layer.id);
        console.log('[TimelinePanel] Created precomp layer for composition:', item.name);
      }
    } else if (item.type === 'footage') {
      // For footage, check if it's an existing asset
      const asset = store.project.assets[item.id];
      if (asset) {
        if (asset.type === 'video') {
          const layer = store.createLayer('video', item.name);
          if (layer) {
            (layer.data as any).assetId = item.id;
            store.selectLayer(layer.id);
            console.log('[TimelinePanel] Created video layer from asset:', item.name);
          }
        } else if (asset.type === 'image') {
          // Helper function to resize comp and create layer
          const resizeAndCreateLayer = (width: number, height: number) => {
            const compId = store.activeCompositionId;
            if (compId && width > 0 && height > 0) {
              console.log('[TimelinePanel] Resizing comp', compId, 'to', width, 'x', height);
              store.updateCompositionSettings(compId, { width, height });
              console.log('[TimelinePanel] Comp resized. New size:', store.width, 'x', store.height);
            }

            const layer = store.createLayer('image', item.name);
            if (layer) {
              (layer.data as any).assetId = item.id;
              (layer.data as any).source = asset.data;
              store.selectLayer(layer.id);
              console.log('[TimelinePanel] Created image layer:', layer.id);
            }
          };

          // If asset already has dimensions, use them directly
          if (asset.width && asset.height && asset.width > 0 && asset.height > 0) {
            console.log('[TimelinePanel] Using cached dimensions:', asset.width, 'x', asset.height);
            resizeAndCreateLayer(asset.width, asset.height);
          } else {
            // Load image to get dimensions
            const img = new Image();
            img.onload = () => {
              console.log('[TimelinePanel] Image loaded:', img.naturalWidth, 'x', img.naturalHeight);
              resizeAndCreateLayer(img.naturalWidth, img.naturalHeight);
            };
            img.onerror = (e) => {
              console.error('[TimelinePanel] Failed to load image:', asset.data, e);
              // Still create the layer even if image fails to load for dimensions
              const layer = store.createLayer('image', item.name);
              if (layer) {
                (layer.data as any).assetId = item.id;
                (layer.data as any).source = asset.data;
                store.selectLayer(layer.id);
              }
            };
            img.src = asset.data;
          }
        }
      } else {
        // Generic footage - create image layer
        const layer = store.createLayer('image', item.name);
        if (layer) {
          store.selectLayer(layer.id);
          console.log('[TimelinePanel] Created image layer:', item.name);
        }
      }
    } else if (item.type === 'solid') {
      const layer = store.createLayer('solid', item.name);
      if (layer) {
        store.selectLayer(layer.id);
        console.log('[TimelinePanel] Created solid layer:', item.name);
      }
    } else if (item.type === 'audio') {
      // Audio tracks don't create layers, they go to the audio panel
      console.log('[TimelinePanel] Audio dropped - should be loaded via AudioPanel');
    }
  } catch (error) {
    console.error('[TimelinePanel] Failed to parse dropped item:', error);
  }
}
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

  // Draw beat markers (onsets)
  if (audioStore.audioAnalysis?.onsets) {
    ctx.strokeStyle = 'rgba(255, 193, 7, 0.6)'; // Gold/amber for beats
    ctx.lineWidth = 1;
    for (const onset of audioStore.audioAnalysis.onsets) {
      const x = (onset / frameCount) * width;
      ctx.beginPath();
      ctx.moveTo(x, 20);
      ctx.lineTo(x, 30);
      ctx.stroke();
    }
    ctx.lineWidth = 1;
  }

  // Draw peak markers (diamonds at top)
  if (audioStore.peakData?.indices) {
    ctx.fillStyle = 'rgba(255, 107, 107, 0.9)'; // Red for peaks
    for (const peakFrame of audioStore.peakData.indices) {
      const x = (peakFrame / frameCount) * width;
      // Draw small diamond
      ctx.beginPath();
      ctx.moveTo(x, 3);
      ctx.lineTo(x + 4, 7);
      ctx.lineTo(x, 11);
      ctx.lineTo(x - 4, 7);
      ctx.closePath();
      ctx.fill();
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

  // Track if this is an audio scrub (Ctrl held at start)
  const isAudioScrub = e.ctrlKey || e.metaKey;

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

    const frame = Math.round(f);
    store.setFrame(frame);

    // Ctrl+drag: Audio scrub - play short audio snippet at current position
    if (isAudioScrub || ev.ctrlKey || ev.metaKey) {
      audioStore.scrubAudio(frame, store.fps);
    }
  };

  update(e);
  window.addEventListener('mousemove', update);
  window.addEventListener('mouseup', () => {
    window.removeEventListener('mousemove', update);
    // Stop any audio scrub when mouse is released
    if (isAudioScrub) {
      audioStore.stopAudio();
    }
  }, { once: true });
}

function startResize(e: MouseEvent) {
  const startX = e.clientX;
  const startW = sidebarWidth.value;
  const onMove = (ev: MouseEvent) => { sidebarWidth.value = Math.max(450, startW + (ev.clientX - startX)); };
  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', () => window.removeEventListener('mousemove', onMove), { once: true });
}

// Work Area functions
function clearWorkArea() {
  workAreaStart.value = null;
  workAreaEnd.value = null;
  playbackStore.clearWorkArea();
}

function startWorkAreaDrag(handle: 'start' | 'end', e: MouseEvent) {
  const rect = rulerCanvas.value!.getBoundingClientRect();
  const scrollX = rulerScrollRef.value?.scrollLeft || trackScrollRef.value?.scrollLeft || 0;

  const update = (ev: MouseEvent) => {
    const currentScrollX = rulerScrollRef.value?.scrollLeft || trackScrollRef.value?.scrollLeft || 0;
    const x = (ev.clientX - rect.left) + currentScrollX;
    let frame = Math.round(Math.max(0, Math.min(store.frameCount - 1, (x / timelineWidth.value) * store.frameCount)));

    if (handle === 'start') {
      // Clamp start to be before end
      if (workAreaEnd.value !== null) {
        frame = Math.min(frame, workAreaEnd.value - 1);
      }
      workAreaStart.value = frame;
    } else {
      // Clamp end to be after start
      if (workAreaStart.value !== null) {
        frame = Math.max(frame, workAreaStart.value + 1);
      }
      workAreaEnd.value = frame;
    }
  };

  update(e);
  window.addEventListener('mousemove', update);
  window.addEventListener('mouseup', () => {
    window.removeEventListener('mousemove', update);
    // Sync final work area to playbackStore
    playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
  }, { once: true });
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

watch(() => [
  computedWidthStyle.value,
  zoomPercent.value,
  store.frameCount,
  audioStore.audioAnalysis,
  audioStore.peakData
], () => nextTick(drawRuler));
</script>

<style scoped>
.timeline-panel { display: flex; flex-direction: column; height: 100%; background: var(--weyl-surface-1, #0f0f0f); color: var(--weyl-text-primary, #eee); font-family: var(--weyl-font-sans, 'Segoe UI', sans-serif); font-size: 13px; user-select: none; }
.timeline-header { height: 40px; background: var(--weyl-surface-2, #161616); border-bottom: 1px solid var(--weyl-border-subtle, #1a1a1a); display: flex; justify-content: space-between; padding: 0 10px; align-items: center; z-index: 20; flex-shrink: 0; }
.header-left, .header-center, .header-right { display: flex; gap: 12px; align-items: center; }
.tool-group { display: flex; gap: 8px; align-items: center; }

/* SMPTE Timecode display */
.timecode { font-family: var(--weyl-font-mono, 'Consolas', 'Courier New', monospace); font-size: 16px; color: var(--weyl-accent, #8B5CF6); font-weight: bold; letter-spacing: 1px; }

/* Menus */
.add-layer-wrapper { position: relative; }
.add-layer-menu {
  /* Position set dynamically via style binding */
  background: var(--weyl-surface-2, #161616);
  border: 1px solid var(--weyl-border-default, #2a2a2a);
  border-radius: 6px;
  display: flex;
  flex-direction: column;
  min-width: 160px;
  max-height: 320px;
  overflow-y: auto;
  z-index: 100000; /* Very high to ensure visibility above viewport */
  box-shadow: 0 -8px 24px rgba(0,0,0,0.6);
}
.add-layer-menu button {
  text-align: left;
  padding: 10px 14px;
  border: none;
  background: transparent;
  color: var(--weyl-text-primary, #ddd);
  cursor: pointer;
  border-bottom: 1px solid var(--weyl-border-subtle, #1a1a1a);
  font-size: 13px;
  display: flex;
  align-items: center;
  gap: 8px;
}
.add-layer-menu button:last-child { border-bottom: none; }
.add-layer-menu button:hover { background: var(--weyl-accent, #8B5CF6); color: white; }
.add-layer-menu button:first-child { border-radius: 5px 5px 0 0; }
.add-layer-menu button:last-child { border-radius: 0 0 5px 5px; }
.add-layer-btn { padding: 6px 12px; background: var(--weyl-surface-3, #1e1e1e); border: 1px solid var(--weyl-border-default, #2a2a2a); color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: bold; }
.add-layer-btn:hover, .add-layer-btn.active { background: var(--weyl-surface-4, #262626); }

.comp-settings-btn { padding: 6px 14px; background: var(--weyl-accent-muted, rgba(139, 92, 246, 0.15)); border: 1px solid var(--weyl-accent, #8B5CF6); color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: 500; }
.comp-settings-btn:hover { background: var(--weyl-accent, #8B5CF6); }
.ai-btn { padding: 6px 12px; background: var(--weyl-accent-gradient, linear-gradient(135deg, #8B5CF6, #A78BFA)); border: none; color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: 500; }
.ai-btn:hover { filter: brightness(1.1); }

.timeline-content { flex: 1; display: flex; overflow: hidden; position: relative; min-height: 0; }
.timeline-sidebar { background: var(--weyl-surface-1, #0f0f0f); border-right: 1px solid var(--weyl-border-subtle, #1a1a1a); display: flex; flex-direction: column; flex-shrink: 0; z-index: 10; }
.sidebar-header-row { height: 30px; background: var(--weyl-surface-2, #161616); display: flex; align-items: center; border-bottom: 1px solid var(--weyl-border-subtle, #1a1a1a); }
.col-header { font-size: 12px; color: var(--weyl-text-muted, #6B7280); display: flex; align-items: center; }
.col-header.col-av-features {
  display: flex;
  gap: 0;
  border-right: 1px solid var(--weyl-border-subtle, #1a1a1a);
  padding: 0 2px;
}
.col-header.col-number { width: 20px; justify-content: center; }
.col-header.col-name { flex: 1; padding-left: 8px; font-weight: 500; }
.col-header.col-switches {
  display: flex;
  gap: 0;
  border-left: 1px solid var(--weyl-border-subtle, #1a1a1a);
  padding: 0 2px;
}
.col-header.col-parent { min-width: 80px; border-left: 1px solid var(--weyl-border-subtle, #1a1a1a); padding: 0 8px; }
.header-icon { display: inline-flex; justify-content: center; align-items: center; width: 22px; height: 28px; font-size: 12px; color: var(--weyl-text-muted, #6B7280); cursor: default; }
.header-icon.clickable { cursor: pointer; transition: color 0.15s; }
.header-icon.clickable:hover { color: var(--weyl-text-secondary, #9CA3AF); }
.header-icon.clickable.active { color: var(--weyl-accent, #8B5CF6); }
.sidebar-scroll-area { flex: 1; overflow-y: auto; overflow-x: hidden; }
.sidebar-scroll-area.drag-over {
  background-color: var(--weyl-accent-muted, rgba(139, 92, 246, 0.15));
  outline: 2px dashed var(--weyl-accent, #8B5CF6);
  outline-offset: -2px;
}

.sidebar-resizer { width: 4px; background: var(--weyl-surface-0, #080808); cursor: col-resize; flex-shrink: 0; z-index: 15; }
.sidebar-resizer:hover { background: var(--weyl-accent, #8B5CF6); }

.track-viewport {
  flex: 1;
  display: flex;
  flex-direction: column;
  overflow: hidden;
  position: relative;
  background: var(--weyl-surface-0, #080808);
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
  background: var(--weyl-surface-2, #161616);
  border-bottom: 1px solid var(--weyl-border-subtle, #1a1a1a);
  cursor: pointer;
  z-index: 10;
}

/* Work Area Bar (Render Range) */
.work-area-bar {
  position: absolute;
  top: 0;
  height: 100%;
  background: var(--weyl-accent-muted, rgba(139, 92, 246, 0.25));
  border-left: 2px solid var(--weyl-accent, #8B5CF6);
  border-right: 2px solid var(--weyl-accent, #8B5CF6);
  z-index: 5;
  cursor: move;
  box-sizing: border-box;
}
.work-area-bar:hover {
  background: rgba(139, 92, 246, 0.35);
}
.work-area-handle {
  position: absolute;
  top: 0;
  width: 10px;
  height: 100%;
  cursor: ew-resize;
  z-index: 6;
}
.work-area-handle-left {
  left: -5px;
}
.work-area-handle-right {
  right: -5px;
}
.work-area-handle:hover {
  background: rgba(139, 92, 246, 0.5);
}

/* Track scroll area - scrolls both horizontally and vertically */
.track-scroll-area {
  flex: 1;
  overflow: auto;
  min-height: 0;
  transition: background-color 0.15s ease;
}

.track-scroll-area.drag-over {
  background-color: var(--weyl-accent-muted, rgba(139, 92, 246, 0.15));
  outline: 2px dashed var(--weyl-accent, #8B5CF6);
  outline-offset: -2px;
}

.layer-bars-container {
  position: relative;
  min-height: 100%;
}

/* Playhead Visuals - Purple accent */
.playhead-head {
  position: absolute; top: 0; width: 2px; height: 30px;
  background: var(--weyl-accent, #8B5CF6); z-index: 20; pointer-events: none;
  box-shadow: 0 0 8px var(--weyl-accent-glow, rgba(139, 92, 246, 0.3));
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
  border-top: 10px solid var(--weyl-accent, #8B5CF6);
}
/* Playhead Hit Area - Invisible but wider for easier grabbing */
.playhead-hit-area {
  position: absolute; top: 0; bottom: 0; width: 24px;
  margin-left: -12px; /* Center on position */
  background: transparent;
  z-index: 30; cursor: ew-resize;
}
.playhead-hit-area:hover {
  background: var(--weyl-accent-muted, rgba(139, 92, 246, 0.15));
}

.playhead-line { position: absolute; top: 0; bottom: 0; width: 2px; background: var(--weyl-accent, #8B5CF6); pointer-events: none; z-index: 10; box-shadow: 0 0 8px var(--weyl-accent-glow, rgba(139, 92, 246, 0.3)); }
.grid-background { position: absolute; inset: 0; pointer-events: none; background-image: linear-gradient(to right, var(--weyl-border-subtle, #1a1a1a) 1px, transparent 1px); background-size: 100px 100%; opacity: 0.3; }
</style>
