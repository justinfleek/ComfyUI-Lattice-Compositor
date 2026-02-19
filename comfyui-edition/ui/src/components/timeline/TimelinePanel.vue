<!--
  @component TimelinePanel
  @description Timeline and layer management panel for Lattice Compositor.
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
        <span class="timecode">{{ formatTimecode(animationStore.currentFrame) }}</span>
        <div class="frame-display">
           <input type="number" :value="animationStore.currentFrame" @change="setFrame" class="frame-input" />
           <span class="fps-label">{{ projectStore.getFps() }} fps</span>
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
           <button class="delete-btn" @click="deleteSelectedLayers" :disabled="selectionStore.selectedLayerIds.length === 0" aria-label="Delete selected layers"><PhTrash /></button>
        </div>

        <div class="tool-group">
          <button class="comp-settings-btn" @click="emit('openCompositionSettings')" title="Composition Settings (Ctrl+K)">
            <PhGearSix /> Comp Settings
          </button>
          <button class="ai-btn" @click="emit('openPathSuggestion')" title="AI Path Suggestion">
            <PhSparkle /> AI
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
              :class="{ active: uiStore.hideMinimizedLayers }"
              title="Hide Minimized Layers - Filter view"
              @click="uiStore.toggleHideMinimizedLayers()"
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
            :allLayers="projectStore.getActiveCompLayers()"
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
                :frameCount="projectStore.getFrameCount()"
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
               :currentFrame="animationStore.currentFrame"
               :totalFrames="projectStore.getFrameCount()"
               :fps="projectStore.getFps()"
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
import {
  type CSSProperties,
  computed,
  inject,
  nextTick,
  onMounted,
  onUnmounted,
  type Ref,
  ref,
  watch,
} from "vue";
import { assertDefined, safeNonNegativeDefault } from "@/utils/typeGuards";
import { findNearestSnap } from "@/services/timelineSnap";
import { useAudioStore } from "@/stores/audioStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useCompositionStore } from "@/stores/compositionStore";
import { useLayerStore } from "@/stores/layerStore";
import { useParticleStore } from "@/stores/particleStore";
import { usePlaybackStore } from "@/stores/playbackStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useUIStore } from "@/stores/uiStore";
import { useCameraStore } from "@/stores/cameraStore";
import { useSegmentationStore } from "@/stores/segmentationStore";
import type { Layer } from "@/types/project";

// Inject work area state from WorkspaceLayout
const workAreaStart = inject<Ref<number | null>>("workAreaStart", ref(null));
const workAreaEnd = inject<Ref<number | null>>("workAreaEnd", ref(null));

const emit = defineEmits<{
  (e: "openCompositionSettings"): void;
  (e: "openPathSuggestion"): void;
}>();

const compositionStore = useCompositionStore();
const layerStore = useLayerStore();
const particleStore = useParticleStore();
const audioStore = useAudioStore();
const playbackStore = usePlaybackStore();
const animationStore = useAnimationStore();
const projectStore = useProjectStore();
const selectionStore = useSelectionStore();
const uiStore = useUIStore();
const cameraStore = useCameraStore();
const segmentationStore = useSegmentationStore();

// Helper function to create AnimationStoreAccess
function getAnimationStoreAccess() {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    currentFrame: animationStore.currentFrame,
    fps: projectStore.getFps(),
    frameCount: projectStore.getFrameCount(),
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// Helper function to create CompositionStoreAccess
function getCompositionStoreAccess() {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    openCompositionIds: projectStore.openCompositionIds,
    compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    switchComposition: (id: string) => compositionStore.switchComposition(getCompositionStoreAccess(), id),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// Helper function to create ParticleStoreAccess
function getParticleStoreAccess() {
  return {
    project: {
      composition: {
        width: projectStore.getWidth(),
        height: projectStore.getHeight(),
      },
      meta: projectStore.project.meta,
    },
    getActiveComp: () => projectStore.getActiveComp(),
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    createLayer: (type: Layer["type"], name?: string) => layerStore.createLayer(type, name),
  };
}
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

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
const filteredLayers = computed(() => {
  const layers = layerStore.getDisplayedLayers(uiStore.hideMinimizedLayers);
  return (layers !== null && layers !== undefined && Array.isArray(layers)) ? layers : [];
});
// Playhead position as percentage of timeline
const playheadPositionPct = computed(
  () => (animationStore.currentFrame / projectStore.getFrameCount()) * 100,
);

// Zoom calculation: 0% = fit viewport exactly, 100% = max zoom (~20 frames visible)
// At 100% zoom with 1200px viewport: 1200/80 = 15 frames visible
const MAX_PPF = 80;

const effectivePpf = computed(() => {
  // minPpf ensures full composition fits viewport at 0% zoom
  const minPpf = viewportWidth.value / projectStore.getFrameCount();
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
  return projectStore.getFrameCount() * effectivePpf.value;
});

const computedWidthStyle = computed(() => `${timelineWidth.value}px`);

// Work area computed properties
const hasWorkArea = computed(
  () => workAreaStart.value !== null && workAreaEnd.value !== null,
);
const workAreaLeftPct = computed(() => {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: workAreaStart.value ∈ number | null → number (already checked for null above)
  if (workAreaStart.value === null) return 0;
  const startValue = (typeof workAreaStart.value === "number" && Number.isFinite(workAreaStart.value)) ? workAreaStart.value : 0;
  return startValue / projectStore.getFrameCount() * 100;
});
const workAreaWidthPct = computed(() => {
  if (workAreaStart.value === null || workAreaEnd.value === null) return 100;
  const start = Math.min(workAreaStart.value, workAreaEnd.value);
  const end = Math.max(workAreaStart.value, workAreaEnd.value);
  return ((end - start) / projectStore.getFrameCount()) * 100;
});
const workAreaStyle = computed(() => {
  if (!hasWorkArea.value) return { display: "none" };
  // Type proof: workAreaStart and workAreaEnd are guaranteed non-null when hasWorkArea is true
  assertDefined(workAreaStart.value, "workAreaStart must exist when hasWorkArea is true");
  assertDefined(workAreaEnd.value, "workAreaEnd must exist when hasWorkArea is true");
  const start = Math.min(workAreaStart.value, workAreaEnd.value);
  const end = Math.max(workAreaStart.value, workAreaEnd.value);
  const frameCount = projectStore.getFrameCount();
  return {
    left: `${(start / frameCount) * 100}%`,
    width: `${((end - start) / frameCount) * 100}%`,
  };
});

const sidebarGridStyle = computed(() => ({
  display: "grid",
  gridTemplateColumns: "24px 24px 30px 24px 24px 24px 1fr 70px 70px",
  alignItems: "center",
  height: "32px",
  width: "100%",
  boxSizing: "border-box",
}));

// Actions
function toggleAddLayerMenu() {
  showAddLayerMenu.value = !showAddLayerMenu.value;
}

// Compute position for fixed dropdown menu
const addLayerMenuStyle = computed((): CSSProperties => {
  if (!showAddLayerMenu.value || !addLayerContainer.value) {
    return {};
  }
  const rect = addLayerContainer.value.getBoundingClientRect();
  return {
    position: "fixed",
    left: `${rect.left}px`,
    bottom: `${window.innerHeight - rect.top + 8}px`,
  };
});

function addLayer(type: string) {
  let newLayer: Layer | undefined;

  if (type === "text") newLayer = layerStore.createTextLayer();
  else if (type === "video") newLayer = layerStore.createLayer("video");
  else if (type === "camera") {
    const { layer: cameraLayer } = cameraStore.createCameraLayer();
    newLayer = cameraLayer;
  } else if (type === "particles") newLayer = particleStore.createParticleLayer(getParticleStoreAccess());
  else newLayer = layerStore.createLayer(type as Layer["type"]);

  showAddLayerMenu.value = false;

  // Auto-select the new layer
  if (newLayer) {
    layerStore.selectLayer(newLayer.id);

    // Activate appropriate tool based on layer type
    if (type === "spline" || type === "shape" || type === "path") {
      setTool("pen");
    } else if (type === "text") {
      setTool("text");
    } else {
      setTool("select");
    }
  }
}

function setTool(tool: "select" | "pen" | "text" | "hand" | "zoom" | "segment") {
  if (tool === "segment") {
    segmentationStore.setSegmentToolActive(true);
  } else {
    segmentationStore.setSegmentToolActive(false);
    selectionStore.setTool(tool);
    segmentationStore.clearSegmentPendingMask();
  }
}

function selectLayer(id: string) {
  layerStore.selectLayer(id);
}
function updateLayer(id: string, u: Partial<Layer>) {
  layerStore.updateLayer(id, u);
}

// Handle audio track seek
function handleAudioSeek(frame: number) {
  animationStore.setFrame(getAnimationStoreAccess(), frame);
  // Also trigger audio scrub for feedback
  audioStore.scrubAudio(frame, projectStore.getFps());
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                      // drag
// ════════════════════════════════════════════════════════════════════════════
function onDragOver(event: DragEvent) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  const types = (dataTransfer != null && typeof dataTransfer === "object" && "types" in dataTransfer && dataTransfer.types != null && Array.isArray(dataTransfer.types)) ? dataTransfer.types : undefined;
  if (types != null && types.includes("application/project-item")) {
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

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  const getData = (dataTransfer != null && typeof dataTransfer === "object" && typeof dataTransfer.getData === "function") ? dataTransfer.getData : undefined;
  const data = getData != null ? getData("application/project-item") : undefined;
  console.log("[TimelinePanel] onDrop called, data:", data);
  if (!data) {
    console.log("[TimelinePanel] No project-item data found");
    return;
  }

  try {
    const item = JSON.parse(data) as {
      id: string;
      name: string;
      type: "composition" | "footage" | "solid" | "audio" | "folder";
      width?: number;
      height?: number;
    };

    console.log("[TimelinePanel] Dropped item:", item);

    // Handle different item types
    if (item.type === "composition") {
      // Create a nested composition layer
      const layer = layerStore.createLayer("nestedComp", item.name);
      if (layer) {
        layerStore.updateLayerData(layer.id, { compositionId: item.id });
        layerStore.selectLayer(layer.id);
        console.log(
          "[TimelinePanel] Created precomp layer for composition:",
          item.name,
        );
      }
    } else if (item.type === "footage") {
      // For footage, check if it's an existing asset
      const asset = projectStore.project.assets[item.id];
      if (asset) {
        if (asset.type === "video") {
          const layer = layerStore.createLayer("video", item.name);
          if (layer) {
            layerStore.updateLayerData(layer.id, { assetId: item.id });
            layerStore.selectLayer(layer.id);
            console.log(
              "[TimelinePanel] Created video layer from asset:",
              item.name,
            );
          }
        } else if (asset.type === "image") {
          // Helper function to resize comp and create layer
          const resizeAndCreateLayer = (width: number, height: number) => {
            const compId = projectStore.activeCompositionId;
            if (compId && width > 0 && height > 0) {
              console.log(
                "[TimelinePanel] Resizing comp",
                compId,
                "to",
                width,
                "x",
                height,
              );
              compositionStore.updateCompositionSettings(getCompositionStoreAccess(), compId, { width, height });
              console.log(
                "[TimelinePanel] Comp resized. New size:",
                projectStore.getWidth(),
                "x",
                projectStore.getHeight(),
              );
            }

            const layer = layerStore.createLayer("image", item.name);
            if (layer) {
              layerStore.updateLayerData(layer.id, { assetId: item.id });
              layerStore.selectLayer(layer.id);
              console.log("[TimelinePanel] Created image layer:", layer.id);
            }
          };

          // If asset already has dimensions, use them directly
          if (
            asset.width &&
            asset.height &&
            asset.width > 0 &&
            asset.height > 0
          ) {
            console.log(
              "[TimelinePanel] Using cached dimensions:",
              asset.width,
              "x",
              asset.height,
            );
            resizeAndCreateLayer(asset.width, asset.height);
          } else {
            // Load image to get dimensions
            const img = new Image();
            img.onload = () => {
              console.log(
                "[TimelinePanel] Image loaded:",
                img.naturalWidth,
                "x",
                img.naturalHeight,
              );
              resizeAndCreateLayer(img.naturalWidth, img.naturalHeight);
            };
            img.onerror = (e) => {
              console.error(
                "[TimelinePanel] Failed to load image:",
                asset.data,
                e,
              );
              // Still create the layer even if image fails to load for dimensions
              const layer = layerStore.createLayer("image", item.name);
              if (layer) {
                layerStore.updateLayerData(layer.id, { assetId: item.id });
                layerStore.selectLayer(layer.id);
              }
            };
            img.src = asset.data;
          }
        }
      } else {
        // Generic footage - create image layer
        const layer = layerStore.createLayer("image", item.name);
        if (layer) {
          layerStore.selectLayer(layer.id);
          console.log("[TimelinePanel] Created image layer:", item.name);
        }
      }
    } else if (item.type === "solid") {
      const layer = layerStore.createLayer("solid", item.name);
      if (layer) {
        layerStore.selectLayer(layer.id);
        console.log("[TimelinePanel] Created solid layer:", item.name);
      }
    } else if (item.type === "audio") {
      // Audio tracks don't create layers, they go to the audio panel
      console.log(
        "[TimelinePanel] Audio dropped - should be loaded via AudioPanel",
      );
    }
  } catch (error) {
    console.error("[TimelinePanel] Failed to parse dropped item:", error);
  }
}
function deleteSelectedLayers() {
  layerStore.deleteSelectedLayers();
}
function setFrame(e: Event) {
  // Type proof: frame number ∈ number | NaN → number (≥ 0, frame index)
  const parsedFrame = parseInt((e.target as HTMLInputElement).value, 10);
  const frame = Number.isInteger(parsedFrame) && parsedFrame >= 0
    ? parsedFrame
    : 0;
  animationStore.setFrame(getAnimationStoreAccess(), frame);
}
function togglePlayback() {
  animationStore.togglePlayback(getAnimationStoreAccess());
}
function handleToggleExpand(id: string, val: boolean) {
  expandedLayers.value[id] = val;
}

// Format frame as timecode (HH;MM;SS;FF) SMPTE format
function formatTimecode(frame: number): string {
  const fps = projectStore.getFps();
  const totalSeconds = Math.floor(frame / fps);
  const frames = Math.floor(frame % fps);
  const seconds = totalSeconds % 60;
  const minutes = Math.floor(totalSeconds / 60) % 60;
  const hours = Math.floor(totalSeconds / 3600);

  const pad = (n: number, len: number = 2) => String(n).padStart(len, "0");
  return `${pad(hours)};${pad(minutes)};${pad(seconds)};${pad(frames)}`;
}

function drawRuler() {
  const cvs = rulerCanvas.value;
  if (!cvs) return;
  const ctx = cvs.getContext("2d");
  if (!ctx) return;

  // Width fills viewport (or larger when zoomed in)
  const width = timelineWidth.value;
  cvs.width = width;
  cvs.height = 30;

  ctx.fillStyle = "#222";
  ctx.fillRect(0, 0, cvs.width, cvs.height);
  ctx.strokeStyle = "#666";
  ctx.fillStyle = "#aaa";
  ctx.font = "11px sans-serif";

  // Calculate label step based on available space, not raw ppf
  // Ensure labels have enough room and don't overlap
  const labelMinWidth = 40; // minimum pixels between labels
  const maxLabels = Math.max(1, Math.floor(width / labelMinWidth));
  const idealStep = Math.ceil(projectStore.getFrameCount() / maxLabels);

  // Round up to a nice number for clean ruler
  const niceSteps = [1, 2, 5, 10, 20, 25, 50, 100, 200];
  const majorStep = niceSteps.find((s) => s >= idealStep) || 200;

  // Minor step is half of major, or 0 if major is 1
  const minorStep = majorStep > 1 ? Math.floor(majorStep / 2) : 0;

  // Proportional positioning: frame position = (frame / frameCount) * width
  // This ensures the ruler fills the viewport when zoomed out
  const frameCount = projectStore.getFrameCount();

  for (let f = 0; f <= frameCount; f++) {
    const x = (f / frameCount) * width;

    if (f % majorStep === 0) {
      // Major Tick
      ctx.strokeStyle = "#888";
      ctx.beginPath();
      ctx.moveTo(x, 12);
      ctx.lineTo(x, 30);
      ctx.stroke();

      // Label - majorStep already accounts for spacing
      ctx.fillStyle = "#ccc";
      ctx.fillText(String(f), x + 3, 10);
    } else if (minorStep > 0 && f % minorStep === 0) {
      // Minor Tick
      ctx.strokeStyle = "#555";
      ctx.beginPath();
      ctx.moveTo(x, 22);
      ctx.lineTo(x, 30);
      ctx.stroke();
    }
  }

  // Draw beat markers (onsets)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const audioAnalysis = (audioStore != null && typeof audioStore === "object" && "audioAnalysis" in audioStore && audioStore.audioAnalysis != null && typeof audioStore.audioAnalysis === "object") ? audioStore.audioAnalysis : undefined;
  const onsets = (audioAnalysis != null && typeof audioAnalysis === "object" && "onsets" in audioAnalysis && Array.isArray(audioAnalysis.onsets)) ? audioAnalysis.onsets : undefined;
  if (onsets != null) {
    ctx.strokeStyle = "rgba(255, 193, 7, 0.6)"; // Gold/amber for beats
    ctx.lineWidth = 1;
    for (const onset of onsets) {
      const x = (onset / frameCount) * width;
      ctx.beginPath();
      ctx.moveTo(x, 20);
      ctx.lineTo(x, 30);
      ctx.stroke();
    }
    ctx.lineWidth = 1;
  }

  // Draw peak markers (diamonds at top)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const peakData = (audioStore != null && typeof audioStore === "object" && "peakData" in audioStore && audioStore.peakData != null && typeof audioStore.peakData === "object") ? audioStore.peakData : undefined;
  const peakIndices = (peakData != null && typeof peakData === "object" && "indices" in peakData && Array.isArray(peakData.indices)) ? peakData.indices : undefined;
  if (peakIndices != null) {
    ctx.fillStyle = "rgba(255, 107, 107, 0.9)"; // Red for peaks
    for (const peakFrame of peakIndices) {
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
  ctx.strokeStyle = "#444";
  ctx.beginPath();
  ctx.moveTo(0, 29.5);
  ctx.lineTo(cvs.width, 29.5);
  ctx.stroke();
}

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
// Helper function to get scrollLeft from rulerScrollRef or trackScrollRef
function getScrollLeft(): number | undefined {
  const rulerRef = rulerScrollRef.value;
  const rulerScrollLeft = (rulerRef !== null && rulerRef !== undefined && typeof rulerRef === "object" && "scrollLeft" in rulerRef && typeof rulerRef.scrollLeft === "number" && Number.isFinite(rulerRef.scrollLeft)) ? rulerRef.scrollLeft : undefined;
  if (rulerScrollLeft !== undefined) return rulerScrollLeft;
  const trackRef = trackScrollRef.value;
  const trackScrollLeft = (trackRef !== null && trackRef !== undefined && typeof trackRef === "object" && "scrollLeft" in trackRef && typeof trackRef.scrollLeft === "number" && Number.isFinite(trackRef.scrollLeft)) ? trackRef.scrollLeft : undefined;
  return trackScrollLeft;
}

function startRulerScrub(e: MouseEvent) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const rulerCanvasValue = rulerCanvas.value;
  const getBoundingClientRect = (rulerCanvasValue != null && typeof rulerCanvasValue === "object" && typeof rulerCanvasValue.getBoundingClientRect === "function") ? rulerCanvasValue.getBoundingClientRect : undefined;
  const rect = getBoundingClientRect != null ? getBoundingClientRect() : undefined;
  if (!rect) return;
  // Type proof: scrollLeft ∈ number | undefined → number (≥ 0, scroll position)
  const _scrollX = safeNonNegativeDefault(
    getScrollLeft(),
    0,
    "scrollLeft",
  );

  // Track if this is an audio scrub (Ctrl held at start)
  const isAudioScrub = e.ctrlKey || e.metaKey;

  const update = (ev: MouseEvent) => {
    // Type proof: scrollLeft ∈ number | undefined → number (≥ 0, scroll position)
    const currentScrollX = safeNonNegativeDefault(
      getScrollLeft(),
      0,
      "scrollLeft",
    );
    const x = ev.clientX - rect.left + currentScrollX;
    // Convert x position to frame using proportional formula
    const frameCount = projectStore.getFrameCount();
    let f = Math.max(
      0,
      Math.min(
        frameCount - 1,
        (x / timelineWidth.value) * frameCount,
      ),
    );

    // Apply snapping (hold Alt/Option to disable)
    if (!ev.altKey && animationStore.snapConfig.enabled) {
      // System F/Omega pattern: Wrap in try/catch for expected "no snap" case
      // When no snap targets are found, it's a valid state (snapping is optional)
      try {
        const snap = findNearestSnap(
          Math.round(f),
          animationStore.snapConfig,
          effectivePpf.value,
          {
            layers: projectStore.getActiveCompLayers(),
            audioAnalysis: audioStore.audioAnalysis,
            peakData: audioStore.peakData,
          },
        );
        f = snap.frame;
      } catch (error) {
        // No snap target found - this is expected when no targets are within threshold
        // Skip snapping and use the original frame
      }
    }

    const frame = Math.round(f);
    animationStore.setFrame(getAnimationStoreAccess(), frame);

    // Ctrl+drag: Audio scrub - play short audio snippet at current position
    if (isAudioScrub || ev.ctrlKey || ev.metaKey) {
      audioStore.scrubAudio(frame, projectStore.getFps());
    }
  };

  update(e);
  window.addEventListener("mousemove", update);
  window.addEventListener(
    "mouseup",
    () => {
      window.removeEventListener("mousemove", update);
      // Stop any audio scrub when mouse is released
      if (isAudioScrub) {
        audioStore.stopAudio();
      }
    },
    { once: true },
  );
}

function startResize(e: MouseEvent) {
  const startX = e.clientX;
  const startW = sidebarWidth.value;
  const onMove = (ev: MouseEvent) => {
    sidebarWidth.value = Math.max(450, startW + (ev.clientX - startX));
  };
  window.addEventListener("mousemove", onMove);
  window.addEventListener(
    "mouseup",
    () => window.removeEventListener("mousemove", onMove),
    { once: true },
  );
}

// Work Area functions
function clearWorkArea() {
  workAreaStart.value = null;
  workAreaEnd.value = null;
  playbackStore.clearWorkArea();
}

function startWorkAreaDrag(handle: "start" | "end", e: MouseEvent) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const rulerCanvasValue = rulerCanvas.value;
  const getBoundingClientRect = (rulerCanvasValue != null && typeof rulerCanvasValue === "object" && typeof rulerCanvasValue.getBoundingClientRect === "function") ? rulerCanvasValue.getBoundingClientRect : undefined;
  const rect = getBoundingClientRect != null ? getBoundingClientRect() : undefined;
  if (!rect) return;
  // Type proof: scrollLeft ∈ number | undefined → number (≥ 0, scroll position)
  const _scrollX = safeNonNegativeDefault(
    getScrollLeft(),
    0,
    "scrollLeft",
  );

  const update = (ev: MouseEvent) => {
    // Type proof: scrollLeft ∈ number | undefined → number (≥ 0, scroll position)
    const currentScrollX = safeNonNegativeDefault(
      getScrollLeft(),
      0,
      "scrollLeft",
    );
    const x = ev.clientX - rect.left + currentScrollX;
    const frameCount = projectStore.getFrameCount();
    let frame = Math.round(
      Math.max(
        0,
        Math.min(
          frameCount - 1,
          (x / timelineWidth.value) * frameCount,
        ),
      ),
    );

    if (handle === "start") {
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
  window.addEventListener("mousemove", update);
  window.addEventListener(
    "mouseup",
    () => {
      window.removeEventListener("mousemove", update);
      // Sync final work area to playbackStore
      playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
    },
    { once: true },
  );
}

// Scroll synchronization between sidebar and track area
function syncSidebarScroll(e: Event) {
  if (isScrollingTrack) return;
  isScrollingSidebar = true;
  const target = e.target as HTMLElement;
  if (trackScrollRef.value) {
    trackScrollRef.value.scrollTop = target.scrollTop;
  }
  requestAnimationFrame(() => {
    isScrollingSidebar = false;
  });
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
    requestAnimationFrame(() => {
      isScrollingTrack = false;
    });
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
  if (
    e.target instanceof HTMLInputElement ||
    e.target instanceof HTMLTextAreaElement
  )
    return;

  // Playback
  if (e.code === "Space") {
    e.preventDefault();
    togglePlayback();
  }

  // Delete
  if (e.code === "Delete" || e.code === "Backspace") {
    e.preventDefault();
    deleteSelectedLayers();
  }

  // Copy/Cut/Paste
  if ((e.ctrlKey || e.metaKey) && e.code === "KeyC") {
    e.preventDefault();
    layerStore.copySelectedLayers(store);
  }
  if ((e.ctrlKey || e.metaKey) && e.code === "KeyX") {
    e.preventDefault();
    layerStore.cutSelectedLayers(store);
  }
  if ((e.ctrlKey || e.metaKey) && e.code === "KeyV") {
    e.preventDefault();
    layerStore.pasteLayers(store);
  }

  // Select All
  if ((e.ctrlKey || e.metaKey) && e.code === "KeyA") {
    e.preventDefault();
    layerStore.selectAllLayers(store);
  }

  // Duplicate (Ctrl+D)
  if ((e.ctrlKey || e.metaKey) && e.code === "KeyD") {
    e.preventDefault();
    layerStore.duplicateSelectedLayers(store);
  }
}

let resizeObserver: ResizeObserver | null = null;

onMounted(() => {
  window.addEventListener("mousedown", (e) => {
    if (
      addLayerContainer.value &&
      !addLayerContainer.value.contains(e.target as Node)
    ) {
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
        viewportWidth.value =
          entry.contentRect.width || elementToObserve.clientWidth || 1000;
        drawRuler(); // Redraw ruler on resize
      }
    });
    resizeObserver.observe(elementToObserve);
  }

  // Draw ruler after a short delay to ensure layout is complete
  setTimeout(() => {
    if (trackScrollRef.value) {
      viewportWidth.value =
        trackScrollRef.value.clientWidth || viewportWidth.value;
    }
    drawRuler();
  }, 50);
});

onUnmounted(() => {
  if (resizeObserver) resizeObserver.disconnect();
});

watch(
  () => [
    computedWidthStyle.value,
    zoomPercent.value,
    projectStore.getFrameCount(store),
    audioStore.audioAnalysis,
    audioStore.peakData,
  ],
  () => nextTick(drawRuler),
);
</script>

<style scoped>
.timeline-panel { display: flex; flex-direction: column; height: 100%; background: var(--lattice-surface-1, #0f0f0f); color: var(--lattice-text-primary, #eee); font-family: var(--lattice-font-sans, 'Segoe UI', sans-serif); font-size: 13px; user-select: none; }
.timeline-header { height: 48px; background: var(--lattice-surface-1, #0f0f0f); display: flex; justify-content: space-between; padding: 0 16px; align-items: center; z-index: 20; flex-shrink: 0; }
.header-left, .header-center, .header-right { display: flex; gap: 12px; align-items: center; }
.tool-group { display: flex; gap: 8px; align-items: center; }

/* SMPTE Timecode display */
.timecode { font-family: var(--lattice-font-mono, 'Consolas', 'Courier New', monospace); font-size: 16px; color: var(--lattice-accent, #8B5CF6); font-weight: bold; letter-spacing: 1px; }

/* Menus */
.add-layer-wrapper { position: relative; }
.add-layer-menu {
  /* Position set dynamically via style binding */
  background: var(--lattice-surface-2, #161616);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
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
  color: var(--lattice-text-primary, #ddd);
  cursor: pointer;
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
  font-size: 13px;
  display: flex;
  align-items: center;
  gap: 8px;
}
.add-layer-menu button:last-child { border-bottom: none; }
.add-layer-menu button:hover { background: var(--lattice-accent, #8B5CF6); color: white; }
.add-layer-menu button:first-child { border-radius: 5px 5px 0 0; }
.add-layer-menu button:last-child { border-radius: 0 0 5px 5px; }
.add-layer-btn { padding: 6px 12px; background: var(--lattice-surface-3, #1e1e1e); border: 1px solid var(--lattice-border-default, #2a2a2a); color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: bold; }
.add-layer-btn:hover, .add-layer-btn.active { background: var(--lattice-surface-4, #262626); }

.comp-settings-btn { padding: 6px 14px; background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15)); border: 1px solid var(--lattice-accent, #8B5CF6); color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: 500; }
.comp-settings-btn:hover { background: var(--lattice-accent, #8B5CF6); }
.ai-btn { padding: 6px 12px; background: var(--lattice-accent-gradient, linear-gradient(135deg, #8B5CF6, #A78BFA)); border: none; color: white; border-radius: 4px; cursor: pointer; font-size: 13px; font-weight: 500; }
.ai-btn:hover { filter: brightness(1.1); }

.timeline-content { flex: 1; display: flex; overflow: hidden; position: relative; min-height: 0; }
.timeline-sidebar { background: var(--lattice-surface-1, #0f0f0f); border-right: 1px solid var(--lattice-border-subtle, #1a1a1a); display: flex; flex-direction: column; flex-shrink: 0; z-index: 10; }
.sidebar-header-row { height: 34px; background: var(--lattice-surface-2, #161616); display: flex; align-items: center; border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); }
.col-header { font-size: 12px; color: var(--lattice-text-muted, #6B7280); display: flex; align-items: center; }
.col-header.col-av-features {
  display: flex;
  gap: 0;
  border-right: 1px solid var(--lattice-border-subtle, #1a1a1a);
  padding: 0 2px;
}
.col-header.col-number { width: 20px; justify-content: center; }
.col-header.col-name { flex: 1; padding-left: 8px; font-weight: 500; }
.col-header.col-switches {
  display: flex;
  gap: 0;
  border-left: 1px solid var(--lattice-border-subtle, #1a1a1a);
  padding: 0 2px;
}
.col-header.col-parent { min-width: 80px; border-left: 1px solid var(--lattice-border-subtle, #1a1a1a); padding: 0 8px; }
.header-icon { display: inline-flex; justify-content: center; align-items: center; width: 26px; height: 32px; font-size: 13px; color: var(--lattice-text-secondary, #9CA3AF); cursor: default; }
.header-icon.clickable { cursor: pointer; transition: color 0.15s; }
.header-icon.clickable:hover { color: var(--lattice-text-secondary, #9CA3AF); }
.header-icon.clickable.active { color: var(--lattice-accent, #8B5CF6); }
.sidebar-scroll-area { flex: 1; overflow-y: auto; overflow-x: hidden; }
.sidebar-scroll-area.drag-over {
  background-color: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
  outline: 2px dashed var(--lattice-accent, #8B5CF6);
  outline-offset: -2px;
}

.sidebar-resizer { width: 4px; background: var(--lattice-surface-0, #080808); cursor: col-resize; flex-shrink: 0; z-index: 15; }
.sidebar-resizer:hover { background: var(--lattice-accent, #8B5CF6); }

.track-viewport {
  flex: 1;
  display: flex;
  flex-direction: column;
  overflow: hidden;
  position: relative;
  background: var(--lattice-surface-1, #121212);
}

/* Ruler wrapper - scrolls horizontally only */
.ruler-scroll-wrapper {
  height: 42px;
  overflow-x: auto;
  overflow-y: hidden;
  flex-shrink: 0;
  scrollbar-width: none; /* Firefox */
  padding-top: 2px;
}
.ruler-scroll-wrapper::-webkit-scrollbar {
  display: none; /* Chrome/Safari */
}

.time-ruler {
  height: 36px;
  margin-top: 4px;
  position: relative;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
  border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);
  cursor: pointer;
  z-index: 10;
}

/* Work Area Bar (Render Range) */
.work-area-bar {
  position: absolute;
  top: 0;
  height: 100%;
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.25));
  border-left: 2px solid var(--lattice-accent, #8B5CF6);
  border-right: 2px solid var(--lattice-accent, #8B5CF6);
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
  background-color: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
  outline: 2px dashed var(--lattice-accent, #8B5CF6);
  outline-offset: -2px;
}

.layer-bars-container {
  position: relative;
  min-height: 100%;
}

/* Playhead Visuals - Purple accent */
.playhead-head {
  position: absolute; top: 0; width: 2px; height: 30px;
  background: var(--lattice-accent, #8B5CF6); z-index: 20; pointer-events: none;
  box-shadow: 0 0 8px var(--lattice-accent-glow, rgba(139, 92, 246, 0.3));
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
  border-top: 10px solid var(--lattice-accent, #8B5CF6);
}
/* Playhead Hit Area - Invisible but wider for easier grabbing */
.playhead-hit-area {
  position: absolute; top: 0; bottom: 0; width: 24px;
  margin-left: -12px; /* Center on position */
  background: transparent;
  z-index: 30; cursor: ew-resize;
}
.playhead-hit-area:hover {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
}

.playhead-line { position: absolute; top: 0; bottom: 0; width: 2px; background: var(--lattice-accent, #8B5CF6); pointer-events: none; z-index: 10; box-shadow: 0 0 8px var(--lattice-accent-glow, rgba(139, 92, 246, 0.3)); }
.grid-background { position: absolute; inset: 0; pointer-events: none; background-image: linear-gradient(to right, var(--lattice-border-subtle, #1a1a1a) 1px, transparent 1px); background-size: 100px 100%; opacity: 0.3; }
</style>
