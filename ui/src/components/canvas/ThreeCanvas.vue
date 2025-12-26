<!--
  @component ThreeCanvas
  @description Main rendering canvas using Three.js WebGL.
  Renders all layer types with real-time preview:
  - Image/Video layers with transforms
  - Text layers with font rendering
  - Shape/Spline layers with bezier paths
  - Particle system visualization
  - 3D camera with depth parallax
  - Effect stack preview (blur, glow, color)

  @features
  - WebGL 2.0 / WebGPU rendering
  - Depth map overlay visualization
  - Spline editor integration (pen tool)
  - Layer transform handles
  - Viewport zoom/pan
  - Frame-accurate playback

  @props None - uses compositorStore directly
  @emits requestPenMode - Request pen tool activation
  @emits pointAdded - Spline control point added
  @emits pathUpdated - Spline path modified
-->
<template>
  <div
    class="three-canvas"
    ref="containerRef"
    @dragover.prevent="onDragOver"
    @dragleave="onDragLeave"
    @drop="onDrop"
    :class="{ 'drag-over': isDragOver }"
  >
    <canvas ref="canvasRef" />

    <SplineEditor
      v-if="activeSplineLayerId || isPenMode"
      :layerId="activeSplineLayerId"
      :currentFrame="store.currentFrame"
      :canvasWidth="compositionWidth"
      :canvasHeight="compositionHeight"
      :containerWidth="canvasWidth"
      :containerHeight="canvasHeight"
      :zoom="zoom"
      :viewportTransform="viewportTransformArray"
      :isPenMode="isPenMode"
      @pointAdded="onPointAdded"
      @pathUpdated="onPathUpdated"
      @togglePenMode="togglePenMode"
      ref="splineEditorRef"
    />

    <!-- Motion Path Overlay (shows position keyframe paths) -->
    <MotionPathOverlay
      v-if="showMotionPath && store.selectedLayerIds.length === 1"
      :layerId="store.selectedLayerIds[0]"
      :currentFrame="store.currentFrame"
      :canvasWidth="compositionWidth"
      :canvasHeight="compositionHeight"
      :containerWidth="canvasWidth"
      :containerHeight="canvasHeight"
      :zoom="zoom"
      :viewportTransform="viewportTransformArray"
      :enabled="showMotionPath"
      @keyframeSelected="onMotionPathKeyframeSelected"
      @goToFrame="onMotionPathGoToFrame"
      @tangentUpdated="onMotionPathTangentUpdated"
    />

    <div class="overlay-controls" v-if="hasDepthMap">
      <label>
        <input type="checkbox" v-model="showDepthOverlay" />
        Depth Overlay
      </label>
      <select v-model="depthColormap" class="colormap-select">
        <option value="viridis">Viridis</option>
        <option value="plasma">Plasma</option>
        <option value="grayscale">Grayscale</option>
      </select>
      <input
        type="range"
        min="0"
        max="100"
        v-model.number="depthOpacity"
        class="opacity-slider"
      />
    </div>

    <!-- Viewer Controls (AE-style bottom bar) -->
    <div class="viewer-controls">
      <select v-model="zoomLevel" class="zoom-dropdown" @change="onZoomSelect">
        <option value="fit">Fit</option>
        <option value="0.25">25%</option>
        <option value="0.33">33%</option>
        <option value="0.5">50%</option>
        <option value="0.75">75%</option>
        <option value="1">100%</option>
        <option value="2">200%</option>
        <option value="4">400%</option>
      </select>
      <span class="zoom-display">{{ zoomDisplayPercent }}%</span>
      <div class="viewer-divider"></div>
      <select v-model="resolution" class="resolution-dropdown" @change="onResolutionChange">
        <option value="full">Full</option>
        <option value="half">Half</option>
        <option value="third">Third</option>
        <option value="quarter">Quarter</option>
        <option value="custom">Custom</option>
      </select>
    </div>

    <div class="loading-overlay" v-if="loading">
      <div class="loading-spinner"></div>
      <span>Loading...</span>
    </div>

    <!-- Segmentation mask preview overlay -->
    <div
      v-if="store.segmentPendingMask"
      class="segment-mask-overlay"
      :style="maskOverlayStyle"
    >
      <img
        :src="'data:image/png;base64,' + store.segmentPendingMask.mask"
        class="mask-preview"
        alt="Segmentation mask"
      />
    </div>

    <!-- Segment box selection preview -->
    <div
      v-if="isDrawingSegmentBox && store.segmentBoxStart && segmentBoxEnd"
      class="segment-box-preview"
      :style="segmentBoxStyle"
    ></div>

    <!-- Shape drawing preview -->
    <svg
      v-if="isDrawingShape && shapePreviewPath"
      class="shape-preview"
      :style="shapePreviewStyle"
    >
      <path :d="shapePreviewPath" />
    </svg>

    <!-- Segmentation loading indicator -->
    <div v-if="store.segmentIsLoading" class="segment-loading">
      <div class="segment-spinner"></div>
      <span>Segmenting...</span>
    </div>

    <!-- Render Mode Controls (upper-left) -->
    <div class="render-mode-controls">
      <button
        :class="{ active: renderMode === 'color' }"
        @click="setRenderMode('color')"
        title="Color Mode"
      >🎨</button>
      <button
        :class="{ active: renderMode === 'depth' }"
        @click="setRenderMode('depth')"
        title="Depth Mode"
      >⬛</button>
      <button
        :class="{ active: renderMode === 'normal' }"
        @click="setRenderMode('normal')"
        title="Normal Mode"
      >🔮</button>
    </div>

    <!-- Transform Mode Controls (below render modes) -->
    <div class="transform-mode-controls">
      <button
        :class="{ active: transformMode === 'translate' }"
        @click="setTransformModeTo('translate')"
        title="Move Tool (W)"
      >↔</button>
      <button
        :class="{ active: transformMode === 'rotate' }"
        @click="setTransformModeTo('rotate')"
        title="Rotate Tool (E)"
      >⟳</button>
      <button
        :class="{ active: transformMode === 'scale' }"
        @click="setTransformModeTo('scale')"
        title="Scale Tool (R)"
      >⤢</button>
    </div>

    <!-- CSS-based Composition Boundary - crisp blue border around composition -->
    <!-- Replaces the 3D LineLoop which can appear blurry due to WebGL line width limitations -->
    <div
      v-if="store.viewOptions.showCompositionBounds !== false"
      class="composition-boundary"
      :style="compositionBoundaryStyle"
    ></div>

    <!-- Safe Frame Guides - CSS-based screen-space overlay -->
    <!-- These stay fixed regardless of camera movement -->
    <div v-if="showSafeFrameGuides" class="safe-frame-container">
      <div class="safe-frame-overlay safe-frame-left" :style="safeFrameLeftStyle"></div>
      <div class="safe-frame-overlay safe-frame-right" :style="safeFrameRightStyle"></div>
      <div class="safe-frame-overlay safe-frame-top" :style="safeFrameTopStyle"></div>
      <div class="safe-frame-overlay safe-frame-bottom" :style="safeFrameBottomStyle"></div>
    </div>

    <!-- Resolution Crop Guides - Center-based dotted boxes for 480p/720p/1080p -->
    <div v-if="showResolutionGuides" class="resolution-guides-container">
      <template v-for="guide in resolutionCropGuides" :key="guide.name">
        <div
          v-if="guide.visible"
          class="resolution-crop-box"
          :style="guide.style"
        >
          <span class="resolution-label" :style="{ color: guide.color }">{{ guide.name }}</span>
        </div>
      </template>
    </div>

    <!-- Marquee Selection Rectangle -->
    <div
      v-if="isMarqueeSelecting && marqueeRectStyle"
      class="marquee-selection"
      :style="marqueeRectStyle"
    >
      <span v-if="marqueeMode !== 'replace'" class="marquee-mode-indicator">
        {{ marqueeMode === 'add' ? '+' : marqueeMode === 'subtract' ? '−' : '∩' }}
      </span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, onMounted, onUnmounted, watch, computed, nextTick, shallowRef } from 'vue';
import * as THREE from 'three';
import { useCompositorStore } from '@/stores/compositorStore';
import { useSelectionStore } from '@/stores/selectionStore';
import { LatticeEngine } from '@/engine';
import type { LatticeEngineConfig, PerformanceStats } from '@/engine';
import type { LayerTransformUpdate } from '@/engine/LatticeEngine';
import type { Layer, ControlPoint } from '@/types/project';
import SplineEditor from './SplineEditor.vue';
import MotionPathOverlay from './MotionPathOverlay.vue';
import {
  useCanvasSelection,
  useCanvasSegmentation,
  useShapeDrawing,
  useViewportGuides,
  type SelectableItem,
  type SelectionMode
} from '@/composables';

// Store
const store = useCompositorStore();
const selection = useSelectionStore();

// Refs
const containerRef = ref<HTMLDivElement | null>(null);
const canvasRef = ref<HTMLCanvasElement | null>(null);
const splineEditorRef = ref<InstanceType<typeof SplineEditor> | null>(null);

// Engine instance (shallowRef for performance - don't make Three.js objects reactive)
const engine = shallowRef<LatticeEngine | null>(null);

// State
const loading = ref(false);
const zoom = ref(1);
const canvasWidth = ref(800);
const canvasHeight = ref(600);
// Composition dimensions (in composition units, not pixels)
const compositionWidth = computed(() => store.width || 832);
const compositionHeight = computed(() => store.height || 480);
const showDepthOverlay = ref(false);
const depthColormap = ref<'viridis' | 'plasma' | 'grayscale'>('viridis');
const depthOpacity = ref(50);
const renderMode = ref<'color' | 'depth' | 'normal'>('color');
const showPerformance = ref(false);
const performanceStats = ref<PerformanceStats>({
  fps: 0,
  frameTime: 0,
  drawCalls: 0,
  triangles: 0,
  textures: 0,
  geometries: 0,
  memoryUsed: 0
});

// Pan/zoom state
const viewportTransform = ref<number[]>([1, 0, 0, 1, 0, 0]);

// Viewer controls
const zoomLevel = ref<string>('fit');
const resolution = ref<'full' | 'half' | 'third' | 'quarter' | 'custom'>('full');

// Computed zoom display percentage
const zoomDisplayPercent = computed(() => Math.round(zoom.value * 100));

// Transform mode for transform controls
const transformMode = ref<'translate' | 'rotate' | 'scale'>('translate');

// Composition guide toggles (showSafeFrameGuides, showResolutionGuides come from useViewportGuides)
const showGrid = ref(false);
const showOutsideOverlay = ref(false);  // Disabled by default until fixed
const showMotionPath = ref(true);  // Motion path visualization enabled by default

// Segmentation composable
const {
  isDrawingSegmentBox,
  segmentBoxEnd,
  startSegmentBox,
  updateSegmentBox,
  cancelSegmentBox,
  finishSegmentBox,
  handleSegmentPoint,
  getSegmentBoxStyle,
  getMaskOverlayStyle
} = useCanvasSegmentation();

// Shape drawing composable
const {
  isDrawingShape,
  shapeDrawStart,
  shapeDrawEnd,
  currentShapeTool,
  isShapeTool,
  shapePreviewBounds,
  shapePreviewPath,
  startDrawing: startShapeDrawing,
  updateDrawing: updateShapeDrawing,
  cancelDrawing: cancelShapeDrawing,
  finishDrawing: finishShapeDrawing
} = useShapeDrawing();

// Viewport guides composable
const {
  showSafeFrameGuides,
  showResolutionGuides,
  cameraUpdateTrigger,
  safeFrameBounds,
  safeFrameLeftStyle,
  safeFrameRightStyle,
  safeFrameTopStyle,
  safeFrameBottomStyle,
  compositionBoundaryStyle,
  resolutionCropGuides,
  triggerGuideUpdate
} = useViewportGuides({
  containerRef,
  engine,
  canvasWidth,
  canvasHeight,
  zoom,
  viewportTransform
});

// ============================================================
// MARQUEE SELECTION (Phase 8 Integration)
// ============================================================

// Enable marquee selection only when using select tool
const marqueeEnabled = computed(() => store.currentTool === 'select');

/**
 * Get all layers as selectable items with their screen-space bounds
 * This is called by the marquee selection composable during drag
 */
function getSelectableItems(): SelectableItem[] {
  if (!engine.value || !containerRef.value) return [];

  const camera = engine.value.getCameraController().camera;
  const items: SelectableItem[] = [];

  for (const layer of store.layers) {
    if (!layer.enabled) continue;

    // Get layer bounds in world space
    const layerObj = engine.value.getLayerObject(layer.id);
    if (!layerObj) continue;

    // Compute bounding box
    const box = new THREE.Box3().setFromObject(layerObj);
    if (box.isEmpty()) continue;

    // Project corners to screen space
    const corners = [
      new THREE.Vector3(box.min.x, box.min.y, box.min.z),
      new THREE.Vector3(box.max.x, box.min.y, box.min.z),
      new THREE.Vector3(box.min.x, box.max.y, box.min.z),
      new THREE.Vector3(box.max.x, box.max.y, box.min.z),
      new THREE.Vector3(box.min.x, box.min.y, box.max.z),
      new THREE.Vector3(box.max.x, box.min.y, box.max.z),
      new THREE.Vector3(box.min.x, box.max.y, box.max.z),
      new THREE.Vector3(box.max.x, box.max.y, box.max.z),
    ];

    const rect = containerRef.value.getBoundingClientRect();
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;

    for (const corner of corners) {
      corner.project(camera);
      const screenX = (corner.x + 1) / 2 * rect.width;
      const screenY = (-corner.y + 1) / 2 * rect.height;
      minX = Math.min(minX, screenX);
      minY = Math.min(minY, screenY);
      maxX = Math.max(maxX, screenX);
      maxY = Math.max(maxY, screenY);
    }

    items.push({
      id: layer.id,
      bounds: {
        x: minX,
        y: minY,
        width: maxX - minX,
        height: maxY - minY,
      },
    });
  }

  return items;
}

/**
 * Handle marquee selection changes
 */
function handleMarqueeSelectionChange(selectedIds: string[], mode: SelectionMode) {
  if (mode === 'replace') {
    if (selectedIds.length === 0) {
      selection.clearSelection();
    } else {
      selection.selectLayers(selectedIds);
    }
  } else if (mode === 'add') {
    for (const id of selectedIds) {
      selection.addToSelection(id);
    }
  } else if (mode === 'subtract') {
    for (const id of selectedIds) {
      selection.removeFromSelection(id);
    }
  }

  // Update engine selection
  if (engine.value) {
    engine.value.selectLayer(selectedIds.length > 0 ? selectedIds[0] : null);
  }
}

// Initialize marquee selection composable
const {
  isSelecting: isMarqueeSelecting,
  selectionRectStyle: marqueeRectStyle,
  selectionMode: marqueeMode,
} = useCanvasSelection({
  canvasRef: containerRef,
  getSelectableItems,
  onSelectionChange: handleMarqueeSelectionChange,
  currentSelection: computed(() => store.selectedLayerIds),
  enabled: marqueeEnabled,
  minDragDistance: 5,
});

// Computed styles for segmentation overlays (use composable methods)
const maskOverlayStyle = computed(() => getMaskOverlayStyle(viewportTransform.value));
const segmentBoxStyle = computed(() => getSegmentBoxStyle(viewportTransform.value));

// Shape preview style (bounds and path come from composable)
const shapePreviewStyle = computed(() => {
  const bounds = shapePreviewBounds.value;
  if (!bounds) return {};

  const vpt = viewportTransform.value;

  // Convert to screen coordinates
  const screenX1 = bounds.x1 * vpt[0] + vpt[4];
  const screenY1 = bounds.y1 * vpt[3] + vpt[5];
  const screenX2 = bounds.x2 * vpt[0] + vpt[4];
  const screenY2 = bounds.y2 * vpt[3] + vpt[5];

  return {
    left: `${Math.min(screenX1, screenX2)}px`,
    top: `${Math.min(screenY1, screenY2)}px`,
    width: `${Math.abs(screenX2 - screenX1)}px`,
    height: `${Math.abs(screenY2 - screenY1)}px`
  };
});

// Safe frame and resolution guides are provided by useViewportGuides composable

// Computed
const hasDepthMap = computed(() => store.depthMap !== null);
const isPenMode = computed(() => store.currentTool === 'pen');

// Drag and drop state
const isDragOver = ref(false);

function onDragOver(event: DragEvent) {
  if (event.dataTransfer?.types.includes('application/project-item')) {
    isDragOver.value = true;
  }
}

function onDragLeave() {
  isDragOver.value = false;
}

function onDrop(event: DragEvent) {
  isDragOver.value = false;

  const data = event.dataTransfer?.getData('application/project-item');
  if (!data) return;

  try {
    const item = JSON.parse(data) as {
      id: string;
      name: string;
      type: 'composition' | 'footage' | 'solid' | 'audio' | 'folder';
    };

    console.log('[ThreeCanvas] Dropped item:', item);

    // Handle footage items (images/videos)
    if (item.type === 'footage') {
      const asset = store.project.assets[item.id];
      if (asset) {
        if (asset.type === 'image') {
          // Load image to get dimensions and resize composition
          const img = new Image();
          img.onload = () => {
            // Resize composition to match image dimensions
            const compId = store.activeCompositionId;
            if (compId) {
              store.updateCompositionSettings(compId, {
                width: img.naturalWidth,
                height: img.naturalHeight
              });
            }

            // Create the layer after resizing
            const layer = store.createLayer('image', item.name);
            if (layer) {
              (layer.data as any).assetId = item.id;
              (layer.data as any).source = asset.data;
              store.selectLayer(layer.id);
              console.log('[ThreeCanvas] Created image layer, resized comp to:', img.naturalWidth, 'x', img.naturalHeight);
            }
          };
          img.src = asset.data;
        } else if (asset.type === 'video') {
          const layer = store.createLayer('video', item.name);
          if (layer) {
            (layer.data as any).assetId = item.id;
            store.selectLayer(layer.id);
            console.log('[ThreeCanvas] Created video layer from drop:', item.name);
          }
        }
      }
    } else if (item.type === 'solid') {
      const layer = store.createLayer('solid', item.name);
      if (layer) {
        store.selectLayer(layer.id);
        console.log('[ThreeCanvas] Created solid layer from drop:', item.name);
      }
    }
  } catch (e) {
    console.error('[ThreeCanvas] Failed to handle drop:', e);
  }
}

const activeSplineLayerId = computed(() => {
  const selectedLayer = store.selectedLayer;
  if (selectedLayer?.type === 'spline') {
    return selectedLayer.id;
  }
  if (isPenMode.value) {
    const splines = store.layers.filter(l => l.type === 'spline');
    return splines.length > 0 ? splines[splines.length - 1].id : null;
  }
  return null;
});

const viewportTransformArray = computed(() => viewportTransform.value);

// Initialize Three.js engine
onMounted(async () => {
  if (!canvasRef.value || !containerRef.value) return;

  const container = containerRef.value;
  const rect = container.getBoundingClientRect();

  canvasWidth.value = rect.width;
  canvasHeight.value = rect.height;

  // Create engine config
  const config: LatticeEngineConfig = {
    canvas: canvasRef.value,
    width: rect.width,
    height: rect.height,
    compositionWidth: store.width || 1920,
    compositionHeight: store.height || 1080,
    pixelRatio: Math.min(window.devicePixelRatio, 2), // Cap at 2 for performance
    antialias: true,
    alpha: true,
    backgroundColor: store.backgroundColor || '#050505',
    powerPreference: 'high-performance'
  };

  try {
    loading.value = true;
    engine.value = new LatticeEngine(config);

    // Wire up callbacks for video/nested composition/camera integration
    engine.value.setAssetGetter((assetId: string) => store.assets[assetId]);
    engine.value.setVideoMetadataCallback((layerId, metadata) => {
      store.onVideoMetadataLoaded(layerId, metadata);
    });
    engine.value.setCameraCallbacks(
      (cameraId: string) => store.getCamera(cameraId),
      (cameraId: string, updates) => store.updateCamera(cameraId, updates),
      (cameraId: string, frame: number) => store.getCameraAtFrame(cameraId, frame)
    );

    // Wire up nested comp rendering - allows nested comp layers to render nested compositions
    // The engine maintains a cache of layer managers and scenes per composition
    // and renders them to offscreen textures when requested.
    engine.value.setNestedCompRenderContext({
      renderComposition: (compositionId: string, frame: number) => {
        // Get the composition data from store
        const comp = store.getComposition(compositionId);
        if (!comp) {
          console.warn('[ThreeCanvas] Nested comp not found:', compositionId);
          return null;
        }

        // Get layers for this composition (they're stored directly on the composition)
        if (!comp.layers || comp.layers.length === 0) {
          // Empty composition - return null (nested comp will show placeholder)
          return null;
        }

        // Render the composition to a texture using the engine's nested comp system
        return engine.value!.renderCompositionToTexture(
          compositionId,
          comp.layers,
          {
            width: comp.settings.width,
            height: comp.settings.height,
            fps: comp.settings.fps
          },
          frame
        );
      },
      getComposition: (compositionId: string) => store.getComposition(compositionId)
    });

    // Wire up audio reactivity - connects audio analysis to layer properties
    engine.value.setAudioReactiveCallback(
      (layerId: string, frame: number) => store.getAudioReactiveValuesForLayer(layerId, frame)
    );

    // Initialize transform controls and wire callback to update store
    engine.value.initializeTransformControls();
    engine.value.setTransformChangeCallback((layerId: string, transform: LayerTransformUpdate) => {
      handleTransformChange(layerId, transform);
    });

    // Initialize particle systems with renderer and composition FPS
    engine.value.initializeParticleSystems();
    engine.value.setCompositionFPS(store.fps || 60);

    // Initialize 3D services (material system, environment maps)
    engine.value.initialize3DServices();

    // Enable orbit controls for 3D navigation
    // Right-click = orbit around selected object/composition center
    // Middle-click = pan
    engine.value.enableOrbitControls();

    // Reset camera to perfect 2D front view (must be after enabling orbit controls)
    engine.value.resetCameraToDefault();

    // Start render loop
    engine.value.start();

    // Initial render
    await nextTick();
    syncLayersToEngine();

    // Initialize property driver system
    store.initializePropertyDriverSystem();

    // Apply initial frame state via MotionEngine
    const initialFrameState = store.getFrameState(store.currentFrame);
    engine.value.applyFrameState(initialFrameState);

    // Setup event listeners
    setupInputHandlers();

    // Handle resize
    const resizeObserver = new ResizeObserver(handleResize);
    resizeObserver.observe(container);

    // Center on composition
    centerOnComposition();

  } catch (err) {
    console.error('[ThreeCanvas] Failed to initialize engine:', err);
  } finally {
    loading.value = false;
  }

  // Setup watchers
  setupWatchers();
});

onUnmounted(() => {
  if (engine.value) {
    engine.value.stop();
    engine.value.dispose();
    engine.value = null;
  }
});

// Setup reactive watchers
function setupWatchers() {
  // Watch layers for changes
  watch(
    () => store.layers,
    () => {
      syncLayersToEngine();
      // Re-evaluate frame to apply layer changes (like 3D toggle)
      if (engine.value) {
        const frameState = store.getFrameState(store.currentFrame);
        engine.value.applyFrameState(frameState);
      }
    },
    { deep: true }
  );

  // Watch current frame - use MotionEngine as single source of truth
  watch(
    () => store.currentFrame,
    (frame) => {
      if (engine.value) {
        // Apply property drivers (sets driven values on layers for override)
        applyPropertyDrivers();

        // Get pre-evaluated frame state from MotionEngine (PURE, deterministic)
        const frameState = store.getFrameState(frame);

        // Apply the evaluated state to the engine
        // This is the canonical path - no interpolation happens in the engine
        engine.value.applyFrameState(frameState);
      }
    }
  );

  // Watch composition size
  watch(
    () => [store.width, store.height],
    ([width, height]) => {
      if (engine.value) {
        // Update engine with new composition dimensions
        engine.value.resize(canvasWidth.value, canvasHeight.value, width as number, height as number);
        // Re-fit to viewport with new composition size
        centerOnComposition();
      }
    }
  );

  // Watch source image
  watch(
    () => store.sourceImage,
    async (imageData) => {
      if (engine.value && imageData) {
        await loadSourceImage(imageData);
      }
    },
    { immediate: true }
  );

  // Watch depth map
  watch(
    () => store.depthMap,
    async (depthData) => {
      if (engine.value && depthData) {
        await loadDepthMap(depthData);
      }
    },
    { immediate: true }
  );

  // Performance stats update
  watch(
    () => engine.value?.getPerformanceStats(),
    (stats) => {
      if (stats) {
        performanceStats.value = stats;
      }
    }
  );

  // Watch active camera and sync to engine
  watch(
    () => store.activeCameraId,
    (activeCameraId) => {
      if (!engine.value) return;

      if (!activeCameraId) {
        engine.value.setActiveCameraLayer(null);
        return;
      }

      // Find the camera layer that references this camera
      const cameraLayer = store.layers.find(
        l => l.type === 'camera' && (l.data as any)?.cameraId === activeCameraId
      );

      if (cameraLayer) {
        engine.value.setActiveCameraLayer(cameraLayer.id);
      }
    },
    { immediate: true }
  );

  // Watch selected layer and sync transform controls
  watch(
    () => store.selectedLayerIds,
    (selectedIds) => {
      if (!engine.value) return;
      // Use first selected layer for transform controls
      const selectedId = selectedIds.length > 0 ? selectedIds[0] : null;
      engine.value.selectLayer(selectedId);
    },
    { deep: true }
  );

  // Watch view options and sync to engine
  watch(
    () => store.viewOptions.showGrid,
    (showGridVisible) => {
      if (!engine.value) return;
      showGrid.value = showGridVisible;
      engine.value.setCompositionGridVisible(showGridVisible);
    },
    { immediate: true }
  );

  // Watch composition bounds toggle
  // Note: The 3D LineLoop bounds are disabled in favor of CSS-based boundary
  // which is always crisp regardless of zoom/pan (WebGL linewidth limitation)
  watch(
    () => store.viewOptions.showCompositionBounds,
    (_showBounds) => {
      if (!engine.value) return;
      // Always hide 3D bounds - CSS version is used instead (see .composition-boundary)
      engine.value.setCompositionBoundsVisible(false);
    },
    { immediate: true }
  );

  // Watch background color changes
  watch(
    () => store.backgroundColor,
    (newColor) => {
      if (!engine.value) return;
      engine.value.setBackground(newColor);
    }
  );
}

// Sync store layers to engine
function syncLayersToEngine() {
  if (!engine.value) return;

  const engineLayerIds = new Set(engine.value.getLayerIds());
  const storeLayerIds = new Set(store.layers.map(l => l.id));

  console.log('[ThreeCanvas] syncLayersToEngine:', {
    engineLayers: Array.from(engineLayerIds),
    storeLayers: Array.from(storeLayerIds),
    storeLayerDetails: store.layers.map(l => ({ id: l.id, type: l.type, name: l.name }))
  });

  // Remove layers no longer in store
  for (const id of engineLayerIds) {
    if (!storeLayerIds.has(id)) {
      console.log('[ThreeCanvas] Removing layer:', id);
      engine.value.removeLayer(id);
    }
  }

  // Add or update layers from store
  for (const layer of store.layers) {
    if (engineLayerIds.has(layer.id)) {
      engine.value.updateLayer(layer.id, layer);
    } else {
      console.log('[ThreeCanvas] Adding layer:', layer.id, layer.type, layer.name);
      engine.value.addLayer(layer);
    }
  }
}

/**
 * Apply property drivers to all layers
 * Calculates driven values from expressions/links and passes to engine
 */
function applyPropertyDrivers() {
  if (!engine.value) return;

  // Clear all previous driven values
  engine.value.clearAllDrivenValues();

  // For each layer, get driven values and apply
  for (const layer of store.layers) {
    const drivenValues = store.getDrivenValuesForLayer(layer.id);
    if (drivenValues.size > 0) {
      engine.value.setLayerDrivenValues(layer.id, drivenValues);
    }
  }
}

// Load source image as background
async function loadSourceImage(imageData: string) {
  if (!engine.value) return;

  try {
    loading.value = true;
    const img = await loadImage(imageData);

    // Create a background image layer in the engine
    // This is handled through the ResourceManager
    engine.value.setBackgroundImage(img);

  } catch (err) {
    console.error('[ThreeCanvas] Failed to load source image:', err);
  } finally {
    loading.value = false;
  }
}

// Load depth map
async function loadDepthMap(depthData: string) {
  if (!engine.value) return;

  try {
    const img = await loadImage(depthData);
    engine.value.setDepthMap(img, {
      colormap: depthColormap.value,
      opacity: depthOpacity.value / 100,
      visible: showDepthOverlay.value
    });
  } catch (err) {
    console.error('[ThreeCanvas] Failed to load depth map:', err);
  }
}

// Image loader utility
function loadImage(src: string): Promise<HTMLImageElement> {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.crossOrigin = 'anonymous';
    img.onload = () => resolve(img);
    img.onerror = reject;
    img.src = src.startsWith('data:') ? src : `data:image/png;base64,${src}`;
  });
}

// Input handling
function setupInputHandlers() {
  const container = containerRef.value;
  const canvas = canvasRef.value;
  if (!container || !canvas) return;

  let isPanning = false;
  let isZooming = false;
  let lastPosX = 0;
  let lastPosY = 0;
  let zoomStartY = 0;
  let zoomStartLevel = 1;

  // Prevent default middle mouse behavior
  container.addEventListener('mousedown', (e: MouseEvent) => {
    if (e.button === 1) {
      e.preventDefault();
    }
  });

  container.addEventListener('auxclick', (e: MouseEvent) => {
    if (e.button === 1) {
      e.preventDefault();
    }
  });

  // Prevent browser context menu on right-click (we'll use it for orbit)
  container.addEventListener('contextmenu', (e: Event) => {
    e.preventDefault();
  });

  // Wheel zoom - simple zoom centered on composition
  canvas.addEventListener('wheel', (e: WheelEvent) => {
    e.preventDefault();

    const delta = e.deltaY;
    let newZoom = zoom.value * (delta > 0 ? 0.9 : 1.1);
    newZoom = Math.min(Math.max(newZoom, 0.1), 10);

    // Update zoom state
    zoom.value = newZoom;
    viewportTransform.value[0] = newZoom;
    viewportTransform.value[3] = newZoom;

    if (engine.value) {
      // Update camera zoom - this maintains centered view unless panning
      engine.value.getCameraController().setZoom(newZoom);
      // Force boundary update after camera change
      cameraUpdateTrigger.value++;
    }
  }, { passive: false });

  // Mouse down
  canvas.addEventListener('mousedown', (e: MouseEvent) => {
    const currentTool = store.currentTool;

    // Middle mouse or Alt+Left for panning
    if (e.button === 1 || currentTool === 'hand' || (e.button === 0 && e.altKey)) {
      isPanning = true;
      lastPosX = e.clientX;
      lastPosY = e.clientY;
      canvas.style.cursor = 'grabbing';
      e.preventDefault();
      return;
    }

    // Zoom tool
    if (currentTool === 'zoom') {
      if (e.shiftKey) {
        // Zoom out on shift+click
        const newZoom = Math.max(zoom.value * 0.7, 0.1);
        zoom.value = newZoom;
        viewportTransform.value[0] = newZoom;
        viewportTransform.value[3] = newZoom;
        if (engine.value) {
          engine.value.setViewportTransform(viewportTransform.value);
        }
      } else {
        // Start drag zoom
        isZooming = true;
        zoomStartY = e.clientY;
        zoomStartLevel = zoom.value;
      }
      return;
    }

    // Text tool - create text layer at click position
    if (currentTool === 'text') {
      const rect = canvas.getBoundingClientRect();
      const scenePos = screenToScene(e.clientX - rect.left, e.clientY - rect.top);

      const newLayer = store.createLayer('text');
      if (newLayer.transform?.position) {
        newLayer.transform.position.value = { x: scenePos.x, y: scenePos.y, z: 0 };
      }
      store.updateLayer(newLayer.id, {
        transform: {
          ...newLayer.transform,
          position: {
            ...newLayer.transform!.position,
            value: { x: scenePos.x, y: scenePos.y, z: 0 }
          }
        }
      });
      store.selectLayer(newLayer.id);
      store.setTool('select');
      return;
    }

    // Segment tool - click to segment or start box selection
    if (currentTool === 'segment' && e.button === 0) {
      const rect = canvas.getBoundingClientRect();
      const scenePos = screenToScene(e.clientX - rect.left, e.clientY - rect.top);

      if (store.segmentMode === 'point') {
        // Point mode - segment at click position
        handleSegmentPoint(scenePos.x, scenePos.y);
      } else {
        // Box mode - start box selection (use composable)
        startSegmentBox(scenePos);
      }
      return;
    }

    // Shape tools - start drawing shape (use composable)
    if (['rectangle', 'ellipse', 'polygon', 'star'].includes(currentTool) && e.button === 0) {
      const rect = canvas.getBoundingClientRect();
      const scenePos = screenToScene(e.clientX - rect.left, e.clientY - rect.top);

      startShapeDrawing(currentTool as 'rectangle' | 'ellipse' | 'polygon' | 'star', scenePos);
      canvas.style.cursor = 'crosshair';
      return;
    }

    // Selection - raycast to find layer
    if (currentTool === 'select' && e.button === 0) {
      // Don't handle selection if transform controls are being dragged
      if (engine.value?.isTransformDragging()) {
        return;
      }

      const rect = canvas.getBoundingClientRect();
      const x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
      const y = -((e.clientY - rect.top) / rect.height) * 2 + 1;

      if (engine.value) {
        const hitLayer = engine.value.raycastLayers(x, y);
        if (hitLayer) {
          store.selectLayer(hitLayer);
          engine.value.selectLayer(hitLayer); // Attach transform controls
        } else {
          store.clearSelection();
          engine.value.selectLayer(null); // Detach transform controls
        }
      }
    }
  });

  // Mouse move
  canvas.addEventListener('mousemove', (e: MouseEvent) => {
    if (isPanning && engine.value) {
      const dx = e.clientX - lastPosX;
      const dy = e.clientY - lastPosY;

      lastPosX = e.clientX;
      lastPosY = e.clientY;

      // Convert screen pixels to world units based on current camera setup
      // The camera controller handles all coordinate transforms
      const camera = engine.value.getCameraController();
      const currentPan = camera.getPan();

      // Calculate world units per screen pixel at current zoom
      // When zoomed out (zoom < 1), each screen pixel represents more world units
      const compHeight = store.height || 1080;
      const fovRad = Math.PI * camera.getFOV() / 180;
      const distance = (compHeight / 2) / Math.tan(fovRad / 2) / zoom.value;
      const viewHeight = 2 * distance * Math.tan(fovRad / 2);
      const container = containerRef.value;

      if (container) {
        const rect = container.getBoundingClientRect();
        const worldPerPixel = viewHeight / rect.height;

        // Update pan - negative dx moves camera left (view shifts right)
        camera.setPan(
          currentPan.x - dx * worldPerPixel,
          currentPan.y - dy * worldPerPixel  // Positive dy should move camera up (view shifts down)
        );
        // Force boundary update after camera pan
        triggerGuideUpdate();
      }
      return;
    }

    if (isZooming && engine.value) {
      const dy = zoomStartY - e.clientY;
      const zoomFactor = 1 + dy * 0.01;
      const newZoom = Math.max(0.1, Math.min(10, zoomStartLevel * zoomFactor));

      zoom.value = newZoom;
      viewportTransform.value[0] = newZoom;
      viewportTransform.value[3] = newZoom;

      engine.value.getCameraController().setZoom(newZoom);
      // Force boundary update after camera zoom
      triggerGuideUpdate();
      return;
    }

    // Handle segment box drawing (use composable)
    if (isDrawingSegmentBox.value && store.segmentBoxStart) {
      const rect = canvas.getBoundingClientRect();
      const scenePos = screenToScene(e.clientX - rect.left, e.clientY - rect.top);
      updateSegmentBox(scenePos);
      return;
    }

    // Handle shape drawing (use composable)
    if (isDrawingShape.value && shapeDrawStart.value) {
      const rect = canvas.getBoundingClientRect();
      const scenePos = screenToScene(e.clientX - rect.left, e.clientY - rect.top);
      updateShapeDrawing(scenePos);
      return;
    }

    // Update cursor based on tool
    const currentTool = store.currentTool;
    if (currentTool === 'hand') canvas.style.cursor = 'grab';
    else if (currentTool === 'zoom') canvas.style.cursor = 'zoom-in';
    else if (currentTool === 'text') canvas.style.cursor = 'text';
    else if (currentTool === 'pen') canvas.style.cursor = 'crosshair';
    else if (currentTool === 'segment') canvas.style.cursor = 'crosshair';
    else if (['rectangle', 'ellipse', 'polygon', 'star'].includes(currentTool)) canvas.style.cursor = 'crosshair';
    else canvas.style.cursor = 'default';
  });

  // Mouse up
  canvas.addEventListener('mouseup', (e: MouseEvent) => {
    if (isPanning) {
      isPanning = false;
      canvas.style.cursor = store.currentTool === 'hand' ? 'grab' : 'default';
    }
    if (isZooming) {
      isZooming = false;
    }

    // Finish segment box selection (use composable)
    if (isDrawingSegmentBox.value && store.segmentBoxStart && segmentBoxEnd.value) {
      finishSegmentBox();
    }

    // Finish shape drawing (use composable)
    if (isDrawingShape.value && shapeDrawStart.value && shapeDrawEnd.value) {
      finishShapeDrawing();
    }
  });

  // Mouse leave
  canvas.addEventListener('mouseleave', () => {
    isPanning = false;
    isZooming = false;
    // Cancel segment box selection (use composable)
    if (isDrawingSegmentBox.value) {
      cancelSegmentBox();
    }
    // Cancel shape drawing (use composable)
    if (isDrawingShape.value) {
      cancelShapeDrawing();
    }
  });
}

// Convert screen coordinates to scene coordinates
function screenToScene(screenX: number, screenY: number): { x: number; y: number } {
  const vpt = viewportTransform.value;
  return {
    x: (screenX - vpt[4]) / vpt[0],
    y: (screenY - vpt[5]) / vpt[3]
  };
}

// Shape drawing handlers and segmentation handlers are provided by composables

/**
 * Handle transform changes from TransformControls
 * Updates the store with the new transform values
 */
function handleTransformChange(layerId: string, transform: LayerTransformUpdate) {
  const layer = store.layers.find(l => l.id === layerId);
  if (!layer) return;

  // Build the update object for the store
  const updates: Partial<Layer> = {};

  if (transform.position && layer.transform) {
    updates.transform = {
      ...layer.transform,
      position: {
        ...layer.transform.position,
        value: {
          x: transform.position.x,
          y: transform.position.y,
          z: transform.position.z ?? (layer.transform.position?.value as any)?.z ?? 0
        }
      }
    };
  }

  // Handle rotation - for 3D layers use rotationX/Y/Z, for 2D use rotation
  if (layer.threeD) {
    if (transform.rotationX !== undefined || transform.rotationY !== undefined || transform.rotationZ !== undefined) {
      if (!updates.transform && layer.transform) {
        updates.transform = { ...layer.transform };
      }
      if (updates.transform) {
        if (transform.rotationX !== undefined) {
          updates.transform.rotationX = { ...layer.transform!.rotationX!, value: transform.rotationX };
        }
        if (transform.rotationY !== undefined) {
          updates.transform.rotationY = { ...layer.transform!.rotationY!, value: transform.rotationY };
        }
        if (transform.rotationZ !== undefined) {
          updates.transform.rotationZ = { ...layer.transform!.rotationZ!, value: transform.rotationZ };
        }
      }
    }
  } else {
    // 2D layer: use rotation (Z axis)
    if (transform.rotation !== undefined && layer.transform) {
      if (!updates.transform) {
        updates.transform = { ...layer.transform };
      }
      updates.transform.rotation = { ...layer.transform.rotation!, value: transform.rotation };
    }
  }

  // Handle scale
  if (transform.scale && layer.transform) {
    if (!updates.transform) {
      updates.transform = { ...layer.transform };
    }
    updates.transform.scale = {
      ...layer.transform.scale,
      value: {
        x: transform.scale.x,
        y: transform.scale.y,
        z: transform.scale.z ?? (layer.transform.scale?.value as any)?.z ?? 100
      }
    };
  }

  // Update the store
  if (Object.keys(updates).length > 0) {
    store.updateLayer(layerId, updates);
  }
}

/**
 * Set transform mode (translate/rotate/scale)
 */
function setTransformModeTo(mode: 'translate' | 'rotate' | 'scale') {
  transformMode.value = mode;
  if (engine.value) {
    engine.value.setTransformMode(mode);
  }
}

// Handle resize
function handleResize(entries: ResizeObserverEntry[]) {
  for (const entry of entries) {
    const { width, height } = entry.contentRect;
    if (width > 0 && height > 0) {
      canvasWidth.value = width;
      canvasHeight.value = height;

      if (engine.value) {
        // Resize the renderer and camera aspect
        engine.value.resize(width, height);
        // Re-fit composition to the new viewport size
        centerOnComposition();
      }
    }
  }
}

// Center viewport on composition (fit to screen)
function centerOnComposition() {
  const container = containerRef.value;
  if (!container || !engine.value) return;

  const padding = 40;

  // Use the engine's fit method - this handles all camera setup correctly
  engine.value.fitCompositionToViewport(padding);

  // Update local zoom state to match what the camera calculated
  const camera = engine.value.getCameraController();
  const calculatedZoom = camera.getZoom();
  zoom.value = calculatedZoom;

  // Update viewport transform for SplineEditor and other overlays
  viewportTransform.value = [calculatedZoom, 0, 0, calculatedZoom, 0, 0];

  // Force boundary recalculation after camera state update
  // Use requestAnimationFrame to ensure the render has completed
  requestAnimationFrame(() => {
    cameraUpdateTrigger.value++;
  });
}

// Render mode switching
function setRenderMode(mode: 'color' | 'depth' | 'normal') {
  renderMode.value = mode;
  if (engine.value) {
    engine.value.setRenderMode(mode);
  }
}

// Spline editor handlers
function onPointAdded(_point: ControlPoint) {
  if (!activeSplineLayerId.value) {
    const newLayer = store.createLayer('spline');
    store.selectLayer(newLayer.id);
  }
}

function onPathUpdated() {
  syncLayersToEngine();
}

function togglePenMode() {
  if (store.currentTool === 'pen') {
    store.setTool('select');
  } else {
    store.setTool('pen');
  }
}

// Motion path event handlers
function onMotionPathKeyframeSelected(keyframeId: string, addToSelection: boolean) {
  // Select the keyframe in the store
  if (addToSelection) {
    store.addKeyframeToSelection?.(keyframeId);
  } else {
    store.selectKeyframe?.(keyframeId);
  }
}

function onMotionPathGoToFrame(frame: number) {
  // Go to the keyframe's frame
  store.setFrame(frame);
}

function onMotionPathTangentUpdated(
  keyframeId: string,
  tangentType: 'in' | 'out',
  delta: { x: number; y: number }
) {
  // Get the selected layer (motion path only shows for single selected layer)
  const layerId = store.selectedLayerIds?.[0];
  if (!layerId) return;

  // Get the layer and its position property
  const layer = store.getLayerById?.(layerId);
  if (!layer) return;

  const positionProp = layer.transform?.position;
  if (!positionProp?.keyframes) return;

  // Find the keyframe by ID
  const keyframe = positionProp.keyframes.find(kf => kf.id === keyframeId);
  if (!keyframe) return;

  // Initialize spatial tangent if not present
  const tangentKey = tangentType === 'in' ? 'spatialInTangent' : 'spatialOutTangent';
  if (!keyframe[tangentKey]) {
    keyframe[tangentKey] = { x: 0, y: 0, z: 0 };
  }

  // Apply delta to spatial tangent
  keyframe[tangentKey]!.x += delta.x;
  keyframe[tangentKey]!.y += delta.y;

  // Mark layer as dirty for re-evaluation
  store.markLayerDirty?.(layerId);

  // Mark project as modified
  if (store.project?.meta) {
    store.project.meta.modified = new Date().toISOString();
  }
}

// Zoom controls
function zoomIn() {
  const newZoom = Math.min(zoom.value * 1.2, 10);
  zoom.value = newZoom;
  viewportTransform.value[0] = newZoom;
  viewportTransform.value[3] = newZoom;
  if (engine.value) {
    engine.value.setViewportTransform(viewportTransform.value);
  }
}

function zoomOut() {
  const newZoom = Math.max(zoom.value * 0.8, 0.1);
  zoom.value = newZoom;
  viewportTransform.value[0] = newZoom;
  viewportTransform.value[3] = newZoom;
  if (engine.value) {
    engine.value.setViewportTransform(viewportTransform.value);
  }
}

function fitToView() {
  centerOnComposition();
}

/**
 * Reset camera to default 3D viewing position
 * Perfect focal length to see full composition
 */
function resetCamera() {
  if (engine.value) {
    engine.value.resetCameraToDefault();
    // Re-center on composition after reset
    centerOnComposition();
  }
}

/**
 * Toggle composition grid visibility
 */
function toggleGrid() {
  // Update through store - the watch will sync to local ref and engine
  store.updateViewOptions({ showGrid: !store.viewOptions.showGrid });
}

/**
 * Toggle outside overlay (safe area) visibility
 * Uses CSS-based overlays for screen-space guides that stay fixed
 */
function toggleOutsideOverlay() {
  showOutsideOverlay.value = !showOutsideOverlay.value;
  showSafeFrameGuides.value = showOutsideOverlay.value;
  // Note: We no longer use the 3D overlay from engine
  // The CSS safe frame guides provide the same visual effect
  // but stay fixed to the screen regardless of camera movement
}

/**
 * Toggle resolution crop guides (480p/720p/1080p)
 * Shows center-based crop guides for standard export resolutions
 */
function toggleResolutionGuides() {
  showResolutionGuides.value = !showResolutionGuides.value;
}

/**
 * Set zoom to a specific level (0.1 to 10)
 */
function setZoom(newZoom: number) {
  newZoom = Math.max(0.1, Math.min(10, newZoom));
  zoom.value = newZoom;
  viewportTransform.value[0] = newZoom;
  viewportTransform.value[3] = newZoom;
  if (engine.value) {
    engine.value.setViewportTransform(viewportTransform.value);
  }
}

/**
 * Handle zoom dropdown selection
 */
function onZoomSelect() {
  if (zoomLevel.value === 'fit') {
    fitToView();
  } else {
    const newZoom = parseFloat(zoomLevel.value);
    if (!isNaN(newZoom)) {
      setZoom(newZoom);
      if (engine.value) {
        engine.value.getCameraController().setZoom(newZoom);
      }
    }
  }
}

/**
 * Handle resolution dropdown change
 */
function onResolutionChange() {
  if (!engine.value) return;

  const comp = store.getActiveComp();
  if (!comp) return;

  const fullWidth = comp.settings.width;
  const fullHeight = comp.settings.height;

  let factor = 1;
  switch (resolution.value) {
    case 'half': factor = 0.5; break;
    case 'third': factor = 1/3; break;
    case 'quarter': factor = 0.25; break;
    default: factor = 1;
  }

  const newWidth = Math.round(fullWidth * factor);
  const newHeight = Math.round(fullHeight * factor);

  // Update renderer resolution (affects render quality)
  engine.value.setResolution(newWidth, newHeight);
  console.log(`[ThreeCanvas] Resolution changed to ${resolution.value}: ${newWidth}x${newHeight}`);
}

// Capture frame for export
async function captureFrame(): Promise<string | null> {
  if (!engine.value) return null;

  const result = engine.value.captureFrame();
  if (!result?.imageData) return null;

  // Convert ImageData to data URL
  const canvas = document.createElement('canvas');
  canvas.width = result.width;
  canvas.height = result.height;
  const ctx = canvas.getContext('2d');
  if (!ctx) return null;

  ctx.putImageData(result.imageData, 0, 0);
  return canvas.toDataURL('image/png');
}

// Capture depth for ComfyUI
async function captureDepth(): Promise<string | null> {
  if (!engine.value) return null;

  const result = engine.value.captureDepth();
  if (!result?.depthBuffer) return null;

  // Convert depth buffer to grayscale image data URL
  const canvas = document.createElement('canvas');
  canvas.width = result.width;
  canvas.height = result.height;
  const ctx = canvas.getContext('2d');
  if (!ctx) return null;

  const imageData = ctx.createImageData(result.width, result.height);
  for (let i = 0; i < result.depthBuffer.length; i++) {
    const value = Math.floor(result.depthBuffer[i] * 255);
    const idx = i * 4;
    imageData.data[idx] = value;     // R
    imageData.data[idx + 1] = value; // G
    imageData.data[idx + 2] = value; // B
    imageData.data[idx + 3] = 255;   // A
  }

  ctx.putImageData(imageData, 0, 0);
  return canvas.toDataURL('image/png');
}

// Watch depth overlay settings
watch(showDepthOverlay, (visible) => {
  if (engine.value) {
    engine.value.setDepthOverlayVisible(visible);
  }
});

watch(depthColormap, (colormap) => {
  if (engine.value) {
    engine.value.setDepthColormap(colormap);
  }
});

watch(depthOpacity, (opacity) => {
  if (engine.value) {
    engine.value.setDepthOpacity(opacity / 100);
  }
});

// Expose public methods
defineExpose({
  engine,
  fitToView,
  zoomIn,
  zoomOut,
  zoom,
  setZoom,
  captureFrame,
  captureDepth,
  showPerformance,
  performanceStats,
  renderMode,
  setRenderMode,
  transformMode,
  setTransformModeTo,
  resetCamera
});
</script>

<style scoped>
.three-canvas {
  position: relative;
  width: 100%;
  height: 100%;
  flex: 1;
  min-height: 0;
  overflow: hidden;
  background: #1a1a1a;
}

.three-canvas.drag-over {
  outline: 2px dashed var(--lattice-accent, #8B5CF6);
  outline-offset: -4px;
  background: rgba(139, 92, 246, 0.1);
}

.three-canvas canvas {
  display: block;
  width: 100%;
  height: 100%;
}

.overlay-controls {
  position: absolute;
  top: 12px;
  right: 12px;
  display: flex;
  align-items: center;
  gap: 8px;
  background: rgba(0, 0, 0, 0.7);
  padding: 6px 10px;
  border-radius: 6px;
  font-size: 12px;
  z-index: 10;
}

.overlay-controls label {
  display: flex;
  align-items: center;
  gap: 4px;
  cursor: pointer;
  color: #e0e0e0;
}

.colormap-select {
  background: #3a3a3a;
  border: none;
  color: #e0e0e0;
  padding: 2px 6px;
  border-radius: 4px;
  font-size: 12px;
}

.opacity-slider {
  width: 60px;
  height: 4px;
  cursor: pointer;
}

.render-mode-controls {
  position: absolute;
  top: 12px;
  left: 12px;
  display: flex;
  gap: 4px;
  background: rgba(0, 0, 0, 0.7);
  padding: 4px;
  border-radius: 6px;
  z-index: 10;
}

.render-mode-controls button {
  background: transparent;
  border: none;
  color: #888;
  padding: 6px 10px;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.15s ease;
}

.render-mode-controls button:hover {
  background: rgba(255, 255, 255, 0.1);
  color: #e0e0e0;
}

.render-mode-controls button.active {
  background: #4a90d9;
  color: #fff;
}

.controls-divider {
  width: 1px;
  height: 20px;
  background: #555;
  margin: 0 4px;
}

.transform-mode-controls {
  position: absolute;
  top: 52px;
  left: 12px;
  display: flex;
  gap: 4px;
  background: rgba(0, 0, 0, 0.7);
  padding: 4px;
  border-radius: 6px;
  z-index: 10;
}

.transform-mode-controls button {
  background: transparent;
  border: none;
  color: #888;
  padding: 6px 10px;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.15s ease;
}

.transform-mode-controls button:hover {
  background: rgba(255, 255, 255, 0.1);
  color: #e0e0e0;
}

.transform-mode-controls button.active {
  background: #ff9900;
  color: #fff;
}

.performance-overlay {
  position: absolute;
  bottom: 12px;
  left: 12px;
  display: flex;
  gap: 12px;
  background: rgba(0, 0, 0, 0.7);
  padding: 6px 10px;
  border-radius: 6px;
  font-size: 13px;
  font-family: monospace;
  color: #8f8;
  z-index: 10;
}

.loading-overlay {
  position: absolute;
  inset: 0;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  background: rgba(0, 0, 0, 0.7);
  color: #e0e0e0;
  gap: 12px;
  z-index: 20;
}

.loading-spinner {
  width: 32px;
  height: 32px;
  border: 3px solid #3a3a3a;
  border-top-color: #4a90d9;
  border-radius: 50%;
  animation: spin 1s linear infinite;
}

@keyframes spin {
  to { transform: rotate(360deg); }
}

/* Segmentation overlays */
.segment-mask-overlay {
  position: absolute;
  pointer-events: none;
  z-index: 15;
}

.segment-mask-overlay .mask-preview {
  width: 100%;
  height: 100%;
  object-fit: fill;
  opacity: 0.6;
  filter: drop-shadow(0 0 3px #00ff00);
  /* Colorize the mask green for visibility */
  mix-blend-mode: screen;
}

.segment-box-preview {
  position: absolute;
  border: 2px dashed #00ff00;
  background: rgba(0, 255, 0, 0.1);
  pointer-events: none;
  z-index: 15;
}

.shape-preview {
  position: absolute;
  pointer-events: none;
  z-index: 15;
  overflow: visible;
}

.shape-preview path {
  fill: rgba(139, 92, 246, 0.2);
  stroke: var(--lattice-accent, #8B5CF6);
  stroke-width: 2;
  stroke-dasharray: 5, 3;
}

.segment-loading {
  position: absolute;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 8px;
  background: rgba(0, 0, 0, 0.85);
  padding: 16px 24px;
  border-radius: 8px;
  z-index: 20;
  color: #e0e0e0;
  font-size: 14px;
}

.segment-spinner {
  width: 24px;
  height: 24px;
  border: 3px solid #3a3a3a;
  border-top-color: #00ff00;
  border-radius: 50%;
  animation: spin 0.8s linear infinite;
}

/* CSS-based Composition Boundary - crisp blue border */
/* Replaces the 3D LineLoop which has blurry rendering due to WebGL linewidth limitation */
.composition-boundary {
  position: absolute;
  pointer-events: none;
  z-index: 4;
  border: 2px solid #4a90d9;
  box-sizing: border-box;
  /* GPU-accelerated rendering for smooth updates during zoom/pan */
  will-change: transform, left, top, width, height;
}

/* Safe Frame Guides - CSS-based screen-space overlays */
/* These stay fixed regardless of 3D camera movement */
.safe-frame-container {
  position: absolute;
  inset: 0;
  pointer-events: none;
  z-index: 5;
  overflow: hidden;
}

.safe-frame-overlay {
  position: absolute;
  background: rgba(0, 0, 0, 0.5);
  pointer-events: none;
}

/* Alternative: Use subtle border instead of dark overlay */
/* Uncomment below for border-style guides like C4D */
/*
.safe-frame-overlay {
  position: absolute;
  background: transparent;
  border: 1px solid rgba(100, 100, 100, 0.3);
}
*/

/* Resolution Crop Guides - Center-based dotted boxes for 480p/720p/1080p */
.resolution-guides-container {
  position: absolute;
  inset: 0;
  pointer-events: none;
  z-index: 6;
  overflow: hidden;
}

.resolution-crop-box {
  position: absolute;
  border: 2px dashed;
  background: transparent;
  pointer-events: none;
  box-sizing: border-box;
}

.resolution-label {
  position: absolute;
  top: 4px;
  right: 4px;
  font-size: 10px;
  font-weight: 600;
  padding: 2px 6px;
  background: rgba(0, 0, 0, 0.7);
  border-radius: 2px;
  letter-spacing: 0.5px;
  text-transform: uppercase;
  white-space: nowrap;
}

/* Viewer Controls (AE-style bottom bar) - positioned bottom-left */
.viewer-controls {
  position: absolute;
  bottom: 12px;
  left: 12px;
  display: flex;
  align-items: center;
  gap: 12px;
  background: rgba(26, 26, 26, 0.95);
  padding: 8px 16px;
  border-radius: 6px;
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  z-index: 15;
}

.zoom-dropdown,
.resolution-dropdown {
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: 13px;
  padding: 6px 12px;
  border-radius: 4px;
  cursor: pointer;
  min-width: 70px;
}

.zoom-dropdown:hover,
.resolution-dropdown:hover {
  background: #3a3a3a;
  border-color: #555;
}

.zoom-dropdown:focus,
.resolution-dropdown:focus {
  outline: none;
  border-color: #4a90d9;
}

.zoom-display {
  color: #4a90d9;
  font-family: 'Consolas', monospace;
  font-size: 13px;
  min-width: 40px;
  text-align: right;
}

.viewer-divider {
  width: 1px;
  height: 16px;
  background: #444;
}

/* Marquee Selection Rectangle */
.marquee-selection {
  position: absolute;
  border: 1px dashed var(--lattice-accent, #8B5CF6);
  background: rgba(139, 92, 246, 0.1);
  pointer-events: none;
  z-index: 20;
  box-sizing: border-box;
}

.marquee-mode-indicator {
  position: absolute;
  top: -20px;
  left: 0;
  background: var(--lattice-accent, #8B5CF6);
  color: white;
  padding: 2px 6px;
  border-radius: 3px;
  font-size: 12px;
  font-weight: bold;
}
</style>
