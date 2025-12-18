<template>
  <div class="viewport-renderer" :class="[`layout-${layout}`]">
    <!-- View panels based on layout -->
    <div
      v-for="(viewType, index) in activeViews"
      :key="index"
      class="view-panel"
      :class="{ active: index === activeViewIndex }"
      @click="setActiveView(index)"
    >
      <!-- View header -->
      <div class="view-header">
        <select
          :value="viewType"
          @change="updateViewType(index, ($event.target as HTMLSelectElement).value as ViewType)"
          class="view-select"
        >
          <option value="active-camera">Active Camera</option>
          <option value="custom-1">Custom View 1</option>
          <option value="custom-2">Custom View 2</option>
          <option value="custom-3">Custom View 3</option>
          <option value="front">Front</option>
          <option value="back">Back</option>
          <option value="left">Left</option>
          <option value="right">Right</option>
          <option value="top">Top</option>
          <option value="bottom">Bottom</option>
        </select>

        <div class="view-tools">
          <button
            v-if="isCustomView(viewType)"
            @click.stop="resetCustomView(viewType)"
            title="Reset View"
          >
            <span class="icon">↺</span>
          </button>
        </div>
      </div>

      <!-- Canvas for this view -->
      <canvas
        :ref="el => setCanvasRef(el as HTMLCanvasElement, index)"
        class="view-canvas"
        @mousedown="onCanvasMouseDown($event, index)"
        @wheel="onCanvasWheel($event, index)"
        @contextmenu.prevent
      />

      <!-- View info overlay -->
      <div class="view-info">
        <span class="view-name">{{ getViewDisplayName(viewType) }}</span>
        <span v-if="isCustomView(viewType)" class="view-coords">
          θ: {{ Math.round(customViews[viewType]?.orbitTheta ?? 0) }}°
          φ: {{ Math.round(customViews[viewType]?.orbitPhi ?? 0) }}°
        </span>
      </div>
    </div>

    <!-- Layout selector -->
    <div class="layout-controls">
      <button
        v-for="layoutOption in layoutOptions"
        :key="layoutOption.value"
        :class="{ active: layout === layoutOption.value }"
        @click="setLayout(layoutOption.value)"
        :title="layoutOption.label"
      >
        {{ layoutOption.icon }}
      </button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted } from 'vue';
import type {
  Camera3D,
  ViewType,
  ViewLayout,
  ViewportState,
  CustomViewState,
  ViewOptions
} from '../../types/camera';
import {
  generateCameraVisualization,
  getCameraViewMatrices,
  getOrthoViewMatrices,
  projectToScreen,
  generate3DAxes,
  generateGrid,
  type LineSegment,
  type ViewMatrices
} from '../../services/camera3DVisualization';
import { vec3 } from '../../services/math3d';
import { useCompositorStore } from '@/stores/compositorStore';

// Store connection
const store = useCompositorStore();

// Get data from store
const camera = computed<Camera3D | null>(() => store.activeCamera);
const compWidth = computed(() => store.width);
const compHeight = computed(() => store.height);
const viewportState = computed(() => store.viewportState);
const viewOptions = computed(() => store.viewOptions);

// Build layers array from store layers
const layers = computed(() => {
  return store.layers
    .filter(l => l.type !== 'camera') // Exclude camera layers themselves
    .map(l => ({
      id: l.id,
      name: l.name,
      position: {
        x: l.transform.position.value.x,
        y: l.transform.position.value.y,
        z: 0 // 2D layers at z=0
      },
      selected: store.selectedLayerIds.includes(l.id)
    }));
});

// Canvas refs for each view
const canvasRefs = ref<(HTMLCanvasElement | null)[]>([null, null, null, null]);
const contexts = ref<(CanvasRenderingContext2D | null)[]>([null, null, null, null]);

// Interaction state
const isDragging = ref(false);
const dragStartPos = ref({ x: 0, y: 0 });
const dragViewIndex = ref(0);
const dragButton = ref(0);

// Layout options
const layoutOptions = [
  { value: '1-view' as ViewLayout, label: '1 View', icon: '□' },
  { value: '2-view-horizontal' as ViewLayout, label: '2 Views Horizontal', icon: '⬚' },
  { value: '2-view-vertical' as ViewLayout, label: '2 Views Vertical', icon: '⬛' },
  { value: '4-view' as ViewLayout, label: '4 Views', icon: '⊞' },
];

// Computed properties
const layout = computed(() => viewportState.value.layout);
const activeViewIndex = computed(() => viewportState.value.activeViewIndex);
const customViews = computed(() => viewportState.value.customViews);

const activeViews = computed(() => {
  switch (viewportState.value.layout) {
    case '1-view':
      return [viewportState.value.views[0]];
    case '2-view-horizontal':
    case '2-view-vertical':
      return viewportState.value.views.slice(0, 2);
    case '4-view':
      return viewportState.value.views.slice(0, 4);
    default:
      return [viewportState.value.views[0]];
  }
});

function setCanvasRef(el: HTMLCanvasElement | null, index: number) {
  canvasRefs.value[index] = el;
  if (el) {
    contexts.value[index] = el.getContext('2d');
  }
}

function isCustomView(viewType: ViewType): viewType is 'custom-1' | 'custom-2' | 'custom-3' {
  return viewType.startsWith('custom-');
}

function getViewDisplayName(viewType: ViewType): string {
  const names: Record<ViewType, string> = {
    'active-camera': 'Camera',
    'custom-1': 'Custom 1',
    'custom-2': 'Custom 2',
    'custom-3': 'Custom 3',
    'front': 'Front',
    'back': 'Back',
    'left': 'Left',
    'right': 'Right',
    'top': 'Top',
    'bottom': 'Bottom',
  };
  return names[viewType];
}

function setActiveView(index: number) {
  store.updateViewportState({
    activeViewIndex: index
  });
}

function updateViewType(index: number, viewType: ViewType) {
  const newViews = [...viewportState.value.views];
  newViews[index] = viewType;
  store.updateViewportState({
    views: newViews
  });
}

function setLayout(newLayout: ViewLayout) {
  // Default views for 4-view layout: active-camera, top, front, right
  const defaultFourViews: ViewType[] = ['active-camera', 'top', 'front', 'right'];

  // Ensure we have enough views
  let newViews = [...viewportState.value.views];
  while (newViews.length < 4) {
    // Fill with appropriate defaults from our 4-view preset
    newViews.push(defaultFourViews[newViews.length] || 'front');
  }

  store.updateViewportState({
    layout: newLayout,
    views: newViews,
    activeViewIndex: Math.min(viewportState.value.activeViewIndex, getViewCount(newLayout) - 1)
  });
}

function getViewCount(layout: ViewLayout): number {
  switch (layout) {
    case '1-view': return 1;
    case '2-view-horizontal':
    case '2-view-vertical': return 2;
    case '4-view': return 4;
    default: return 1;
  }
}

function resetCustomView(viewType: 'custom-1' | 'custom-2' | 'custom-3') {
  const defaultView: CustomViewState = {
    orbitCenter: { x: compWidth.value / 2, y: compHeight.value / 2, z: 0 },
    orbitDistance: 2000,
    orbitPhi: 60,
    orbitTheta: 45,
    orthoZoom: 1,
    orthoOffset: { x: 0, y: 0 }
  };

  store.updateViewportState({
    customViews: {
      ...viewportState.value.customViews,
      [viewType]: defaultView
    }
  });
}

// Mouse interaction handlers
function onCanvasMouseDown(e: MouseEvent, viewIndex: number) {
  isDragging.value = true;
  dragStartPos.value = { x: e.clientX, y: e.clientY };
  dragViewIndex.value = viewIndex;
  dragButton.value = e.button;

  document.addEventListener('mousemove', onCanvasMouseMove);
  document.addEventListener('mouseup', onCanvasMouseUp);
}

function onCanvasMouseMove(e: MouseEvent) {
  if (!isDragging.value) return;

  const dx = e.clientX - dragStartPos.value.x;
  const dy = e.clientY - dragStartPos.value.y;
  dragStartPos.value = { x: e.clientX, y: e.clientY };

  const viewType = activeViews.value[dragViewIndex.value];

  if (isCustomView(viewType)) {
    const customView = customViews.value[viewType];

    if (dragButton.value === 0) {
      // Left button: orbit
      const newTheta = customView.orbitTheta + dx * 0.5;
      const newPhi = Math.max(1, Math.min(179, customView.orbitPhi + dy * 0.5));

      store.updateViewportState({
        customViews: {
          ...viewportState.value.customViews,
          [viewType]: {
            ...customView,
            orbitTheta: newTheta,
            orbitPhi: newPhi
          }
        }
      });
    } else if (dragButton.value === 1 || dragButton.value === 2) {
      // Middle/right button: pan
      store.updateViewportState({
        customViews: {
          ...viewportState.value.customViews,
          [viewType]: {
            ...customView,
            orthoOffset: {
              x: customView.orthoOffset.x + dx,
              y: customView.orthoOffset.y + dy
            }
          }
        }
      });
    }
  }
}

function onCanvasMouseUp() {
  isDragging.value = false;
  document.removeEventListener('mousemove', onCanvasMouseMove);
  document.removeEventListener('mouseup', onCanvasMouseUp);
}

function onCanvasWheel(e: WheelEvent, viewIndex: number) {
  e.preventDefault();

  const viewType = activeViews.value[viewIndex];

  if (isCustomView(viewType)) {
    const customView = customViews.value[viewType];
    const zoomFactor = e.deltaY > 0 ? 1.1 : 0.9;

    store.updateViewportState({
      customViews: {
        ...viewportState.value.customViews,
        [viewType]: {
          ...customView,
          orbitDistance: customView.orbitDistance * zoomFactor
        }
      }
    });
  }
}

// Rendering
function render() {
  activeViews.value.forEach((viewType, index) => {
    const canvas = canvasRefs.value[index];
    const ctx = contexts.value[index];
    if (!canvas || !ctx) return;

    // Update canvas size
    const rect = canvas.getBoundingClientRect();
    const dpr = window.devicePixelRatio || 1;
    canvas.width = rect.width * dpr;
    canvas.height = rect.height * dpr;
    ctx.scale(dpr, dpr);

    // Clear
    ctx.fillStyle = '#1a1a1a';
    ctx.fillRect(0, 0, rect.width, rect.height);

    // Get view matrices
    let matrices: ViewMatrices;
    if (viewType === 'active-camera' && camera.value) {
      matrices = getCameraViewMatrices(camera.value, compWidth.value, compHeight.value);
    } else if (isCustomView(viewType)) {
      matrices = getOrthoViewMatrices(viewType, compWidth.value, compHeight.value, customViews.value[viewType]);
    } else {
      matrices = getOrthoViewMatrices(viewType, compWidth.value, compHeight.value);
    }

    // Collect all lines to draw
    const lines: LineSegment[] = [];

    // Grid
    if (viewOptions.value.showGrid) {
      lines.push(...generateGrid(compWidth.value, compHeight.value));
    }

    // 3D axes
    if (viewOptions.value.show3DReferenceAxes) {
      lines.push(...generate3DAxes(vec3(compWidth.value / 2, compHeight.value / 2, 0)));
    }

    // Composition bounds
    if (viewOptions.value.showCompositionBounds) {
      const viz = generateCameraVisualization(
        camera.value ?? createDummyCamera(),
        compWidth.value,
        compHeight.value,
        false,
        true,
        false
      );
      lines.push(...viz.compositionBounds);
    }

    // Camera visualization (not for active-camera view)
    if (viewType !== 'active-camera' && camera.value) {
      const showWireframe = viewOptions.value.cameraWireframes === 'always' ||
        (viewOptions.value.cameraWireframes === 'selected');

      if (showWireframe) {
        const viz = generateCameraVisualization(
          camera.value,
          compWidth.value,
          compHeight.value,
          true,
          false,
          viewOptions.value.showFocalPlane
        );
        lines.push(...viz.body);
        lines.push(...viz.frustum);
        lines.push(...viz.focalPlane);
        if (viz.poiLine) {
          lines.push(viz.poiLine);
        }
      }
    }

    // Draw all lines
    for (const line of lines) {
      const start = projectToScreen(line.start, matrices.viewProjection, rect.width, rect.height);
      const end = projectToScreen(line.end, matrices.viewProjection, rect.width, rect.height);

      if (!start.visible && !end.visible) continue;

      ctx.beginPath();
      ctx.strokeStyle = line.color;
      ctx.lineWidth = 1;
      ctx.moveTo(start.x, start.y);
      ctx.lineTo(end.x, end.y);
      ctx.stroke();
    }

    // Draw layer handles
    if (viewOptions.value.showLayerHandles) {
      for (const layer of layers.value) {
        const pos = projectToScreen(layer.position, matrices.viewProjection, rect.width, rect.height);
        if (!pos.visible) continue;

        ctx.beginPath();
        ctx.fillStyle = layer.selected ? '#ffcc00' : '#888888';
        ctx.arc(pos.x, pos.y, layer.selected ? 6 : 4, 0, Math.PI * 2);
        ctx.fill();

        ctx.fillStyle = '#ffffff';
        ctx.font = '10px sans-serif';
        ctx.fillText(layer.name, pos.x + 8, pos.y + 4);
      }
    }
  });
}

function createDummyCamera(): Camera3D {
  return {
    id: 'dummy',
    name: 'Dummy',
    type: 'two-node',
    position: { x: compWidth.value / 2, y: compHeight.value / 2, z: -1500 },
    pointOfInterest: { x: compWidth.value / 2, y: compHeight.value / 2, z: 0 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    zoom: 1778,
    focalLength: 50,
    angleOfView: 39.6,
    filmSize: 36,
    measureFilmSize: 'horizontal',
    depthOfField: {
      enabled: false,
      focusDistance: 1500,
      aperture: 50,
      fStop: 2.8,
      blurLevel: 1,
      lockToZoom: false
    },
    iris: {
      shape: 7,
      rotation: 0,
      roundness: 0,
      aspectRatio: 1,
      diffractionFringe: 0
    },
    highlight: {
      gain: 0,
      threshold: 1,
      saturation: 1
    },
    autoOrient: 'off',
    nearClip: 1,
    farClip: 10000
  };
}

// Animation loop
let animationId: number;

function animate() {
  render();
  animationId = requestAnimationFrame(animate);
}

// Keyboard shortcut handler
function onKeyDown(e: KeyboardEvent) {
  // Only handle if viewport is focused (not typing in input)
  if (document.activeElement?.tagName === 'INPUT' ||
      document.activeElement?.tagName === 'TEXTAREA' ||
      document.activeElement?.tagName === 'SELECT') {
    return;
  }

  const activeView = activeViews.value[activeViewIndex.value];

  // Numpad shortcuts for view presets
  switch (e.code) {
    case 'Numpad1':
      if (e.ctrlKey) {
        // Ctrl+Numpad1 = Back view
        updateViewType(activeViewIndex.value, 'back');
      } else {
        // Numpad1 = Front view
        updateViewType(activeViewIndex.value, 'front');
      }
      e.preventDefault();
      break;

    case 'Numpad3':
      if (e.ctrlKey) {
        // Ctrl+Numpad3 = Left view
        updateViewType(activeViewIndex.value, 'left');
      } else {
        // Numpad3 = Right view
        updateViewType(activeViewIndex.value, 'right');
      }
      e.preventDefault();
      break;

    case 'Numpad7':
      if (e.ctrlKey) {
        // Ctrl+Numpad7 = Bottom view
        updateViewType(activeViewIndex.value, 'bottom');
      } else {
        // Numpad7 = Top view
        updateViewType(activeViewIndex.value, 'top');
      }
      e.preventDefault();
      break;

    case 'Numpad0':
      // Numpad0 = Active camera view
      updateViewType(activeViewIndex.value, 'active-camera');
      e.preventDefault();
      break;

    case 'Numpad5':
      // Numpad5 = Toggle between ortho and perspective (switch to custom)
      if (!isCustomView(activeView)) {
        // Switch to custom view with current orientation
        const targetView = 'custom-1' as const;
        let theta = 0;
        let phi = 90;

        // Map current ortho view to spherical coords
        switch (activeView) {
          case 'front': theta = 0; phi = 90; break;
          case 'back': theta = 180; phi = 90; break;
          case 'left': theta = -90; phi = 90; break;
          case 'right': theta = 90; phi = 90; break;
          case 'top': theta = 0; phi = 1; break;
          case 'bottom': theta = 0; phi = 179; break;
          default: theta = 45; phi = 60;
        }

        store.updateViewportState({
          customViews: {
            ...viewportState.value.customViews,
            [targetView]: {
              ...viewportState.value.customViews[targetView],
              orbitTheta: theta,
              orbitPhi: phi,
            }
          }
        });
        updateViewType(activeViewIndex.value, targetView);
      } else {
        // Already in custom view, snap to nearest ortho view
        const theta = customViews.value[activeView].orbitTheta % 360;
        const phi = customViews.value[activeView].orbitPhi;

        // Determine closest ortho view
        let closestView: ViewType = 'front';
        if (phi < 30) {
          closestView = 'top';
        } else if (phi > 150) {
          closestView = 'bottom';
        } else {
          // Check theta for horizontal views
          const normalizedTheta = ((theta % 360) + 360) % 360;
          if (normalizedTheta >= 315 || normalizedTheta < 45) {
            closestView = 'front';
          } else if (normalizedTheta >= 45 && normalizedTheta < 135) {
            closestView = 'right';
          } else if (normalizedTheta >= 135 && normalizedTheta < 225) {
            closestView = 'back';
          } else {
            closestView = 'left';
          }
        }
        updateViewType(activeViewIndex.value, closestView);
      }
      e.preventDefault();
      break;

    case 'NumpadDecimal':
    case 'Period':
      // Focus on selected layer
      focusOnSelectedLayer();
      e.preventDefault();
      break;

    case 'Home':
      // Reset view
      if (isCustomView(activeView)) {
        resetCustomView(activeView);
      }
      e.preventDefault();
      break;

    case 'KeyG':
      // Toggle grid
      if (!e.ctrlKey && !e.metaKey) {
        store.updateViewOptions({
          showGrid: !viewOptions.value.showGrid
        });
        e.preventDefault();
      }
      break;

    case 'KeyH':
      // Toggle layer handles
      if (!e.ctrlKey && !e.metaKey) {
        store.updateViewOptions({
          showLayerHandles: !viewOptions.value.showLayerHandles
        });
        e.preventDefault();
      }
      break;

    case 'KeyC':
      // Toggle composition bounds
      if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
        store.updateViewOptions({
          showCompositionBounds: !viewOptions.value.showCompositionBounds
        });
        e.preventDefault();
      }
      break;

    case 'KeyA':
      // Toggle 3D axes
      if (!e.ctrlKey && !e.metaKey && e.shiftKey) {
        store.updateViewOptions({
          show3DReferenceAxes: !viewOptions.value.show3DReferenceAxes
        });
        e.preventDefault();
      }
      break;
  }
}

function focusOnSelectedLayer() {
  // Find first selected layer
  const selectedLayer = store.layers.find(l => store.selectedLayerIds.includes(l.id));
  if (!selectedLayer) return;

  // Get layer bounds (simplified - assumes layer at origin with 100x100 size)
  const pos = selectedLayer.transform.position.value;
  const width = 100; // Would need actual layer dimensions
  const height = 100;

  // Update custom view to focus on layer
  const activeView = activeViews.value[activeViewIndex.value];
  if (isCustomView(activeView)) {
    store.updateViewportState({
      customViews: {
        ...viewportState.value.customViews,
        [activeView]: {
          ...customViews.value[activeView],
          orbitCenter: { x: pos.x + width / 2, y: pos.y + height / 2, z: 0 },
          orbitDistance: Math.max(width, height) * 3, // Zoom to fit
        }
      }
    });
  }
}

onMounted(() => {
  animate();
  // Add keyboard listener
  window.addEventListener('keydown', onKeyDown);
});

onUnmounted(() => {
  cancelAnimationFrame(animationId);
  // Remove keyboard listener
  window.removeEventListener('keydown', onKeyDown);
});

// Re-render when store values change
watch([camera, viewportState, viewOptions, layers], () => {
  // Animation loop handles this
}, { deep: true });
</script>

<style scoped>
.viewport-renderer {
  position: relative;
  width: 100%;
  height: 100%;
  display: grid;
  gap: 2px;
  background: #0a0a0a;
}

.layout-1-view {
  grid-template-columns: 1fr;
  grid-template-rows: 1fr;
}

.layout-2-view-horizontal {
  grid-template-columns: 1fr 1fr;
  grid-template-rows: 1fr;
}

.layout-2-view-vertical {
  grid-template-columns: 1fr;
  grid-template-rows: 1fr 1fr;
}

.layout-4-view {
  grid-template-columns: 1fr 1fr;
  grid-template-rows: 1fr 1fr;
}

.view-panel {
  position: relative;
  background: #1a1a1a;
  border: 1px solid #333;
  overflow: hidden;
}

.view-panel.active {
  border-color: #7c9cff;
}

.view-header {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  height: 24px;
  display: flex;
  align-items: center;
  padding: 0 4px;
  background: rgba(0, 0, 0, 0.7);
  z-index: 10;
}

.view-select {
  flex: 1;
  background: transparent;
  border: none;
  color: #888;
  font-size: 13px;
  cursor: pointer;
  outline: none;
}

.view-select:hover {
  color: #e0e0e0;
}

.view-tools {
  display: flex;
  gap: 4px;
}

.view-tools button {
  width: 20px;
  height: 20px;
  border: none;
  background: transparent;
  color: #666;
  cursor: pointer;
  font-size: 12px;
}

.view-tools button:hover {
  color: #e0e0e0;
}

.view-canvas {
  width: 100%;
  height: 100%;
  display: block;
}

.view-info {
  position: absolute;
  bottom: 4px;
  left: 4px;
  display: flex;
  gap: 8px;
  font-size: 12px;
  color: #666;
  pointer-events: none;
}

.layout-controls {
  position: absolute;
  top: 4px;
  right: 4px;
  display: flex;
  gap: 2px;
  z-index: 20;
}

.layout-controls button {
  width: 24px;
  height: 24px;
  border: 1px solid #333;
  border-radius: 3px;
  background: rgba(30, 30, 30, 0.9);
  color: #666;
  cursor: pointer;
  font-size: 12px;
}

.layout-controls button:hover {
  background: #333;
  color: #e0e0e0;
}

.layout-controls button.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}
</style>
