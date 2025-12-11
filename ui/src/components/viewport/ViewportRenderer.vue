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

interface Props {
  camera: Camera3D | null;
  compWidth: number;
  compHeight: number;
  viewportState: ViewportState;
  viewOptions: ViewOptions;
  layers?: Array<{
    id: string;
    name: string;
    position: { x: number; y: number; z: number };
    selected: boolean;
  }>;
}

const props = withDefaults(defineProps<Props>(), {
  layers: () => []
});

const emit = defineEmits<{
  (e: 'update:viewportState', state: ViewportState): void;
  (e: 'selectLayer', layerId: string): void;
}>();

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
const layout = computed(() => props.viewportState.layout);
const activeViewIndex = computed(() => props.viewportState.activeViewIndex);
const customViews = computed(() => props.viewportState.customViews);

const activeViews = computed(() => {
  switch (props.viewportState.layout) {
    case '1-view':
      return [props.viewportState.views[0]];
    case '2-view-horizontal':
    case '2-view-vertical':
      return props.viewportState.views.slice(0, 2);
    case '4-view':
      return props.viewportState.views.slice(0, 4);
    default:
      return [props.viewportState.views[0]];
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
  emit('update:viewportState', {
    ...props.viewportState,
    activeViewIndex: index
  });
}

function updateViewType(index: number, viewType: ViewType) {
  const newViews = [...props.viewportState.views];
  newViews[index] = viewType;
  emit('update:viewportState', {
    ...props.viewportState,
    views: newViews
  });
}

function setLayout(newLayout: ViewLayout) {
  // Ensure we have enough views
  let newViews = [...props.viewportState.views];
  while (newViews.length < 4) {
    newViews.push('front');
  }

  emit('update:viewportState', {
    ...props.viewportState,
    layout: newLayout,
    views: newViews,
    activeViewIndex: Math.min(props.viewportState.activeViewIndex, getViewCount(newLayout) - 1)
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
    orbitCenter: { x: props.compWidth / 2, y: props.compHeight / 2, z: 0 },
    orbitDistance: 2000,
    orbitPhi: 60,
    orbitTheta: 45,
    orthoZoom: 1,
    orthoOffset: { x: 0, y: 0 }
  };

  emit('update:viewportState', {
    ...props.viewportState,
    customViews: {
      ...props.viewportState.customViews,
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

      emit('update:viewportState', {
        ...props.viewportState,
        customViews: {
          ...props.viewportState.customViews,
          [viewType]: {
            ...customView,
            orbitTheta: newTheta,
            orbitPhi: newPhi
          }
        }
      });
    } else if (dragButton.value === 1 || dragButton.value === 2) {
      // Middle/right button: pan
      emit('update:viewportState', {
        ...props.viewportState,
        customViews: {
          ...props.viewportState.customViews,
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

    emit('update:viewportState', {
      ...props.viewportState,
      customViews: {
        ...props.viewportState.customViews,
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
    if (viewType === 'active-camera' && props.camera) {
      matrices = getCameraViewMatrices(props.camera, props.compWidth, props.compHeight);
    } else if (isCustomView(viewType)) {
      matrices = getOrthoViewMatrices(viewType, props.compWidth, props.compHeight, customViews.value[viewType]);
    } else {
      matrices = getOrthoViewMatrices(viewType, props.compWidth, props.compHeight);
    }

    // Collect all lines to draw
    const lines: LineSegment[] = [];

    // Grid
    if (props.viewOptions.showGrid) {
      lines.push(...generateGrid(props.compWidth, props.compHeight));
    }

    // 3D axes
    if (props.viewOptions.show3DReferenceAxes) {
      lines.push(...generate3DAxes(vec3(props.compWidth / 2, props.compHeight / 2, 0)));
    }

    // Composition bounds
    if (props.viewOptions.showCompositionBounds) {
      const viz = generateCameraVisualization(
        props.camera ?? createDummyCamera(),
        props.compWidth,
        props.compHeight,
        false,
        true,
        false
      );
      lines.push(...viz.compositionBounds);
    }

    // Camera visualization (not for active-camera view)
    if (viewType !== 'active-camera' && props.camera) {
      const showWireframe = props.viewOptions.cameraWireframes === 'always' ||
        (props.viewOptions.cameraWireframes === 'selected');

      if (showWireframe) {
        const viz = generateCameraVisualization(
          props.camera,
          props.compWidth,
          props.compHeight,
          true,
          false,
          props.viewOptions.showFocalPlane
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
    if (props.viewOptions.showLayerHandles) {
      for (const layer of props.layers) {
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
    position: { x: props.compWidth / 2, y: props.compHeight / 2, z: -1500 },
    pointOfInterest: { x: props.compWidth / 2, y: props.compHeight / 2, z: 0 },
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

onMounted(() => {
  animate();
});

onUnmounted(() => {
  cancelAnimationFrame(animationId);
});

// Re-render when props change
watch(() => [props.camera, props.viewportState, props.viewOptions, props.layers], () => {
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
  font-size: 11px;
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
  font-size: 10px;
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
