<template>
  <div class="spline-editor">
    <!-- Spline toolbar (shown when a spline layer is selected) -->
    <div v-if="layerId && hasControlPoints" class="spline-toolbar">
      <!-- Pen Tool Options -->
      <div class="toolbar-group pen-tools">
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: isPenMode }"
          @click="emit('togglePenMode')"
          title="Add Points (P)"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <path fill="currentColor" d="M20.71,7.04C21.1,6.65 21.1,6 20.71,5.63L18.37,3.29C18,2.9 17.35,2.9 16.96,3.29L15.12,5.12L18.87,8.87L20.71,7.04Z M3,17.25V21H6.75L17.81,9.93L14.06,6.18L3,17.25Z"/>
          </svg>
        </button>
        <button
          class="toolbar-btn icon-btn"
          :disabled="!selectedPointId"
          @click="deleteSelectedPoint"
          title="Delete Point (Del)"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <path fill="currentColor" d="M19,4H15.5L14.5,3H9.5L8.5,4H5V6H19M6,19A2,2 0 0,0 8,21H16A2,2 0 0,0 18,19V7H6V19Z"/>
          </svg>
        </button>
        <div class="toolbar-separator"></div>
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: selectedPointType === 'smooth' }"
          :disabled="!selectedPointId"
          @click="setPointType('smooth')"
          title="Smooth Point (bezier handles)"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <circle cx="12" cy="12" r="6" fill="none" stroke="currentColor" stroke-width="2"/>
          </svg>
        </button>
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: selectedPointType === 'corner' }"
          :disabled="!selectedPointId"
          @click="setPointType('corner')"
          title="Corner Point (linear)"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <rect x="6" y="6" width="12" height="12" fill="none" stroke="currentColor" stroke-width="2"/>
          </svg>
        </button>
      </div>
      <div class="toolbar-separator"></div>
      <!-- Path Operations -->
      <div class="toolbar-group">
        <button
          class="toolbar-btn"
          @click="smoothSpline"
          title="Smooth path handles"
        >
          Smooth
        </button>
        <button
          class="toolbar-btn"
          @click="simplifySpline"
          title="Simplify path (reduce control points)"
        >
          Simplify
        </button>
      </div>
      <div class="toolbar-group">
        <label class="tolerance-label">
          Tolerance:
          <input
            type="range"
            v-model.number="smoothTolerance"
            min="1"
            max="50"
            step="1"
            class="tolerance-slider"
          />
          <span class="tolerance-value">{{ smoothTolerance }}px</span>
        </label>
      </div>
      <div class="toolbar-info">
        {{ visibleControlPoints.length }} points
      </div>
    </div>

    <!-- Control point visuals are rendered via SVG overlay -->
    <svg
      class="control-overlay"
      :viewBox="`0 0 ${canvasWidth} ${canvasHeight}`"
      :style="overlayStyle"
      @mousedown="handleMouseDown"
      @mousemove="handleMouseMove"
      @mouseup="handleMouseUp"
      @mouseleave="handleMouseUp"
      @contextmenu="handleRightClick"
    >
      <!-- Handle lines -->
      <template v-for="point in visibleControlPoints" :key="`handles-${point.id}`">
        <line
          v-if="point.handleIn && selectedPointId === point.id"
          :x1="point.x"
          :y1="point.y"
          :x2="point.handleIn.x"
          :y2="point.handleIn.y"
          class="handle-line"
        />
        <line
          v-if="point.handleOut && selectedPointId === point.id"
          :x1="point.x"
          :y1="point.y"
          :x2="point.handleOut.x"
          :y2="point.handleOut.y"
          class="handle-line"
        />
      </template>

      <!-- Handle points -->
      <template v-for="point in visibleControlPoints" :key="`handle-points-${point.id}`">
        <circle
          v-if="point.handleIn && selectedPointId === point.id"
          :cx="point.handleIn.x"
          :cy="point.handleIn.y"
          r="4"
          class="handle-point"
          :class="{ active: dragTarget?.type === 'handleIn' && dragTarget.pointId === point.id }"
          @mousedown.stop="startDragHandle(point.id, 'in', $event)"
        />
        <circle
          v-if="point.handleOut && selectedPointId === point.id"
          :cx="point.handleOut.x"
          :cy="point.handleOut.y"
          r="4"
          class="handle-point"
          :class="{ active: dragTarget?.type === 'handleOut' && dragTarget.pointId === point.id }"
          @mousedown.stop="startDragHandle(point.id, 'out', $event)"
        />
      </template>

      <!-- Control points -->
      <g v-for="point in visibleControlPoints" :key="`point-${point.id}`">
        <!-- Keyframe indicator ring (shown when point has keyframes) -->
        <circle
          v-if="pointHasKeyframes(point.id)"
          :cx="point.x"
          :cy="point.y"
          r="9"
          class="keyframe-indicator"
        />
        <!-- Main control point -->
        <circle
          :cx="point.x"
          :cy="point.y"
          r="6"
          class="control-point"
          :class="{
            selected: selectedPointId === point.id,
            corner: point.type === 'corner',
            smooth: point.type === 'smooth',
            keyframed: pointHasKeyframes(point.id)
          }"
          @mousedown.stop="startDragPoint(point.id, $event)"
        />

        <!-- Z-depth handle (shown when point is selected and layer is 3D) -->
        <g
          v-if="selectedPointId === point.id && is3DLayer"
          class="z-handle-group"
        >
          <!-- Vertical Z-axis line -->
          <line
            :x1="point.x + 15"
            :y1="point.y - 30"
            :x2="point.x + 15"
            :y2="point.y + 30"
            class="z-axis-line"
          />
          <!-- Z-axis arrow markers -->
          <polygon
            :points="`${point.x + 15},${point.y - 35} ${point.x + 12},${point.y - 28} ${point.x + 18},${point.y - 28}`"
            class="z-arrow"
          />
          <polygon
            :points="`${point.x + 15},${point.y + 35} ${point.x + 12},${point.y + 28} ${point.x + 18},${point.y + 28}`"
            class="z-arrow"
          />
          <!-- Z-depth handle (draggable diamond) -->
          <polygon
            :points="getZHandlePoints(point)"
            class="z-handle"
            :class="{ active: dragTarget?.type === 'depth' && dragTarget.pointId === point.id }"
            @mousedown.stop="startDragDepth(point.id, $event)"
          />
          <!-- Depth value label -->
          <text
            :x="point.x + 25"
            :y="point.y + getDepthOffset(point)"
            class="z-label"
          >
            Z: {{ getPointDepth(point).toFixed(0) }}
          </text>
        </g>
      </g>

      <!-- Preview point when in pen mode -->
      <circle
        v-if="previewPoint && isPenMode"
        :cx="previewPoint.x"
        :cy="previewPoint.y"
        r="4"
        class="preview-point"
      />

      <!-- Close path indicator - shows when hovering near first point -->
      <circle
        v-if="canClosePath && closePathPreview"
        :cx="visibleControlPoints[0].x"
        :cy="visibleControlPoints[0].y"
        r="10"
        class="close-indicator"
      />
    </svg>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { ControlPoint, SplineData, EvaluatedControlPoint } from '@/types/project';

interface Props {
  layerId: string | null;
  currentFrame: number;     // Current timeline frame for animation evaluation
  canvasWidth: number;      // Composition width (e.g., 832)
  canvasHeight: number;     // Composition height (e.g., 480)
  containerWidth: number;   // DOM container width (CSS pixels)
  containerHeight: number;  // DOM container height (CSS pixels)
  zoom: number;
  viewportTransform: number[];
  isPenMode: boolean;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: 'pointAdded', point: ControlPoint): void;
  (e: 'pointMoved', pointId: string, x: number, y: number): void;
  (e: 'handleMoved', pointId: string, handleType: 'in' | 'out', x: number, y: number): void;
  (e: 'pointDeleted', pointId: string): void;
  (e: 'pathUpdated'): void;
  (e: 'pathClosed'): void;
  (e: 'togglePenMode'): void;
}>();

const store = useCompositorStore();

// State
const selectedPointId = ref<string | null>(null);
const previewPoint = ref<{ x: number; y: number } | null>(null);
const closePathPreview = ref(false);
const dragTarget = ref<{
  type: 'point' | 'handleIn' | 'handleOut' | 'depth';
  pointId: string;
  startX: number;
  startY: number;
  startDepth?: number;
} | null>(null);

// Check if the layer is in 3D mode
const is3DLayer = computed(() => {
  if (!props.layerId) return false;
  const layer = store.layers.find(l => l.id === props.layerId);
  return layer?.threeD ?? false;
});

// Toolbar state
const smoothTolerance = ref(10);

// Check if spline has control points
const hasControlPoints = computed(() => visibleControlPoints.value.length > 0);

// Get type of selected point
const selectedPointType = computed<'smooth' | 'corner' | null>(() => {
  if (!selectedPointId.value) return null;
  const point = visibleControlPoints.value.find(p => p.id === selectedPointId.value);
  return point?.type ?? null;
});

// Delete the selected point
function deleteSelectedPoint() {
  if (selectedPointId.value && props.layerId) {
    const pointId = selectedPointId.value;
    store.deleteSplineControlPoint(props.layerId, pointId);
    emit('pointDeleted', pointId);
    emit('pathUpdated');
    selectedPointId.value = null;
  }
}

// Set the point type (smooth = bezier with handles, corner = linear)
function setPointType(type: 'smooth' | 'corner') {
  if (!selectedPointId.value || !props.layerId) return;

  const point = visibleControlPoints.value.find(p => p.id === selectedPointId.value);
  if (!point) return;

  if (type === 'corner') {
    // Convert to corner: remove handles
    store.updateSplineControlPoint(props.layerId, selectedPointId.value, {
      type: 'corner',
      handleIn: null,
      handleOut: null
    });
  } else {
    // Convert to smooth: create default handles if needed
    const handleOffset = 30;
    const updates: any = { type: 'smooth' };

    if (!point.handleIn) {
      updates.handleIn = { x: point.x - handleOffset, y: point.y };
    }
    if (!point.handleOut) {
      updates.handleOut = { x: point.x + handleOffset, y: point.y };
    }

    store.updateSplineControlPoint(props.layerId, selectedPointId.value, updates);
  }

  emit('pathUpdated');
}

// Smooth spline handles
function smoothSpline() {
  if (!props.layerId) return;
  store.smoothSplineHandles(props.layerId, smoothTolerance.value * 2); // Map 1-50 to 2-100%
  emit('pathUpdated');
}

// Simplify spline (reduce control points)
function simplifySpline() {
  if (!props.layerId) return;
  store.simplifySpline(props.layerId, smoothTolerance.value);
  emit('pathUpdated');
}

// Get control points from active spline layer (evaluated at current frame if animated)
const visibleControlPoints = computed<(ControlPoint | EvaluatedControlPoint)[]>(() => {
  if (!props.layerId) return [];

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return [];

  const splineData = layer.data as SplineData;

  // If animated, get evaluated control points at current frame
  if (splineData.animated && splineData.animatedControlPoints) {
    return store.getEvaluatedSplinePoints(props.layerId, props.currentFrame);
  }

  // Otherwise return static control points
  return splineData.controlPoints || [];
});

// Check if a control point has keyframes (for visual indicator)
function pointHasKeyframes(pointId: string): boolean {
  if (!props.layerId) return false;
  return store.hasSplinePointKeyframes(props.layerId, pointId);
}

// ============================================================================
// Z-DEPTH HANDLE HELPERS
// ============================================================================

// Get depth value from a control point
function getPointDepth(point: ControlPoint | EvaluatedControlPoint): number {
  return point.depth ?? 0;
}

// Get visual Y offset for Z-handle based on depth (maps depth to -30..30 range)
function getDepthOffset(point: ControlPoint | EvaluatedControlPoint): number {
  const depth = getPointDepth(point);
  // Map depth 0-1000 to visual offset -30 to 30
  return Math.max(-30, Math.min(30, -depth / 16.67));
}

// Get SVG points for Z-handle diamond shape
function getZHandlePoints(point: ControlPoint | EvaluatedControlPoint): string {
  const x = point.x + 15;
  const y = point.y + getDepthOffset(point);
  const size = 5;
  return `${x},${y - size} ${x + size},${y} ${x},${y + size} ${x - size},${y}`;
}

// Start dragging the depth handle
function startDragDepth(pointId: string, event: MouseEvent) {
  const point = visibleControlPoints.value.find(p => p.id === pointId);
  if (!point) return;

  const pos = getMousePos(event);
  dragTarget.value = {
    type: 'depth',
    pointId,
    startX: pos.x,
    startY: pos.y,
    startDepth: getPointDepth(point)
  };

  selectedPointId.value = pointId;
}

// Check if path can be closed (at least 3 points, not already closed)
const canClosePath = computed(() => {
  if (!props.layerId || visibleControlPoints.value.length < 3) return false;

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return false;

  const splineData = layer.data as SplineData;
  return !splineData.closed;
});

// Check if we're close to the first point
const CLOSE_THRESHOLD = 15; // pixels

// Calculate overlay position and size to match Three.js render area
// Must account for zoom level - at 25% zoom, the composition is 25% the size
const overlayStyle = computed(() => {
  const containerAspect = props.containerWidth / props.containerHeight;
  const compAspect = props.canvasWidth / props.canvasHeight;

  // First, calculate the "fit" size (100% zoom would fill the available space)
  let fitWidth: number;
  let fitHeight: number;

  if (containerAspect > compAspect) {
    // Container is wider - composition fits to height at 100%
    fitHeight = props.containerHeight;
    fitWidth = props.canvasWidth * (props.containerHeight / props.canvasHeight);
  } else {
    // Container is taller - composition fits to width at 100%
    fitWidth = props.containerWidth;
    fitHeight = props.canvasHeight * (props.containerWidth / props.canvasWidth);
  }

  // Apply zoom factor - zoom of 1 = 100%, zoom of 0.25 = 25%
  const zoomFactor = props.zoom || 1;
  const width = fitWidth * zoomFactor;
  const height = fitHeight * zoomFactor;

  // Center the overlay in the container
  const left = (props.containerWidth - width) / 2;
  const top = (props.containerHeight - height) / 2;

  return {
    position: 'absolute' as const,
    left: `${left}px`,
    top: `${top}px`,
    width: `${width}px`,
    height: `${height}px`,
    pointerEvents: 'all' as const
  };
});

// Convert screen coords (relative to SVG) to composition coords
function screenToCanvas(screenX: number, screenY: number): { x: number; y: number } {
  // The SVG is now sized to match the composition area
  // Its viewBox is 0 0 canvasWidth canvasHeight
  // So we just need to scale from SVG element coords to viewBox coords
  const svgRect = overlayStyle.value;
  const svgWidth = parseFloat(svgRect.width);
  const svgHeight = parseFloat(svgRect.height);

  // Scale from SVG element size to composition (viewBox) size
  const x = (screenX / svgWidth) * props.canvasWidth;
  const y = (screenY / svgHeight) * props.canvasHeight;

  return { x, y };
}

// Get mouse position relative to SVG
function getMousePos(event: MouseEvent): { x: number; y: number } {
  const svg = event.currentTarget as SVGSVGElement;
  const rect = svg.getBoundingClientRect();
  const screenX = event.clientX - rect.left;
  const screenY = event.clientY - rect.top;
  return screenToCanvas(screenX, screenY);
}

// Handle mouse events
function handleMouseDown(event: MouseEvent) {
  if (!props.isPenMode) return;

  const pos = getMousePos(event);

  // In pen mode, add new point on click
  if (props.layerId) {
    const layer = store.layers.find(l => l.id === props.layerId);
    if (layer && layer.type === 'spline') {
      const newPoint: ControlPoint = {
        id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        x: pos.x,
        y: pos.y,
        handleIn: null,
        handleOut: null,
        type: 'corner'
      };

      // Add point via store action
      store.addSplineControlPoint(props.layerId, newPoint);

      // Select the new point
      selectedPointId.value = newPoint.id;

      // Start dragging to create handle
      dragTarget.value = {
        type: 'handleOut',
        pointId: newPoint.id,
        startX: pos.x,
        startY: pos.y
      };

      emit('pointAdded', newPoint);
      emit('pathUpdated');
    }
  }
}

function handleMouseMove(event: MouseEvent) {
  const pos = getMousePos(event);

  // Update preview point in pen mode
  if (props.isPenMode) {
    previewPoint.value = pos;
  }

  // Check proximity to first point for close path preview
  if (canClosePath.value && visibleControlPoints.value.length > 0) {
    const firstPoint = visibleControlPoints.value[0];
    const dx = pos.x - firstPoint.x;
    const dy = pos.y - firstPoint.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    closePathPreview.value = dist < CLOSE_THRESHOLD;
  } else {
    closePathPreview.value = false;
  }

  // Handle dragging
  if (dragTarget.value && props.layerId) {
    const layer = store.layers.find(l => l.id === props.layerId);
    if (!layer || layer.type !== 'spline') return;

    const splineData = layer.data as SplineData;
    const point = splineData.controlPoints?.find(p => p.id === dragTarget.value!.pointId);
    if (!point) return;

    if (dragTarget.value.type === 'point') {
      // Move the control point
      const dx = pos.x - point.x;
      const dy = pos.y - point.y;

      // Build update with moved handles
      const updates: any = { x: pos.x, y: pos.y };
      if (point.handleIn) {
        updates.handleIn = { x: point.handleIn.x + dx, y: point.handleIn.y + dy };
      }
      if (point.handleOut) {
        updates.handleOut = { x: point.handleOut.x + dx, y: point.handleOut.y + dy };
      }

      // Update via store
      store.updateSplineControlPoint(props.layerId, point.id, updates);

      emit('pointMoved', point.id, pos.x, pos.y);
    } else if (dragTarget.value.type === 'handleIn') {
      const updates: any = { handleIn: { x: pos.x, y: pos.y } };

      // Mirror to handleOut if smooth
      if (point.type === 'smooth') {
        const dx = pos.x - point.x;
        const dy = pos.y - point.y;
        updates.handleOut = { x: point.x - dx, y: point.y - dy };
      }

      store.updateSplineControlPoint(props.layerId, point.id, updates);
      emit('handleMoved', point.id, 'in', pos.x, pos.y);
    } else if (dragTarget.value.type === 'handleOut') {
      const updates: any = { handleOut: { x: pos.x, y: pos.y } };

      // Mirror to handleIn if smooth
      if (point.type === 'smooth') {
        const dx = pos.x - point.x;
        const dy = pos.y - point.y;
        updates.handleIn = { x: point.x - dx, y: point.y - dy };
      }

      store.updateSplineControlPoint(props.layerId, point.id, updates);
      emit('handleMoved', point.id, 'out', pos.x, pos.y);
    } else if (dragTarget.value.type === 'depth') {
      // Update depth based on Y-axis drag
      // Dragging up increases depth, dragging down decreases
      const dy = dragTarget.value.startY - pos.y;
      const depthScale = 10; // How much depth changes per pixel of drag
      const newDepth = Math.max(0, (dragTarget.value.startDepth ?? 0) + dy * depthScale);

      store.updateSplineControlPoint(props.layerId, point.id, { depth: newDepth });
    }

    emit('pathUpdated');
  }
}

function handleMouseUp() {
  if (dragTarget.value && props.layerId) {
    // If we were creating a new handle by dragging, convert to smooth point
    const layer = store.layers.find(l => l.id === props.layerId);
    if (layer && layer.type === 'spline') {
      const splineData = layer.data as SplineData;
      const point = splineData.controlPoints?.find(p => p.id === dragTarget.value!.pointId);
      if (point && point.handleOut) {
        // Check if handle was dragged far enough
        const dx = point.handleOut.x - point.x;
        const dy = point.handleOut.y - point.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist > 5) {
          // Convert to smooth and create mirrored handleIn via store
          store.updateSplineControlPoint(props.layerId, point.id, {
            type: 'smooth',
            handleIn: { x: point.x - dx, y: point.y - dy }
          });
        } else {
          // Too small, remove handle via store
          store.updateSplineControlPoint(props.layerId, point.id, {
            handleOut: null
          });
        }
      }
    }

    dragTarget.value = null;
    emit('pathUpdated');
  }
}

// Right-click to close path
function handleRightClick(event: MouseEvent) {
  event.preventDefault();
  event.stopPropagation();

  if (!props.layerId || !canClosePath.value) return;

  const pos = getMousePos(event);

  // Check if clicking near first point
  if (visibleControlPoints.value.length > 0) {
    const firstPoint = visibleControlPoints.value[0];
    const dx = pos.x - firstPoint.x;
    const dy = pos.y - firstPoint.y;
    const dist = Math.sqrt(dx * dx + dy * dy);

    if (dist < CLOSE_THRESHOLD) {
      closePath();
      return;
    }
  }

  // Also allow closing path from anywhere with right-click when in pen mode
  if (props.isPenMode && visibleControlPoints.value.length >= 3) {
    closePath();
  }
}

// Close the path
function closePath() {
  if (!props.layerId) return;

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return;

  // Update the spline data to closed
  store.updateLayerData(props.layerId, { closed: true });

  emit('pathClosed');
  emit('pathUpdated');
}

function startDragPoint(pointId: string, event: MouseEvent) {
  selectedPointId.value = pointId;

  if (!props.isPenMode) {
    const pos = getMousePos(event);
    dragTarget.value = {
      type: 'point',
      pointId,
      startX: pos.x,
      startY: pos.y
    };
  }
}

function startDragHandle(pointId: string, handleType: 'in' | 'out', event: MouseEvent) {
  const pos = getMousePos(event);
  dragTarget.value = {
    type: handleType === 'in' ? 'handleIn' : 'handleOut',
    pointId,
    startX: pos.x,
    startY: pos.y
  };
}

// Delete selected point on Delete key
function handleKeyDown(event: KeyboardEvent) {
  if (event.key === 'Delete' || event.key === 'Backspace') {
    if (selectedPointId.value && props.layerId) {
      const layer = store.layers.find(l => l.id === props.layerId);
      if (layer && layer.type === 'spline') {
        const pointId = selectedPointId.value;
        // Delete via store action
        store.deleteSplineControlPoint(props.layerId, pointId);
        emit('pointDeleted', pointId);
        emit('pathUpdated');
        selectedPointId.value = null;
      }
    }
  }
}

onMounted(() => {
  window.addEventListener('keydown', handleKeyDown);
});

onUnmounted(() => {
  window.removeEventListener('keydown', handleKeyDown);
});

// Expose selected point for external access
defineExpose({
  selectedPointId,
  clearSelection: () => { selectedPointId.value = null; }
});
</script>

<style scoped>
.spline-editor {
  position: absolute;
  inset: 0;
  pointer-events: none;
}

.control-overlay {
  /* Position and size set via inline styles (overlayStyle) */
  pointer-events: all;
}

.control-point {
  fill: #ffffff;
  stroke: #00ff00;
  stroke-width: 2;
  cursor: pointer;
  transition: fill 0.1s, transform 0.1s;
}

.control-point:hover {
  fill: #00ff00;
}

.control-point.selected {
  fill: #00ff00;
  stroke: #ffffff;
}

.control-point.corner {
  /* Square appearance for corner points */
}

.control-point.smooth {
  /* Circle for smooth points */
}

.control-point.keyframed {
  fill: #ffcc00;
  stroke: #ff8800;
}

.control-point.keyframed.selected {
  fill: #ff8800;
  stroke: #ffffff;
}

.keyframe-indicator {
  fill: none;
  stroke: #ff8800;
  stroke-width: 2;
  stroke-dasharray: 3 2;
  opacity: 0.8;
  pointer-events: none;
}

/* Z-Depth Handle Styles */
.z-handle-group {
  pointer-events: all;
}

.z-axis-line {
  stroke: #0088ff;
  stroke-width: 1;
  stroke-dasharray: 2 2;
  opacity: 0.6;
}

.z-arrow {
  fill: #0088ff;
  opacity: 0.6;
}

.z-handle {
  fill: #0088ff;
  stroke: #ffffff;
  stroke-width: 1;
  cursor: ns-resize;
  transition: fill 0.1s;
}

.z-handle:hover {
  fill: #00bbff;
}

.z-handle.active {
  fill: #ffffff;
  stroke: #0088ff;
}

.z-label {
  fill: #0088ff;
  font-size: 10px;
  font-family: monospace;
  pointer-events: none;
}

.handle-line {
  stroke: #00ff00;
  stroke-width: 1;
  stroke-dasharray: 4 2;
  opacity: 0.7;
}

.handle-point {
  fill: #00ff00;
  stroke: #ffffff;
  stroke-width: 1;
  cursor: pointer;
}

.handle-point:hover,
.handle-point.active {
  fill: #ffffff;
  stroke: #00ff00;
}

.preview-point {
  fill: rgba(0, 255, 0, 0.5);
  stroke: #00ff00;
  stroke-width: 1;
  pointer-events: none;
}

.close-indicator {
  fill: rgba(0, 255, 0, 0.2);
  stroke: #00ff00;
  stroke-width: 2;
  stroke-dasharray: 4 2;
  pointer-events: none;
  animation: pulse 0.5s ease-in-out infinite alternate;
}

@keyframes pulse {
  from { opacity: 0.5; }
  to { opacity: 1; }
}

/* Spline Toolbar Styles - bottom center popup for spline layers */
.spline-toolbar {
  position: absolute;
  bottom: 8px;
  left: 50%;
  transform: translateX(-50%);
  display: flex;
  align-items: center;
  gap: 12px;
  padding: 6px 10px;
  background: rgba(30, 30, 30, 0.95);
  border: 1px solid rgba(0, 255, 100, 0.3);
  border-radius: 6px;
  z-index: 100;
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.3);
  pointer-events: all;
}

.toolbar-group {
  display: flex;
  align-items: center;
  gap: 6px;
}

.toolbar-btn {
  padding: 4px 10px;
  background: rgba(0, 200, 100, 0.2);
  border: 1px solid rgba(0, 255, 100, 0.4);
  border-radius: 4px;
  color: #00ff66;
  font-size: 11px;
  font-weight: 500;
  cursor: pointer;
  transition: all 0.15s;
}

.toolbar-btn:hover {
  background: rgba(0, 255, 100, 0.3);
  border-color: #00ff66;
}

.toolbar-btn:active {
  background: #00ff66;
  color: #000;
}

.toolbar-btn.icon-btn {
  padding: 4px 6px;
  min-width: 26px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.toolbar-btn.icon-btn.active {
  background: rgba(0, 255, 100, 0.4);
  border-color: #00ff66;
}

.toolbar-btn:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.toolbar-btn:disabled:hover {
  background: rgba(0, 200, 100, 0.2);
  border-color: rgba(0, 255, 100, 0.4);
}

.toolbar-separator {
  width: 1px;
  height: 18px;
  background: rgba(255, 255, 255, 0.2);
  margin: 0 4px;
}

.pen-tools {
  gap: 4px;
}

.tolerance-label {
  display: flex;
  align-items: center;
  gap: 6px;
  font-size: 11px;
  color: rgba(255, 255, 255, 0.7);
}

.tolerance-slider {
  width: 80px;
  height: 4px;
  -webkit-appearance: none;
  appearance: none;
  background: rgba(255, 255, 255, 0.2);
  border-radius: 2px;
  cursor: pointer;
}

.tolerance-slider::-webkit-slider-thumb {
  -webkit-appearance: none;
  width: 12px;
  height: 12px;
  background: #00ff66;
  border-radius: 50%;
  cursor: pointer;
}

.tolerance-slider::-moz-range-thumb {
  width: 12px;
  height: 12px;
  background: #00ff66;
  border-radius: 50%;
  border: none;
  cursor: pointer;
}

.tolerance-value {
  min-width: 32px;
  font-family: monospace;
  color: #00ff66;
}

.toolbar-info {
  font-size: 10px;
  color: rgba(255, 255, 255, 0.5);
  padding-left: 8px;
  border-left: 1px solid rgba(255, 255, 255, 0.1);
}
</style>
