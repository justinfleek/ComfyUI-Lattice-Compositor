<template>
  <div class="spline-editor">
    <!-- Spline toolbar (shown when a spline layer is selected) -->
    <div v-if="layerId" class="spline-toolbar">
      <!-- Pen Tool Options -->
      <div class="toolbar-group pen-tools">
        <!-- Pen Tool (add points at end) -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: isPenMode && penSubMode === 'add' }"
          @click="setPenSubMode('add')"
          title="Pen Tool (P) - Add points at end of path"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <path fill="currentColor" d="M20.71,7.04C21.1,6.65 21.1,6 20.71,5.63L18.37,3.29C18,2.9 17.35,2.9 16.96,3.29L15.12,5.12L18.87,8.87L20.71,7.04Z M3,17.25V21H6.75L17.81,9.93L14.06,6.18L3,17.25Z"/>
          </svg>
          <span class="tool-label">Pen</span>
        </button>
        <!-- Add Point Tool (insert on segment) -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: isPenMode && penSubMode === 'insert' }"
          @click="setPenSubMode('insert')"
          title="Add Point (+) - Click on path to insert point"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <path fill="currentColor" d="M20.71,7.04C21.1,6.65 21.1,6 20.71,5.63L18.37,3.29C18,2.9 17.35,2.9 16.96,3.29L15.12,5.12L18.87,8.87L20.71,7.04Z M3,17.25V21H6.75L17.81,9.93L14.06,6.18L3,17.25Z"/>
            <circle cx="18" cy="18" r="5" fill="#1e1e1e"/>
            <path fill="currentColor" d="M18,15v6M15,18h6" stroke="currentColor" stroke-width="1.5"/>
          </svg>
          <span class="tool-label">Pen+</span>
        </button>
        <!-- Delete Point Tool -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: isPenMode && penSubMode === 'delete' }"
          @click="setPenSubMode('delete')"
          title="Delete Point (-) - Click point to remove"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <path fill="currentColor" d="M20.71,7.04C21.1,6.65 21.1,6 20.71,5.63L18.37,3.29C18,2.9 17.35,2.9 16.96,3.29L15.12,5.12L18.87,8.87L20.71,7.04Z M3,17.25V21H6.75L17.81,9.93L14.06,6.18L3,17.25Z"/>
            <circle cx="18" cy="18" r="5" fill="#1e1e1e"/>
            <path fill="currentColor" d="M15,18h6" stroke="currentColor" stroke-width="1.5"/>
          </svg>
          <span class="tool-label">Pen-</span>
        </button>
        <!-- Convert Point Tool -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: isPenMode && penSubMode === 'convert' }"
          @click="setPenSubMode('convert')"
          title="Convert Point (^) - Click to toggle smooth/corner"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <path fill="currentColor" d="M12,2L6,8H9V14H6L12,20L18,14H15V8H18L12,2Z" transform="rotate(180 12 11)"/>
          </svg>
          <span class="tool-label">Convert</span>
        </button>
      </div>
      <div class="toolbar-separator"></div>
      <!-- Path Operations -->
      <div class="toolbar-group" v-if="hasControlPoints">
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
        <button
          class="toolbar-btn"
          :class="{ active: isClosed }"
          @click="toggleClosePath"
          title="Toggle closed path"
        >
          {{ isClosed ? 'Open' : 'Close' }}
        </button>
      </div>
      <div class="toolbar-group" v-if="hasControlPoints">
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
      <div class="toolbar-info" v-if="hasControlPoints">
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

        <!-- Axis handles (shown when point is selected) -->
        <g v-if="selectedPointId === point.id && !props.isPenMode" class="axis-handles">
          <!-- X-axis handle (red, horizontal) -->
          <line
            :x1="point.x + 10"
            :y1="point.y"
            :x2="point.x + 40"
            :y2="point.y"
            class="axis-line axis-x"
          />
          <polygon
            :points="`${point.x + 45},${point.y} ${point.x + 38},${point.y - 4} ${point.x + 38},${point.y + 4}`"
            class="axis-arrow axis-x"
          />
          <rect
            :x="point.x + 35"
            :y="point.y - 6"
            width="16"
            height="12"
            class="axis-handle-area axis-x"
            :class="{ active: dragTarget?.type === 'axisX' && dragTarget.pointId === point.id }"
            @mousedown.stop="startDragAxis(point.id, 'X', $event)"
          />

          <!-- Y-axis handle (green, vertical) -->
          <line
            :x1="point.x"
            :y1="point.y + 10"
            :x2="point.x"
            :y2="point.y + 40"
            class="axis-line axis-y"
          />
          <polygon
            :points="`${point.x},${point.y + 45} ${point.x - 4},${point.y + 38} ${point.x + 4},${point.y + 38}`"
            class="axis-arrow axis-y"
          />
          <rect
            :x="point.x - 6"
            :y="point.y + 35"
            width="12"
            height="16"
            class="axis-handle-area axis-y"
            :class="{ active: dragTarget?.type === 'axisY' && dragTarget.pointId === point.id }"
            @mousedown.stop="startDragAxis(point.id, 'Y', $event)"
          />

          <!-- Free move indicator (center square) -->
          <rect
            :x="point.x - 4"
            :y="point.y - 4"
            width="8"
            height="8"
            class="free-move-handle"
            @mousedown.stop="startDragPoint(point.id, $event)"
          />
        </g>

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

      <!-- Preview curve when dragging to create bezier -->
      <path
        v-if="previewCurve"
        :d="previewCurve"
        class="preview-curve"
        fill="none"
      />

      <!-- Preview point when in pen mode -->
      <circle
        v-if="previewPoint && isPenMode"
        :cx="previewPoint.x"
        :cy="previewPoint.y"
        r="4"
        class="preview-point"
      />

      <!-- Insert point indicator (when hovering over path in insert mode) -->
      <circle
        v-if="insertPreviewPoint && penSubMode === 'insert'"
        :cx="insertPreviewPoint.x"
        :cy="insertPreviewPoint.y"
        r="5"
        class="insert-preview-point"
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
const previewCurve = ref<string | null>(null);
const insertPreviewPoint = ref<{ x: number; y: number; segmentIndex: number } | null>(null);
const penSubMode = ref<'add' | 'insert' | 'delete' | 'convert'>('add');
const dragTarget = ref<{
  type: 'point' | 'handleIn' | 'handleOut' | 'depth' | 'newPoint' | 'axisX' | 'axisY';
  pointId: string;
  startX: number;
  startY: number;
  startDepth?: number;
  newPointX?: number;
  newPointY?: number;
  originalX?: number;
  originalY?: number;
} | null>(null);

// Check if the layer is in 3D mode
const is3DLayer = computed(() => {
  if (!props.layerId) return false;
  const layer = store.layers.find(l => l.id === props.layerId);
  return layer?.threeD ?? false;
});

// Check if path is closed
const isClosed = computed(() => {
  if (!props.layerId) return false;
  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || layer.type !== 'spline') return false;
  return (layer.data as SplineData)?.closed ?? false;
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

// Set pen sub-mode
function setPenSubMode(mode: 'add' | 'insert' | 'delete' | 'convert') {
  penSubMode.value = mode;
  // Activate pen mode if not already active
  if (!props.isPenMode) {
    emit('togglePenMode');
  }
}

// Toggle closed path
function toggleClosePath() {
  if (!props.layerId) return;
  store.updateLayerData(props.layerId, { closed: !isClosed.value });
  emit('pathUpdated');
}

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

// Find closest point on path for insert mode
function findClosestPointOnPath(pos: { x: number; y: number }): { x: number; y: number; segmentIndex: number; t: number } | null {
  const points = visibleControlPoints.value;
  if (points.length < 2) return null;

  let closest: { x: number; y: number; segmentIndex: number; t: number; dist: number } | null = null;

  // Check each segment
  const numSegments = isClosed.value ? points.length : points.length - 1;
  for (let i = 0; i < numSegments; i++) {
    const p0 = points[i];
    const p1 = points[(i + 1) % points.length];

    // Simple line segment check (could be improved with bezier curve check)
    // For now, use linear interpolation
    for (let t = 0; t <= 1; t += 0.05) {
      const x = p0.x + t * (p1.x - p0.x);
      const y = p0.y + t * (p1.y - p0.y);
      const dist = Math.sqrt((pos.x - x) ** 2 + (pos.y - y) ** 2);

      if (!closest || dist < closest.dist) {
        closest = { x, y, segmentIndex: i, t, dist };
      }
    }
  }

  // Only return if within threshold
  if (closest && closest.dist < 20) {
    return { x: closest.x, y: closest.y, segmentIndex: closest.segmentIndex, t: closest.t };
  }
  return null;
}

// Handle mouse events
function handleMouseDown(event: MouseEvent) {
  if (!props.isPenMode) return;

  const pos = getMousePos(event);

  if (!props.layerId) return;
  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || layer.type !== 'spline') return;

  // Handle different pen sub-modes
  if (penSubMode.value === 'add') {
    // Add point at end of path
    const newPoint: ControlPoint = {
      id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      x: pos.x,
      y: pos.y,
      handleIn: null,
      handleOut: null,
      type: 'corner'
    };

    store.addSplineControlPoint(props.layerId, newPoint);
    selectedPointId.value = newPoint.id;

    // Start dragging to create handle (for curve preview)
    dragTarget.value = {
      type: 'newPoint',
      pointId: newPoint.id,
      startX: pos.x,
      startY: pos.y,
      newPointX: pos.x,
      newPointY: pos.y
    };

    emit('pointAdded', newPoint);
    emit('pathUpdated');

  } else if (penSubMode.value === 'insert') {
    // Insert point on path segment
    const closest = findClosestPointOnPath(pos);
    if (closest) {
      const newPoint: ControlPoint = {
        id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        x: closest.x,
        y: closest.y,
        handleIn: null,
        handleOut: null,
        type: 'corner'
      };

      // Insert after the segment start point
      store.insertSplineControlPoint(props.layerId, newPoint, closest.segmentIndex + 1);
      selectedPointId.value = newPoint.id;
      emit('pointAdded', newPoint);
      emit('pathUpdated');
    }

  } else if (penSubMode.value === 'delete') {
    // Delete clicked point
    const clickedPoint = findClickedPoint(pos);
    if (clickedPoint) {
      store.deleteSplineControlPoint(props.layerId, clickedPoint.id);
      emit('pointDeleted', clickedPoint.id);
      emit('pathUpdated');
      selectedPointId.value = null;
    }

  } else if (penSubMode.value === 'convert') {
    // Convert clicked point type
    const clickedPoint = findClickedPoint(pos);
    if (clickedPoint) {
      const newType = clickedPoint.type === 'smooth' ? 'corner' : 'smooth';
      if (newType === 'corner') {
        store.updateSplineControlPoint(props.layerId, clickedPoint.id, {
          type: 'corner',
          handleIn: null,
          handleOut: null
        });
      } else {
        // Create default handles for smooth point
        const handleOffset = 30;
        store.updateSplineControlPoint(props.layerId, clickedPoint.id, {
          type: 'smooth',
          handleIn: { x: clickedPoint.x - handleOffset, y: clickedPoint.y },
          handleOut: { x: clickedPoint.x + handleOffset, y: clickedPoint.y }
        });
      }
      selectedPointId.value = clickedPoint.id;
      emit('pathUpdated');
    }
  }
}

// Find point at position
function findClickedPoint(pos: { x: number; y: number }): (ControlPoint | EvaluatedControlPoint) | null {
  const threshold = 10;
  for (const point of visibleControlPoints.value) {
    const dist = Math.sqrt((pos.x - point.x) ** 2 + (pos.y - point.y) ** 2);
    if (dist < threshold) {
      return point;
    }
  }
  return null;
}

// Generate curve preview SVG path
function generateCurvePreview(lastPoint: ControlPoint | EvaluatedControlPoint, handleOut: { x: number; y: number }, newPos: { x: number; y: number }): string {
  // Create a cubic bezier from last point to new position
  const h1x = handleOut.x;
  const h1y = handleOut.y;
  // Mirror the handle for a symmetric curve
  const h2x = newPos.x - (handleOut.x - lastPoint.x);
  const h2y = newPos.y - (handleOut.y - lastPoint.y);

  return `M ${lastPoint.x},${lastPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${newPos.x},${newPos.y}`;
}

function handleMouseMove(event: MouseEvent) {
  const pos = getMousePos(event);

  // Update preview point in pen mode
  if (props.isPenMode) {
    previewPoint.value = pos;

    // Show insert preview when in insert mode
    if (penSubMode.value === 'insert') {
      const closest = findClosestPointOnPath(pos);
      insertPreviewPoint.value = closest;
    } else {
      insertPreviewPoint.value = null;
    }
  }

  // Generate curve preview when dragging new point
  if (dragTarget.value?.type === 'newPoint') {
    const points = visibleControlPoints.value;
    if (points.length >= 2) {
      const newPoint = points.find(p => p.id === dragTarget.value!.pointId);
      const prevPointIndex = points.indexOf(newPoint!) - 1;
      if (newPoint && prevPointIndex >= 0) {
        const prevPoint = points[prevPointIndex];
        // Create handle based on drag direction
        const handleOut = { x: pos.x, y: pos.y };
        previewCurve.value = generateCurvePreview(prevPoint, handleOut, newPoint);

        // Also update the handle in real-time
        if (props.layerId) {
          const dx = pos.x - newPoint.x;
          const dy = pos.y - newPoint.y;
          if (Math.sqrt(dx * dx + dy * dy) > 5) {
            store.updateSplineControlPoint(props.layerId, newPoint.id, {
              handleOut: { x: pos.x, y: pos.y },
              handleIn: { x: newPoint.x - dx, y: newPoint.y - dy },
              type: 'smooth'
            });
          }
        }
      }
    }
  } else {
    previewCurve.value = null;
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
    } else if (dragTarget.value.type === 'axisX') {
      // Move only along X-axis
      const dx = pos.x - dragTarget.value.startX;
      const newX = (dragTarget.value.originalX ?? point.x) + dx;

      // Move handles along with point
      const handleDx = newX - point.x;
      const updates: any = { x: newX };
      if (point.handleIn) {
        updates.handleIn = { x: point.handleIn.x + handleDx, y: point.handleIn.y };
      }
      if (point.handleOut) {
        updates.handleOut = { x: point.handleOut.x + handleDx, y: point.handleOut.y };
      }

      store.updateSplineControlPoint(props.layerId, point.id, updates);
      emit('pointMoved', point.id, newX, point.y);
    } else if (dragTarget.value.type === 'axisY') {
      // Move only along Y-axis
      const dy = pos.y - dragTarget.value.startY;
      const newY = (dragTarget.value.originalY ?? point.y) + dy;

      // Move handles along with point
      const handleDy = newY - point.y;
      const updates: any = { y: newY };
      if (point.handleIn) {
        updates.handleIn = { x: point.handleIn.x, y: point.handleIn.y + handleDy };
      }
      if (point.handleOut) {
        updates.handleOut = { x: point.handleOut.x, y: point.handleOut.y + handleDy };
      }

      store.updateSplineControlPoint(props.layerId, point.id, updates);
      emit('pointMoved', point.id, point.x, newY);
    }

    emit('pathUpdated');
  }
}

function handleMouseUp() {
  // Clear curve preview
  previewCurve.value = null;

  if (dragTarget.value && props.layerId) {
    // Handle newPoint type - just clear the drag target, handles already updated
    if (dragTarget.value.type === 'newPoint') {
      dragTarget.value = null;
      emit('pathUpdated');
      return;
    }

    // If we were creating a new handle by dragging, convert to smooth point
    const layer = store.layers.find(l => l.id === props.layerId);
    if (layer && layer.type === 'spline') {
      const splineData = layer.data as SplineData;
      const point = splineData.controlPoints?.find(p => p.id === dragTarget.value!.pointId);
      if (point && point.handleOut && dragTarget.value.type === 'handleOut') {
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

function startDragAxis(pointId: string, axis: 'X' | 'Y', event: MouseEvent) {
  const pos = getMousePos(event);
  const point = visibleControlPoints.value.find(p => p.id === pointId);
  if (!point) return;

  dragTarget.value = {
    type: axis === 'X' ? 'axisX' : 'axisY',
    pointId,
    startX: pos.x,
    startY: pos.y,
    originalX: point.x,
    originalY: point.y
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

.preview-curve {
  stroke: rgba(0, 255, 0, 0.6);
  stroke-width: 2;
  stroke-dasharray: 8 4;
  pointer-events: none;
}

.insert-preview-point {
  fill: rgba(0, 200, 255, 0.6);
  stroke: #00ccff;
  stroke-width: 2;
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

/* Axis Handles */
.axis-handles {
  pointer-events: none;
}

.axis-line {
  stroke-width: 2;
  pointer-events: none;
}

.axis-line.axis-x {
  stroke: #ff4444;
}

.axis-line.axis-y {
  stroke: #44ff44;
}

.axis-arrow {
  pointer-events: none;
}

.axis-arrow.axis-x {
  fill: #ff4444;
}

.axis-arrow.axis-y {
  fill: #44ff44;
}

.axis-handle-area {
  fill: transparent;
  cursor: pointer;
  pointer-events: all;
}

.axis-handle-area.axis-x {
  cursor: ew-resize;
}

.axis-handle-area.axis-x:hover,
.axis-handle-area.axis-x.active {
  fill: rgba(255, 68, 68, 0.3);
}

.axis-handle-area.axis-y {
  cursor: ns-resize;
}

.axis-handle-area.axis-y:hover,
.axis-handle-area.axis-y.active {
  fill: rgba(68, 255, 68, 0.3);
}

.free-move-handle {
  fill: rgba(255, 255, 255, 0.3);
  stroke: #ffffff;
  stroke-width: 1;
  cursor: move;
  pointer-events: all;
}

.free-move-handle:hover {
  fill: rgba(255, 255, 255, 0.6);
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
