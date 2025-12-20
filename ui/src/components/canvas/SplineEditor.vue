<template>
  <div class="spline-editor">
    <!-- Tool tip popup (shows guidance for active tool) -->
    <div v-if="layerId && isPenMode" class="tool-tip-popup">
      {{ activeToolTip }}
    </div>

    <!-- Hover feedback (shown when hovering over points with delete/insert tools) -->
    <div v-if="hoverFeedback" class="hover-feedback" :style="hoverFeedbackStyle">
      {{ hoverFeedback }}
    </div>

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
          @click="smoothSelectedPoints"
          :title="selectedPointIds.length > 0 ? 'Smooth selected points' : 'Smooth all path handles'"
        >
          Smooth{{ selectedPointIds.length > 0 ? ` (${selectedPointIds.length})` : '' }}
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
        {{ visibleControlPoints.length }} points{{ selectedPointIds.length > 0 ? ` (${selectedPointIds.length} selected)` : '' }}
      </div>
      <!-- Z-Depth controls (shown when 3D layer or when point is selected) -->
      <div class="toolbar-group z-depth-controls" v-if="selectedPointId">
        <label class="z-depth-label">
          Z:
          <input
            type="number"
            :value="selectedPointDepth"
            @input="updateSelectedPointDepth"
            class="z-depth-input"
            step="10"
          />
        </label>
        <span class="z-depth-hint">(↑/↓ keys)</span>
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
          :style="{ stroke: strokeColor }"
        />
        <line
          v-if="point.handleOut && selectedPointId === point.id"
          :x1="point.x"
          :y1="point.y"
          :x2="point.handleOut.x"
          :y2="point.handleOut.y"
          class="handle-line"
          :style="{ stroke: strokeColor }"
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
          :style="{ fill: strokeColor }"
          @mousedown.stop="startDragHandle(point.id, 'in', $event)"
        />
        <circle
          v-if="point.handleOut && selectedPointId === point.id"
          :cx="point.handleOut.x"
          :cy="point.handleOut.y"
          r="4"
          class="handle-point"
          :class="{ active: dragTarget?.type === 'handleOut' && dragTarget.pointId === point.id }"
          :style="{ fill: strokeColor }"
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
          r="8"
          class="keyframe-indicator"
          :style="{ stroke: strokeColor }"
        />
        <!-- Main control point (r=5, 15% smaller than 6) -->
        <circle
          :cx="point.x"
          :cy="point.y"
          r="5"
          class="control-point"
          :class="{
            selected: selectedPointId === point.id || selectedPointIds.includes(point.id),
            corner: point.type === 'corner',
            smooth: point.type === 'smooth',
            keyframed: pointHasKeyframes(point.id),
            'will-delete': isPenMode && penSubMode === 'delete' && hoveredPointId === point.id,
            'will-convert': isPenMode && penSubMode === 'convert' && hoveredPointId === point.id
          }"
          :style="{ fill: strokeColor, stroke: '#ffffff' }"
          @mousedown.stop="handlePointClick(point.id, $event)"
          @mouseenter="handlePointHover(point.id)"
          @mouseleave="handlePointLeave"
        />

        <!-- Axis handles (shown when point is selected, not in pen mode) -->
        <g v-if="selectedPointId === point.id && !props.isPenMode" class="axis-handles">
          <!-- Selection ring -->
          <circle
            :cx="point.x"
            :cy="point.y"
            r="10"
            class="selection-ring"
            :style="{ stroke: strokeColor }"
          />

          <!-- X-axis handle (red, horizontal arrow) -->
          <g class="axis-x-group">
            <line
              :x1="point.x + 12"
              :y1="point.y"
              :x2="point.x + 35"
              :y2="point.y"
              class="axis-line axis-x"
            />
            <polygon
              :points="`${point.x + 40},${point.y} ${point.x + 33},${point.y - 4} ${point.x + 33},${point.y + 4}`"
              class="axis-arrow axis-x"
            />
            <rect
              :x="point.x + 12"
              :y="point.y - 8"
              width="30"
              height="16"
              class="axis-hit-area"
              @mousedown.stop="startDragAxis(point.id, 'X', $event)"
            />
          </g>

          <!-- Y-axis handle (green, vertical arrow) -->
          <g class="axis-y-group">
            <line
              :x1="point.x"
              :y1="point.y + 12"
              :x2="point.x"
              :y2="point.y + 35"
              class="axis-line axis-y"
            />
            <polygon
              :points="`${point.x},${point.y + 40} ${point.x - 4},${point.y + 33} ${point.x + 4},${point.y + 33}`"
              class="axis-arrow axis-y"
            />
            <rect
              :x="point.x - 8"
              :y="point.y + 12"
              width="16"
              height="30"
              class="axis-hit-area"
              @mousedown.stop="startDragAxis(point.id, 'Y', $event)"
            />
          </g>
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
import { interpolateProperty } from '@/services/interpolation';
import type { ControlPoint, SplineData, PathLayerData, EvaluatedControlPoint } from '@/types/project';

// Helper: Check if layer is a spline or path type (both use control points)
function isSplineOrPathType(layerType: string | undefined): layerType is 'spline' | 'path' {
  return layerType === 'spline' || layerType === 'path';
}

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
const selectedPointIds = ref<string[]>([]); // Multi-select support
const hoveredPointId = ref<string | null>(null);
const hoverFeedback = ref<string | null>(null);
const hoverFeedbackPos = ref<{ x: number; y: number } | null>(null);
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
  // Screen coordinates for axis dragging (zoom-independent)
  screenStartX?: number;
  screenStartY?: number;
} | null>(null);

// Computed: active tool tip text
const activeToolTip = computed(() => {
  switch (penSubMode.value) {
    case 'add':
      return 'Click to add points. Drag after clicking to create curved handles. Right-click to finish drawing.';
    case 'insert':
      return 'Click on the path to insert a new point on that segment.';
    case 'delete':
      return 'Click on any point to delete it from the path.';
    case 'convert':
      return 'Click on a point to toggle between smooth (curved) and corner (sharp) type.';
    default:
      return '';
  }
});

// Computed: hover feedback style (positioned near mouse)
const hoverFeedbackStyle = computed(() => {
  if (!hoverFeedbackPos.value) return { display: 'none' };
  // Convert composition coords to screen coords
  const svgStyle = overlayStyle.value;
  const svgWidth = parseFloat(svgStyle.width);
  const svgHeight = parseFloat(svgStyle.height);
  const left = parseFloat(svgStyle.left) + (hoverFeedbackPos.value.x / props.canvasWidth) * svgWidth;
  const top = parseFloat(svgStyle.top) + (hoverFeedbackPos.value.y / props.canvasHeight) * svgHeight - 25;
  return {
    position: 'absolute' as const,
    left: `${left}px`,
    top: `${top}px`,
    transform: 'translateX(-50%)'
  };
});

// Computed: selected point's depth value
const selectedPointDepth = computed(() => {
  if (!selectedPointId.value) return 0;
  const point = visibleControlPoints.value.find(p => p.id === selectedPointId.value);
  return point?.depth ?? 0;
});

// Update selected point's depth from input
function updateSelectedPointDepth(event: Event) {
  if (!selectedPointId.value || !props.layerId) return;
  const input = event.target as HTMLInputElement;
  const newDepth = Math.max(0, parseFloat(input.value) || 0);
  store.updateSplineControlPoint(props.layerId, selectedPointId.value, { depth: newDepth });
  emit('pathUpdated');
}

// Adjust depth by delta (used by keyboard shortcuts)
function adjustSelectedPointDepth(delta: number) {
  if (!selectedPointId.value || !props.layerId) return;
  const point = visibleControlPoints.value.find(p => p.id === selectedPointId.value);
  const currentDepth = point?.depth ?? 0;
  const newDepth = Math.max(0, currentDepth + delta);
  store.updateSplineControlPoint(props.layerId, selectedPointId.value, { depth: newDepth });
  emit('pathUpdated');
}

// Check if the layer is in 3D mode
const is3DLayer = computed(() => {
  if (!props.layerId) return false;
  const layer = store.layers.find(l => l.id === props.layerId);
  return layer?.threeD ?? false;
});

// ============================================================================
// LAYER TRANSFORM - Apply layer's position/rotation/scale to control points
// ============================================================================

// Get layer's transform properties (evaluated at current frame)
const layerTransform = computed(() => {
  if (!props.layerId) {
    return { position: { x: 0, y: 0 }, rotation: 0, scale: { x: 100, y: 100 }, anchorPoint: { x: 0, y: 0 } };
  }

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer) {
    return { position: { x: 0, y: 0 }, rotation: 0, scale: { x: 100, y: 100 }, anchorPoint: { x: 0, y: 0 } };
  }

  const t = layer.transform;

  // Get values, checking for animation - use interpolateProperty for animated values
  const getVal = (prop: any, defaultVal: any) => {
    if (!prop) return defaultVal;
    if (prop.animated && prop.keyframes?.length > 0) {
      return interpolateProperty(prop, props.currentFrame) ?? defaultVal;
    }
    return prop.value ?? defaultVal;
  };

  const position = getVal(t.position, { x: props.canvasWidth / 2, y: props.canvasHeight / 2 });
  const anchorPoint = getVal(t.anchorPoint, { x: 0, y: 0 });
  const scale = getVal(t.scale, { x: 100, y: 100 });

  // For 2D layers use rotation, for 3D use rotationZ
  let rotation = 0;
  if (layer.threeD && t.rotationZ) {
    rotation = getVal(t.rotationZ, 0);
  } else if (t.rotation) {
    rotation = getVal(t.rotation, 0);
  }

  return { position, rotation, scale, anchorPoint };
});

// Transform a point from layer space to composition space
function transformPoint(p: { x: number; y: number }): { x: number; y: number } {
  const { position, rotation, scale, anchorPoint } = layerTransform.value;

  // Step 1: Subtract anchor point (move anchor to origin)
  let x = p.x - anchorPoint.x;
  let y = p.y - anchorPoint.y;

  // Step 2: Apply scale (convert from percentage)
  x *= scale.x / 100;
  y *= scale.y / 100;

  // Step 3: Apply rotation (convert degrees to radians)
  const rad = (rotation * Math.PI) / 180;
  const cos = Math.cos(rad);
  const sin = Math.sin(rad);
  const rx = x * cos - y * sin;
  const ry = x * sin + y * cos;

  // Step 4: Add position (move to composition location)
  return {
    x: rx + position.x,
    y: ry + position.y
  };
}

// Inverse transform: from composition space to layer space
function inverseTransformPoint(p: { x: number; y: number }): { x: number; y: number } {
  const { position, rotation, scale, anchorPoint } = layerTransform.value;

  // Step 1: Subtract position
  let x = p.x - position.x;
  let y = p.y - position.y;

  // Step 2: Inverse rotation (negative angle)
  const rad = (-rotation * Math.PI) / 180;
  const cos = Math.cos(rad);
  const sin = Math.sin(rad);
  const rx = x * cos - y * sin;
  const ry = x * sin + y * cos;

  // Step 3: Inverse scale
  x = rx / (scale.x / 100);
  y = ry / (scale.y / 100);

  // Step 4: Add anchor point back
  return {
    x: x + anchorPoint.x,
    y: y + anchorPoint.y
  };
}

// Check if path is closed
const isClosed = computed(() => {
  if (!props.layerId) return false;
  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type)) return false;
  return (layer.data as SplineData | PathLayerData)?.closed ?? false;
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

// Set pen sub-mode - clicking active tool deselects it
function setPenSubMode(mode: 'add' | 'insert' | 'delete' | 'convert') {
  // If clicking the same mode that's already active, turn off pen mode
  if (props.isPenMode && penSubMode.value === mode) {
    emit('togglePenMode');
    return;
  }

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

// Smooth spline handles - either selected points or all
function smoothSelectedPoints() {
  if (!props.layerId) return;

  if (selectedPointIds.value.length > 0) {
    // Smooth only selected points
    smoothSpecificPoints(selectedPointIds.value);
  } else if (selectedPointId.value) {
    // Smooth only the single selected point
    smoothSpecificPoints([selectedPointId.value]);
  } else {
    // Smooth all points
    store.smoothSplineHandles(props.layerId, smoothTolerance.value * 2);
  }
  emit('pathUpdated');
}

// Smooth specific points by ID
function smoothSpecificPoints(pointIds: string[]) {
  if (!props.layerId) return;

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type) || !layer.data) return;

  const splineData = layer.data as SplineData | PathLayerData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length < 2) return;

  const factor = Math.max(0, Math.min(100, smoothTolerance.value * 2)) / 100;

  for (const pointId of pointIds) {
    const i = controlPoints.findIndex(cp => cp.id === pointId);
    if (i < 0) continue;

    const cp = controlPoints[i];
    const prev = controlPoints[(i - 1 + controlPoints.length) % controlPoints.length];
    const next = controlPoints[(i + 1) % controlPoints.length];

    // Skip first/last point if path is not closed
    if (!splineData.closed && (i === 0 || i === controlPoints.length - 1)) continue;

    // Calculate direction vectors
    const toPrev = { x: prev.x - cp.x, y: prev.y - cp.y };
    const toNext = { x: next.x - cp.x, y: next.y - cp.y };

    // Average direction (tangent)
    const avgDir = { x: toNext.x - toPrev.x, y: toNext.y - toPrev.y };
    const avgLength = Math.sqrt(avgDir.x * avgDir.x + avgDir.y * avgDir.y);

    if (avgLength < 0.01) continue;

    const normalized = { x: avgDir.x / avgLength, y: avgDir.y / avgLength };

    // Calculate ideal handle length
    const distPrev = Math.sqrt(toPrev.x * toPrev.x + toPrev.y * toPrev.y);
    const distNext = Math.sqrt(toNext.x * toNext.x + toNext.y * toNext.y);
    const handleLength = (distPrev + distNext) / 6;

    // Calculate ideal smooth handles
    const idealIn = { x: cp.x - normalized.x * handleLength, y: cp.y - normalized.y * handleLength };
    const idealOut = { x: cp.x + normalized.x * handleLength, y: cp.y + normalized.y * handleLength };

    // Update handles
    store.updateSplineControlPoint(props.layerId!, pointId, {
      type: 'smooth',
      handleIn: {
        x: cp.handleIn ? cp.handleIn.x + (idealIn.x - cp.handleIn.x) * factor : idealIn.x * factor + cp.x * (1 - factor),
        y: cp.handleIn ? cp.handleIn.y + (idealIn.y - cp.handleIn.y) * factor : idealIn.y * factor + cp.y * (1 - factor)
      },
      handleOut: {
        x: cp.handleOut ? cp.handleOut.x + (idealOut.x - cp.handleOut.x) * factor : idealOut.x * factor + cp.x * (1 - factor),
        y: cp.handleOut ? cp.handleOut.y + (idealOut.y - cp.handleOut.y) * factor : idealOut.y * factor + cp.y * (1 - factor)
      }
    });
  }
}

// Simplify spline (reduce control points)
function simplifySpline() {
  if (!props.layerId) return;
  store.simplifySpline(props.layerId, smoothTolerance.value);
  emit('pathUpdated');
}

// Get control points from active spline layer (evaluated at current frame if animated)
// These are in LAYER SPACE (raw coordinates)
const rawControlPoints = computed<(ControlPoint | EvaluatedControlPoint)[]>(() => {
  if (!props.layerId) return [];

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type) || !layer.data) return [];

  const layerData = layer.data as SplineData | PathLayerData;

  // If animated, get evaluated control points at current frame
  if (layerData.animated && layerData.animatedControlPoints) {
    return store.getEvaluatedSplinePoints(props.layerId, props.currentFrame);
  }

  // Otherwise return static control points
  return layerData.controlPoints || [];
});

// Interface for transformed control point (includes both raw and transformed coords)
interface TransformedControlPoint {
  id: string;
  // Raw layer-space coordinates (for editing)
  rawX: number;
  rawY: number;
  // Transformed composition-space coordinates (for display)
  x: number;
  y: number;
  depth?: number;
  handleIn: { x: number; y: number } | null;
  handleOut: { x: number; y: number } | null;
  // Raw handles for editing
  rawHandleIn: { x: number; y: number } | null;
  rawHandleOut: { x: number; y: number } | null;
  type: 'corner' | 'smooth' | 'symmetric';
}

// Transform control points from layer space to composition space for display
const visibleControlPoints = computed<TransformedControlPoint[]>(() => {
  return rawControlPoints.value.map(cp => {
    const transformed = transformPoint({ x: cp.x, y: cp.y });
    const transformedHandleIn = cp.handleIn ? transformPoint(cp.handleIn) : null;
    const transformedHandleOut = cp.handleOut ? transformPoint(cp.handleOut) : null;

    return {
      id: cp.id,
      rawX: cp.x,
      rawY: cp.y,
      x: transformed.x,
      y: transformed.y,
      depth: cp.depth,
      handleIn: transformedHandleIn,
      handleOut: transformedHandleOut,
      rawHandleIn: cp.handleIn ? { ...cp.handleIn } : null,
      rawHandleOut: cp.handleOut ? { ...cp.handleOut } : null,
      type: cp.type
    };
  });
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
    startDepth: getPointDepth(point),
    // Store screen coordinates for zoom-independent movement
    screenStartX: event.clientX,
    screenStartY: event.clientY
  };

  selectedPointId.value = pointId;
}

// Check if path can be closed (at least 3 points, not already closed)
const canClosePath = computed(() => {
  if (!props.layerId || visibleControlPoints.value.length < 3) return false;

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type) || !layer.data) return false;

  const layerData = layer.data as SplineData | PathLayerData;
  return !layerData.closed;
});

// Get the stroke color from the layer data (for point colors)
const strokeColor = computed(() => {
  if (!props.layerId) return '#00ff66'; // default green

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type) || !layer.data) return '#00ff66';

  // Path layers use guideColor (cyan), spline layers use stroke
  if (layer.type === 'path') {
    const pathData = layer.data as PathLayerData;
    return pathData.guideColor || '#00FFFF'; // cyan for paths
  }

  const splineData = layer.data as SplineData;
  // Use 'stroke' (the actual property name) or 'strokeColor' for compatibility
  return (splineData as any).stroke || (splineData as any).strokeColor || '#00ff66';
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

// Evaluate cubic bezier curve at parameter t
function evaluateBezier(p0: { x: number; y: number }, h0: { x: number; y: number } | null, h1: { x: number; y: number } | null, p1: { x: number; y: number }, t: number): { x: number; y: number } {
  // Use handles if they exist, otherwise use control points (linear)
  const cp0 = p0;
  const cp1 = h0 || p0; // handleOut of p0
  const cp2 = h1 || p1; // handleIn of p1
  const cp3 = p1;

  // Cubic bezier formula: B(t) = (1-t)³P0 + 3(1-t)²tP1 + 3(1-t)t²P2 + t³P3
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  const t2 = t * t;
  const t3 = t2 * t;

  return {
    x: mt3 * cp0.x + 3 * mt2 * t * cp1.x + 3 * mt * t2 * cp2.x + t3 * cp3.x,
    y: mt3 * cp0.y + 3 * mt2 * t * cp1.y + 3 * mt * t2 * cp2.y + t3 * cp3.y
  };
}

// Find closest point on path for insert mode (uses proper bezier interpolation)
function findClosestPointOnPath(pos: { x: number; y: number }): { x: number; y: number; segmentIndex: number; t: number } | null {
  const points = visibleControlPoints.value;
  if (points.length < 2) return null;

  let closest: { x: number; y: number; segmentIndex: number; t: number; dist: number } | null = null;

  // Check each segment
  const numSegments = isClosed.value ? points.length : points.length - 1;
  for (let i = 0; i < numSegments; i++) {
    const p0 = points[i];
    const p1 = points[(i + 1) % points.length];

    // Get handles for bezier curve
    const h0 = p0.handleOut; // handleOut of p0
    const h1 = p1.handleIn;  // handleIn of p1

    // Sample the bezier curve at multiple points
    for (let t = 0; t <= 1; t += 0.02) { // More samples for accuracy
      const pt = evaluateBezier(p0, h0, h1, p1, t);
      const dist = Math.sqrt((pos.x - pt.x) ** 2 + (pos.y - pt.y) ** 2);

      if (!closest || dist < closest.dist) {
        closest = { x: pt.x, y: pt.y, segmentIndex: i, t, dist };
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
  // Convert composition-space position to layer-space for storing
  const layerPos = inverseTransformPoint(pos);

  if (!props.layerId) return;
  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type)) return;

  // Handle different pen sub-modes
  if (penSubMode.value === 'add') {
    // Add point at end of path (in layer space)
    const newPoint: ControlPoint = {
      id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      x: layerPos.x,
      y: layerPos.y,
      handleIn: null,
      handleOut: null,
      type: 'corner'
    };

    store.addSplineControlPoint(props.layerId, newPoint);
    selectedPointId.value = newPoint.id;

    // Start dragging to create handle (for curve preview)
    // Store both composition-space (for preview) and layer-space coords
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
    // findClosestPointOnPath works in composition space, so convert result to layer space
    const closest = findClosestPointOnPath(pos);
    if (closest) {
      const closestLayerPos = inverseTransformPoint({ x: closest.x, y: closest.y });
      const newPoint: ControlPoint = {
        id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        x: closestLayerPos.x,
        y: closestLayerPos.y,
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

// Generate curve preview SVG path from previous point to new point
// prevPoint: the previous control point
// newPoint: the new point being created
// dragPos: where the user is dragging (sets the handles)
function generateCurvePreview(
  prevPoint: ControlPoint | EvaluatedControlPoint,
  newPoint: { x: number; y: number },
  dragPos: { x: number; y: number }
): string {
  // Calculate the handle offset from the drag
  // The drag position defines where handleOut of newPoint will be
  const dx = dragPos.x - newPoint.x;
  const dy = dragPos.y - newPoint.y;
  const dragDist = Math.sqrt(dx * dx + dy * dy);

  // h1 = handleOut of prevPoint (how curve LEAVES prevPoint)
  // If prevPoint has handleOut, use it. Otherwise use a default based on direction to newPoint.
  let h1x: number, h1y: number;
  if (prevPoint.handleOut) {
    h1x = prevPoint.handleOut.x;
    h1y = prevPoint.handleOut.y;
  } else {
    // Default: 1/3 of the way toward newPoint
    const dirX = newPoint.x - prevPoint.x;
    const dirY = newPoint.y - prevPoint.y;
    h1x = prevPoint.x + dirX * 0.33;
    h1y = prevPoint.y + dirY * 0.33;
  }

  // h2 = handleIn of newPoint (how curve ARRIVES at newPoint)
  // This is the MIRROR of the drag direction (opposite of handleOut)
  const h2x = newPoint.x - dx;
  const h2y = newPoint.y - dy;

  return `M ${prevPoint.x},${prevPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${newPoint.x},${newPoint.y}`;
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

      // Show hover feedback for insert mode
      if (closest) {
        hoverFeedbackPos.value = { x: closest.x, y: closest.y };
        hoverFeedback.value = 'Click to add point to spline';
      } else if (!hoveredPointId.value) {
        hoverFeedback.value = null;
      }
    } else {
      insertPreviewPoint.value = null;
      // Only clear hover feedback if not hovering over a point
      if (!hoveredPointId.value) {
        hoverFeedback.value = null;
      }
    }

    // Show preview curve from last point to mouse in 'add' mode (before clicking)
    if (penSubMode.value === 'add' && !dragTarget.value) {
      const points = visibleControlPoints.value;
      if (points.length > 0) {
        const lastPoint = points[points.length - 1];
        // Use bezier curve preview that follows the last point's handleOut
        if (lastPoint.handleOut) {
          // Create a smooth curve using the existing handleOut
          // Mirror the handleOut direction for the incoming handle of the preview point
          const h1x = lastPoint.handleOut.x;
          const h1y = lastPoint.handleOut.y;
          // Calculate mirrored handle for the target point
          const dx = pos.x - lastPoint.x;
          const dy = pos.y - lastPoint.y;
          const h2x = pos.x - dx * 0.3;
          const h2y = pos.y - dy * 0.3;
          previewCurve.value = `M ${lastPoint.x},${lastPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${pos.x},${pos.y}`;
        } else {
          // No handleOut, show a gentle curve based on direction
          const dx = pos.x - lastPoint.x;
          const dy = pos.y - lastPoint.y;
          const h1x = lastPoint.x + dx * 0.3;
          const h1y = lastPoint.y + dy * 0.3;
          const h2x = pos.x - dx * 0.3;
          const h2y = pos.y - dy * 0.3;
          previewCurve.value = `M ${lastPoint.x},${lastPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${pos.x},${pos.y}`;
        }
      }
    }
  }

  // Generate curve preview when dragging new point
  if (dragTarget.value?.type === 'newPoint') {
    const points = visibleControlPoints.value;
    if (points.length >= 1) {
      const newPoint = points.find(p => p.id === dragTarget.value!.pointId);
      const newPointIndex = points.indexOf(newPoint!);
      const prevPointIndex = newPointIndex - 1;

      // Convert to layer-space for handle updates
      const layerPos = inverseTransformPoint(pos);
      // Get raw (layer-space) coordinates of the new point
      const rawNewPointX = newPoint?.rawX ?? newPoint?.x ?? 0;
      const rawNewPointY = newPoint?.rawY ?? newPoint?.y ?? 0;

      if (newPoint && prevPointIndex >= 0) {
        const prevPoint = points[prevPointIndex];
        // Generate preview showing curve from prev point to new point based on drag
        // Preview uses composition-space coordinates
        previewCurve.value = generateCurvePreview(prevPoint, newPoint, pos);

        // Update the handle in layer-space
        if (props.layerId) {
          const dx = layerPos.x - rawNewPointX;
          const dy = layerPos.y - rawNewPointY;
          if (Math.sqrt(dx * dx + dy * dy) > 5) {
            store.updateSplineControlPoint(props.layerId, newPoint.id, {
              handleOut: { x: layerPos.x, y: layerPos.y },
              handleIn: { x: rawNewPointX - dx, y: rawNewPointY - dy },
              type: 'smooth'
            });
          }
        }
      } else if (newPoint && prevPointIndex < 0) {
        // First point - no preview curve needed, but show handles being created
        if (props.layerId) {
          const dx = layerPos.x - rawNewPointX;
          const dy = layerPos.y - rawNewPointY;
          if (Math.sqrt(dx * dx + dy * dy) > 5) {
            store.updateSplineControlPoint(props.layerId, newPoint.id, {
              handleOut: { x: layerPos.x, y: layerPos.y },
              handleIn: { x: rawNewPointX - dx, y: rawNewPointY - dy },
              type: 'smooth'
            });
          }
        }
      }
    }
  } else if (!props.isPenMode || penSubMode.value !== 'add') {
    // Only clear preview if not in add mode (add mode sets its own preview above)
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
    if (!layer || !isSplineOrPathType(layer.type)) return;

    const layerData = layer.data as SplineData | PathLayerData;
    const point = layerData.controlPoints?.find(p => p.id === dragTarget.value!.pointId);
    if (!point) return;

    // Convert composition-space position to layer-space for storing
    const layerPos = inverseTransformPoint(pos);

    if (dragTarget.value.type === 'point') {
      // Move the control point (in layer space)
      const dx = layerPos.x - point.x;
      const dy = layerPos.y - point.y;

      // Build update with moved handles (also in layer space)
      const updates: any = { x: layerPos.x, y: layerPos.y };
      if (point.handleIn) {
        updates.handleIn = { x: point.handleIn.x + dx, y: point.handleIn.y + dy };
      }
      if (point.handleOut) {
        updates.handleOut = { x: point.handleOut.x + dx, y: point.handleOut.y + dy };
      }

      // Update via store
      store.updateSplineControlPoint(props.layerId, point.id, updates);

      emit('pointMoved', point.id, layerPos.x, layerPos.y);
    } else if (dragTarget.value.type === 'handleIn') {
      // Use layer-space coordinates for handle positions
      const updates: any = { handleIn: { x: layerPos.x, y: layerPos.y } };

      // Mirror to handleOut if smooth
      if (point.type === 'smooth') {
        const dx = layerPos.x - point.x;
        const dy = layerPos.y - point.y;
        updates.handleOut = { x: point.x - dx, y: point.y - dy };
      }

      store.updateSplineControlPoint(props.layerId, point.id, updates);
      emit('handleMoved', point.id, 'in', layerPos.x, layerPos.y);
    } else if (dragTarget.value.type === 'handleOut') {
      // Use layer-space coordinates for handle positions
      const updates: any = { handleOut: { x: layerPos.x, y: layerPos.y } };

      // Mirror to handleIn if smooth
      if (point.type === 'smooth') {
        const dx = layerPos.x - point.x;
        const dy = layerPos.y - point.y;
        updates.handleIn = { x: point.x - dx, y: point.y - dy };
      }

      store.updateSplineControlPoint(props.layerId, point.id, updates);
      emit('handleMoved', point.id, 'out', layerPos.x, layerPos.y);
    } else if (dragTarget.value.type === 'depth') {
      // Update depth based on Y-axis drag (using screen coordinates for zoom independence)
      // Dragging up (negative screenDy) increases depth
      const screenDy = event.clientY - (dragTarget.value.screenStartY ?? event.clientY);
      const depthScale = 2; // How much depth changes per screen pixel of drag
      const newDepth = Math.max(0, (dragTarget.value.startDepth ?? 0) - screenDy * depthScale);

      store.updateSplineControlPoint(props.layerId, point.id, { depth: newDepth });
    } else if (dragTarget.value.type === 'axisX') {
      // Move only along X-axis using SCREEN pixel deltas for consistent feel
      // This ensures 1 screen pixel = 1 canvas unit regardless of zoom
      const screenDx = event.clientX - (dragTarget.value.screenStartX ?? event.clientX);
      const dx = screenDx; // 1:1 screen-to-canvas movement
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
      // Move only along Y-axis using SCREEN pixel deltas
      const screenDy = event.clientY - (dragTarget.value.screenStartY ?? event.clientY);
      const dy = screenDy; // 1:1 screen-to-canvas movement
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
    if (layer && isSplineOrPathType(layer.type)) {
      const layerData = layer.data as SplineData | PathLayerData;
      const point = layerData.controlPoints?.find(p => p.id === dragTarget.value!.pointId);
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

// Right-click to END spline drawing (exit pen mode, NOT close the path)
function handleRightClick(event: MouseEvent) {
  event.preventDefault();
  event.stopPropagation();

  if (!props.layerId) return;

  // Right-click finishes the current spline drawing (exits pen mode)
  // It does NOT close the path - use the Close button for that
  if (props.isPenMode) {
    // Exit pen mode
    emit('togglePenMode');

    // Clear any preview state
    previewCurve.value = null;
    previewPoint.value = null;
    insertPreviewPoint.value = null;
    closePathPreview.value = false;
    hoverFeedback.value = null;
    hoveredPointId.value = null;
  }
}

// Close the path
function closePath() {
  if (!props.layerId) return;

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type) || !layer.data) return;

  // Update the spline data to closed
  store.updateLayerData(props.layerId, { closed: true });

  emit('pathClosed');
  emit('pathUpdated');
}

// Handle click on control point - determines action based on pen sub-mode
function handlePointClick(pointId: string, event: MouseEvent) {
  const point = visibleControlPoints.value.find(p => p.id === pointId);
  if (!point) return;

  if (props.isPenMode) {
    // Handle pen sub-modes
    if (penSubMode.value === 'delete') {
      // Delete this point
      if (props.layerId) {
        store.deleteSplineControlPoint(props.layerId, pointId);
        emit('pointDeleted', pointId);
        emit('pathUpdated');
        selectedPointId.value = null;
        hoveredPointId.value = null;
        hoverFeedback.value = null;
      }
      return;
    } else if (penSubMode.value === 'convert') {
      // Toggle point type
      if (props.layerId) {
        const newType = point.type === 'smooth' ? 'corner' : 'smooth';
        if (newType === 'corner') {
          store.updateSplineControlPoint(props.layerId, pointId, {
            type: 'corner',
            handleIn: null,
            handleOut: null
          });
        } else {
          // Create default handles for smooth point
          const handleOffset = 30;
          store.updateSplineControlPoint(props.layerId, pointId, {
            type: 'smooth',
            handleIn: { x: point.x - handleOffset, y: point.y },
            handleOut: { x: point.x + handleOffset, y: point.y }
          });
        }
        selectedPointId.value = pointId;
        emit('pathUpdated');
      }
      return;
    }
  }

  // Default: select point and start dragging (for move operations)
  // Handle multi-select with Shift key
  if (event.shiftKey) {
    if (selectedPointIds.value.includes(pointId)) {
      // Remove from selection
      selectedPointIds.value = selectedPointIds.value.filter(id => id !== pointId);
    } else {
      // Add to selection
      selectedPointIds.value = [...selectedPointIds.value, pointId];
    }
    selectedPointId.value = pointId;
  } else {
    selectedPointId.value = pointId;
    selectedPointIds.value = [pointId]; // Reset multi-select to single
  }

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

// Handle hover over control point - show feedback for delete/convert modes
function handlePointHover(pointId: string) {
  hoveredPointId.value = pointId;
  const point = visibleControlPoints.value.find(p => p.id === pointId);

  if (props.isPenMode && point) {
    hoverFeedbackPos.value = { x: point.x, y: point.y };

    if (penSubMode.value === 'delete') {
      hoverFeedback.value = 'Click to delete point';
    } else if (penSubMode.value === 'convert') {
      const currentType = point.type === 'smooth' ? 'smooth' : 'corner';
      const newType = currentType === 'smooth' ? 'corner' : 'smooth';
      hoverFeedback.value = `Click to convert to ${newType}`;
    } else {
      hoverFeedback.value = null;
    }
  } else {
    hoverFeedback.value = null;
  }
}

// Handle mouse leave from control point
function handlePointLeave() {
  hoveredPointId.value = null;
  hoverFeedback.value = null;
  hoverFeedbackPos.value = null;
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

// Start axis-constrained drag
function startDragAxis(pointId: string, axis: 'X' | 'Y', event: MouseEvent) {
  const point = visibleControlPoints.value.find(p => p.id === pointId);
  if (!point) return;

  // Get both canvas and screen coordinates
  const pos = getMousePos(event);

  selectedPointId.value = pointId;
  dragTarget.value = {
    type: axis === 'X' ? 'axisX' : 'axisY',
    pointId,
    startX: pos.x,
    startY: pos.y,
    originalX: point.x,
    originalY: point.y,
    // Store screen coordinates for zoom-independent movement
    screenStartX: event.clientX,
    screenStartY: event.clientY
  };
}

// Handle keyboard shortcuts for spline editing
function handleKeyDown(event: KeyboardEvent) {
  // Delete selected point on Delete/Backspace key
  if (event.key === 'Delete' || event.key === 'Backspace') {
    if (selectedPointId.value && props.layerId) {
      const layer = store.layers.find(l => l.id === props.layerId);
      if (layer && isSplineOrPathType(layer.type)) {
        const pointId = selectedPointId.value;
        // Delete via store action
        store.deleteSplineControlPoint(props.layerId, pointId);
        emit('pointDeleted', pointId);
        emit('pathUpdated');
        selectedPointId.value = null;
        selectedPointIds.value = [];
      }
    }
  }

  // Arrow Up/Down to adjust Z-depth of selected point
  if (event.key === 'ArrowUp' && selectedPointId.value) {
    event.preventDefault();
    const delta = event.shiftKey ? 100 : 10; // Shift for larger increments
    adjustSelectedPointDepth(delta);
  }
  if (event.key === 'ArrowDown' && selectedPointId.value) {
    event.preventDefault();
    const delta = event.shiftKey ? -100 : -10;
    adjustSelectedPointDepth(delta);
  }

  // Escape to deselect point
  if (event.key === 'Escape') {
    selectedPointId.value = null;
    selectedPointIds.value = [];
    hoverFeedback.value = null;
    if (props.isPenMode) {
      emit('togglePenMode');
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
  selectedPointIds,
  clearSelection: () => {
    selectedPointId.value = null;
    selectedPointIds.value = [];
  }
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

/* Selection ring - shown around selected point */
.selection-ring {
  fill: none;
  stroke: #00ff66;
  stroke-width: 2;
  stroke-dasharray: 4 2;
  pointer-events: none;
  opacity: 0.8;
}

/* Axis handles for X/Y movement */
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

.axis-hit-area {
  fill: transparent;
  cursor: pointer;
  pointer-events: all;
}

.axis-x-group .axis-hit-area {
  cursor: ew-resize;
}

.axis-x-group .axis-hit-area:hover ~ .axis-line,
.axis-x-group .axis-hit-area:hover ~ .axis-arrow {
  filter: brightness(1.3);
}

.axis-y-group .axis-hit-area {
  cursor: ns-resize;
}

.axis-y-group .axis-hit-area:hover ~ .axis-line,
.axis-y-group .axis-hit-area:hover ~ .axis-arrow {
  filter: brightness(1.3);
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

/* Tool tip popup - guidance text above toolbar */
.tool-tip-popup {
  position: absolute;
  bottom: 55px;
  left: 50%;
  transform: translateX(-50%);
  background: rgba(0, 0, 0, 0.85);
  color: #ffffff;
  padding: 6px 12px;
  border-radius: 4px;
  font-size: 11px;
  white-space: nowrap;
  z-index: 101;
  pointer-events: none;
  border: 1px solid rgba(0, 255, 100, 0.3);
  box-shadow: 0 2px 8px rgba(0, 0, 0, 0.3);
}

/* Hover feedback - text that follows mouse for delete/add feedback */
.hover-feedback {
  position: absolute;
  background: rgba(0, 0, 0, 0.9);
  color: #ffcc00;
  padding: 4px 8px;
  border-radius: 3px;
  font-size: 10px;
  white-space: nowrap;
  z-index: 102;
  pointer-events: none;
  border: 1px solid rgba(255, 204, 0, 0.5);
}

/* Control point states for delete/convert preview */
.control-point.will-delete {
  fill: #ff4444 !important;
  stroke: #ffffff !important;
  animation: pulse-delete 0.3s ease-in-out infinite alternate;
}

@keyframes pulse-delete {
  from { opacity: 0.7; }
  to { opacity: 1; }
}

.control-point.will-convert {
  fill: #ff8800 !important;
  stroke: #ffffff !important;
  stroke-width: 3;
}

/* Multi-select highlight */
.control-point.selected {
  stroke-width: 3;
}

/* Z-depth controls */
.z-depth-controls {
  border-left: 1px solid rgba(255, 255, 255, 0.1);
  padding-left: 8px;
}

.z-depth-label {
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: 11px;
  color: #0088ff;
}

.z-depth-input {
  width: 50px;
  padding: 2px 4px;
  background: rgba(0, 136, 255, 0.2);
  border: 1px solid rgba(0, 136, 255, 0.4);
  border-radius: 3px;
  color: #0088ff;
  font-size: 10px;
  font-family: monospace;
  text-align: right;
}

.z-depth-input:focus {
  outline: none;
  border-color: #0088ff;
  background: rgba(0, 136, 255, 0.3);
}

.z-depth-hint {
  font-size: 9px;
  color: rgba(255, 255, 255, 0.4);
  margin-left: 4px;
}
</style>
