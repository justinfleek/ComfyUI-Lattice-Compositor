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
    <SplineToolbar
      v-if="layerId"
      :isPenMode="isPenMode"
      :penSubMode="penSubMode"
      :hasControlPoints="hasControlPoints"
      :controlPointCount="visibleControlPoints.length"
      :selectedPointCount="selectedPointIds.length"
      :hasSelectedPoint="!!selectedPointId"
      :selectedPointDepth="selectedPointDepth"
      :isClosed="isClosed"
      :isSplineAnimated="isSplineAnimated"
      v-model:smoothTolerance="smoothTolerance"
      @setPenSubMode="setPenSubMode"
      @smoothSelectedPoints="smoothSelectedPoints"
      @simplifySpline="simplifySpline"
      @toggleClosePath="toggleClosePath"
      @updateSelectedPointDepth="updateSelectedPointDepth"
      @toggleSplineAnimation="toggleSplineAnimation"
      @keyframeSelectedPoints="keyframeSelectedPoints"
    />

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
          :class="{ active: getDragTargetType() === 'handleIn' && getDragTargetPointId() === point.id }"
          :style="{ fill: strokeColor }"
          @mousedown.stop="startDragHandle(point.id, 'in', $event)"
        />
        <circle
          v-if="point.handleOut && selectedPointId === point.id"
          :cx="point.handleOut.x"
          :cy="point.handleOut.y"
          r="4"
          class="handle-point"
          :class="{ active: getDragTargetType() === 'handleOut' && getDragTargetPointId() === point.id }"
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
            :class="{ active: getDragTargetType() === 'depth' && getDragTargetPointId() === point.id }"
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
/**
 * SplineEditor - Control point editor for spline and path layers
 * Refactored to use useSplineInteraction composable for interaction logic.
 */
import { computed, type ComputedRef, onMounted, onUnmounted, ref, toRef } from "vue";
import { assertDefined, safeNonNegativeDefault } from "@/utils/typeGuards";
import { useSplineInteraction } from "@/composables/useSplineInteraction";
import { interpolateProperty } from "@/services/interpolation";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "@/stores/projectStore";
import type {
  AnimatableProperty,
  ControlPoint,
  EvaluatedControlPoint,
  PathLayerData,
  PropertyValue,
  SplineData,
} from "@/types/project";

// Helper: Check if layer is a spline or path type
function isSplineOrPathType(
  layerType: string | undefined,
): layerType is "spline" | "path" {
  return layerType === "spline" || layerType === "path";
}

interface Props {
  layerId: string | null;
  currentFrame: number;
  canvasWidth: number;
  canvasHeight: number;
  containerWidth: number;
  containerHeight: number;
  zoom: number;
  viewportTransform: number[];
  isPenMode: boolean;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: "pointAdded", point: ControlPoint): void;
  (e: "pointMoved", pointId: string, x: number, y: number): void;
  (
    e: "handleMoved",
    pointId: string,
    handleType: "in" | "out",
    x: number,
    y: number,
  ): void;
  (e: "pointDeleted", pointId: string): void;
  (e: "pathUpdated"): void;
  (e: "pathClosed"): void;
  (e: "togglePenMode"): void;
}>();

const layerStore = useLayerStore();
const projectStore = useProjectStore();

// Toolbar state
const smoothTolerance = ref(10);
const strokeColor = "#00ff00";

// ============================================================================
// LAYER TRANSFORM
// ============================================================================

const layerTransform = computed(() => {
  if (!props.layerId) {
    return {
      position: { x: 0, y: 0 },
      rotation: 0,
      scale: { x: 100, y: 100 },
      anchorPoint: { x: 0, y: 0 },
    };
  }

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
  if (!layer) {
    return {
      position: { x: 0, y: 0 },
      rotation: 0,
      scale: { x: 100, y: 100 },
      anchorPoint: { x: 0, y: 0 },
    };
  }

  const t = layer.transform;

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  const getVal = <T extends PropertyValue>(
    prop: AnimatableProperty<T> | undefined,
    defaultVal: T,
  ): T => {
    if (!prop) return defaultVal;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const keyframes = (prop != null && typeof prop === "object" && "keyframes" in prop && prop.keyframes != null && Array.isArray(prop.keyframes)) ? prop.keyframes : undefined;
    const keyframesLength = keyframes != null ? keyframes.length : 0;
    if (prop.animated && keyframesLength > 0) {
      // Pattern match: interpolateProperty result ∈ T | undefined → T (use default if undefined)
      const interpolated = interpolateProperty(prop, props.currentFrame);
      return (interpolated !== undefined && interpolated !== null) ? interpolated as T : defaultVal;
    }
    // Pattern match: prop.value ∈ T | undefined → T (use default if undefined)
    const value = prop.value;
    return (value !== undefined && value !== null) ? value as T : defaultVal;
  };

  const position = getVal(t.position, {
    x: props.canvasWidth / 2,
    y: props.canvasHeight / 2,
  });
  const anchorPoint = getVal(t.anchorPoint, { x: 0, y: 0 });
  const scale = getVal(t.scale, { x: 100, y: 100 });

  let rotation = 0;
  if (layer.threeD && t.rotationZ) {
    rotation = getVal(t.rotationZ, 0);
  } else if (t.rotation) {
    rotation = getVal(t.rotation, 0);
  }

  return { position, rotation, scale, anchorPoint };
});

function transformPoint(p: { x: number; y: number }): { x: number; y: number } {
  const { position, rotation, scale, anchorPoint } = layerTransform.value;

  let x = p.x - anchorPoint.x;
  let y = p.y - anchorPoint.y;

  x *= scale.x / 100;
  y *= scale.y / 100;

  const rad = (rotation * Math.PI) / 180;
  const cos = Math.cos(rad);
  const sin = Math.sin(rad);
  const rx = x * cos - y * sin;
  const ry = x * sin + y * cos;

  return { x: rx + position.x, y: ry + position.y };
}

function inverseTransformPoint(p: { x: number; y: number }): {
  x: number;
  y: number;
} {
  const { position, rotation, scale, anchorPoint } = layerTransform.value;

  let x = p.x - position.x;
  let y = p.y - position.y;

  const rad = (-rotation * Math.PI) / 180;
  const cos = Math.cos(rad);
  const sin = Math.sin(rad);
  const rx = x * cos - y * sin;
  const ry = x * sin + y * cos;

  x = rx / (scale.x / 100);
  y = ry / (scale.y / 100);

  return { x: x + anchorPoint.x, y: y + anchorPoint.y };
}

// ============================================================================
// COMPUTED PROPERTIES
// ============================================================================

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
const isClosed = computed(() => {
  if (!props.layerId) return false;
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type)) return false;
  const layerData = layer.data as SplineData | PathLayerData;
  return (layerData !== null && layerData !== undefined && typeof layerData === "object" && "closed" in layerData && typeof layerData.closed === "boolean") ? layerData.closed : false;
});

const is3DLayer = computed(() => {
  if (!props.layerId) return false;
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
  return (layer !== null && layer !== undefined && typeof layer === "object" && "threeD" in layer && typeof layer.threeD === "boolean") ? layer.threeD : false;
});

const isSplineAnimated = computed(() => {
  if (!props.layerId) return false;
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
  if (!layer || layer.type !== "spline") return false;
  const splineData = layer.data as SplineData;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const animated = (splineData != null && typeof splineData === "object" && "animated" in splineData && typeof splineData.animated === "boolean" && splineData.animated) ? true : false;
  return animated === true;
});

const rawControlPoints = computed<(ControlPoint | EvaluatedControlPoint)[]>(
  () => {
    if (!props.layerId) return [];

    const layer = projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
    if (!layer || !isSplineOrPathType(layer.type) || !layer.data) return [];

    const layerData = layer.data as SplineData | PathLayerData;

    if (layerData.animated && layerData.animatedControlPoints) {
      return layerStore.getEvaluatedSplinePoints(props.layerId, props.currentFrame);
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const controlPoints = layerData.controlPoints;
    return (controlPoints !== null && controlPoints !== undefined && Array.isArray(controlPoints)) ? controlPoints : [];
  },
);

interface TransformedControlPoint extends ControlPoint {
  rawX: number;
  rawY: number;
  rawHandleIn: { x: number; y: number } | null;
  rawHandleOut: { x: number; y: number } | null;
}

const visibleControlPoints = computed<TransformedControlPoint[]>(() => {
  return rawControlPoints.value.map((cp) => {
    const transformed = transformPoint({ x: cp.x, y: cp.y });
    const transformedHandleIn = cp.handleIn
      ? transformPoint(cp.handleIn)
      : null;
    const transformedHandleOut = cp.handleOut
      ? transformPoint(cp.handleOut)
      : null;

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
      type: cp.type,
    };
  });
});

const hasControlPoints = computed(() => visibleControlPoints.value.length > 0);

const canClosePath = computed(() => {
  return visibleControlPoints.value.length >= 3 && !isClosed.value;
});

const overlayStyle = computed(() => {
  const compAspect = props.canvasWidth / props.canvasHeight;
  const containerAspect = props.containerWidth / props.containerHeight;

  let fitWidth: number, fitHeight: number;
  if (compAspect > containerAspect) {
    fitWidth = props.containerWidth;
    fitHeight = props.containerWidth / compAspect;
  } else {
    fitHeight = props.containerHeight;
    fitWidth = props.containerHeight * compAspect;
  }

  const zoomFactor = props.zoom || 1;
  const width = fitWidth * zoomFactor;
  const height = fitHeight * zoomFactor;

  // Apply viewport pan offset to keep SVG aligned with the canvas.
  // viewportTransform[4,5] contain screen-pixel pan offsets. The SVG must
  // move with the viewport so mouse coordinates stay aligned with canvas
  // content during pan operations.
  const vpt = props.viewportTransform;
  const panOffsetX = vpt && vpt.length > 4 && Number.isFinite(vpt[4]) ? vpt[4] : 0;
  const panOffsetY = vpt && vpt.length > 5 && Number.isFinite(vpt[5]) ? vpt[5] : 0;

  // Center position plus pan offset
  const centerLeft = (props.containerWidth - width) / 2;
  const centerTop = (props.containerHeight - height) / 2;
  const left = centerLeft + panOffsetX;
  const top = centerTop + panOffsetY;

  return {
    position: "absolute" as const,
    left: `${left}px`,
    top: `${top}px`,
    width: `${width}px`,
    height: `${height}px`,
    pointerEvents: "all" as const,
  };
});

// ============================================================================
// USE SPLINE INTERACTION COMPOSABLE
// ============================================================================

const interaction = useSplineInteraction({
  layerId: toRef(props, "layerId"),
  currentFrame: toRef(props, "currentFrame"),
  canvasWidth: toRef(props, "canvasWidth"),
  canvasHeight: toRef(props, "canvasHeight"),
  containerWidth: toRef(props, "containerWidth"),
  containerHeight: toRef(props, "containerHeight"),
  zoom: toRef(props, "zoom"),
  isPenMode: toRef(props, "isPenMode"),
  visibleControlPoints: visibleControlPoints as ComputedRef<(ControlPoint | EvaluatedControlPoint)[]>,
  isClosed,
  overlayStyle: overlayStyle as ComputedRef<{
    width: string;
    height: string;
    left: string;
    top: string;
  }>,
  transformPoint,
  inverseTransformPoint,
  layerStore,
  emit: {
    pointAdded: (point) => emit("pointAdded", point),
    pointMoved: (pointId, x, y) => emit("pointMoved", pointId, x, y),
    handleMoved: (pointId, handleType, x, y) =>
      emit("handleMoved", pointId, handleType, x, y),
    pointDeleted: (pointId) => emit("pointDeleted", pointId),
    pathUpdated: () => emit("pathUpdated"),
    pathClosed: () => emit("pathClosed"),
    togglePenMode: () => emit("togglePenMode"),
  },
});

const {
  selectedPointId,
  selectedPointIds,
  hoveredPointId,
  hoverFeedback,
  hoverFeedbackStyle,
  previewPoint,
  closePathPreview,
  previewCurve,
  insertPreviewPoint,
  penSubMode,
  dragTarget,
  activeToolTip,
  setPenSubMode,
  handleMouseDown,
  handleMouseMove,
  handleMouseUp,
  handleRightClick,
  handlePointClick,
  handlePointHover,
  handlePointLeave,
  startDragHandle,
  startDragAxis,
  startDragDepth,
  handleKeyDown,
  clearSelection,
} = interaction;

// ============================================================================
// COMPONENT-SPECIFIC FUNCTIONS
// ============================================================================

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
function getDragTargetType(): string | undefined {
  const dragTargetValue = dragTarget.value;
  return (dragTargetValue != null && typeof dragTargetValue === "object" && "type" in dragTargetValue && typeof dragTargetValue.type === "string") ? dragTargetValue.type : undefined;
}

function getDragTargetPointId(): string | undefined {
  const dragTargetValue = dragTarget.value;
  return (dragTargetValue != null && typeof dragTargetValue === "object" && "pointId" in dragTargetValue && typeof dragTargetValue.pointId === "string") ? dragTargetValue.pointId : undefined;
}

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
const selectedPointDepth = computed(() => {
  if (!selectedPointId.value) return 0;
  const point = visibleControlPoints.value.find(
    (p) => p.id === selectedPointId.value,
  );
  return (point !== null && point !== undefined && typeof point === "object" && "depth" in point && typeof point.depth === "number" && Number.isFinite(point.depth)) ? point.depth : 0;
});

function updateSelectedPointDepth(event: Event) {
  if (!selectedPointId.value || !props.layerId) return;
  const input = event.target as HTMLInputElement;
  // Type proof: depth ∈ number | NaN → number (≥ 0, z-coordinate depth)
  const parsedDepth = parseFloat(input.value);
  const depth = Number.isFinite(parsedDepth) && parsedDepth >= 0 ? parsedDepth : 0;
  const newDepth = Math.max(0, depth);
  layerStore.updateSplineControlPoint(props.layerId, selectedPointId.value, {
    depth: newDepth,
  });
  emit("pathUpdated");
}

function adjustSelectedPointDepth(delta: number) {
  if (!selectedPointId.value || !props.layerId) return;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  const point = visibleControlPoints.value.find(
    (p) => p.id === selectedPointId.value,
  );
  const currentDepth = (point !== null && point !== undefined && typeof point === "object" && "depth" in point && typeof point.depth === "number" && Number.isFinite(point.depth)) ? point.depth : 0;
  const newDepth = Math.max(0, currentDepth + delta);
  layerStore.updateSplineControlPoint(props.layerId, selectedPointId.value, {
    depth: newDepth,
  });
  emit("pathUpdated");
}

function toggleClosePath() {
  if (!props.layerId) return;
  layerStore.updateLayerData(props.layerId, { closed: !isClosed.value });
  emit("pathUpdated");
}

function smoothSelectedPoints() {
  if (!props.layerId) return;

  if (selectedPointIds.value.length > 0) {
    smoothSpecificPoints(selectedPointIds.value);
  } else if (selectedPointId.value) {
    smoothSpecificPoints([selectedPointId.value]);
  } else {
    layerStore.smoothSplineHandles(props.layerId, smoothTolerance.value * 2);
  }
  emit("pathUpdated");
}

function smoothSpecificPoints(pointIds: string[]) {
  if (!props.layerId) return;

  const layer = projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
  if (!layer || !isSplineOrPathType(layer.type) || !layer.data) return;

  const splineData = layer.data as SplineData | PathLayerData;
  const controlPoints = splineData.controlPoints;
  if (!controlPoints || controlPoints.length < 2) return;

  const factor = Math.max(0, Math.min(100, smoothTolerance.value * 2)) / 100;

  for (const pointId of pointIds) {
    const i = controlPoints.findIndex((cp) => cp.id === pointId);
    if (i < 0) continue;

    const cp = controlPoints[i];
    const prev =
      controlPoints[(i - 1 + controlPoints.length) % controlPoints.length];
    const next = controlPoints[(i + 1) % controlPoints.length];

    if (!splineData.closed && (i === 0 || i === controlPoints.length - 1))
      continue;

    const toPrev = { x: prev.x - cp.x, y: prev.y - cp.y };
    const toNext = { x: next.x - cp.x, y: next.y - cp.y };

    const avgDir = { x: toNext.x - toPrev.x, y: toNext.y - toPrev.y };
    const avgLength = Math.sqrt(avgDir.x * avgDir.x + avgDir.y * avgDir.y);

    if (avgLength < 0.01) continue;

    const normalized = { x: avgDir.x / avgLength, y: avgDir.y / avgLength };

    const distPrev = Math.sqrt(toPrev.x * toPrev.x + toPrev.y * toPrev.y);
    const distNext = Math.sqrt(toNext.x * toNext.x + toNext.y * toNext.y);
    const handleLength = (distPrev + distNext) / 6;

    const idealIn = {
      x: cp.x - normalized.x * handleLength,
      y: cp.y - normalized.y * handleLength,
    };
    const idealOut = {
      x: cp.x + normalized.x * handleLength,
      y: cp.y + normalized.y * handleLength,
    };

    // Type proof: layerId is guaranteed non-null by guard clause at function start
    assertDefined(props.layerId, "layerId must exist when smoothSpecificPoints is called");
    layerStore.updateSplineControlPoint(props.layerId, pointId, {
      type: "smooth",
      handleIn: {
        x: cp.handleIn
          ? cp.handleIn.x + (idealIn.x - cp.handleIn.x) * factor
          : idealIn.x * factor + cp.x * (1 - factor),
        y: cp.handleIn
          ? cp.handleIn.y + (idealIn.y - cp.handleIn.y) * factor
          : idealIn.y * factor + cp.y * (1 - factor),
      },
      handleOut: {
        x: cp.handleOut
          ? cp.handleOut.x + (idealOut.x - cp.handleOut.x) * factor
          : idealOut.x * factor + cp.x * (1 - factor),
        y: cp.handleOut
          ? cp.handleOut.y + (idealOut.y - cp.handleOut.y) * factor
          : idealOut.y * factor + cp.y * (1 - factor),
      },
    });
  }
}

function simplifySpline() {
  if (!props.layerId) return;
  layerStore.simplifySpline(props.layerId, smoothTolerance.value);
  emit("pathUpdated");
}

function toggleSplineAnimation() {
  if (!props.layerId) return;
  layerStore.enableSplineAnimation(props.layerId);
  emit("pathUpdated");
}

function keyframeSelectedPoints() {
  if (!props.layerId || selectedPointIds.value.length === 0) return;
  const frame = props.currentFrame;
  for (const pointId of selectedPointIds.value) {
    layerStore.addSplinePointPositionKeyframe(props.layerId, pointId, frame);
  }
  emit("pathUpdated");
}

function pointHasKeyframes(pointId: string): boolean {
  if (!props.layerId) return false;
  return layerStore.hasSplinePointKeyframes(props.layerId, pointId);
}

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
function getPointDepth(point: ControlPoint | EvaluatedControlPoint): number {
  return (typeof point.depth === "number" && Number.isFinite(point.depth)) ? point.depth : 0;
}

function getDepthOffset(point: ControlPoint | EvaluatedControlPoint): number {
  const depth = getPointDepth(point);
  return Math.max(-30, Math.min(30, -depth / 16.67));
}

function getZHandlePoints(
  point: ControlPoint | EvaluatedControlPoint,
): string {
  const x = point.x + 15;
  const y = point.y + getDepthOffset(point);
  const size = 5;
  return `${x},${y - size} ${x + size},${y} ${x},${y + size} ${x - size},${y}`;
}

function handleKeyDownWithDepth(event: KeyboardEvent) {
  if (event.key === "ArrowUp" && selectedPointId.value) {
    event.preventDefault();
    const delta = event.shiftKey ? 100 : 10;
    adjustSelectedPointDepth(delta);
    return;
  }
  if (event.key === "ArrowDown" && selectedPointId.value) {
    event.preventDefault();
    const delta = event.shiftKey ? -100 : -10;
    adjustSelectedPointDepth(delta);
    return;
  }

  handleKeyDown(event);
}

onMounted(() => {
  window.addEventListener("keydown", handleKeyDownWithDepth);
});

onUnmounted(() => {
  window.removeEventListener("keydown", handleKeyDownWithDepth);
});

defineExpose({
  selectedPointId,
  selectedPointIds,
  clearSelection,
});
</script>

<style scoped>
.spline-editor {
  position: absolute;
  inset: 0;
  pointer-events: none;
}

.control-overlay {
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

.selection-ring {
  fill: none;
  stroke: #00ff66;
  stroke-width: 2;
  stroke-dasharray: 4 2;
  pointer-events: none;
  opacity: 0.8;
}

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

.control-point.selected {
  stroke-width: 3;
}
</style>
