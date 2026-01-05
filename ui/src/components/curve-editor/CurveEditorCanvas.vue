<template>
  <div class="curve-editor-canvas" ref="containerRef">
    <!-- Curve Editor Toolbar -->
    <div class="curve-toolbar">
      <div class="curve-mode-toggle">
        <button
          :class="{ active: graphMode === 'value' }"
          @click="setGraphMode('value')"
          title="Edit Value Graph"
        >
          <span class="icon">📈</span> Value
        </button>
        <button
          :class="{ active: graphMode === 'speed' }"
          @click="setGraphMode('speed')"
          title="Edit Speed Graph"
        >
          <span class="icon">⚡</span> Speed
        </button>
      </div>

      <!-- Keyframe Value Editor -->
      <div v-if="selectedKeyframeData" class="keyframe-value-editor">
        <span class="value-label">Frame:</span>
        <input
          type="number"
          class="value-input frame-input"
          :value="selectedKeyframeData.frame"
          @change="updateSelectedKeyframeFrame"
          @keydown.enter="($event.target as HTMLInputElement).blur()"
        />
        <span class="value-label">Value:</span>
        <input
          type="number"
          class="value-input"
          :value="formatValueForInput(selectedKeyframeData.value)"
          @change="updateSelectedKeyframeValue"
          @keydown.enter="($event.target as HTMLInputElement).blur()"
          step="0.1"
        />
      </div>

      <div class="zoom-controls">
        <button @click="zoomIn" title="Zoom In">+</button>
        <span class="zoom-level">{{ zoomLevel.toFixed(1) }}px/f</span>
        <button @click="zoomOut" title="Zoom Out">−</button>
        <button @click="fitToView" title="Fit All">⊡</button>
      </div>
    </div>

    <!-- Y-axis value labels -->
    <div class="y-axis">
      <div class="y-axis-unit">{{ yAxisUnit }}</div>
      <div
        v-for="label in yAxisLabels"
        :key="label.value"
        class="y-label"
        :style="{ top: `${label.percent}%` }"
      >
        {{ label.text }}
      </div>
    </div>

    <!-- Main canvas area -->
    <div class="canvas-area" ref="canvasAreaRef">
      <canvas
        ref="canvasRef"
        @mousedown="handleMouseDown"
        @wheel.prevent="handleWheel"
      ></canvas>

      <!-- Keyframe points (DOM for interaction) - Only in Value mode -->
      <template v-if="graphMode === 'value'">
        <template v-for="curve in visibleCurves" :key="curve.id">
          <div
            v-for="kf in curve.keyframes"
            :key="kf.id"
            class="keyframe-point"
            :class="{
              selected: selectedKeyframeIds.includes(kf.id),
              'interp-linear': kf.interpolation === 'linear',
              'interp-bezier': kf.interpolation === 'bezier' || isEasingInterpolation(kf.interpolation),
              'interp-hold': kf.interpolation === 'hold'
            }"
            :style="getKeyframeStyle(curve, kf)"
            @mousedown.stop="startKeyframeDrag(curve, kf, $event)"
            @click.stop="selectKeyframe(kf.id, $event)"
            :title="`${curve.name}: ${formatValue(kf.value)} @ Frame ${kf.frame} (${kf.interpolation})`"
          >
            <div class="point-inner" :style="{ background: curve.color }"></div>
          </div>

          <!-- Bezier handles for selected keyframes -->
          <template v-for="kf in curve.keyframes" :key="'handles-' + kf.id">
            <template v-if="selectedKeyframeIds.includes(kf.id) && kf.interpolation === 'bezier'">
              <!-- In handle -->
              <template v-if="kf.inHandle?.enabled">
                <div
                  class="bezier-handle"
                  :style="getHandleStyle(curve, kf, 'in')"
                  @mousedown.stop="startHandleDrag(curve, kf, 'in', $event)"
                ></div>
                <svg class="handle-line-svg">
                  <line
                    :x1="getHandleLineCoords(curve, kf, 'in').x1"
                    :y1="getHandleLineCoords(curve, kf, 'in').y1"
                    :x2="getHandleLineCoords(curve, kf, 'in').x2"
                    :y2="getHandleLineCoords(curve, kf, 'in').y2"
                    :stroke="curve.color"
                    stroke-width="1"
                  />
                </svg>
              </template>
              <!-- Out handle -->
              <template v-if="kf.outHandle?.enabled">
                <div
                  class="bezier-handle"
                  :style="getHandleStyle(curve, kf, 'out')"
                  @mousedown.stop="startHandleDrag(curve, kf, 'out', $event)"
                ></div>
                <svg class="handle-line-svg">
                  <line
                    :x1="getHandleLineCoords(curve, kf, 'out').x1"
                    :y1="getHandleLineCoords(curve, kf, 'out').y1"
                    :x2="getHandleLineCoords(curve, kf, 'out').x2"
                    :y2="getHandleLineCoords(curve, kf, 'out').y2"
                    :stroke="curve.color"
                    stroke-width="1"
                  />
                </svg>
              </template>
            </template>
          </template>
        </template>
      </template>

      <!-- Playhead -->
      <div
        class="playhead"
        :style="{ left: `${playheadPx}px` }"
      ></div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, nextTick, onMounted, onUnmounted, ref, watch } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import type { Keyframe } from "@/types/project";

// ═══════════════════════════════════════════════════════════════════
// CONSTANTS - Curve Colors
// ═══════════════════════════════════════════════════════════════════

const CURVE_COLORS: Record<string, string> = {
  "Position X": "#ff4d4d", // Red
  "Position Y": "#4dff4d", // Green
  "Position Z": "#4d4dff", // Blue
  "Scale X": "#ffb34d", // Orange
  "Scale Y": "#ffff4d", // Yellow
  Rotation: "#d94dff", // Purple
  Opacity: "#4dffff", // Cyan
  "Anchor Point X": "#ff4d4d",
  "Anchor Point Y": "#4dff4d",
};

// ═══════════════════════════════════════════════════════════════════
// TYPES
// ═══════════════════════════════════════════════════════════════════

interface CurveData {
  id: string;
  layerId: string;
  propertyPath: string;
  name: string;
  color: string;
  keyframes: Keyframe<any>[];
}

// ═══════════════════════════════════════════════════════════════════
// PROPS & EMITS
// ═══════════════════════════════════════════════════════════════════

const props = defineProps<{
  frameCount: number;
  currentFrame: number;
  selectedPropertyIds: string[];
  graphMode: "value" | "speed";
}>();

const emit = defineEmits<{
  (e: "selectKeyframe", id: string, addToSelection: boolean): void;
  (e: "update:graphMode", mode: "value" | "speed"): void;
}>();

const store = useCompositorStore();

// ═══════════════════════════════════════════════════════════════════
// REFS
// ═══════════════════════════════════════════════════════════════════

const _containerRef = ref<HTMLDivElement | null>(null);
const canvasAreaRef = ref<HTMLDivElement | null>(null);
const canvasRef = ref<HTMLCanvasElement | null>(null);

// ═══════════════════════════════════════════════════════════════════
// VIEWPORT STATE (Zoom & Pan)
// ═══════════════════════════════════════════════════════════════════

const zoomLevel = ref(5.0); // Pixels per frame
const scrollOffset = ref(0); // Frame at left edge

// ═══════════════════════════════════════════════════════════════════
// COORDINATE TRANSFORMS
// ═══════════════════════════════════════════════════════════════════

function frameToPixel(frame: number): number {
  return (frame - scrollOffset.value) * zoomLevel.value;
}

function pixelToFrame(pixel: number): number {
  return pixel / zoomLevel.value + scrollOffset.value;
}

function valueToPixel(value: number, height: number): number {
  const range = valueRange.value;
  const normalized = (value - range.min) / (range.max - range.min);
  return height - normalized * height; // Flip Y (0 at bottom)
}

function pixelToValue(pixel: number, height: number): number {
  const range = valueRange.value;
  const normalized = (height - pixel) / height;
  return range.min + normalized * (range.max - range.min);
}

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Selection
// ═══════════════════════════════════════════════════════════════════

const selectedKeyframeIds = computed(() => store.selectedKeyframeIds);

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Playhead Position
// ═══════════════════════════════════════════════════════════════════

const _playheadPx = computed(() => frameToPixel(props.currentFrame));

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Collect All Curves (with Separated Dimensions)
// ═══════════════════════════════════════════════════════════════════

const allCurves = computed<CurveData[]>(() => {
  const curves: CurveData[] = [];

  store.layers.forEach((layer) => {
    // Position X/Y (always separated for graph editing)
    if (
      layer.transform.position.animated &&
      layer.transform.position.keyframes.length > 0
    ) {
      const pos = layer.transform.position;
      curves.push({
        id: `${layer.id}-position-x`,
        layerId: layer.id,
        propertyPath: "transform.position",
        name: "Position X",
        color: CURVE_COLORS["Position X"],
        keyframes: pos.keyframes.map((kf) => ({
          ...kf,
          value: typeof kf.value === "object" ? kf.value.x : kf.value,
        })),
      });
      curves.push({
        id: `${layer.id}-position-y`,
        layerId: layer.id,
        propertyPath: "transform.position",
        name: "Position Y",
        color: CURVE_COLORS["Position Y"],
        keyframes: pos.keyframes.map((kf) => ({
          ...kf,
          value: typeof kf.value === "object" ? kf.value.y : kf.value,
        })),
      });
    }

    // Scale X/Y
    if (
      layer.transform.scale.animated &&
      layer.transform.scale.keyframes.length > 0
    ) {
      const scale = layer.transform.scale;
      curves.push({
        id: `${layer.id}-scale-x`,
        layerId: layer.id,
        propertyPath: "transform.scale",
        name: "Scale X",
        color: CURVE_COLORS["Scale X"],
        keyframes: scale.keyframes.map((kf) => ({
          ...kf,
          value: typeof kf.value === "object" ? kf.value.x : kf.value,
        })),
      });
      curves.push({
        id: `${layer.id}-scale-y`,
        layerId: layer.id,
        propertyPath: "transform.scale",
        name: "Scale Y",
        color: CURVE_COLORS["Scale Y"],
        keyframes: scale.keyframes.map((kf) => ({
          ...kf,
          value: typeof kf.value === "object" ? kf.value.y : kf.value,
        })),
      });
    }

    // Rotation
    if (
      layer.transform.rotation.animated &&
      layer.transform.rotation.keyframes.length > 0
    ) {
      curves.push({
        id: `${layer.id}-rotation`,
        layerId: layer.id,
        propertyPath: "transform.rotation",
        name: "Rotation",
        color: CURVE_COLORS.Rotation,
        keyframes: layer.transform.rotation.keyframes,
      });
    }

    // Opacity
    if (layer.opacity.animated && layer.opacity.keyframes.length > 0) {
      curves.push({
        id: `${layer.id}-opacity`,
        layerId: layer.id,
        propertyPath: "opacity",
        name: "Opacity",
        color: CURVE_COLORS.Opacity,
        keyframes: layer.opacity.keyframes,
      });
    }
  });

  return curves;
});

// Filter by selected properties
const visibleCurves = computed(() => {
  if (props.selectedPropertyIds.length === 0) {
    return allCurves.value;
  }
  return allCurves.value.filter((c) =>
    props.selectedPropertyIds.includes(c.id),
  );
});

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Value Range (Auto-scale Y axis)
// ═══════════════════════════════════════════════════════════════════

const valueRange = computed(() => {
  if (props.graphMode === "speed") {
    // Speed mode: 0 to max speed
    let maxSpeed = 100;
    visibleCurves.value.forEach((curve) => {
      for (let f = 0; f < props.frameCount - 1; f++) {
        const speed = calculateSpeedAtFrame(curve, f);
        maxSpeed = Math.max(maxSpeed, speed);
      }
    });
    return { min: 0, max: maxSpeed * 1.2 };
  }

  // Value mode
  const values: number[] = [];
  visibleCurves.value.forEach((curve) => {
    curve.keyframes.forEach((kf) => {
      const v = typeof kf.value === "number" ? kf.value : 0;
      values.push(v);
    });
  });

  if (values.length === 0) {
    return { min: 0, max: 100 };
  }

  const min = Math.min(...values);
  const max = Math.max(...values);
  const padding = Math.max((max - min) * 0.15, 20);

  return { min: min - padding, max: max + padding };
});

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Y-Axis Labels & Units
// ═══════════════════════════════════════════════════════════════════

const _yAxisUnit = computed(() => {
  if (props.graphMode === "speed") {
    const hasRotation = visibleCurves.value.some((c) =>
      c.name.includes("Rotation"),
    );
    return hasRotation ? "deg/sec" : "px/sec";
  }
  const hasRotation = visibleCurves.value.some((c) =>
    c.name.includes("Rotation"),
  );
  const hasOpacity = visibleCurves.value.some((c) =>
    c.name.includes("Opacity"),
  );
  if (hasRotation) return "deg";
  if (hasOpacity) return "%";
  return "px";
});

const _yAxisLabels = computed(() => {
  const range = valueRange.value;
  const labels: { value: number; percent: number; text: string }[] = [];
  const steps = 5;
  const stepSize = (range.max - range.min) / steps;

  for (let i = 0; i <= steps; i++) {
    const value = range.max - i * stepSize;
    labels.push({
      value,
      percent: (i / steps) * 100,
      text: value.toFixed(0),
    });
  }

  return labels;
});

// ═══════════════════════════════════════════════════════════════════
// COMPUTED - Selected Keyframe Data for Value Editing
// ═══════════════════════════════════════════════════════════════════

interface SelectedKeyframeInfo {
  curve: CurveData;
  keyframe: Keyframe<any>;
  frame: number;
  value: number;
}

const selectedKeyframeData = computed<SelectedKeyframeInfo | null>(() => {
  if (selectedKeyframeIds.value.length !== 1) return null;

  const selectedId = selectedKeyframeIds.value[0];

  for (const curve of visibleCurves.value) {
    const kf = curve.keyframes.find((k) => k.id === selectedId);
    if (kf) {
      return {
        curve,
        keyframe: kf,
        frame: kf.frame,
        value: typeof kf.value === "number" ? kf.value : 0,
      };
    }
  }

  return null;
});

function _formatValueForInput(value: number): string {
  return value.toFixed(2);
}

function _updateSelectedKeyframeFrame(e: Event) {
  const data = selectedKeyframeData.value;
  if (!data) return;

  const input = e.target as HTMLInputElement;
  const newFrame = Math.max(
    0,
    Math.min(props.frameCount - 1, parseInt(input.value, 10) || 0),
  );

  store.moveKeyframe(
    data.curve.layerId,
    data.curve.propertyPath,
    data.keyframe.id,
    newFrame,
  );
  draw();
}

function _updateSelectedKeyframeValue(e: Event) {
  const data = selectedKeyframeData.value;
  if (!data) return;

  const input = e.target as HTMLInputElement;
  const newValue = parseFloat(input.value) || 0;

  // Update the keyframe value
  store.setKeyframeValue(
    data.curve.layerId,
    data.curve.propertyPath,
    data.keyframe.id,
    newValue,
  );
  draw();
}

// ═══════════════════════════════════════════════════════════════════
// SPEED GRAPH MATH - Calculate derivative
// ═══════════════════════════════════════════════════════════════════

function calculateSpeedAtFrame(curve: CurveData, frame: number): number {
  const fps = store.fps || 30;
  const epsilon = 1 / fps;

  const v1 = sampleCurveValue(curve, frame);
  const v2 = sampleCurveValue(curve, frame + epsilon);

  return Math.abs(v2 - v1) * fps;
}

// Sample curve value at any float frame (with bezier interpolation)
function sampleCurveValue(curve: CurveData, t: number): number {
  const kfs = [...curve.keyframes].sort((a, b) => a.frame - b.frame);
  if (kfs.length === 0) return 0;
  if (kfs.length === 1) return kfs[0].value;

  // Before first keyframe
  if (t <= kfs[0].frame) return kfs[0].value;
  // After last keyframe
  if (t >= kfs[kfs.length - 1].frame) return kfs[kfs.length - 1].value;

  // Find segment
  let i = 0;
  while (i < kfs.length - 1 && kfs[i + 1].frame < t) i++;

  const kf1 = kfs[i];
  const kf2 = kfs[i + 1];
  const duration = kf2.frame - kf1.frame;
  const localT = (t - kf1.frame) / duration;

  const v1 = typeof kf1.value === "number" ? kf1.value : 0;
  const v2 = typeof kf2.value === "number" ? kf2.value : 0;

  const interp = kf1.interpolation || "linear";

  if (interp === "hold") {
    return v1;
  } else if (
    interp === "bezier" &&
    kf1.outHandle?.enabled &&
    kf2.inHandle?.enabled
  ) {
    // Cubic bezier interpolation
    return cubicBezierValue(
      v1,
      v1 + (kf1.outHandle?.value || 0),
      v2 + (kf2.inHandle?.value || 0),
      v2,
      localT,
    );
  } else {
    // Linear
    return v1 + (v2 - v1) * localT;
  }
}

// Cubic bezier value calculation
function cubicBezierValue(
  p0: number,
  p1: number,
  p2: number,
  p3: number,
  t: number,
): number {
  const mt = 1 - t;
  return (
    mt * mt * mt * p0 +
    3 * mt * mt * t * p1 +
    3 * mt * t * t * p2 +
    t * t * t * p3
  );
}

// ═══════════════════════════════════════════════════════════════════
// DRAWING
// ═══════════════════════════════════════════════════════════════════

function draw() {
  const canvas = canvasRef.value;
  const container = canvasAreaRef.value;
  if (!canvas || !container) return;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  const rect = container.getBoundingClientRect();
  canvas.width = rect.width;
  canvas.height = rect.height;

  const w = canvas.width;
  const h = canvas.height;
  const range = valueRange.value;

  ctx.clearRect(0, 0, w, h);

  // Grid
  drawGrid(ctx, w, h, range);

  // Curves
  visibleCurves.value.forEach((curve) => {
    if (curve.keyframes.length < 1) return;

    // Two-pass: black outline then colored
    for (let pass = 0; pass < 2; pass++) {
      ctx.strokeStyle = pass === 0 ? "#000" : curve.color;
      ctx.lineWidth = pass === 0 ? 4 : 2;
      ctx.beginPath();

      if (props.graphMode === "value") {
        drawValueCurve(ctx, curve, h, range);
      } else {
        drawSpeedCurve(ctx, curve, h);
      }

      ctx.stroke();
    }
  });
}

function drawGrid(
  ctx: CanvasRenderingContext2D,
  w: number,
  h: number,
  range: { min: number; max: number },
) {
  ctx.strokeStyle = "#333";
  ctx.lineWidth = 1;

  // Vertical grid (time) - based on zoom
  const frameStep = Math.max(1, Math.floor(50 / zoomLevel.value));
  const startFrame = Math.floor(scrollOffset.value);
  const endFrame = Math.ceil(scrollOffset.value + w / zoomLevel.value);

  for (let f = startFrame; f <= endFrame; f += frameStep) {
    const x = frameToPixel(f);
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, h);
    ctx.stroke();
  }

  // Horizontal grid (value)
  const valueStep = (range.max - range.min) / 5;
  for (let v = range.min; v <= range.max; v += valueStep) {
    const y = valueToPixel(v, h);
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(w, y);
    ctx.stroke();
  }

  // Zero line
  if (range.min < 0 && range.max > 0) {
    ctx.strokeStyle = "#555";
    ctx.lineWidth = 1;
    const zeroY = valueToPixel(0, h);
    ctx.beginPath();
    ctx.moveTo(0, zeroY);
    ctx.lineTo(w, zeroY);
    ctx.stroke();
  }
}

function drawValueCurve(
  ctx: CanvasRenderingContext2D,
  curve: CurveData,
  h: number,
  _range: { min: number; max: number },
) {
  const sorted = [...curve.keyframes].sort((a, b) => a.frame - b.frame);

  for (let i = 0; i < sorted.length; i++) {
    const kf = sorted[i];
    const v = typeof kf.value === "number" ? kf.value : 0;
    const x = frameToPixel(kf.frame);
    const y = valueToPixel(v, h);

    if (i === 0) {
      ctx.moveTo(x, y);
      continue;
    }

    const prev = sorted[i - 1];
    const prevV = typeof prev.value === "number" ? prev.value : 0;
    const interp = prev.interpolation || "linear";

    if (interp === "hold") {
      const _prevX = frameToPixel(prev.frame);
      const prevY = valueToPixel(prevV, h);
      ctx.lineTo(x, prevY);
      ctx.lineTo(x, y);
    } else if (
      interp === "bezier" &&
      prev.outHandle?.enabled &&
      kf.inHandle?.enabled
    ) {
      const cp1x = frameToPixel(prev.frame + prev.outHandle.frame);
      const cp1y = valueToPixel(prevV + prev.outHandle.value, h);
      const cp2x = frameToPixel(kf.frame + kf.inHandle.frame);
      const cp2y = valueToPixel(v + kf.inHandle.value, h);
      ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }
}

// SPEED GRAPH - The "Bell Curve" (derivative visualization)
function drawSpeedCurve(
  ctx: CanvasRenderingContext2D,
  curve: CurveData,
  h: number,
) {
  const _speedRange = valueRange.value;
  const step = 0.5; // Sample every half frame for smoothness

  const startFrame = Math.max(0, scrollOffset.value - 10);
  const endFrame = Math.min(
    props.frameCount,
    scrollOffset.value + ctx.canvas.width / zoomLevel.value + 10,
  );

  let first = true;

  for (let f = startFrame; f <= endFrame; f += step) {
    const speed = calculateSpeedAtFrame(curve, f);
    const x = frameToPixel(f);
    const y = valueToPixel(speed, h);

    if (first) {
      ctx.moveTo(x, y);
      first = false;
    } else {
      ctx.lineTo(x, y);
    }
  }
}

// ═══════════════════════════════════════════════════════════════════
// POSITIONING HELPERS
// ═══════════════════════════════════════════════════════════════════

function _getKeyframeStyle(_curve: CurveData, kf: Keyframe<any>) {
  const value = typeof kf.value === "number" ? kf.value : 0;
  const h = canvasRef.value?.height || 300;
  return {
    left: `${frameToPixel(kf.frame)}px`,
    top: `${valueToPixel(value, h)}px`,
  };
}

function _getHandleStyle(
  curve: CurveData,
  kf: Keyframe<any>,
  type: "in" | "out",
) {
  const handle = type === "in" ? kf.inHandle : kf.outHandle;
  if (!handle?.enabled) return { display: "none" };

  const kfValue = typeof kf.value === "number" ? kf.value : 0;
  const handleFrame = kf.frame + handle.frame;
  const handleValue = kfValue + handle.value;
  const h = canvasRef.value?.height || 300;

  return {
    left: `${frameToPixel(handleFrame)}px`,
    top: `${valueToPixel(handleValue, h)}px`,
    background: curve.color,
  };
}

function _getHandleLineCoords(
  _curve: CurveData,
  kf: Keyframe<any>,
  type: "in" | "out",
) {
  const handle = type === "in" ? kf.inHandle : kf.outHandle;
  if (!handle?.enabled) return { x1: 0, y1: 0, x2: 0, y2: 0 };

  const kfValue = typeof kf.value === "number" ? kf.value : 0;
  const h = canvasRef.value?.height || 300;

  return {
    x1: frameToPixel(kf.frame),
    y1: valueToPixel(kfValue, h),
    x2: frameToPixel(kf.frame + handle.frame),
    y2: valueToPixel(kfValue + handle.value, h),
  };
}

function _formatValue(value: any): string {
  if (typeof value === "number") return value.toFixed(1);
  if (typeof value === "object") return JSON.stringify(value);
  return String(value);
}

/**
 * Check if interpolation type is an easing function (not linear/bezier/hold)
 */
function _isEasingInterpolation(interpolation: string): boolean {
  return (
    interpolation.startsWith("easeIn") ||
    interpolation.startsWith("easeOut") ||
    interpolation.startsWith("easeInOut")
  );
}

// ═══════════════════════════════════════════════════════════════════
// ZOOM & PAN CONTROLS
// ═══════════════════════════════════════════════════════════════════

function _handleWheel(event: WheelEvent) {
  if (event.ctrlKey || event.metaKey) {
    // Zoom
    const zoomFactor = event.deltaY > 0 ? 0.9 : 1.1;
    zoomLevel.value = Math.max(0.5, Math.min(50, zoomLevel.value * zoomFactor));
  } else {
    // Pan
    scrollOffset.value += event.deltaY / zoomLevel.value;
    scrollOffset.value = Math.max(0, scrollOffset.value);
  }
  draw();
}

function _zoomIn() {
  zoomLevel.value = Math.min(50, zoomLevel.value * 1.2);
  draw();
}

function _zoomOut() {
  zoomLevel.value = Math.max(0.5, zoomLevel.value / 1.2);
  draw();
}

function _fitToView() {
  const w = canvasRef.value?.width || 800;
  zoomLevel.value = w / props.frameCount;
  scrollOffset.value = 0;
  draw();
}

function _setGraphMode(mode: "value" | "speed") {
  emit("update:graphMode", mode);
}

// ═══════════════════════════════════════════════════════════════════
// INTERACTION - Dragging
// ═══════════════════════════════════════════════════════════════════

let isDragging = false;
let dragType: "keyframe" | "handle" | "pan" | null = null;
let dragCurve: CurveData | null = null;
let dragKeyframe: Keyframe<any> | null = null;
let dragHandleType: "in" | "out" | null = null;
let dragStartPos = { x: 0, y: 0 };

function _handleMouseDown(event: MouseEvent) {
  if (event.button === 1 || (event.button === 0 && event.shiftKey)) {
    // Middle mouse or shift+left = pan
    isDragging = true;
    dragType = "pan";
    dragStartPos = { x: event.clientX, y: event.clientY };
    document.addEventListener("mousemove", handleMouseMove);
    document.addEventListener("mouseup", handleMouseUp);
    event.preventDefault();
  }
}

function _startKeyframeDrag(
  curve: CurveData,
  kf: Keyframe<any>,
  event: MouseEvent,
) {
  isDragging = true;
  dragType = "keyframe";
  dragCurve = curve;
  dragKeyframe = kf;
  document.addEventListener("mousemove", handleMouseMove);
  document.addEventListener("mouseup", handleMouseUp);
  event.preventDefault();
}

function _startHandleDrag(
  curve: CurveData,
  kf: Keyframe<any>,
  handleType: "in" | "out",
  event: MouseEvent,
) {
  isDragging = true;
  dragType = "handle";
  dragCurve = curve;
  dragKeyframe = kf;
  dragHandleType = handleType;
  document.addEventListener("mousemove", handleMouseMove);
  document.addEventListener("mouseup", handleMouseUp);
  event.preventDefault();
}

function handleMouseMove(event: MouseEvent) {
  if (!isDragging || !canvasAreaRef.value) return;

  const rect = canvasAreaRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;
  const h = rect.height;

  if (dragType === "pan") {
    const dx = event.clientX - dragStartPos.x;
    scrollOffset.value -= dx / zoomLevel.value;
    scrollOffset.value = Math.max(0, scrollOffset.value);
    dragStartPos = { x: event.clientX, y: event.clientY };
  } else if (dragType === "keyframe" && dragCurve && dragKeyframe) {
    const newFrame = Math.round(pixelToFrame(x));
    const clampedFrame = Math.max(0, Math.min(props.frameCount - 1, newFrame));
    store.moveKeyframe(
      dragCurve.layerId,
      dragCurve.propertyPath,
      dragKeyframe.id,
      clampedFrame,
    );
  } else if (
    dragType === "handle" &&
    dragCurve &&
    dragKeyframe &&
    dragHandleType
  ) {
    const mouseFrame = pixelToFrame(x);
    const mouseValue = pixelToValue(y, h);
    const kfValue =
      typeof dragKeyframe.value === "number" ? dragKeyframe.value : 0;

    const frameOffset = mouseFrame - dragKeyframe.frame;
    const valueOffset = mouseValue - kfValue;

    // Ctrl+drag breaks handles (sets controlMode to 'corner')
    const breakHandle = event.ctrlKey || event.metaKey;

    store.setKeyframeHandleWithMode(
      dragCurve.layerId,
      dragCurve.propertyPath,
      dragKeyframe.id,
      dragHandleType,
      { frame: frameOffset, value: valueOffset, enabled: true },
      breakHandle,
    );
  }

  draw();
}

function handleMouseUp() {
  isDragging = false;
  dragType = null;
  dragCurve = null;
  dragKeyframe = null;
  dragHandleType = null;
  document.removeEventListener("mousemove", handleMouseMove);
  document.removeEventListener("mouseup", handleMouseUp);
}

function _selectKeyframe(id: string, event: MouseEvent) {
  emit("selectKeyframe", id, event.shiftKey);
}

// ═══════════════════════════════════════════════════════════════════
// LIFECYCLE
// ═══════════════════════════════════════════════════════════════════

watch(
  () => [
    visibleCurves.value,
    props.frameCount,
    props.currentFrame,
    props.graphMode,
  ],
  () => nextTick(draw),
  { deep: true },
);

onMounted(() => {
  nextTick(draw);
  window.addEventListener("resize", draw);
});

onUnmounted(() => {
  window.removeEventListener("resize", draw);
});
</script>

<style scoped>
.curve-editor-canvas {
  display: flex;
  flex-direction: column;
  width: 100%;
  height: 100%;
  min-height: 300px;
  background: #1a1a1a;
}

.curve-toolbar {
  height: 32px;
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 0 12px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.curve-mode-toggle {
  display: flex;
  gap: 4px;
}

.curve-mode-toggle button {
  padding: 4px 10px;
  border: 1px solid #444;
  background: #2a2a2a;
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  font-size: 13px;
  transition: all 0.15s ease;
}

.curve-mode-toggle button:hover {
  background: #333;
  color: #fff;
}

.curve-mode-toggle button.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}

/* Keyframe Value Editor */
.keyframe-value-editor {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 0 12px;
  border-left: 1px solid #333;
  border-right: 1px solid #333;
}

.value-label {
  font-size: 13px;
  color: #888;
}

.value-input {
  width: 70px;
  padding: 3px 6px;
  border: 1px solid #444;
  border-radius: 3px;
  background: #2a2a2a;
  color: #3498db;
  font-size: 13px;
  text-align: right;
}

.value-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.value-input.frame-input {
  width: 50px;
}

.zoom-controls {
  display: flex;
  align-items: center;
  gap: 6px;
}

.zoom-controls button {
  width: 24px;
  height: 24px;
  border: 1px solid #444;
  background: #2a2a2a;
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  font-size: 14px;
}

.zoom-controls button:hover {
  background: #333;
  color: #fff;
}

.zoom-level {
  font-size: 12px;
  color: #666;
  min-width: 50px;
  text-align: center;
}

.y-axis {
  position: absolute;
  left: 0;
  top: 32px;
  bottom: 0;
  width: 50px;
  border-right: 1px solid #333;
  background: #1e1e1e;
}

.y-axis-unit {
  position: absolute;
  top: 4px;
  right: 8px;
  font-size: 11px;
  color: #888;
  text-transform: uppercase;
}

.y-label {
  position: absolute;
  right: 8px;
  transform: translateY(-50%);
  font-size: 12px;
  color: #666;
  font-family: monospace;
}

.canvas-area {
  flex: 1;
  position: relative;
  overflow: hidden;
  margin-left: 50px;
}

.canvas-area canvas {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
}

.keyframe-point {
  position: absolute;
  width: 12px;
  height: 12px;
  transform: translate(-50%, -50%);
  cursor: grab;
  z-index: 10;
}

.keyframe-point:active {
  cursor: grabbing;
}

.point-inner {
  width: 100%;
  height: 100%;
  border-radius: 50%;
  border: 2px solid #000;
  box-sizing: border-box;
  transition: transform 0.1s ease;
}

.keyframe-point:hover .point-inner {
  transform: scale(1.3);
}

.keyframe-point.selected .point-inner {
  background: #fff !important;
  border-color: #7c9cff;
  box-shadow: 0 0 0 3px rgba(124, 156, 255, 0.4);
}

/* Keyframe icon shapes by interpolation type */

/* Linear: diamond shape */
.keyframe-point.interp-linear .point-inner {
  border-radius: 0;
  transform: rotate(45deg);
}

.keyframe-point.interp-linear:hover .point-inner {
  transform: rotate(45deg) scale(1.3);
}

/* Bezier/Easing: circle (default) */
.keyframe-point.interp-bezier .point-inner {
  border-radius: 50%;
}

/* Hold: square shape */
.keyframe-point.interp-hold .point-inner {
  border-radius: 2px;
}

.bezier-handle {
  position: absolute;
  width: 8px;
  height: 8px;
  border-radius: 50%;
  border: 1px solid #000;
  transform: translate(-50%, -50%);
  cursor: grab;
  z-index: 11;
}

.bezier-handle:hover {
  transform: translate(-50%, -50%) scale(1.3);
}

.bezier-handle:active {
  cursor: grabbing;
}

.handle-line-svg {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  pointer-events: none;
  z-index: 9;
  overflow: visible;
}

.playhead {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  background: #ff4444;
  pointer-events: none;
  z-index: 20;
  box-shadow: 0 0 4px rgba(255, 68, 68, 0.5);
}
</style>
