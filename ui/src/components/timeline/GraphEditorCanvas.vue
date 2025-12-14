<template>
  <div class="graph-editor-canvas" ref="containerRef">
    <!-- Y-axis value labels -->
    <div class="y-axis">
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
        @wheel="handleWheel"
      ></canvas>

      <!-- Keyframe points (rendered as DOM for easier interaction) -->
      <template v-for="curve in visibleCurves" :key="curve.id">
        <div
          v-for="kf in curve.keyframes"
          :key="kf.id"
          class="keyframe-point"
          :class="{ selected: selectedKeyframeIds.includes(kf.id) }"
          :style="getKeyframeStyle(curve, kf)"
          @mousedown.stop="startKeyframeDrag(curve, kf, $event)"
          @click.stop="selectKeyframe(kf.id, $event)"
          :title="`${curve.name}: ${formatValue(kf.value)} @ Frame ${kf.frame}`"
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

      <!-- Playhead -->
      <div
        class="playhead"
        :style="{ left: `${playheadPercent}%` }"
      ></div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted, nextTick } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, Keyframe, AnimatableProperty } from '@/types/project';

// Property curve colors
const CURVE_COLORS: Record<string, string> = {
  'Position X': '#ff6b6b',
  'Position Y': '#4ecdc4',
  'Position Z': '#ab47bc',
  'Scale X': '#ffa726',
  'Scale Y': '#ffee58',
  'Scale Z': '#7c9cff',
  'Rotation': '#ab47bc',
  'Rotation X': '#ff6b6b',
  'Rotation Y': '#4ecdc4',
  'Rotation Z': '#ab47bc',
  'Opacity': '#7c9cff',
  'Anchor Point X': '#90a4ae',
  'Anchor Point Y': '#78909c',
};

interface CurveData {
  id: string;
  layerId: string;
  propertyPath: string;
  name: string;
  color: string;
  keyframes: Keyframe<any>[];
  visible: boolean;
}

const props = defineProps<{
  frameCount: number;
  currentFrame: number;
}>();

const emit = defineEmits<{
  (e: 'selectKeyframe', id: string, addToSelection: boolean): void;
}>();

const store = useCompositorStore();

const containerRef = ref<HTMLDivElement | null>(null);
const canvasAreaRef = ref<HTMLDivElement | null>(null);
const canvasRef = ref<HTMLCanvasElement | null>(null);

// View state
const viewMin = ref(0);
const viewMax = ref(500);
const pan = ref({ x: 0, y: 0 });

// Selection
const selectedKeyframeIds = computed(() => store.selectedKeyframeIds);

// Collect all animated properties as curves
const allCurves = computed<CurveData[]>(() => {
  const curves: CurveData[] = [];

  store.layers.forEach(layer => {
    // Transform position (split into X, Y, Z)
    if (layer.transform.position.animated && layer.transform.position.keyframes.length > 0) {
      const pos = layer.transform.position;
      curves.push({
        id: `${layer.id}-position-x`,
        layerId: layer.id,
        propertyPath: 'transform.position',
        name: 'Position X',
        color: CURVE_COLORS['Position X'],
        keyframes: pos.keyframes.map(kf => ({
          ...kf,
          value: typeof kf.value === 'object' ? kf.value.x : kf.value
        })),
        visible: true
      });
      curves.push({
        id: `${layer.id}-position-y`,
        layerId: layer.id,
        propertyPath: 'transform.position',
        name: 'Position Y',
        color: CURVE_COLORS['Position Y'],
        keyframes: pos.keyframes.map(kf => ({
          ...kf,
          value: typeof kf.value === 'object' ? kf.value.y : kf.value
        })),
        visible: true
      });
    }

    // Scale
    if (layer.transform.scale.animated && layer.transform.scale.keyframes.length > 0) {
      const scale = layer.transform.scale;
      curves.push({
        id: `${layer.id}-scale-x`,
        layerId: layer.id,
        propertyPath: 'transform.scale',
        name: 'Scale X',
        color: CURVE_COLORS['Scale X'],
        keyframes: scale.keyframes.map(kf => ({
          ...kf,
          value: typeof kf.value === 'object' ? kf.value.x : kf.value
        })),
        visible: true
      });
      curves.push({
        id: `${layer.id}-scale-y`,
        layerId: layer.id,
        propertyPath: 'transform.scale',
        name: 'Scale Y',
        color: CURVE_COLORS['Scale Y'],
        keyframes: scale.keyframes.map(kf => ({
          ...kf,
          value: typeof kf.value === 'object' ? kf.value.y : kf.value
        })),
        visible: true
      });
    }

    // Rotation
    if (layer.transform.rotation.animated && layer.transform.rotation.keyframes.length > 0) {
      curves.push({
        id: `${layer.id}-rotation`,
        layerId: layer.id,
        propertyPath: 'transform.rotation',
        name: 'Rotation',
        color: CURVE_COLORS['Rotation'],
        keyframes: layer.transform.rotation.keyframes,
        visible: true
      });
    }

    // Opacity
    if (layer.opacity.animated && layer.opacity.keyframes.length > 0) {
      curves.push({
        id: `${layer.id}-opacity`,
        layerId: layer.id,
        propertyPath: 'opacity',
        name: 'Opacity',
        color: CURVE_COLORS['Opacity'],
        keyframes: layer.opacity.keyframes,
        visible: true
      });
    }
  });

  return curves;
});

const visibleCurves = computed(() => allCurves.value.filter(c => c.visible));

// Calculate value range from all visible curves
const valueRange = computed(() => {
  const values: number[] = [];

  visibleCurves.value.forEach(curve => {
    curve.keyframes.forEach(kf => {
      const v = typeof kf.value === 'number' ? kf.value : 0;
      values.push(v);
    });
  });

  if (values.length === 0) {
    return { min: 0, max: 100 };
  }

  const min = Math.min(...values);
  const max = Math.max(...values);
  const padding = Math.max((max - min) * 0.15, 20);

  return {
    min: min - padding,
    max: max + padding
  };
});

// Y-axis labels
const yAxisLabels = computed(() => {
  const range = valueRange.value;
  const labels: { value: number; percent: number; text: string }[] = [];
  const steps = 5;
  const stepSize = (range.max - range.min) / steps;

  for (let i = 0; i <= steps; i++) {
    const value = range.max - (i * stepSize);
    labels.push({
      value,
      percent: (i / steps) * 100,
      text: value.toFixed(0)
    });
  }

  return labels;
});

// Playhead position
const playheadPercent = computed(() => {
  return (props.currentFrame / props.frameCount) * 100;
});

// Coordinate transforms
function frameToX(frame: number): number {
  return (frame / props.frameCount) * 100;
}

function valueToY(value: number): number {
  const range = valueRange.value;
  return ((range.max - value) / (range.max - range.min)) * 100;
}

function xToFrame(xPercent: number): number {
  return (xPercent / 100) * props.frameCount;
}

function yToValue(yPercent: number): number {
  const range = valueRange.value;
  return range.max - (yPercent / 100) * (range.max - range.min);
}

// Get keyframe position style
function getKeyframeStyle(curve: CurveData, kf: Keyframe<any>) {
  const value = typeof kf.value === 'number' ? kf.value : 0;
  return {
    left: `${frameToX(kf.frame)}%`,
    top: `${valueToY(value)}%`
  };
}

// Get handle position style
function getHandleStyle(curve: CurveData, kf: Keyframe<any>, type: 'in' | 'out') {
  const handle = type === 'in' ? kf.inHandle : kf.outHandle;
  if (!handle?.enabled) return { display: 'none' };

  const kfValue = typeof kf.value === 'number' ? kf.value : 0;
  const handleFrame = kf.frame + handle.frame;
  const handleValue = kfValue + handle.value;

  return {
    left: `${frameToX(handleFrame)}%`,
    top: `${valueToY(handleValue)}%`,
    background: curve.color
  };
}

// Get handle line coordinates
function getHandleLineCoords(curve: CurveData, kf: Keyframe<any>, type: 'in' | 'out') {
  const handle = type === 'in' ? kf.inHandle : kf.outHandle;
  if (!handle?.enabled) return { x1: '0', y1: '0', x2: '0', y2: '0' };

  const kfValue = typeof kf.value === 'number' ? kf.value : 0;
  const handleFrame = kf.frame + handle.frame;
  const handleValue = kfValue + handle.value;

  return {
    x1: `${frameToX(kf.frame)}%`,
    y1: `${valueToY(kfValue)}%`,
    x2: `${frameToX(handleFrame)}%`,
    y2: `${valueToY(handleValue)}%`
  };
}

function formatValue(value: any): string {
  if (typeof value === 'number') return value.toFixed(1);
  if (typeof value === 'object') return JSON.stringify(value);
  return String(value);
}

// Draw the graph
function draw() {
  const canvas = canvasRef.value;
  const container = canvasAreaRef.value;
  if (!canvas || !container) return;

  const ctx = canvas.getContext('2d');
  if (!ctx) return;

  // Set canvas size
  const rect = container.getBoundingClientRect();
  canvas.width = rect.width;
  canvas.height = rect.height;

  const w = canvas.width;
  const h = canvas.height;
  const range = valueRange.value;

  // Clear
  ctx.clearRect(0, 0, w, h);

  // Draw grid
  ctx.strokeStyle = '#333';
  ctx.lineWidth = 1;

  // Vertical grid lines (time)
  const frameStep = Math.max(1, Math.floor(props.frameCount / 20));
  for (let f = 0; f <= props.frameCount; f += frameStep) {
    const x = (f / props.frameCount) * w;
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, h);
    ctx.stroke();
  }

  // Horizontal grid lines (value)
  const valueStep = (range.max - range.min) / 5;
  for (let v = range.min; v <= range.max; v += valueStep) {
    const y = ((range.max - v) / (range.max - range.min)) * h;
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(w, y);
    ctx.stroke();
  }

  // Zero line (if in range)
  if (range.min < 0 && range.max > 0) {
    ctx.strokeStyle = '#555';
    ctx.lineWidth = 1;
    const zeroY = ((range.max - 0) / (range.max - range.min)) * h;
    ctx.beginPath();
    ctx.moveTo(0, zeroY);
    ctx.lineTo(w, zeroY);
    ctx.stroke();
  }

  // Draw curves
  visibleCurves.value.forEach(curve => {
    if (curve.keyframes.length < 2) return;

    const sorted = [...curve.keyframes].sort((a, b) => a.frame - b.frame);

    // Two-pass: black outline then colored
    for (let pass = 0; pass < 2; pass++) {
      ctx.strokeStyle = pass === 0 ? '#000' : curve.color;
      ctx.lineWidth = pass === 0 ? 4 : 2;

      ctx.beginPath();

      for (let i = 0; i < sorted.length - 1; i++) {
        const kf1 = sorted[i];
        const kf2 = sorted[i + 1];

        const v1 = typeof kf1.value === 'number' ? kf1.value : 0;
        const v2 = typeof kf2.value === 'number' ? kf2.value : 0;

        const x1 = (kf1.frame / props.frameCount) * w;
        const y1 = ((range.max - v1) / (range.max - range.min)) * h;
        const x2 = (kf2.frame / props.frameCount) * w;
        const y2 = ((range.max - v2) / (range.max - range.min)) * h;

        if (i === 0) {
          ctx.moveTo(x1, y1);
        }

        const interp = kf1.interpolation || 'linear';

        if (interp === 'hold') {
          ctx.lineTo(x2, y1);
          ctx.lineTo(x2, y2);
        } else if (interp === 'bezier' && kf1.outHandle?.enabled && kf2.inHandle?.enabled) {
          const cp1x = ((kf1.frame + kf1.outHandle.frame) / props.frameCount) * w;
          const cp1y = ((range.max - (v1 + kf1.outHandle.value)) / (range.max - range.min)) * h;
          const cp2x = ((kf2.frame + kf2.inHandle.frame) / props.frameCount) * w;
          const cp2y = ((range.max - (v2 + kf2.inHandle.value)) / (range.max - range.min)) * h;
          ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x2, y2);
        } else {
          ctx.lineTo(x2, y2);
        }
      }

      ctx.stroke();
    }
  });
}

// Mouse interactions
let isDragging = false;
let dragType: 'keyframe' | 'handle' | 'pan' | null = null;
let dragCurve: CurveData | null = null;
let dragKeyframe: Keyframe<any> | null = null;
let dragHandleType: 'in' | 'out' | null = null;
let dragStartPos = { x: 0, y: 0 };

function handleMouseDown(event: MouseEvent) {
  if (event.button === 1 || (event.button === 0 && event.shiftKey)) {
    // Middle mouse or shift+left = pan
    isDragging = true;
    dragType = 'pan';
    dragStartPos = { x: event.clientX, y: event.clientY };
    document.addEventListener('mousemove', handleMouseMove);
    document.addEventListener('mouseup', handleMouseUp);
    event.preventDefault();
  }
}

function startKeyframeDrag(curve: CurveData, kf: Keyframe<any>, event: MouseEvent) {
  isDragging = true;
  dragType = 'keyframe';
  dragCurve = curve;
  dragKeyframe = kf;
  document.addEventListener('mousemove', handleMouseMove);
  document.addEventListener('mouseup', handleMouseUp);
  event.preventDefault();
}

function startHandleDrag(curve: CurveData, kf: Keyframe<any>, handleType: 'in' | 'out', event: MouseEvent) {
  isDragging = true;
  dragType = 'handle';
  dragCurve = curve;
  dragKeyframe = kf;
  dragHandleType = handleType;
  document.addEventListener('mousemove', handleMouseMove);
  document.addEventListener('mouseup', handleMouseUp);
  event.preventDefault();
}

function handleMouseMove(event: MouseEvent) {
  if (!isDragging || !canvasAreaRef.value) return;

  const rect = canvasAreaRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;
  const xPercent = (x / rect.width) * 100;
  const yPercent = (y / rect.height) * 100;

  if (dragType === 'keyframe' && dragCurve && dragKeyframe) {
    const newFrame = Math.round(xToFrame(xPercent));
    const newValue = yToValue(yPercent);
    const clampedFrame = Math.max(0, Math.min(props.frameCount - 1, newFrame));

    store.moveKeyframe(dragCurve.layerId, dragCurve.propertyPath, dragKeyframe.id, clampedFrame);
    // Note: Value update would need to handle vector properties properly
  } else if (dragType === 'handle' && dragCurve && dragKeyframe && dragHandleType) {
    const mouseFrame = xToFrame(xPercent);
    const mouseValue = yToValue(yPercent);
    const kfValue = typeof dragKeyframe.value === 'number' ? dragKeyframe.value : 0;

    const frameOffset = mouseFrame - dragKeyframe.frame;
    const valueOffset = mouseValue - kfValue;

    store.setKeyframeHandle(
      dragCurve.layerId,
      dragCurve.propertyPath,
      dragKeyframe.id,
      dragHandleType,
      { frame: frameOffset, value: valueOffset, enabled: true }
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
  document.removeEventListener('mousemove', handleMouseMove);
  document.removeEventListener('mouseup', handleMouseUp);
}

function handleWheel(event: WheelEvent) {
  // Could implement zoom here
  event.preventDefault();
}

function selectKeyframe(id: string, event: MouseEvent) {
  emit('selectKeyframe', id, event.shiftKey);
}

// Watch and redraw
watch(
  () => [visibleCurves.value, props.frameCount, props.currentFrame],
  () => nextTick(draw),
  { deep: true }
);

onMounted(() => {
  nextTick(draw);
  window.addEventListener('resize', draw);
});

onUnmounted(() => {
  window.removeEventListener('resize', draw);
});
</script>

<style scoped>
.graph-editor-canvas {
  display: flex;
  width: 100%;
  height: 100%;
  min-height: 300px;
  background: #1a1a1a;
}

.y-axis {
  width: 50px;
  position: relative;
  border-right: 1px solid #333;
  background: #1e1e1e;
}

.y-label {
  position: absolute;
  right: 8px;
  transform: translateY(-50%);
  font-size: 10px;
  color: #666;
  font-family: monospace;
}

.canvas-area {
  flex: 1;
  position: relative;
  overflow: hidden;
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
