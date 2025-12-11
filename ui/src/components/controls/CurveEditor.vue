<template>
  <div class="curve-editor">
    <!-- Preset Buttons -->
    <div class="preset-buttons">
      <button
        v-for="preset in presets"
        :key="preset.name"
        :class="{ active: isActivePreset(preset) }"
        @click="applyPreset(preset)"
        :title="preset.name"
      >
        {{ preset.label }}
      </button>
    </div>

    <!-- SVG Curve Display -->
    <svg
      :viewBox="`0 0 ${size} ${size}`"
      class="curve-svg"
      @mousedown="onSvgMouseDown"
      ref="svgRef"
    >
      <!-- Grid -->
      <line
        :x1="0" :y1="size / 2"
        :x2="size" :y2="size / 2"
        class="grid-line"
      />
      <line
        :x1="size / 2" :y1="0"
        :x2="size / 2" :y2="size"
        class="grid-line"
      />

      <!-- Linear Reference Line -->
      <line
        :x1="padding" :y1="size - padding"
        :x2="size - padding" :y2="padding"
        class="reference-line"
      />

      <!-- Bezier Curve -->
      <path
        :d="curvePath"
        class="curve-path"
        fill="none"
      />

      <!-- Control Point 1 Handle Line -->
      <line
        :x1="padding"
        :y1="size - padding"
        :x2="cp1Screen.x"
        :y2="cp1Screen.y"
        class="handle-line"
      />

      <!-- Control Point 2 Handle Line -->
      <line
        :x1="size - padding"
        :y1="padding"
        :x2="cp2Screen.x"
        :y2="cp2Screen.y"
        class="handle-line"
      />

      <!-- Start Point -->
      <circle
        :cx="padding"
        :cy="size - padding"
        r="4"
        class="endpoint"
      />

      <!-- End Point -->
      <circle
        :cx="size - padding"
        :cy="padding"
        r="4"
        class="endpoint"
      />

      <!-- Control Point 1 -->
      <circle
        :cx="cp1Screen.x"
        :cy="cp1Screen.y"
        r="5"
        class="control-point"
        :class="{ dragging: draggingPoint === 1 }"
        @mousedown.stop="startDrag(1, $event)"
      />

      <!-- Control Point 2 -->
      <circle
        :cx="cp2Screen.x"
        :cy="cp2Screen.y"
        r="5"
        class="control-point"
        :class="{ dragging: draggingPoint === 2 }"
        @mousedown.stop="startDrag(2, $event)"
      />
    </svg>

    <!-- Coordinate Display -->
    <div class="coords-display">
      <span>CP1: {{ cp1x.toFixed(2) }}, {{ cp1y.toFixed(2) }}</span>
      <span>CP2: {{ cp2x.toFixed(2) }}, {{ cp2y.toFixed(2) }}</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from 'vue';

interface Props {
  cp1x: number;
  cp1y: number;
  cp2x: number;
  cp2y: number;
  size?: number;
}

const props = withDefaults(defineProps<Props>(), {
  size: 100
});

const emit = defineEmits<{
  (e: 'update:cp1x', value: number): void;
  (e: 'update:cp1y', value: number): void;
  (e: 'update:cp2x', value: number): void;
  (e: 'update:cp2y', value: number): void;
}>();

const svgRef = ref<SVGSVGElement | null>(null);
const draggingPoint = ref<1 | 2 | null>(null);

const padding = 10;
const innerSize = computed(() => props.size - padding * 2);

interface Preset {
  name: string;
  label: string;
  cp1x: number;
  cp1y: number;
  cp2x: number;
  cp2y: number;
}

const presets: Preset[] = [
  { name: 'Linear', label: 'Lin', cp1x: 0, cp1y: 0, cp2x: 1, cp2y: 1 },
  { name: 'Ease In', label: 'In', cp1x: 0.42, cp1y: 0, cp2x: 1, cp2y: 1 },
  { name: 'Ease Out', label: 'Out', cp1x: 0, cp1y: 0, cp2x: 0.58, cp2y: 1 },
  { name: 'Ease In-Out', label: 'IO', cp1x: 0.42, cp1y: 0, cp2x: 0.58, cp2y: 1 },
];

// Convert normalized coordinates (0-1) to screen coordinates
function toScreen(x: number, y: number): { x: number; y: number } {
  return {
    x: padding + x * innerSize.value,
    y: props.size - padding - y * innerSize.value
  };
}

// Convert screen coordinates to normalized coordinates
function toNormalized(screenX: number, screenY: number): { x: number; y: number } {
  return {
    x: Math.max(0, Math.min(1, (screenX - padding) / innerSize.value)),
    y: Math.max(0, Math.min(1, (props.size - padding - screenY) / innerSize.value))
  };
}

const cp1Screen = computed(() => toScreen(props.cp1x, props.cp1y));
const cp2Screen = computed(() => toScreen(props.cp2x, props.cp2y));

const curvePath = computed(() => {
  const start = toScreen(0, 0);
  const end = toScreen(1, 1);

  return `M ${start.x} ${start.y} C ${cp1Screen.value.x} ${cp1Screen.value.y}, ${cp2Screen.value.x} ${cp2Screen.value.y}, ${end.x} ${end.y}`;
});

function isActivePreset(preset: Preset): boolean {
  const tolerance = 0.01;
  return (
    Math.abs(props.cp1x - preset.cp1x) < tolerance &&
    Math.abs(props.cp1y - preset.cp1y) < tolerance &&
    Math.abs(props.cp2x - preset.cp2x) < tolerance &&
    Math.abs(props.cp2y - preset.cp2y) < tolerance
  );
}

function applyPreset(preset: Preset): void {
  emit('update:cp1x', preset.cp1x);
  emit('update:cp1y', preset.cp1y);
  emit('update:cp2x', preset.cp2x);
  emit('update:cp2y', preset.cp2y);
}

function startDrag(point: 1 | 2, e: MouseEvent): void {
  draggingPoint.value = point;
  document.addEventListener('mousemove', onDrag);
  document.addEventListener('mouseup', stopDrag);
  e.preventDefault();
}

function onDrag(e: MouseEvent): void {
  if (!draggingPoint.value || !svgRef.value) return;

  const rect = svgRef.value.getBoundingClientRect();
  const scaleX = props.size / rect.width;
  const scaleY = props.size / rect.height;

  const screenX = (e.clientX - rect.left) * scaleX;
  const screenY = (e.clientY - rect.top) * scaleY;

  const normalized = toNormalized(screenX, screenY);

  // Allow y to go beyond 0-1 for overshoot effects
  const clampedY = Math.max(-0.5, Math.min(1.5, normalized.y));

  if (draggingPoint.value === 1) {
    emit('update:cp1x', normalized.x);
    emit('update:cp1y', clampedY);
  } else {
    emit('update:cp2x', normalized.x);
    emit('update:cp2y', clampedY);
  }
}

function stopDrag(): void {
  draggingPoint.value = null;
  document.removeEventListener('mousemove', onDrag);
  document.removeEventListener('mouseup', stopDrag);
}

function onSvgMouseDown(_e: MouseEvent): void {
  // Click on empty area - do nothing for now
}
</script>

<style scoped>
.curve-editor {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.preset-buttons {
  display: flex;
  gap: 4px;
}

.preset-buttons button {
  flex: 1;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #888;
  font-size: 10px;
  cursor: pointer;
  transition: all 0.1s;
}

.preset-buttons button:hover {
  background: #333;
  color: #e0e0e0;
}

.preset-buttons button.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}

.curve-svg {
  width: 100%;
  aspect-ratio: 1;
  background: #1e1e1e;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  cursor: default;
}

.grid-line {
  stroke: #333;
  stroke-width: 1;
  stroke-dasharray: 2 2;
}

.reference-line {
  stroke: #444;
  stroke-width: 1;
  stroke-dasharray: 4 4;
}

.curve-path {
  stroke: #7c9cff;
  stroke-width: 2;
  stroke-linecap: round;
}

.handle-line {
  stroke: #666;
  stroke-width: 1;
}

.endpoint {
  fill: #888;
}

.control-point {
  fill: #7c9cff;
  stroke: #fff;
  stroke-width: 2;
  cursor: grab;
  transition: r 0.1s;
}

.control-point:hover {
  r: 6;
}

.control-point.dragging {
  r: 7;
  cursor: grabbing;
}

.coords-display {
  display: flex;
  justify-content: space-between;
  font-size: 10px;
  color: #666;
  font-family: monospace;
}
</style>
