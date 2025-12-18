<template>
  <div class="audio-mapping-curve" :style="{ height: `${height}px` }">
    <canvas
      ref="canvasRef"
      class="curve-canvas"
      @mousemove="handleMouseMove"
      @mouseleave="handleMouseLeave"
    />
    <div
      class="playhead"
      :style="{ left: `${playheadPosition}%` }"
    />
    <div
      v-if="hoverInfo"
      class="hover-tooltip"
      :style="{ left: `${hoverInfo.x}px` }"
    >
      Frame {{ hoverInfo.frame }}<br />
      Raw: {{ hoverInfo.raw.toFixed(3) }}<br />
      Mapped: {{ hoverInfo.mapped.toFixed(3) }}
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted } from 'vue';
import type { AudioAnalysis } from '@/services/audioFeatures';
import { getFeatureAtFrame } from '@/services/audioFeatures';
import type { AudioMapping } from '@/services/audioReactiveMapping';

interface Props {
  mapping: AudioMapping;
  analysis: AudioAnalysis;
  currentFrame: number;
  totalFrames: number;
  height?: number;
}

const props = withDefaults(defineProps<Props>(), {
  height: 30
});

// Refs
const canvasRef = ref<HTMLCanvasElement | null>(null);
const hoverInfo = ref<{ x: number; frame: number; raw: number; mapped: number } | null>(null);

// Computed
const playheadPosition = computed(() =>
  (props.currentFrame / props.totalFrames) * 100
);

// Methods
function handleMouseMove(event: MouseEvent): void {
  const canvas = canvasRef.value;
  if (!canvas) return;

  const rect = canvas.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const ratio = x / rect.width;
  const frame = Math.round(ratio * props.totalFrames);

  const raw = getFeatureAtFrame(props.analysis, props.mapping.feature, frame);
  const mapped = applyMapping(raw);

  hoverInfo.value = { x, frame, raw, mapped };
}

function handleMouseLeave(): void {
  hoverInfo.value = null;
}

function applyMapping(value: number): number {
  const m = props.mapping;

  // Apply threshold
  if (value < m.threshold) {
    value = 0;
  }

  // Apply inversion
  if (m.invert) {
    value = 1 - value;
  }

  // Apply sensitivity
  value *= m.sensitivity;

  // Apply offset
  value += m.offset;

  // Clamp
  return Math.max(m.min, Math.min(m.max, value));
}

function draw(): void {
  const canvas = canvasRef.value;
  if (!canvas) return;

  // Set canvas size to match container
  const rect = canvas.parentElement?.getBoundingClientRect();
  if (rect) {
    canvas.width = rect.width;
    canvas.height = props.height;
  }

  const ctx = canvas.getContext('2d');
  if (!ctx) return;

  const width = canvas.width;
  const height = canvas.height;

  // Clear
  ctx.fillStyle = '#1a1a1a';
  ctx.fillRect(0, 0, width, height);

  // Draw threshold line
  if (props.mapping.threshold > 0) {
    const thresholdY = height - props.mapping.threshold * height * 0.9 - 2;
    ctx.strokeStyle = 'rgba(255, 193, 7, 0.5)';
    ctx.setLineDash([4, 4]);
    ctx.beginPath();
    ctx.moveTo(0, thresholdY);
    ctx.lineTo(width, thresholdY);
    ctx.stroke();
    ctx.setLineDash([]);
  }

  // Collect points
  const rawPoints: number[] = [];
  const mappedPoints: number[] = [];

  for (let frame = 0; frame < props.totalFrames; frame++) {
    const raw = getFeatureAtFrame(props.analysis, props.mapping.feature, frame);
    const mapped = applyMapping(raw);
    rawPoints.push(raw);
    mappedPoints.push(mapped);
  }

  // Draw raw feature curve (thin line)
  ctx.strokeStyle = 'rgba(74, 144, 217, 0.4)';
  ctx.lineWidth = 1;
  ctx.beginPath();

  for (let i = 0; i < rawPoints.length; i++) {
    const x = (i / rawPoints.length) * width;
    const y = height - rawPoints[i] * height * 0.9 - 2;

    if (i === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }
  ctx.stroke();

  // Draw mapped output curve (filled area)
  ctx.fillStyle = 'rgba(74, 144, 217, 0.3)';
  ctx.beginPath();
  ctx.moveTo(0, height);

  for (let i = 0; i < mappedPoints.length; i++) {
    const x = (i / mappedPoints.length) * width;
    const y = height - mappedPoints[i] * height * 0.9 - 2;
    ctx.lineTo(x, y);
  }

  ctx.lineTo(width, height);
  ctx.closePath();
  ctx.fill();

  // Draw mapped curve outline
  ctx.strokeStyle = '#4a90d9';
  ctx.lineWidth = 1.5;
  ctx.beginPath();

  for (let i = 0; i < mappedPoints.length; i++) {
    const x = (i / mappedPoints.length) * width;
    const y = height - mappedPoints[i] * height * 0.9 - 2;

    if (i === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }
  ctx.stroke();

  // Draw current frame marker
  const currentX = (props.currentFrame / props.totalFrames) * width;
  const currentMapped = mappedPoints[props.currentFrame] ?? 0;
  const currentY = height - currentMapped * height * 0.9 - 2;

  ctx.fillStyle = '#ff6b6b';
  ctx.beginPath();
  ctx.arc(currentX, currentY, 4, 0, Math.PI * 2);
  ctx.fill();
}

// Watch for changes
watch(
  () => [props.mapping, props.analysis, props.currentFrame, props.totalFrames],
  () => {
    draw();
  },
  { deep: true }
);

// Lifecycle
let resizeObserver: ResizeObserver | null = null;

onMounted(() => {
  draw();

  // Handle resize
  resizeObserver = new ResizeObserver(() => {
    draw();
  });

  if (canvasRef.value?.parentElement) {
    resizeObserver.observe(canvasRef.value.parentElement);
  }
});

onUnmounted(() => {
  resizeObserver?.disconnect();
});
</script>

<style scoped>
.audio-mapping-curve {
  position: relative;
  width: 100%;
  background: #1a1a1a;
  border-radius: 4px;
  overflow: hidden;
}

.curve-canvas {
  width: 100%;
  height: 100%;
  cursor: crosshair;
}

.playhead {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  background: #ff6b6b;
  pointer-events: none;
  z-index: 10;
}

.hover-tooltip {
  position: absolute;
  bottom: 100%;
  transform: translateX(-50%);
  padding: 4px 8px;
  background: #333;
  border: 1px solid #444;
  border-radius: 4px;
  font-size: 12px;
  color: #fff;
  white-space: nowrap;
  pointer-events: none;
  z-index: 20;
  margin-bottom: 4px;
}
</style>
