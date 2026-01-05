<template>
  <canvas
    ref="canvasRef"
    class="histogram-canvas"
    :width="canvasWidth"
    :height="canvasHeight"
  />
</template>

<script setup lang="ts">
import { onMounted, ref, watch } from "vue";

interface HistogramResult {
  red: number[];
  green: number[];
  blue: number[];
  luminance: number[];
  maxCount: number;
}

const props = defineProps<{
  data: HistogramResult | null;
  brightness: number;
}>();

const canvasRef = ref<HTMLCanvasElement | null>(null);
const canvasWidth = 256;
const canvasHeight = 150;

// Colors
const COLORS = {
  red: "rgba(255, 80, 80, 0.7)",
  green: "rgba(80, 255, 80, 0.7)",
  blue: "rgba(80, 80, 255, 0.7)",
  luminance: "rgba(200, 200, 200, 0.5)",
  grid: "rgba(60, 60, 60, 0.5)",
};

onMounted(() => {
  drawHistogram();
});

watch([() => props.data, () => props.brightness], () => {
  drawHistogram();
});

function drawHistogram() {
  const canvas = canvasRef.value;
  if (!canvas) return;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  // Clear
  ctx.fillStyle = "#000";
  ctx.fillRect(0, 0, canvasWidth, canvasHeight);

  // Draw grid lines
  ctx.strokeStyle = COLORS.grid;
  ctx.lineWidth = 1;

  // Vertical grid (at 64, 128, 192)
  for (let i = 1; i < 4; i++) {
    const x = i * 64;
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, canvasHeight);
    ctx.stroke();
  }

  // Horizontal grid
  for (let i = 1; i < 4; i++) {
    const y = (i * canvasHeight) / 4;
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(canvasWidth, y);
    ctx.stroke();
  }

  if (!props.data) return;

  const { red, green, blue, luminance, maxCount } = props.data;
  const adjustedMax = maxCount / props.brightness;

  // Draw luminance first (in back)
  drawChannel(ctx, luminance, adjustedMax, COLORS.luminance);

  // Draw RGB channels with additive blending
  ctx.globalCompositeOperation = "screen";

  drawChannel(ctx, red, adjustedMax, COLORS.red);
  drawChannel(ctx, green, adjustedMax, COLORS.green);
  drawChannel(ctx, blue, adjustedMax, COLORS.blue);

  ctx.globalCompositeOperation = "source-over";
}

function drawChannel(
  ctx: CanvasRenderingContext2D,
  data: number[],
  maxCount: number,
  color: string,
) {
  ctx.fillStyle = color;
  ctx.beginPath();
  ctx.moveTo(0, canvasHeight);

  for (let i = 0; i < 256; i++) {
    const height = Math.min(canvasHeight, (data[i] / maxCount) * canvasHeight);
    ctx.lineTo(i, canvasHeight - height);
  }

  ctx.lineTo(255, canvasHeight);
  ctx.closePath();
  ctx.fill();
}
</script>

<style scoped>
.histogram-canvas {
  width: 100%;
  height: 100%;
  image-rendering: pixelated;
}
</style>
