<template>
  <canvas
    ref="canvasRef"
    class="parade-canvas"
    :width="canvasWidth"
    :height="canvasHeight"
  />
</template>

<script setup lang="ts">
import { ref, watch, onMounted } from 'vue';

interface WaveformResult {
  lumaPoints: Float32Array;
  width: number;
  height: number;
}

interface ParadeResult {
  red: WaveformResult;
  green: WaveformResult;
  blue: WaveformResult;
}

const props = defineProps<{
  data: ParadeResult | null;
  brightness: number;
}>();

const canvasRef = ref<HTMLCanvasElement | null>(null);
const canvasWidth = 384;  // 128 * 3 channels
const canvasHeight = 150;

const CHANNEL_WIDTH = canvasWidth / 3;

// Channel colors
const COLORS = {
  red: [255, 100, 100],
  green: [100, 255, 100],
  blue: [100, 100, 255]
};

onMounted(() => {
  drawParade();
});

watch([() => props.data, () => props.brightness], () => {
  drawParade();
});

function drawParade() {
  const canvas = canvasRef.value;
  if (!canvas) return;

  const ctx = canvas.getContext('2d');
  if (!ctx) return;

  // Clear
  ctx.fillStyle = '#000';
  ctx.fillRect(0, 0, canvasWidth, canvasHeight);

  // Draw grid for each channel
  drawGrid(ctx, 0, 'R');
  drawGrid(ctx, CHANNEL_WIDTH, 'G');
  drawGrid(ctx, CHANNEL_WIDTH * 2, 'B');

  // Draw separators
  ctx.strokeStyle = 'rgba(80, 80, 80, 0.8)';
  ctx.lineWidth = 1;

  ctx.beginPath();
  ctx.moveTo(CHANNEL_WIDTH, 0);
  ctx.lineTo(CHANNEL_WIDTH, canvasHeight);
  ctx.moveTo(CHANNEL_WIDTH * 2, 0);
  ctx.lineTo(CHANNEL_WIDTH * 2, canvasHeight);
  ctx.stroke();

  if (!props.data) return;

  const { red, green, blue } = props.data;

  // Draw each channel
  drawChannel(ctx, red, 0, COLORS.red);
  drawChannel(ctx, green, CHANNEL_WIDTH, COLORS.green);
  drawChannel(ctx, blue, CHANNEL_WIDTH * 2, COLORS.blue);
}

function drawGrid(ctx: CanvasRenderingContext2D, offsetX: number, label: string) {
  ctx.strokeStyle = 'rgba(60, 60, 60, 0.5)';
  ctx.lineWidth = 1;

  // Horizontal lines
  for (let i = 1; i < 4; i++) {
    const y = (i * canvasHeight / 4);
    ctx.beginPath();
    ctx.moveTo(offsetX, y);
    ctx.lineTo(offsetX + CHANNEL_WIDTH, y);
    ctx.stroke();
  }

  // Label
  ctx.fillStyle = 'rgba(100, 100, 100, 0.8)';
  ctx.font = '10px monospace';
  ctx.textAlign = 'center';
  ctx.fillText(label, offsetX + CHANNEL_WIDTH / 2, canvasHeight - 4);
}

function drawChannel(
  ctx: CanvasRenderingContext2D,
  data: WaveformResult,
  offsetX: number,
  color: number[]
) {
  const { lumaPoints } = data;
  const alpha = Math.min(1, 0.4 * props.brightness);

  ctx.fillStyle = `rgba(${color[0]}, ${color[1]}, ${color[2]}, ${alpha})`;

  for (let i = 0; i < lumaPoints.length; i += 2) {
    const x = offsetX + lumaPoints[i] * CHANNEL_WIDTH;
    const y = lumaPoints[i + 1] * canvasHeight;

    ctx.fillRect(x, y, 1, 1);
  }
}
</script>

<style scoped>
.parade-canvas {
  width: 100%;
  height: 100%;
  image-rendering: pixelated;
}
</style>
