<template>
  <canvas
    ref="canvasRef"
    class="waveform-canvas"
    :width="canvasWidth"
    :height="canvasHeight"
  />
</template>

<script setup lang="ts">
import { onMounted, ref, watch } from "vue";

interface WaveformResult {
  lumaPoints: Float32Array;
  width: number;
  height: number;
}

const props = defineProps<{
  data: WaveformResult | null;
  brightness: number;
}>();

const canvasRef = ref<HTMLCanvasElement | null>(null);
const canvasWidth = 256;
const canvasHeight = 150;

//                                                                       // ire
const _IRE_LEVELS = {
  black: 0, // 0 IRE (16 in 8-bit video)
  white: 100, // 100 IRE (235 in 8-bit video)
  super: 109, // Super white
};

onMounted(() => {
  drawWaveform();
});

watch([() => props.data, () => props.brightness], () => {
  drawWaveform();
});

function drawWaveform() {
  const canvas = canvasRef.value;
  if (!canvas) return;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  // Clear
  ctx.fillStyle = "#000";
  ctx.fillRect(0, 0, canvasWidth, canvasHeight);

  // Draw grid and IRE levels
  drawGrid(ctx);

  if (!props.data) return;

  const { lumaPoints } = props.data;

  // Draw waveform points
  const alpha = Math.min(1, 0.3 * props.brightness);
  ctx.fillStyle = `rgba(0, 255, 0, ${alpha})`;

  for (let i = 0; i < lumaPoints.length; i += 2) {
    const x = lumaPoints[i] * canvasWidth;
    const y = lumaPoints[i + 1] * canvasHeight;

    ctx.fillRect(x, y, 1, 1);
  }
}

function drawGrid(ctx: CanvasRenderingContext2D) {
  ctx.strokeStyle = "rgba(60, 60, 60, 0.5)";
  ctx.lineWidth = 1;

  // Horizontal lines at IRE levels
  const irePositions = [0, 25, 50, 75, 100];

  irePositions.forEach((ire) => {
    const y = canvasHeight - (ire / 100) * canvasHeight;
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(canvasWidth, y);
    ctx.stroke();
  });

  //                                                                       // ire
  ctx.fillStyle = "rgba(100, 100, 100, 0.8)";
  ctx.font = "9px monospace";
  ctx.textAlign = "left";

  irePositions.forEach((ire) => {
    const y = canvasHeight - (ire / 100) * canvasHeight;
    ctx.fillText(`${ire}`, 2, y - 2);
  });

  // Legal range indicators
  ctx.strokeStyle = "rgba(255, 200, 0, 0.3)";
  ctx.lineWidth = 1;

  // Black level (16/255 ≈ 6.3%)
  const blackY = canvasHeight - (16 / 255) * canvasHeight;
  ctx.beginPath();
  ctx.moveTo(0, blackY);
  ctx.lineTo(canvasWidth, blackY);
  ctx.stroke();

  // White level (235/255 ≈ 92%)
  const whiteY = canvasHeight - (235 / 255) * canvasHeight;
  ctx.beginPath();
  ctx.moveTo(0, whiteY);
  ctx.lineTo(canvasWidth, whiteY);
  ctx.stroke();
}
</script>

<style scoped>
.waveform-canvas {
  width: 100%;
  height: 100%;
  image-rendering: pixelated;
}
</style>
