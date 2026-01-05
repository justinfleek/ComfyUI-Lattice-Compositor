<template>
  <canvas
    ref="canvasRef"
    class="vectorscope-canvas"
    :width="canvasSize"
    :height="canvasSize"
  />
</template>

<script setup lang="ts">
import { onMounted, ref, watch } from "vue";

interface VectorscopeResult {
  data: Uint32Array;
  maxCount: number;
  targets: {
    r: [number, number];
    y: [number, number];
    g: [number, number];
    c: [number, number];
    b: [number, number];
    m: [number, number];
    skinLine: [[number, number], [number, number]];
  };
}

const props = withDefaults(
  defineProps<{
    data: VectorscopeResult | null;
    brightness: number;
    showTargets: boolean;
    showSkinLine: boolean;
  }>(),
  {
    showTargets: true,
    showSkinLine: true,
  },
);

const canvasRef = ref<HTMLCanvasElement | null>(null);
const canvasSize = 256;

// Target colors
const TARGET_COLORS: Record<string, string> = {
  r: "#FF4040",
  y: "#FFFF40",
  g: "#40FF40",
  c: "#40FFFF",
  b: "#4040FF",
  m: "#FF40FF",
};

onMounted(() => {
  drawVectorscope();
});

watch([() => props.data, () => props.brightness], () => {
  drawVectorscope();
});

function drawVectorscope() {
  const canvas = canvasRef.value;
  if (!canvas) return;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  const center = canvasSize / 2;

  // Clear
  ctx.fillStyle = "#000";
  ctx.fillRect(0, 0, canvasSize, canvasSize);

  // Draw graticule
  drawGraticule(ctx, center);

  if (!props.data) return;

  const { data, maxCount, targets } = props.data;

  // Draw vectorscope data
  const imageData = ctx.createImageData(canvasSize, canvasSize);
  const adjustedMax = maxCount / props.brightness;

  for (let i = 0; i < data.length; i++) {
    if (data[i] > 0) {
      const intensity = Math.min(255, (data[i] / adjustedMax) * 255 * 2);
      const pixelIndex = i * 4;

      // Green tint for standard vectorscope look
      imageData.data[pixelIndex] = intensity * 0.3; // R
      imageData.data[pixelIndex + 1] = intensity; // G
      imageData.data[pixelIndex + 2] = intensity * 0.3; // B
      imageData.data[pixelIndex + 3] = 255; // A
    }
  }

  ctx.putImageData(imageData, 0, 0);

  // Draw targets on top
  if (props.showTargets && targets) {
    drawTargets(ctx, targets);
  }

  // Draw skin tone line
  if (props.showSkinLine && targets) {
    drawSkinLine(ctx, targets.skinLine);
  }
}

function drawGraticule(ctx: CanvasRenderingContext2D, center: number) {
  ctx.strokeStyle = "rgba(60, 60, 60, 0.5)";
  ctx.lineWidth = 1;

  // Outer circle
  ctx.beginPath();
  ctx.arc(center, center, center - 4, 0, Math.PI * 2);
  ctx.stroke();

  // 75% circle
  ctx.beginPath();
  ctx.arc(center, center, (center - 4) * 0.75, 0, Math.PI * 2);
  ctx.stroke();

  // 50% circle
  ctx.beginPath();
  ctx.arc(center, center, (center - 4) * 0.5, 0, Math.PI * 2);
  ctx.stroke();

  // 25% circle
  ctx.beginPath();
  ctx.arc(center, center, (center - 4) * 0.25, 0, Math.PI * 2);
  ctx.stroke();

  // Cross hairs
  ctx.beginPath();
  ctx.moveTo(center, 4);
  ctx.lineTo(center, canvasSize - 4);
  ctx.moveTo(4, center);
  ctx.lineTo(canvasSize - 4, center);
  ctx.stroke();

  // Diagonal lines (45 degree increments)
  const diagonalLength = center - 4;
  const angles = [45, 135, 225, 315];

  angles.forEach((angle) => {
    const rad = (angle * Math.PI) / 180;
    ctx.beginPath();
    ctx.moveTo(center, center);
    ctx.lineTo(
      center + Math.cos(rad) * diagonalLength,
      center + Math.sin(rad) * diagonalLength,
    );
    ctx.stroke();
  });
}

function drawTargets(
  ctx: CanvasRenderingContext2D,
  targets: VectorscopeResult["targets"],
) {
  const targetSize = 6;

  Object.entries(targets).forEach(([key, pos]) => {
    if (key === "skinLine") return;

    const color = TARGET_COLORS[key];
    if (!color) return;

    const [x, y] = pos as [number, number];

    // Draw target box
    ctx.strokeStyle = color;
    ctx.lineWidth = 1;
    ctx.strokeRect(
      x - targetSize / 2,
      y - targetSize / 2,
      targetSize,
      targetSize,
    );

    // Draw label
    ctx.fillStyle = color;
    ctx.font = "10px monospace";
    ctx.textAlign = "center";
    ctx.fillText(key.toUpperCase(), x, y - targetSize);
  });
}

function drawSkinLine(
  ctx: CanvasRenderingContext2D,
  skinLine: [[number, number], [number, number]],
) {
  const [[x1, y1], [x2, y2]] = skinLine;

  ctx.strokeStyle = "rgba(255, 180, 100, 0.6)";
  ctx.lineWidth = 2;
  ctx.setLineDash([4, 4]);

  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.lineTo(x2, y2);
  ctx.stroke();

  ctx.setLineDash([]);

  // Label
  ctx.fillStyle = "rgba(255, 180, 100, 0.8)";
  ctx.font = "9px monospace";
  ctx.textAlign = "left";
  ctx.fillText("I", x2 + 4, y2);
}
</script>

<style scoped>
.vectorscope-canvas {
  width: 100%;
  height: 100%;
  max-width: 256px;
  max-height: 256px;
  margin: auto;
  display: block;
  image-rendering: pixelated;
}
</style>
