<template>
  <div class="eyedropper-tool">
    <button
      class="eyedropper-button"
      :class="{ active: isActive }"
      @click="toggleEyedropper"
      :title="isActive ? 'Click on canvas to sample' : 'Sample color for white balance'"
    >
      <span class="icon">{{ isActive ? '✱' : '⊙' }}</span>
      <span class="label">{{ isActive ? 'Sampling...' : 'White Balance' }}</span>
    </button>

    <div v-if="sampledColor" class="sampled-preview">
      <div
        class="color-swatch"
        :style="{ backgroundColor: sampledColorHex }"
      />
      <div class="color-info">
        <span>R: {{ sampledColor.r }}</span>
        <span>G: {{ sampledColor.g }}</span>
        <span>B: {{ sampledColor.b }}</span>
      </div>
      <div class="correction-values">
        <span>Temp: {{ correction.temperature.toFixed(1) }}</span>
        <span>Tint: {{ correction.tint.toFixed(1) }}</span>
      </div>
      <button class="apply-button" @click="applyCorrection">Apply</button>
      <button class="clear-button" @click="clearSample">Clear</button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref } from "vue";
import { calculateWhiteBalanceCorrection } from "@/services/colorAnalysis/histogramService";

interface SampledColor {
  r: number;
  g: number;
  b: number;
}

const emit =
  defineEmits<
    (e: "apply", correction: { temperature: number; tint: number }) => void
  >();

const isActive = ref(false);
const sampledColor = ref<SampledColor | null>(null);

const sampledColorHex = computed(() => {
  if (!sampledColor.value) return "#000";
  const { r, g, b } = sampledColor.value;
  return `rgb(${r}, ${g}, ${b})`;
});

const correction = computed(() => {
  if (!sampledColor.value) return { temperature: 0, tint: 0 };
  return calculateWhiteBalanceCorrection(
    sampledColor.value.r,
    sampledColor.value.g,
    sampledColor.value.b,
  );
});

let canvasClickHandler: ((e: MouseEvent) => void) | null = null;

onMounted(() => {
  // Set up canvas click handler
  canvasClickHandler = (e: MouseEvent) => {
    if (!isActive.value) return;

    const canvas = e.target as HTMLCanvasElement;
    if (!canvas || !canvas.tagName || canvas.tagName !== "CANVAS") return;

    e.preventDefault();
    e.stopPropagation();

    // Get canvas coordinates
    const rect = canvas.getBoundingClientRect();
    const x = Math.round((e.clientX - rect.left) * (canvas.width / rect.width));
    const y = Math.round(
      (e.clientY - rect.top) * (canvas.height / rect.height),
    );

    // Sample pixel
    const color = samplePixel(canvas, x, y);
    if (color) {
      sampledColor.value = color;
      isActive.value = false;
      document.body.style.cursor = "";
    }
  };

  document.addEventListener("click", canvasClickHandler, true);
});

onUnmounted(() => {
  if (canvasClickHandler) {
    document.removeEventListener("click", canvasClickHandler, true);
  }
  document.body.style.cursor = "";
});

function toggleEyedropper() {
  isActive.value = !isActive.value;

  if (isActive.value) {
    document.body.style.cursor = "crosshair";
  } else {
    document.body.style.cursor = "";
  }
}

function samplePixel(
  canvas: HTMLCanvasElement,
  x: number,
  y: number,
): SampledColor | null {
  // Try 2D context first
  const ctx2d = canvas.getContext("2d", { willReadFrequently: true });
  if (ctx2d) {
    const pixel = ctx2d.getImageData(x, y, 1, 1).data;
    return { r: pixel[0], g: pixel[1], b: pixel[2] };
  }

  // Try WebGL
  const gl = canvas.getContext("webgl2") || canvas.getContext("webgl");
  if (gl) {
    const pixel = new Uint8Array(4);
    // WebGL Y is inverted
    gl.readPixels(
      x,
      canvas.height - y - 1,
      1,
      1,
      gl.RGBA,
      gl.UNSIGNED_BYTE,
      pixel,
    );
    return { r: pixel[0], g: pixel[1], b: pixel[2] };
  }

  return null;
}

function applyCorrection() {
  if (correction.value) {
    emit("apply", correction.value);
  }
}

function clearSample() {
  sampledColor.value = null;
}
</script>

<style scoped>
.eyedropper-tool {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.eyedropper-button {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 12px;
  background: var(--lattice-surface-2);
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-primary);
  font-size: var(--lattice-font-size-sm);
  cursor: pointer;
  transition: all 0.15s ease;
}

.eyedropper-button:hover {
  border-color: var(--lattice-accent);
}

.eyedropper-button.active {
  background: var(--lattice-accent-muted);
  border-color: var(--lattice-accent);
  color: var(--lattice-accent);
}

.eyedropper-button .icon {
  font-size: 14px;
}

.sampled-preview {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 8px;
  padding: 8px;
  background: var(--lattice-surface-2);
  border-radius: var(--lattice-radius-sm);
}

.color-swatch {
  width: 32px;
  height: 32px;
  border-radius: var(--lattice-radius-sm);
  border: 1px solid var(--lattice-border-default);
}

.color-info {
  display: flex;
  flex-direction: column;
  gap: 2px;
  font-size: var(--lattice-font-size-xs);
  font-family: monospace;
  color: var(--lattice-text-secondary);
}

.correction-values {
  display: flex;
  flex-direction: column;
  gap: 2px;
  font-size: var(--lattice-font-size-xs);
  font-family: monospace;
  color: var(--lattice-accent);
}

.apply-button {
  padding: 4px 12px;
  background: var(--lattice-accent);
  border: none;
  border-radius: var(--lattice-radius-sm);
  color: white;
  font-size: var(--lattice-font-size-sm);
  cursor: pointer;
}

.apply-button:hover {
  background: var(--lattice-accent-hover);
}

.clear-button {
  padding: 4px 8px;
  background: var(--lattice-surface-3);
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-secondary);
  font-size: var(--lattice-font-size-sm);
  cursor: pointer;
}

.clear-button:hover {
  border-color: var(--lattice-text-secondary);
}
</style>
