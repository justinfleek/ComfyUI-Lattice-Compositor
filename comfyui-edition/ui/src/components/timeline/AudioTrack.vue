<template>
  <div class="audio-track" :style="{ height: `${height}px` }">
    <!-- Track Header -->
    <div class="track-header">
      <i class="pi pi-volume-up" />
      <span class="track-name">Audio</span>
      <span v-if="analysis" class="bpm-badge">{{ analysis.bpm }} BPM</span>
    </div>

    <!-- Waveform Display -->
    <div class="waveform-container" ref="containerRef">
      <canvas
        ref="canvasRef"
        class="waveform-canvas"
        @click="handleClick"
        @mousemove="handleMouseMove"
        @mouseleave="handleMouseLeave"
      />

      <!-- Playhead -->
      <div
        class="playhead"
        :style="{ left: `${playheadPosition}%` }"
      />

      <!-- Hover Indicator -->
      <div
        v-if="hoverFrame !== null"
        class="hover-indicator"
        :style="{ left: `${hoverPosition}%` }"
      >
        <div class="hover-tooltip">
          Frame {{ hoverFrame }}<br />
          {{ formatTime(hoverFrame / fps) }}
        </div>
      </div>

      <!-- Beat Markers (Onsets) -->
      <div
        v-for="onset in visibleOnsets"
        :key="`onset-${onset}`"
        class="beat-marker"
        :style="{ left: `${(onset / totalFrames) * 100}%` }"
      />

      <!-- Peak Markers -->
      <div
        v-for="peak in visiblePeaks"
        :key="`peak-${peak}`"
        class="peak-marker"
        :style="{ left: `${(peak / totalFrames) * 100}%` }"
      >
        <div class="peak-diamond" />
      </div>
    </div>

    <!-- No Audio Message -->
    <div v-if="!audioBuffer" class="no-audio">
      <i class="pi pi-upload" />
      <span>No audio loaded</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref, watch } from "vue";
import type { AudioAnalysis, PeakData } from "@/services/audioFeatures";

interface Props {
  audioBuffer: AudioBuffer | null;
  analysis: AudioAnalysis | null;
  peakData: PeakData | null;
  currentFrame: number;
  totalFrames: number;
  fps: number;
  height?: number;
}

const props = withDefaults(defineProps<Props>(), {
  height: 60,
});

const emit = defineEmits<(e: "seek", frame: number) => void>();

// Refs
const containerRef = ref<HTMLDivElement | null>(null);
const canvasRef = ref<HTMLCanvasElement | null>(null);
const hoverFrame = ref<number | null>(null);

// Computed
const playheadPosition = computed(
  () => (props.currentFrame / props.totalFrames) * 100,
);

const hoverPosition = computed(() =>
  hoverFrame.value !== null ? (hoverFrame.value / props.totalFrames) * 100 : 0,
);

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
const visibleOnsets = computed(() => {
  const analysis = props.analysis;
  return (analysis !== null && analysis !== undefined && typeof analysis === "object" && "onsets" in analysis && Array.isArray(analysis.onsets)) ? analysis.onsets : [];
});

const visiblePeaks = computed(() => {
  const peakData = props.peakData;
  return (peakData !== null && peakData !== undefined && typeof peakData === "object" && "indices" in peakData && Array.isArray(peakData.indices)) ? peakData.indices : [];
});

const fps = computed(() => props.fps);

// Methods
function handleClick(event: MouseEvent): void {
  if (!containerRef.value) return;

  const rect = containerRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const ratio = x / rect.width;
  const frame = Math.round(ratio * props.totalFrames);

  emit("seek", Math.max(0, Math.min(frame, props.totalFrames - 1)));
}

function handleMouseMove(event: MouseEvent): void {
  if (!containerRef.value) return;

  const rect = containerRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const ratio = x / rect.width;
  hoverFrame.value = Math.round(ratio * props.totalFrames);
}

function handleMouseLeave(): void {
  hoverFrame.value = null;
}

function formatTime(seconds: number): string {
  const mins = Math.floor(seconds / 60);
  const secs = Math.floor(seconds % 60);
  const ms = Math.floor((seconds % 1) * 100);
  return `${mins}:${secs.toString().padStart(2, "0")}.${ms.toString().padStart(2, "0")}`;
}

function drawWaveform(): void {
  const canvas = canvasRef.value;
  const container = containerRef.value;
  if (!canvas || !container || !props.audioBuffer) return;

  // Set canvas size
  const rect = container.getBoundingClientRect();
  canvas.width = rect.width;
  canvas.height = props.height;

  const ctx = canvas.getContext("2d")!;
  const width = canvas.width;
  const height = canvas.height;

  // Clear
  ctx.fillStyle = "#1e1e1e";
  ctx.fillRect(0, 0, width, height);

  // Draw waveform
  const channelData = props.audioBuffer.getChannelData(0);
  const samplesPerPixel = Math.ceil(channelData.length / width);

  ctx.strokeStyle = "#3d5a80";
  ctx.lineWidth = 1;
  ctx.beginPath();

  const midY = height / 2;

  for (let x = 0; x < width; x++) {
    const startSample = x * samplesPerPixel;
    const endSample = Math.min(
      startSample + samplesPerPixel,
      channelData.length,
    );

    let min = 0;
    let max = 0;

    for (let i = startSample; i < endSample; i++) {
      if (channelData[i] < min) min = channelData[i];
      if (channelData[i] > max) max = channelData[i];
    }

    const yMin = midY + min * (height / 2) * 0.9;
    const yMax = midY + max * (height / 2) * 0.9;

    ctx.moveTo(x, yMin);
    ctx.lineTo(x, yMax);
  }

  ctx.stroke();

  // Draw amplitude envelope overlay
  if (props.analysis) {
    ctx.strokeStyle = "#4a90d9";
    ctx.lineWidth = 1.5;
    ctx.beginPath();

    const envelope = props.analysis.amplitudeEnvelope;
    for (let i = 0; i < envelope.length; i++) {
      const x = (i / envelope.length) * width;
      const y = height - envelope[i] * height * 0.8 - 5;

      if (i === 0) {
        ctx.moveTo(x, y);
      } else {
        ctx.lineTo(x, y);
      }
    }

    ctx.stroke();
  }

  // Draw RMS energy (lighter overlay)
  if (props.analysis) {
    ctx.strokeStyle = "rgba(74, 144, 217, 0.3)";
    ctx.lineWidth = 1;
    ctx.beginPath();

    const rms = props.analysis.rmsEnergy;
    for (let i = 0; i < rms.length; i++) {
      const x = (i / rms.length) * width;
      const y = height - rms[i] * height * 0.6 - 5;

      if (i === 0) {
        ctx.moveTo(x, y);
      } else {
        ctx.lineTo(x, y);
      }
    }

    ctx.stroke();
  }
}

// Watch for changes
watch(
  () => [props.audioBuffer, props.analysis, props.peakData],
  () => {
    drawWaveform();
  },
);

// Lifecycle
onMounted(() => {
  drawWaveform();

  // Handle resize
  const resizeObserver = new ResizeObserver(() => {
    drawWaveform();
  });

  if (containerRef.value) {
    resizeObserver.observe(containerRef.value);
  }

  onUnmounted(() => {
    resizeObserver.disconnect();
  });
});
</script>

<style scoped>
.audio-track {
  display: flex;
  background: #1e1e1e;
  border-bottom: 1px solid #333;
}

.track-header {
  width: 150px;
  flex-shrink: 0;
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 0 12px;
  background: #252525;
  border-right: 1px solid #333;
  font-size: 12px;
}

.track-header i {
  color: #4a90d9;
}

.track-name {
  color: #aaa;
}

.bpm-badge {
  margin-left: auto;
  padding: 2px 6px;
  background: #4a90d9;
  color: #fff;
  border-radius: 3px;
  font-size: 12px;
  font-weight: 500;
}

.waveform-container {
  flex: 1;
  position: relative;
  overflow: hidden;
}

.waveform-canvas {
  width: 100%;
  height: 100%;
  cursor: pointer;
}

.playhead {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 2px;
  background: #ff6b6b;
  pointer-events: none;
  z-index: 10;
}

.hover-indicator {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  background: rgba(255, 255, 255, 0.3);
  pointer-events: none;
  z-index: 5;
}

.hover-tooltip {
  position: absolute;
  bottom: 100%;
  left: 50%;
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
}

.beat-marker {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  background: rgba(255, 193, 7, 0.5);
  pointer-events: none;
  z-index: 3;
}

.peak-marker {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 2px;
  background: rgba(255, 107, 107, 0.6);
  pointer-events: none;
  z-index: 4;
}

.peak-diamond {
  position: absolute;
  top: 2px;
  left: 50%;
  transform: translateX(-50%) rotate(45deg);
  width: 6px;
  height: 6px;
  background: #ff6b6b;
  border: 1px solid #fff;
  box-shadow: 0 0 4px rgba(255, 107, 107, 0.8);
}

.no-audio {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
  color: #666;
  font-size: 12px;
}

.no-audio i {
  font-size: 16px;
}
</style>
