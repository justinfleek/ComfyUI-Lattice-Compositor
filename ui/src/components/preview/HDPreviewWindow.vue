<!--
  @component HDPreviewWindow
  @description Full-resolution preview window for Lattice Compositor.
  Opens as a modal overlay for high-quality playback review:
  - Full resolution rendering (up to 4K)
  - Playback controls (play, pause, step, loop)
  - Frame scrubbing via timeline
  - Scalable preview (50%-200%)
  - Fullscreen mode (F11)
  - Frame timing display

  @features
  - Real-time frame rendering from composition
  - Keyboard navigation (Escape to close)
  - Resolution badge display
  - Zoom controls for preview scaling

  @props visible - Boolean to show/hide window
  @emits close - Request to close the preview window
-->
<template>
  <Teleport to="body">
    <div
      v-if="visible"
      class="hd-preview-overlay"
      @keydown.escape="$emit('close')"
      tabindex="0"
      ref="overlayRef"
    >
      <div class="hd-preview-container" :style="containerStyle">
        <!-- Header -->
        <div class="preview-header">
          <div class="header-left">
            <span class="preview-title">HD Preview</span>
            <span class="resolution-badge">{{ resolutionLabel }}</span>
          </div>
          <div class="header-center">
            <div class="playback-controls">
              <button @click="goToStart" title="Go to Start">⏮</button>
              <button @click="stepBackward" title="Step Back">◀</button>
              <button @click="togglePlayback" :class="{ playing: isPlaying }">
                {{ isPlaying ? '⏸' : '▶' }}
              </button>
              <button @click="stepForward" title="Step Forward">▶</button>
              <button @click="goToEnd" title="Go to End">⏭</button>
            </div>
            <div class="timecode">
              {{ formattedTimecode }}
            </div>
          </div>
          <div class="header-right">
            <select v-model="previewScale" class="scale-select">
              <option value="0.5">50%</option>
              <option value="0.75">75%</option>
              <option value="1">100%</option>
              <option value="1.5">150%</option>
              <option value="2">200%</option>
              <option value="fit">Fit</option>
            </select>
            <button
              @click="toggleFullscreen"
              :title="isFullscreen ? 'Exit Fullscreen' : 'Enter Fullscreen'"
            >
              {{ isFullscreen ? '⛶' : '⛶' }}
            </button>
            <button @click="$emit('close')" title="Close Preview (Esc)">✕</button>
          </div>
        </div>

        <!-- Canvas Container -->
        <div class="canvas-container" ref="canvasContainerRef">
          <canvas
            ref="previewCanvas"
            :width="canvasWidth"
            :height="canvasHeight"
            :style="canvasStyle"
          />

          <!-- Loading Overlay -->
          <div v-if="isRendering" class="rendering-overlay">
            <div class="spinner"></div>
            <span>Rendering frame {{ currentFrame }}...</span>
          </div>

          <!-- Frame Info Overlay -->
          <div class="frame-info-overlay">
            <span>Frame {{ currentFrame }} / {{ frameCount }}</span>
            <span v-if="renderTime">{{ renderTime.toFixed(1) }}ms</span>
          </div>
        </div>

        <!-- Progress Bar -->
        <div class="progress-bar">
          <div
            class="progress-fill"
            :style="{ width: `${(currentFrame / (frameCount - 1)) * 100}%` }"
          />
          <input
            type="range"
            :min="0"
            :max="frameCount - 1"
            :value="currentFrame"
            @input="onScrub"
            class="scrubber"
          />
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted, nextTick } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { storeToRefs } from 'pinia';

const props = defineProps<{
  visible: boolean;
  engine?: any;
}>();

const emit = defineEmits<{
  (e: 'close'): void;
}>();

const store = useCompositorStore();
const { currentFrame, frameCount, fps, isPlaying } = storeToRefs(store);

// Refs
const overlayRef = ref<HTMLElement | null>(null);
const canvasContainerRef = ref<HTMLElement | null>(null);
const previewCanvas = ref<HTMLCanvasElement | null>(null);

// State
const previewScale = ref<string | number>('fit');
const isFullscreen = ref(false);
const isRendering = ref(false);
const renderTime = ref<number | null>(null);
const containerWidth = ref(1280);
const containerHeight = ref(720);

// Computed
const compWidth = computed(() => store.getActiveComp()?.settings.width || 1024);
const compHeight = computed(() => store.getActiveComp()?.settings.height || 576);

const canvasWidth = computed(() => {
  if (previewScale.value === 'fit') {
    const aspect = compWidth.value / compHeight.value;
    const maxWidth = containerWidth.value - 48;
    const maxHeight = containerHeight.value - 140;
    if (maxWidth / maxHeight > aspect) {
      return Math.round(maxHeight * aspect);
    }
    return maxWidth;
  }
  return Math.round(compWidth.value * Number(previewScale.value));
});

const canvasHeight = computed(() => {
  if (previewScale.value === 'fit') {
    const aspect = compWidth.value / compHeight.value;
    const maxWidth = containerWidth.value - 48;
    const maxHeight = containerHeight.value - 140;
    if (maxWidth / maxHeight > aspect) {
      return maxHeight;
    }
    return Math.round(maxWidth / aspect);
  }
  return Math.round(compHeight.value * Number(previewScale.value));
});

const resolutionLabel = computed(() => {
  return `${compWidth.value}x${compHeight.value}`;
});

const formattedTimecode = computed(() => {
  const seconds = currentFrame.value / fps.value;
  const mins = Math.floor(seconds / 60);
  const secs = Math.floor(seconds % 60);
  const frames = currentFrame.value % fps.value;
  return `${String(mins).padStart(2, '0')}:${String(secs).padStart(2, '0')}:${String(frames).padStart(2, '0')}`;
});

const containerStyle = computed(() => ({
  width: isFullscreen.value ? '100vw' : '90vw',
  height: isFullscreen.value ? '100vh' : '90vh',
  maxWidth: isFullscreen.value ? 'none' : '1600px',
  maxHeight: isFullscreen.value ? 'none' : '900px',
}));

const canvasStyle = computed(() => ({
  width: `${canvasWidth.value}px`,
  height: `${canvasHeight.value}px`,
}));

// Methods
function togglePlayback() {
  store.togglePlayback();
}

function goToStart() {
  store.setCurrentFrame(0);
}

function goToEnd() {
  store.setCurrentFrame(frameCount.value - 1);
}

function stepForward() {
  store.setCurrentFrame(Math.min(currentFrame.value + 1, frameCount.value - 1));
}

function stepBackward() {
  store.setCurrentFrame(Math.max(currentFrame.value - 1, 0));
}

function onScrub(e: Event) {
  const target = e.target as HTMLInputElement;
  store.setCurrentFrame(parseInt(target.value, 10));
}

function toggleFullscreen() {
  if (!document.fullscreenElement) {
    overlayRef.value?.requestFullscreen();
    isFullscreen.value = true;
  } else {
    document.exitFullscreen();
    isFullscreen.value = false;
  }
}

async function renderFrame() {
  if (!previewCanvas.value || !props.engine) return;

  const start = performance.now();
  isRendering.value = true;

  try {
    const ctx = previewCanvas.value.getContext('2d');
    if (!ctx) return;

    // Get the engine's rendered frame
    const sourceCanvas = props.engine.getCanvas?.() || props.engine.renderer?.domElement;
    if (sourceCanvas) {
      ctx.clearRect(0, 0, canvasWidth.value, canvasHeight.value);
      ctx.drawImage(
        sourceCanvas,
        0, 0, sourceCanvas.width, sourceCanvas.height,
        0, 0, canvasWidth.value, canvasHeight.value
      );
    }

    renderTime.value = performance.now() - start;
  } finally {
    isRendering.value = false;
  }
}

function updateContainerSize() {
  if (canvasContainerRef.value) {
    const rect = canvasContainerRef.value.getBoundingClientRect();
    containerWidth.value = rect.width;
    containerHeight.value = rect.height;
  }
}

// Watchers
watch(() => props.visible, async (visible) => {
  if (visible) {
    await nextTick();
    overlayRef.value?.focus();
    updateContainerSize();
    renderFrame();
  }
});

watch(currentFrame, () => {
  if (props.visible) {
    renderFrame();
  }
});

// Lifecycle
onMounted(() => {
  window.addEventListener('resize', updateContainerSize);
  document.addEventListener('fullscreenchange', () => {
    isFullscreen.value = !!document.fullscreenElement;
  });
});

onUnmounted(() => {
  window.removeEventListener('resize', updateContainerSize);
});
</script>

<style scoped>
.hd-preview-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.9);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
  outline: none;
}

.hd-preview-container {
  background: #1a1a1a;
  border-radius: 8px;
  display: flex;
  flex-direction: column;
  overflow: hidden;
  box-shadow: 0 20px 60px rgba(0, 0, 0, 0.5);
}

.preview-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 12px 16px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.header-left,
.header-center,
.header-right {
  display: flex;
  align-items: center;
  gap: 12px;
}

.preview-title {
  font-weight: 600;
  font-size: 14px;
  color: #fff;
}

.resolution-badge {
  padding: 2px 8px;
  background: #6366f1;
  border-radius: 4px;
  font-size: 11px;
  font-weight: 600;
  color: white;
}

.playback-controls {
  display: flex;
  gap: 4px;
}

.playback-controls button {
  width: 32px;
  height: 32px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: #333;
  border: none;
  border-radius: 4px;
  color: #ccc;
  cursor: pointer;
  font-size: 14px;
  transition: background 0.2s;
}

.playback-controls button:hover {
  background: #444;
  color: white;
}

.playback-controls button.playing {
  background: #6366f1;
  color: white;
}

.timecode {
  font-family: monospace;
  font-size: 14px;
  color: #888;
  padding: 4px 12px;
  background: #1a1a1a;
  border-radius: 4px;
}

.scale-select {
  padding: 6px 8px;
  background: #333;
  border: 1px solid #444;
  border-radius: 4px;
  color: #ccc;
  font-size: 12px;
}

.header-right button {
  width: 32px;
  height: 32px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: #333;
  border: none;
  border-radius: 4px;
  color: #ccc;
  cursor: pointer;
  font-size: 16px;
  transition: background 0.2s;
}

.header-right button:hover {
  background: #444;
  color: white;
}

.canvas-container {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  background: #0a0a0a;
  position: relative;
  overflow: hidden;
}

.canvas-container canvas {
  background: #000;
  box-shadow: 0 4px 20px rgba(0, 0, 0, 0.5);
}

.rendering-overlay {
  position: absolute;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 12px;
  color: #888;
  font-size: 14px;
}

.spinner {
  width: 32px;
  height: 32px;
  border: 3px solid #333;
  border-top-color: #6366f1;
  border-radius: 50%;
  animation: spin 1s linear infinite;
}

@keyframes spin {
  to { transform: rotate(360deg); }
}

.frame-info-overlay {
  position: absolute;
  bottom: 12px;
  right: 12px;
  display: flex;
  gap: 12px;
  padding: 4px 12px;
  background: rgba(0, 0, 0, 0.7);
  border-radius: 4px;
  font-size: 12px;
  color: #888;
}

.progress-bar {
  position: relative;
  height: 32px;
  background: #252525;
  border-top: 1px solid #333;
}

.progress-fill {
  position: absolute;
  top: 0;
  left: 0;
  height: 100%;
  background: linear-gradient(90deg, #6366f1 0%, #8b5cf6 100%);
  opacity: 0.3;
  pointer-events: none;
}

.scrubber {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  margin: 0;
  -webkit-appearance: none;
  appearance: none;
  background: transparent;
  cursor: pointer;
}

.scrubber::-webkit-slider-thumb {
  -webkit-appearance: none;
  width: 4px;
  height: 32px;
  background: #6366f1;
  cursor: ew-resize;
}

.scrubber::-moz-range-thumb {
  width: 4px;
  height: 32px;
  background: #6366f1;
  border: none;
  cursor: ew-resize;
}
</style>
