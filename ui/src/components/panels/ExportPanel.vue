<template>
  <div class="export-panel">
    <div class="panel-header">
      <span class="panel-title">Export Video</span>
    </div>

    <div class="panel-content">
      <!-- Codec Selection -->
      <div class="control-section">
        <div class="section-header">
          <span class="section-title">Format</span>
        </div>
        <div class="control-row">
          <label>Codec</label>
          <select v-model="selectedCodec" :disabled="isExporting">
            <option v-for="codec in availableCodecs" :key="codec.value" :value="codec.value">
              {{ codec.label }}
            </option>
          </select>
        </div>
        <div class="control-row">
          <label>Quality</label>
          <select v-model="selectedQuality" :disabled="isExporting">
            <option value="low">Low (smaller file)</option>
            <option value="medium">Medium</option>
            <option value="high">High</option>
            <option value="lossless">Lossless (largest)</option>
          </select>
        </div>
      </div>

      <!-- Composition Info -->
      <div class="control-section">
        <div class="section-header">
          <span class="section-title">Output</span>
        </div>
        <div class="info-grid">
          <div class="info-item">
            <span class="info-label">Size</span>
            <span class="info-value">{{ outputWidth }} x {{ outputHeight }}</span>
          </div>
          <div class="info-item">
            <span class="info-label">Frame Rate</span>
            <span class="info-value">{{ frameRate }} fps</span>
          </div>
          <div class="info-item">
            <span class="info-label">Duration</span>
            <span class="info-value">{{ duration }}</span>
          </div>
          <div class="info-item">
            <span class="info-label">Total Frames</span>
            <span class="info-value">{{ totalFrames }}</span>
          </div>
        </div>
      </div>

      <!-- Progress -->
      <div class="progress-section" v-if="isExporting || exportComplete">
        <div class="progress-header">
          <span>{{ exportStatusText }}</span>
          <span v-if="isExporting">{{ exportProgress.percentage.toFixed(1) }}%</span>
        </div>
        <div class="progress-bar">
          <div class="progress-fill" :style="{ width: `${exportProgress.percentage}%` }"></div>
        </div>
        <div class="progress-details" v-if="isExporting">
          <span>Frame {{ exportProgress.framesEncoded }} / {{ exportProgress.totalFrames }}</span>
          <span>{{ formatBytes(exportProgress.bytesWritten) }}</span>
        </div>
      </div>

      <!-- Actions -->
      <div class="actions-section">
        <button
          v-if="!isExporting"
          class="export-btn primary"
          :disabled="!canExport"
          @click="startExport"
        >
          Export Video
        </button>
        <button
          v-if="isExporting"
          class="export-btn cancel"
          @click="cancelExport"
        >
          Cancel
        </button>
        <button
          v-if="exportComplete && encodedVideo"
          class="export-btn download"
          @click="downloadExport"
        >
          Download {{ formatBytes(encodedVideo.size) }}
        </button>
      </div>

      <!-- WebCodecs Support Warning -->
      <div class="warning-message" v-if="!webCodecsSupported">
        <span class="warning-icon">⚠️</span>
        <span>WebCodecs API not supported in this browser. Video export unavailable.</span>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import {
  isWebCodecsSupported,
  getSupportedCodecs,
  WebCodecsVideoEncoder,
  downloadVideo,
  type VideoEncoderConfig,
  type EncodingProgress,
  type EncodedVideo,
} from '@/services/export/videoEncoder';

const store = useCompositorStore();

// State
const webCodecsSupported = ref(false);
const availableCodecs = ref<{ value: string; label: string }[]>([]);
const selectedCodec = ref<'avc' | 'vp9' | 'vp8'>('avc');
const selectedQuality = ref<'low' | 'medium' | 'high' | 'lossless'>('high');
const isExporting = ref(false);
const exportComplete = ref(false);
const encodedVideo = ref<EncodedVideo | null>(null);
const currentEncoder = ref<WebCodecsVideoEncoder | null>(null);
const exportProgress = ref<EncodingProgress>({
  framesEncoded: 0,
  totalFrames: 0,
  percentage: 0,
  bytesWritten: 0,
});

// Computed
const activeComp = computed(() => store.getActiveComp());
const outputWidth = computed(() => activeComp.value?.settings.width || 1024);
const outputHeight = computed(() => activeComp.value?.settings.height || 1024);
const frameRate = computed(() => activeComp.value?.settings.fps || 16);
const totalFrames = computed(() => activeComp.value?.settings.frameCount || 81);
const duration = computed(() => {
  const seconds = totalFrames.value / frameRate.value;
  const m = Math.floor(seconds / 60);
  const s = (seconds % 60).toFixed(2);
  return m > 0 ? `${m}m ${s}s` : `${s}s`;
});
const canExport = computed(() => webCodecsSupported.value && !isExporting.value && store.layers.length > 0);
const exportStatusText = computed(() => {
  if (exportComplete.value) return 'Export complete!';
  if (isExporting.value) return 'Encoding...';
  return 'Ready';
});

// Lifecycle
onMounted(async () => {
  webCodecsSupported.value = isWebCodecsSupported();
  if (webCodecsSupported.value) {
    const codecs = await getSupportedCodecs();
    availableCodecs.value = [];
    if (codecs.includes('avc')) {
      availableCodecs.value.push({ value: 'avc', label: 'H.264 (MP4)' });
    }
    if (codecs.includes('vp9')) {
      availableCodecs.value.push({ value: 'vp9', label: 'VP9 (WebM)' });
    }
    if (codecs.includes('vp8')) {
      availableCodecs.value.push({ value: 'vp8', label: 'VP8 (WebM)' });
    }
    if (availableCodecs.value.length > 0) {
      selectedCodec.value = availableCodecs.value[0].value as 'avc' | 'vp9' | 'vp8';
    }
  }
});

// Methods
async function startExport() {
  if (!canExport.value) return;

  isExporting.value = true;
  exportComplete.value = false;
  encodedVideo.value = null;

  const config: VideoEncoderConfig = {
    width: outputWidth.value,
    height: outputHeight.value,
    frameRate: frameRate.value,
    codec: selectedCodec.value,
    quality: selectedQuality.value,
  };

  const encoder = new WebCodecsVideoEncoder(config);
  currentEncoder.value = encoder;

  try {
    await encoder.initialize((progress) => {
      exportProgress.value = progress;
    });

    // Create an offscreen canvas for rendering
    const canvas = new OffscreenCanvas(outputWidth.value, outputHeight.value);
    const ctx = canvas.getContext('2d');
    if (!ctx) throw new Error('Could not get 2D context');

    // Render and encode each frame
    for (let frame = 0; frame < totalFrames.value; frame++) {
      if (!isExporting.value) break; // User cancelled

      // Set frame in store (triggers render)
      store.setFrame(frame);

      // Small delay to allow render
      await new Promise(resolve => setTimeout(resolve, 10));

      // Get the rendered frame from the canvas
      // Note: This requires the ThreeCanvas to provide a way to get the current frame
      // For now, we'll render a placeholder - in production this would hook into the engine
      const frameImage = await captureCurrentFrame(canvas, ctx);

      await encoder.encodeFrame(frameImage, frame, totalFrames.value);
    }

    if (isExporting.value) {
      encodedVideo.value = await encoder.finalize();
      exportComplete.value = true;
    }
  } catch (error) {
    console.error('Export failed:', error);
    alert(`Export failed: ${(error as Error).message}`);
  } finally {
    isExporting.value = false;
    currentEncoder.value = null;
  }
}

async function captureCurrentFrame(
  canvas: OffscreenCanvas,
  ctx: OffscreenCanvasRenderingContext2D
): Promise<OffscreenCanvas> {
  // Try to get the WebGL canvas from the Three.js renderer
  const glCanvas = document.querySelector('.three-canvas canvas') as HTMLCanvasElement;

  if (glCanvas) {
    ctx.drawImage(glCanvas, 0, 0, canvas.width, canvas.height);
  } else {
    // Fallback: render a gradient placeholder
    const gradient = ctx.createLinearGradient(0, 0, canvas.width, canvas.height);
    gradient.addColorStop(0, '#1a1a2e');
    gradient.addColorStop(1, '#16213e');
    ctx.fillStyle = gradient;
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.fillStyle = '#fff';
    ctx.font = '24px sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText('Frame ' + store.currentFrame, canvas.width / 2, canvas.height / 2);
  }

  return canvas;
}

function cancelExport() {
  isExporting.value = false;
  if (currentEncoder.value) {
    currentEncoder.value.cancel();
    currentEncoder.value = null;
  }
}

function downloadExport() {
  if (encodedVideo.value) {
    const compName = activeComp.value?.name || 'composition';
    downloadVideo(encodedVideo.value, `${compName}-export`);
  }
}

function formatBytes(bytes: number): string {
  if (bytes === 0) return '0 B';
  const k = 1024;
  const sizes = ['B', 'KB', 'MB', 'GB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  return parseFloat((bytes / Math.pow(k, i)).toFixed(1)) + ' ' + sizes[i];
}
</script>

<style scoped>
.export-panel {
  background: var(--surface-ground, #1e1e2e);
  border-radius: 8px;
  overflow: hidden;
  display: flex;
  flex-direction: column;
}

.panel-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 12px 16px;
  background: var(--surface-card, #252535);
  border-bottom: 1px solid var(--surface-border, #333345);
}

.panel-title {
  font-weight: 600;
  font-size: 14px;
  color: var(--text-color, #e0e0e0);
}

.panel-content {
  padding: 16px;
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.control-section {
  background: var(--surface-card, #252535);
  border-radius: 6px;
  padding: 12px;
}

.section-header {
  margin-bottom: 12px;
}

.section-title {
  font-size: 12px;
  font-weight: 600;
  color: var(--text-color-secondary, #a0a0a0);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.control-row {
  display: flex;
  align-items: center;
  gap: 12px;
  margin-bottom: 8px;
}

.control-row:last-child {
  margin-bottom: 0;
}

.control-row label {
  min-width: 80px;
  font-size: 13px;
  color: var(--text-color, #e0e0e0);
}

.control-row select {
  flex: 1;
  padding: 6px 10px;
  background: var(--surface-ground, #1e1e2e);
  border: 1px solid var(--surface-border, #333345);
  border-radius: 4px;
  color: var(--text-color, #e0e0e0);
  font-size: 13px;
}

.control-row select:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.info-grid {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 8px;
}

.info-item {
  display: flex;
  justify-content: space-between;
  font-size: 13px;
}

.info-label {
  color: var(--text-color-secondary, #a0a0a0);
}

.info-value {
  color: var(--text-color, #e0e0e0);
  font-weight: 500;
}

.progress-section {
  background: var(--surface-card, #252535);
  border-radius: 6px;
  padding: 12px;
}

.progress-header {
  display: flex;
  justify-content: space-between;
  margin-bottom: 8px;
  font-size: 13px;
  color: var(--text-color, #e0e0e0);
}

.progress-bar {
  height: 8px;
  background: var(--surface-ground, #1e1e2e);
  border-radius: 4px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: linear-gradient(90deg, #4f46e5, #7c3aed);
  transition: width 0.1s ease;
}

.progress-details {
  display: flex;
  justify-content: space-between;
  margin-top: 8px;
  font-size: 12px;
  color: var(--text-color-secondary, #a0a0a0);
}

.actions-section {
  display: flex;
  gap: 8px;
  flex-wrap: wrap;
}

.export-btn {
  flex: 1;
  min-width: 120px;
  padding: 10px 16px;
  border: none;
  border-radius: 6px;
  font-size: 14px;
  font-weight: 500;
  cursor: pointer;
  transition: background 0.2s, opacity 0.2s;
}

.export-btn.primary {
  background: linear-gradient(135deg, #4f46e5, #7c3aed);
  color: white;
}

.export-btn.primary:hover:not(:disabled) {
  background: linear-gradient(135deg, #4338ca, #6d28d9);
}

.export-btn.primary:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.export-btn.cancel {
  background: var(--surface-ground, #1e1e2e);
  color: var(--text-color, #e0e0e0);
  border: 1px solid var(--surface-border, #333345);
}

.export-btn.cancel:hover {
  background: #2a2a3a;
}

.export-btn.download {
  background: #059669;
  color: white;
}

.export-btn.download:hover {
  background: #047857;
}

.warning-message {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 12px;
  background: rgba(234, 179, 8, 0.1);
  border: 1px solid rgba(234, 179, 8, 0.3);
  border-radius: 6px;
  font-size: 13px;
  color: #fbbf24;
}

.warning-icon {
  font-size: 16px;
}
</style>
