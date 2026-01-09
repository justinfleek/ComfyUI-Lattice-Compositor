<template>
  <div class="export-panel">
    <div class="panel-header">
      <span class="panel-title">Export</span>
    </div>

    <div class="panel-content">
      <!-- Export Mode Toggle -->
      <div class="control-section">
        <div class="section-header">
          <span class="section-title">Export Mode</span>
        </div>
        <div class="mode-toggle">
          <button
            class="mode-btn"
            :class="{ active: exportMode === 'video' }"
            @click="exportMode = 'video'"
            :disabled="isExporting"
          >
            Video
          </button>
          <button
            class="mode-btn"
            :class="{ active: exportMode === 'sequence' }"
            @click="exportMode = 'sequence'"
            :disabled="isExporting"
          >
            Frame Sequence
          </button>
        </div>
      </div>

      <!-- Video Codec Selection (Video Mode) -->
      <div class="control-section" v-if="exportMode === 'video'">
        <div class="section-header">
          <span class="section-title">Video Format</span>
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

      <!-- Frame Sequence Format (Sequence Mode) -->
      <div class="control-section" v-if="exportMode === 'sequence'">
        <div class="section-header">
          <span class="section-title">Sequence Format</span>
        </div>
        <div class="control-row">
          <label>Format</label>
          <select v-model="sequenceFormat" :disabled="isExporting">
            <option value="png">PNG (Lossless)</option>
            <option value="jpeg">JPEG (Lossy)</option>
            <option value="webp">WebP (Modern)</option>
            <option value="tiff" :disabled="!backendAvailable">TIFF 16-bit (Backend)</option>
            <option value="exr" :disabled="!backendAvailable">OpenEXR HDR (Backend)</option>
            <option value="dpx" :disabled="!backendAvailable">DPX Film (Backend)</option>
          </select>
        </div>
        <div class="control-row" v-if="sequenceFormat === 'jpeg' || sequenceFormat === 'webp'">
          <label>Quality</label>
          <input type="range" v-model.number="sequenceQuality" min="1" max="100" :disabled="isExporting" />
          <span class="quality-value">{{ sequenceQuality }}%</span>
        </div>
        <div class="format-info">
          <div class="info-badge" :class="sequenceFormatInfo.requiresBackend ? 'backend' : 'browser'">
            {{ sequenceFormatInfo.requiresBackend ? 'Backend Required' : 'Browser Export' }}
          </div>
          <span class="format-desc">{{ sequenceFormatInfo.description }}</span>
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
          {{ exportMode === 'video' ? 'Export Video' : 'Export Frames' }}
        </button>
        <button
          v-if="isExporting"
          class="export-btn cancel"
          @click="cancelExport"
        >
          Cancel
        </button>
        <button
          v-if="exportComplete && encodedVideo && exportMode === 'video'"
          class="export-btn download"
          @click="downloadExport"
        >
          Download {{ formatBytes(encodedVideo.size) }}
        </button>
        <button
          v-if="exportComplete && sequenceResult && exportMode === 'sequence'"
          class="export-btn download"
          @click="downloadSequence"
        >
          Download ZIP ({{ formatBytes(sequenceResult.totalSize) }})
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
import { computed, onMounted, ref } from "vue";
import {
  downloadBlob,
  exportFrameSequence,
  type FrameFormat,
  type FrameSequenceResult,
  getFormatInfo,
} from "@/services/export/frameSequenceExporter";
import {
  downloadVideo,
  type EncodedVideo,
  type EncodingProgress,
  getSupportedCodecs,
  isWebCodecsSupported,
  type VideoEncoderConfig,
  WebCodecsVideoEncoder,
} from "@/services/export/videoEncoder";
import { useCompositorStore } from "@/stores/compositorStore";

const store = useCompositorStore();

// State
const exportMode = ref<"video" | "sequence">("video");
const webCodecsSupported = ref(false);
const backendAvailable = ref(false); // TODO: Check if ComfyUI backend is available
const availableCodecs = ref<{ value: string; label: string }[]>([]);
const selectedCodec = ref<"avc" | "vp9" | "vp8">("avc");
const selectedQuality = ref<"low" | "medium" | "high" | "lossless">("high");
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

// Frame sequence state
const sequenceFormat = ref<FrameFormat>("png");
const sequenceQuality = ref(95);
const sequenceResult = ref<FrameSequenceResult | null>(null);

// Computed format info
const sequenceFormatInfo = computed(() => getFormatInfo(sequenceFormat.value));

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
const canExport = computed(() => {
  if (isExporting.value || store.layers.length === 0) return false;
  if (exportMode.value === "video") return webCodecsSupported.value;
  return true; // Frame sequence always available (browser formats)
});
const exportStatusText = computed(() => {
  if (exportComplete.value) return "Export complete!";
  if (isExporting.value) {
    if (exportMode.value === "sequence") return "Rendering frames...";
    return "Encoding...";
  }
  return "Ready";
});

// Lifecycle
onMounted(async () => {
  webCodecsSupported.value = isWebCodecsSupported();
  if (webCodecsSupported.value) {
    const codecs = await getSupportedCodecs();
    availableCodecs.value = [];
    if (codecs.includes("avc")) {
      availableCodecs.value.push({ value: "avc", label: "H.264 (MP4)" });
    }
    if (codecs.includes("vp9")) {
      availableCodecs.value.push({ value: "vp9", label: "VP9 (WebM)" });
    }
    if (codecs.includes("vp8")) {
      availableCodecs.value.push({ value: "vp8", label: "VP8 (WebM)" });
    }
    if (availableCodecs.value.length > 0) {
      selectedCodec.value = availableCodecs.value[0].value as
        | "avc"
        | "vp9"
        | "vp8";
    }
  }
});

// Methods
async function startExport() {
  if (!canExport.value) return;

  isExporting.value = true;
  exportComplete.value = false;
  encodedVideo.value = null;
  sequenceResult.value = null;

  if (exportMode.value === "sequence") {
    await startFrameSequenceExport();
  } else {
    await startVideoExport();
  }
}

async function startFrameSequenceExport() {
  try {
    const result = await exportFrameSequence(
      async (frame: number) => {
        // Set frame in store (triggers render)
        store.setFrame(frame);

        // Small delay to allow render
        await new Promise((resolve) => setTimeout(resolve, 10));

        // Get the WebGL canvas from the Three.js renderer
        const glCanvas = document.querySelector(
          ".three-canvas canvas",
        ) as HTMLCanvasElement;

        if (glCanvas) {
          // Create a new canvas with the composition dimensions
          const canvas = document.createElement("canvas");
          canvas.width = outputWidth.value;
          canvas.height = outputHeight.value;
          const ctx = canvas.getContext("2d");
          if (ctx) {
            ctx.drawImage(glCanvas, 0, 0, canvas.width, canvas.height);
          }
          return canvas;
        }

        // Fallback: create placeholder
        const canvas = document.createElement("canvas");
        canvas.width = outputWidth.value;
        canvas.height = outputHeight.value;
        const ctx = canvas.getContext("2d");
        if (ctx) {
          ctx.fillStyle = "#050505";
          ctx.fillRect(0, 0, canvas.width, canvas.height);
          ctx.fillStyle = "#fff";
          ctx.font = "24px sans-serif";
          ctx.textAlign = "center";
          ctx.fillText(`Frame ${frame}`, canvas.width / 2, canvas.height / 2);
        }
        return canvas;
      },
      {
        format: sequenceFormat.value,
        quality: sequenceQuality.value,
        filenamePattern: `${activeComp.value?.name || "frame"}_{frame:04d}`,
        outputDir: "",
        startFrame: 0,
        endFrame: totalFrames.value - 1,
      },
      (current, total) => {
        exportProgress.value = {
          framesEncoded: current,
          totalFrames: total,
          percentage: (current / total) * 100,
          bytesWritten: 0,
        };
      },
    );

    sequenceResult.value = result;
    exportComplete.value = result.success;

    if (result.errors.length > 0) {
      console.warn("Frame sequence export warnings:", result.errors);
    }
  } catch (error) {
    console.error("Frame sequence export failed:", error);
    alert(`Export failed: ${(error as Error).message}`);
  } finally {
    isExporting.value = false;
  }
}

async function startVideoExport() {
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
    const ctx = canvas.getContext("2d");
    if (!ctx) throw new Error("Could not get 2D context");

    // Render and encode each frame
    for (let frame = 0; frame < totalFrames.value; frame++) {
      if (!isExporting.value) break; // User cancelled

      // Set frame in store (triggers render)
      store.setFrame(frame);

      // Small delay to allow render
      await new Promise((resolve) => setTimeout(resolve, 10));

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
    console.error("Export failed:", error);
    alert(`Export failed: ${(error as Error).message}`);
  } finally {
    isExporting.value = false;
    currentEncoder.value = null;
  }
}

async function captureCurrentFrame(
  canvas: OffscreenCanvas,
  ctx: OffscreenCanvasRenderingContext2D,
): Promise<OffscreenCanvas> {
  // Try to get the WebGL canvas from the Three.js renderer
  const glCanvas = document.querySelector(
    ".three-canvas canvas",
  ) as HTMLCanvasElement;

  if (glCanvas) {
    ctx.drawImage(glCanvas, 0, 0, canvas.width, canvas.height);
  } else {
    // Fallback: render a gradient placeholder
    const gradient = ctx.createLinearGradient(
      0,
      0,
      canvas.width,
      canvas.height,
    );
    gradient.addColorStop(0, "#050505");
    gradient.addColorStop(1, "#0a0a0a");
    ctx.fillStyle = gradient;
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    ctx.fillStyle = "#fff";
    ctx.font = "24px sans-serif";
    ctx.textAlign = "center";
    ctx.fillText(
      `Frame ${store.currentFrame}`,
      canvas.width / 2,
      canvas.height / 2,
    );
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
    const compName = activeComp.value?.name || "composition";
    downloadVideo(encodedVideo.value, `${compName}-export`);
  }
}

function downloadSequence() {
  if (!sequenceResult.value || sequenceResult.value.frames.length === 0) return;

  // For single frames or small sequences, download individually
  if (sequenceResult.value.frames.length <= 10) {
    for (const frame of sequenceResult.value.frames) {
      if (frame.blob) {
        downloadBlob(frame.blob, frame.filename);
      }
    }
  } else {
    // For larger sequences, we would use JSZip in production
    // For now, download first 10 frames as a sample
    console.log("Large sequence export - downloading first 10 frames");
    const sampleFrames = sequenceResult.value.frames.slice(0, 10);
    for (const frame of sampleFrames) {
      if (frame.blob) {
        downloadBlob(frame.blob, frame.filename);
      }
    }
    alert(
      `Downloaded first 10 frames as sample.\n` +
        `Full ZIP export requires JSZip library.\n` +
        `Total frames: ${sequenceResult.value.frames.length}`,
    );
  }
}

function formatBytes(bytes: number): string {
  if (bytes === 0) return "0 B";
  const k = 1024;
  const sizes = ["B", "KB", "MB", "GB"];
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  return `${parseFloat((bytes / k ** i).toFixed(1))} ${sizes[i]}`;
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
  flex: 1;
  padding: 16px;
  display: flex;
  flex-direction: column;
  gap: 16px;
  overflow-y: auto;
  overflow-x: hidden;
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

/* Mode Toggle */
.mode-toggle {
  display: flex;
  gap: 4px;
  background: var(--surface-ground, #1e1e2e);
  border-radius: 6px;
  padding: 4px;
}

.mode-btn {
  flex: 1;
  padding: 8px 16px;
  border: none;
  border-radius: 4px;
  background: transparent;
  color: var(--text-color-secondary, #a0a0a0);
  font-size: 13px;
  font-weight: 500;
  cursor: pointer;
  transition: background 0.2s, color 0.2s;
}

.mode-btn:hover:not(:disabled) {
  background: rgba(255, 255, 255, 0.05);
  color: var(--text-color, #e0e0e0);
}

.mode-btn.active {
  background: var(--primary-color, #4f46e5);
  color: white;
}

.mode-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

/* Quality Slider */
.control-row input[type="range"] {
  flex: 1;
  height: 4px;
  background: var(--surface-ground, #1e1e2e);
  border-radius: 2px;
  cursor: pointer;
}

.quality-value {
  min-width: 40px;
  text-align: right;
  font-size: 13px;
  color: var(--text-color, #e0e0e0);
}

/* Format Info */
.format-info {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-top: 8px;
  padding-top: 8px;
  border-top: 1px solid var(--surface-border, #333345);
}

.info-badge {
  padding: 2px 8px;
  border-radius: 4px;
  font-size: 11px;
  font-weight: 600;
  text-transform: uppercase;
}

.info-badge.browser {
  background: rgba(34, 197, 94, 0.2);
  color: #22c55e;
}

.info-badge.backend {
  background: rgba(234, 179, 8, 0.2);
  color: #eab308;
}

.format-desc {
  font-size: 12px;
  color: var(--text-color-secondary, #a0a0a0);
}
</style>
