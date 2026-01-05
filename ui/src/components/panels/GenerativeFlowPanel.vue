<template>
  <div class="generative-flow-panel">
    <div class="panel-header">
      <h3>Generative Flow</h3>
      <span class="subtitle">Data-driven trajectory generation for Wan-Move</span>
    </div>

    <div class="section">
      <label class="section-label">Flow Pattern</label>
      <select v-model="selectedPreset" class="preset-select">
        <option value="custom">Custom Pattern</option>
        <optgroup label="Presets">
          <option v-for="(_, name) in FLOW_PRESETS" :key="name" :value="name">
            {{ formatPresetName(name) }}
          </option>
        </optgroup>
      </select>
    </div>

    <div v-if="selectedPreset === 'custom'" class="section">
      <label class="section-label">Pattern Type</label>
      <select v-model="patternType" class="pattern-select">
        <option value="spiral">Spiral</option>
        <option value="wave">Wave</option>
        <option value="explosion">Explosion</option>
        <option value="vortex">Vortex</option>
        <option value="data-river">Data River</option>
        <option value="morph">Morph</option>
        <option value="swarm">Swarm</option>
      </select>
    </div>

    <div class="section">
      <label class="section-label">Trajectory Count</label>
      <div class="input-row">
        <input
          type="number"
          v-model.number="numPoints"
          min="10"
          max="1000"
          step="10"
          class="num-input"
        />
        <span class="input-hint">10-1000 trajectories</span>
      </div>
    </div>

    <div class="section">
      <label class="section-label">Duration</label>
      <div class="input-row">
        <input
          type="number"
          v-model.number="numFrames"
          min="17"
          max="241"
          step="16"
          class="num-input"
        />
        <span class="input-hint">{{ (numFrames / 16).toFixed(1) }}s @ 16fps</span>
      </div>
    </div>

    <div class="section">
      <label class="section-label">Resolution</label>
      <div class="resolution-row">
        <input
          type="number"
          v-model.number="width"
          min="256"
          max="1920"
          step="8"
          class="res-input"
        />
        <span class="res-x">×</span>
        <input
          type="number"
          v-model.number="height"
          min="256"
          max="1080"
          step="8"
          class="res-input"
        />
        <button class="preset-btn" @click="setResolution(832, 480)" title="Wan-Move default">
          480p
        </button>
        <button class="preset-btn" @click="setResolution(1280, 720)">
          720p
        </button>
      </div>
    </div>

    <div class="section">
      <label class="section-label">Seed</label>
      <div class="input-row">
        <input
          type="number"
          v-model.number="seed"
          min="0"
          class="num-input"
        />
        <button class="randomize-btn" @click="randomizeSeed" title="Randomize seed">
          🎲
        </button>
      </div>
    </div>

    <!-- Data-driven option -->
    <div class="section" v-if="hasDataAssets">
      <label class="section-label">
        <input type="checkbox" v-model="useDataDriven" />
        Use Data Source
      </label>

      <div v-if="useDataDriven" class="data-options">
        <select v-model="selectedDataAsset" class="data-select">
          <option v-for="asset in dataAssets" :key="asset.name" :value="asset.name">
            {{ asset.name }}
          </option>
        </select>

        <select v-model="dataMapping" class="data-select">
          <option value="speed">Speed</option>
          <option value="amplitude">Amplitude</option>
          <option value="phase">Phase</option>
          <option value="direction">Direction</option>
        </select>
      </div>
    </div>

    <!-- Preview -->
    <div class="preview-section">
      <canvas ref="previewCanvas" class="preview-canvas" width="280" height="160"></canvas>
      <button class="preview-btn" @click="generatePreview" :disabled="isGenerating">
        {{ isGenerating ? 'Generating...' : 'Preview' }}
      </button>
    </div>

    <!-- Actions -->
    <div class="actions">
      <button class="action-btn secondary" @click="exportJSON" :disabled="!generatedTrajectory">
        Export JSON
      </button>
      <button class="action-btn primary" @click="exportForWanMove" :disabled="!generatedTrajectory">
        Export for Wan-Move
      </button>
    </div>

    <!-- Status -->
    <div v-if="statusMessage" class="status" :class="statusType">
      {{ statusMessage }}
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, ref, watch } from "vue";
import { getAllDataAssets } from "@/services/dataImport";
import {
  exportAsJSON,
  exportAsNPYData,
  FLOW_PRESETS,
  type GenerativeFlowConfig,
  generateDataRiverFlow,
  generateExplosionFlow,
  generateFromPreset,
  generateMorphFlow,
  generateSpiralFlow,
  generateSwarmFlow,
  generateVortexFlow,
  generateWaveFlow,
  type WanMoveTrajectory,
} from "@/services/export/wanMoveExport";
import { useCompositorStore } from "@/stores/compositorStore";

const _store = useCompositorStore();

// State
const selectedPreset = ref<string>("neural-flow");
const patternType = ref<GenerativeFlowConfig["pattern"]>("spiral");
const numPoints = ref(200);
const numFrames = ref(81); // 5 seconds @ 16fps
const width = ref(832);
const height = ref(480);
const seed = ref(42);
const _useDataDriven = ref(false);
const selectedDataAsset = ref("");
const _dataMapping = ref<"speed" | "amplitude" | "phase" | "direction">(
  "speed",
);
const isGenerating = ref(false);
const generatedTrajectory = ref<WanMoveTrajectory | null>(null);
const statusMessage = ref("");
const statusType = ref<"success" | "error" | "info">("info");
const previewCanvas = ref<HTMLCanvasElement | null>(null);

// Computed
const dataAssets = computed(() => getAllDataAssets());
const _hasDataAssets = computed(() => dataAssets.value.length > 0);

// Methods
function _formatPresetName(name: string): string {
  return name
    .split("-")
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
    .join(" ");
}

function _setResolution(w: number, h: number) {
  width.value = w;
  height.value = h;
}

function _randomizeSeed() {
  seed.value = Math.floor(Math.random() * 1000000);
}

function generateTrajectory(): WanMoveTrajectory {
  if (
    selectedPreset.value !== "custom" &&
    selectedPreset.value in FLOW_PRESETS
  ) {
    return generateFromPreset(
      selectedPreset.value as keyof typeof FLOW_PRESETS,
      numPoints.value,
      numFrames.value,
      width.value,
      height.value,
      seed.value,
    );
  }

  const config: GenerativeFlowConfig = {
    pattern: patternType.value,
    numPoints: numPoints.value,
    numFrames: numFrames.value,
    width: width.value,
    height: height.value,
    params: { seed: seed.value },
  };

  switch (patternType.value) {
    case "spiral":
      return generateSpiralFlow(config);
    case "wave":
      return generateWaveFlow(config);
    case "explosion":
      return generateExplosionFlow(config);
    case "vortex":
      return generateVortexFlow(config);
    case "data-river":
      return generateDataRiverFlow(config);
    case "morph":
      return generateMorphFlow(config);
    case "swarm":
      return generateSwarmFlow(config);
    default:
      return generateSpiralFlow(config);
  }
}

async function _generatePreview() {
  isGenerating.value = true;
  statusMessage.value = "";

  try {
    // Generate trajectory
    generatedTrajectory.value = generateTrajectory();

    // Draw preview
    drawPreview();

    statusMessage.value = `Generated ${generatedTrajectory.value.metadata.numPoints} trajectories`;
    statusType.value = "success";
  } catch (error) {
    statusMessage.value = `Error: ${error instanceof Error ? error.message : "Unknown error"}`;
    statusType.value = "error";
  } finally {
    isGenerating.value = false;
  }
}

function drawPreview() {
  const canvas = previewCanvas.value;
  if (!canvas || !generatedTrajectory.value) return;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  const { tracks, metadata } = generatedTrajectory.value;
  const scaleX = canvas.width / metadata.width;
  const scaleY = canvas.height / metadata.height;

  // Clear
  ctx.fillStyle = "#0a0a0a";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  // Draw trajectories
  const maxTracks = Math.min(tracks.length, 100); // Limit for performance
  const step = Math.max(1, Math.floor(tracks.length / maxTracks));

  for (let i = 0; i < tracks.length; i += step) {
    const track = tracks[i];
    if (track.length < 2) continue;

    // Color based on index
    const hue = (i / tracks.length) * 360;
    ctx.strokeStyle = `hsla(${hue}, 70%, 60%, 0.6)`;
    ctx.lineWidth = 1;

    ctx.beginPath();
    ctx.moveTo(track[0][0] * scaleX, track[0][1] * scaleY);

    for (let j = 1; j < track.length; j += 2) {
      ctx.lineTo(track[j][0] * scaleX, track[j][1] * scaleY);
    }

    ctx.stroke();

    // Draw start point
    ctx.fillStyle = `hsla(${hue}, 70%, 70%, 0.8)`;
    ctx.beginPath();
    ctx.arc(track[0][0] * scaleX, track[0][1] * scaleY, 2, 0, Math.PI * 2);
    ctx.fill();
  }

  // Draw frame info
  ctx.fillStyle = "rgba(255,255,255,0.5)";
  ctx.font = "10px monospace";
  ctx.fillText(`${tracks.length} pts × ${metadata.numFrames} frames`, 5, 12);
}

function _exportJSON() {
  if (!generatedTrajectory.value) return;

  const json = exportAsJSON(generatedTrajectory.value);
  downloadFile(json, "trajectory.json", "application/json");

  statusMessage.value = "Exported trajectory.json";
  statusType.value = "success";
}

function _exportForWanMove() {
  if (!generatedTrajectory.value) return;

  const npyData = exportAsNPYData(generatedTrajectory.value);

  // Export as JSON with shape info (for use with Python conversion)
  const exportData = {
    tracks: Array.from(npyData.tracks),
    visibility: Array.from(npyData.visibility),
    shape: npyData.shape,
    metadata: generatedTrajectory.value.metadata,
    _note: "Use numpy.array(tracks).reshape(shape.tracks) in Python",
  };

  downloadFile(
    JSON.stringify(exportData, null, 2),
    "wan_move_trajectory.json",
    "application/json",
  );

  statusMessage.value =
    "Exported wan_move_trajectory.json - reshape in Python for .npy";
  statusType.value = "success";
}

function downloadFile(content: string, filename: string, mimeType: string) {
  const blob = new Blob([content], { type: mimeType });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = filename;
  a.click();
  URL.revokeObjectURL(url);
}

// Watch for preset changes
watch(selectedPreset, (newPreset) => {
  if (newPreset !== "custom" && newPreset in FLOW_PRESETS) {
    const preset = FLOW_PRESETS[newPreset as keyof typeof FLOW_PRESETS];
    patternType.value = preset.pattern;
  }
});

// Initialize
onMounted(() => {
  if (dataAssets.value.length > 0) {
    selectedDataAsset.value = dataAssets.value[0].name;
  }
});
</script>

<style scoped>
.generative-flow-panel {
  padding: 12px;
  display: flex;
  flex-direction: column;
  gap: 12px;
  font-size: var(--lattice-font-sm, 12px);
  color: var(--lattice-text-primary, #e5e5e5);
}

.panel-header h3 {
  margin: 0;
  font-size: var(--lattice-font-md, 14px);
  font-weight: 600;
}

.subtitle {
  font-size: var(--lattice-font-xs, 11px);
  color: var(--lattice-text-muted, #6b7280);
}

.section {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.section-label {
  font-size: var(--lattice-font-xs, 11px);
  color: var(--lattice-text-secondary, #9ca3af);
  display: flex;
  align-items: center;
  gap: 6px;
}

.preset-select,
.pattern-select,
.data-select {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  padding: 6px 8px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: var(--lattice-font-sm, 12px);
}

.input-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.num-input,
.res-input {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  padding: 6px 8px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: var(--lattice-font-sm, 12px);
  width: 80px;
}

.res-input {
  width: 60px;
}

.input-hint {
  font-size: var(--lattice-font-xs, 11px);
  color: var(--lattice-text-muted, #6b7280);
}

.resolution-row {
  display: flex;
  align-items: center;
  gap: 6px;
}

.res-x {
  color: var(--lattice-text-muted, #6b7280);
}

.preset-btn,
.randomize-btn {
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  padding: 4px 8px;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: var(--lattice-font-xs, 11px);
  cursor: pointer;
}

.preset-btn:hover,
.randomize-btn:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.data-options {
  display: flex;
  flex-direction: column;
  gap: 6px;
  padding-left: 20px;
  margin-top: 4px;
}

.preview-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.preview-canvas {
  background: #0a0a0a;
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  width: 100%;
  aspect-ratio: 832 / 480;
}

.preview-btn {
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  padding: 8px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: var(--lattice-font-sm, 12px);
  cursor: pointer;
}

.preview-btn:hover:not(:disabled) {
  background: var(--lattice-accent, #8b5cf6);
}

.preview-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.actions {
  display: flex;
  gap: 8px;
}

.action-btn {
  flex: 1;
  padding: 8px 12px;
  border-radius: 4px;
  font-size: var(--lattice-font-sm, 12px);
  cursor: pointer;
  border: none;
}

.action-btn.secondary {
  background: var(--lattice-surface-3, #222222);
  color: var(--lattice-text-primary, #e5e5e5);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.action-btn.primary {
  background: var(--lattice-accent, #8b5cf6);
  color: white;
}

.action-btn:hover:not(:disabled) {
  filter: brightness(1.1);
}

.action-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.status {
  padding: 8px;
  border-radius: 4px;
  font-size: var(--lattice-font-xs, 11px);
}

.status.success {
  background: rgba(16, 185, 129, 0.2);
  color: #10b981;
}

.status.error {
  background: rgba(239, 68, 68, 0.2);
  color: #ef4444;
}

.status.info {
  background: rgba(139, 92, 246, 0.2);
  color: #8b5cf6;
}
</style>
