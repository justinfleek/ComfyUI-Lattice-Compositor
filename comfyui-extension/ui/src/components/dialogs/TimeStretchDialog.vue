<!--
  @component TimeStretchDialog
  @description Dialog for time stretch operations on video/nested comp layers.
  Provides Stretch Factor percentage control and Hold In Place pivot options.

  @features
  - Stretch Factor percentage (100% = normal, 200% = half speed, 50% = double speed)
  - Hold In Place options: Layer In-point, Current Frame, Layer Out-point
  - Preview of new duration
  - Keyboard shortcut: Ctrl+Shift+Alt+R
-->
<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="cancel">
      <div class="dialog-container">
        <div class="dialog-header">
          <h2>Time Stretch</h2>
          <button class="close-btn" @click="cancel" title="Close">&times;</button>
        </div>

        <div class="dialog-body">
          <!-- Original Info -->
          <div class="info-section">
            <div class="info-row">
              <span class="info-label">Original Duration:</span>
              <span class="info-value">{{ formatDuration(originalDuration) }}</span>
            </div>
            <div class="info-row">
              <span class="info-label">Original Speed:</span>
              <span class="info-value">{{ (100 / currentStretchFactor).toFixed(1) }}%</span>
            </div>
          </div>

          <!-- Stretch Factor -->
          <div class="control-section">
            <div class="control-row">
              <label for="stretch-factor">Stretch Factor:</label>
              <div class="input-group">
                <input
                  id="stretch-factor"
                  type="number"
                  v-model.number="stretchFactor"
                  min="10"
                  max="1000"
                  step="1"
                  class="stretch-input"
                  @input="updatePreview"
                />
                <span class="unit">%</span>
              </div>
            </div>
            <p class="hint">
              100% = normal speed, 200% = half speed (2x duration), 50% = double speed (0.5x duration)
            </p>

            <!-- Speed presets -->
            <div class="presets">
              <button
                v-for="preset in speedPresets"
                :key="preset.value"
                class="preset-btn"
                :class="{ active: stretchFactor === preset.value }"
                @click="stretchFactor = preset.value; updatePreview()"
              >
                {{ preset.label }}
              </button>
            </div>
          </div>

          <!-- Hold In Place -->
          <div class="control-section">
            <div class="control-row">
              <label for="hold-in-place">Hold In Place:</label>
              <select id="hold-in-place" v-model="holdInPlace" class="select-input">
                <option value="in-point">Layer In-point</option>
                <option value="current-frame">Current Frame</option>
                <option value="out-point">Layer Out-point</option>
              </select>
            </div>
            <p class="hint">
              The layer will stretch from this anchor point.
            </p>
          </div>

          <!-- New Duration Preview -->
          <div class="preview-section">
            <div class="info-row highlight">
              <span class="info-label">New Duration:</span>
              <span class="info-value">{{ formatDuration(newDuration) }}</span>
            </div>
            <div class="info-row highlight">
              <span class="info-label">Effective Speed:</span>
              <span class="info-value">{{ effectiveSpeed.toFixed(1) }}%</span>
            </div>
          </div>

          <!-- Reverse Option -->
          <div class="control-section">
            <label class="checkbox-row">
              <input type="checkbox" v-model="reversePlayback" />
              <span>Reverse Playback</span>
            </label>
          </div>
        </div>

        <div class="dialog-footer">
          <button class="btn btn-secondary" @click="reset">Reset</button>
          <div class="spacer"></div>
          <button class="btn btn-secondary" @click="cancel">Cancel</button>
          <button class="btn btn-primary" @click="apply">Apply</button>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref, watch } from "vue";
import { useProjectStore } from "@/stores/projectStore";
import { useLayerStore } from "@/stores/layerStore";
import { useAnimationStore } from "@/stores/animationStore";
import type { Layer, NestedCompData, VideoData } from "@/types/project";

const props = defineProps<{
  visible: boolean;
  layerId: string;
}>();

const emit = defineEmits<{
  (e: "close"): void;
  (e: "applied"): void;
}>();

const projectStore = useProjectStore();
const layerStore = useLayerStore();
const animationStore = useAnimationStore();

// State
const stretchFactor = ref(100);
const holdInPlace = ref<"in-point" | "current-frame" | "out-point">("in-point");
const reversePlayback = ref(false);
const originalDuration = ref(0);
const currentStretchFactor = ref(100);

// Speed presets
const speedPresets = [
  { label: "25%", value: 400 }, // Quarter speed
  { label: "50%", value: 200 }, // Half speed
  { label: "100%", value: 100 }, // Normal
  { label: "200%", value: 50 }, // Double speed
  { label: "400%", value: 25 }, // 4x speed
];

// Computed
const layer = computed<Layer | undefined>(() => {
  return projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
});

const newDuration = computed(() => {
  return originalDuration.value * (stretchFactor.value / 100);
});

const effectiveSpeed = computed(() => {
  const speed = (100 / stretchFactor.value) * 100;
  return reversePlayback.value ? -speed : speed;
});

// Initialize when dialog opens
watch(
  () => props.visible,
  (visible) => {
    if (visible && layer.value) {
      initializeFromLayer();
    }
  },
);

function initializeFromLayer() {
  if (!layer.value) return;

  const data = layer.value.data as VideoData | NestedCompData;

  // Calculate original duration from layer
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.value.startFrame/endFrame ∈ number | undefined → number (defaults)
  const layerValue = layer.value;
  const startFrame = (typeof layerValue === "object" && layerValue !== null && "startFrame" in layerValue && typeof layerValue.startFrame === "number" && Number.isFinite(layerValue.startFrame)) ? layerValue.startFrame : 0;
  const endFrame = (typeof layerValue === "object" && layerValue !== null && "endFrame" in layerValue && typeof layerValue.endFrame === "number" && Number.isFinite(layerValue.endFrame)) ? layerValue.endFrame : projectStore.getFrameCount();
  const fps = projectStore.getFps() || 30;
  originalDuration.value = (endFrame - startFrame) / fps;

  // Get current speed/stretch factor
  if ("speed" in data && data.speed) {
    currentStretchFactor.value = 100 / data.speed;
    stretchFactor.value = currentStretchFactor.value;
    reversePlayback.value = data.speed < 0;
  } else {
    currentStretchFactor.value = 100;
    stretchFactor.value = 100;
    reversePlayback.value = false;
  }
}

function updatePreview() {
  // Preview calculations are automatic via computed properties
}

function reset() {
  stretchFactor.value = 100;
  reversePlayback.value = false;
  holdInPlace.value = "in-point";
}

function cancel() {
  emit("close");
}

function apply() {
  if (!layer.value) return;

  const speed = (reversePlayback.value ? -1 : 1) * (100 / stretchFactor.value);
  const fps = projectStore.getFps() || 30;

  // Calculate new layer bounds based on hold in place
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.value.startFrame/endFrame ∈ number | undefined → number (defaults)
  const layerValue = layer.value;
  let newStartFrame = (typeof layerValue === "object" && layerValue !== null && "startFrame" in layerValue && typeof layerValue.startFrame === "number" && Number.isFinite(layerValue.startFrame)) ? layerValue.startFrame : 0;
  let newEndFrame = (typeof layerValue === "object" && layerValue !== null && "endFrame" in layerValue && typeof layerValue.endFrame === "number" && Number.isFinite(layerValue.endFrame)) ? layerValue.endFrame : projectStore.getFrameCount();
  const currentDurationFrames = newEndFrame - newStartFrame;
  const newDurationFrames = Math.round(
    currentDurationFrames * (stretchFactor.value / currentStretchFactor.value),
  );

  switch (holdInPlace.value) {
    case "in-point":
      // Stretch from start
      newEndFrame = newStartFrame + newDurationFrames;
      break;
    case "current-frame": {
      // Stretch around current frame
      const currentFrame = animationStore.currentFrame;
      const ratio = (currentFrame - newStartFrame) / currentDurationFrames;
      newStartFrame = Math.round(currentFrame - ratio * newDurationFrames);
      newEndFrame = newStartFrame + newDurationFrames;
      break;
    }
    case "out-point":
      // Stretch from end
      newStartFrame = newEndFrame - newDurationFrames;
      break;
  }

  // Apply time stretch
  layerStore.timeStretchLayer(props.layerId, {
    stretchFactor: stretchFactor.value,
    holdInPlace: holdInPlace.value,
    reverse: reversePlayback.value,
    newStartFrame,
    newEndFrame,
    speed,
  });

  emit("applied");
  emit("close");
}

function formatDuration(seconds: number): string {
  const mins = Math.floor(seconds / 60);
  const secs = Math.floor(seconds % 60);
  const frames = Math.floor((seconds % 1) * (projectStore.getFps() || 30));
  return `${mins}:${secs.toString().padStart(2, "0")}:${frames.toString().padStart(2, "0")}`;
}

// Keyboard shortcut handler
function handleKeyDown(e: KeyboardEvent) {
  if (!props.visible) return;

  if (e.key === "Escape") {
    cancel();
  } else if (e.key === "Enter" && !e.shiftKey) {
    apply();
  }
}

onMounted(() => {
  document.addEventListener("keydown", handleKeyDown);
});

onUnmounted(() => {
  document.removeEventListener("keydown", handleKeyDown);
});
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.dialog-container {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: var(--lattice-radius-lg, 8px);
  box-shadow: var(--lattice-shadow-panel, 0 8px 32px rgba(0,0,0,0.4));
  min-width: 380px;
  max-width: 480px;
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 16px 20px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.dialog-header h2 {
  margin: 0;
  font-size: 16px;
  font-weight: 600;
  color: var(--lattice-text-primary, #e5e5e5);
}

.close-btn {
  background: none;
  border: none;
  color: var(--lattice-text-muted, #6b7280);
  font-size: 20px;
  cursor: pointer;
  padding: 4px 8px;
  border-radius: var(--lattice-radius-sm, 2px);
}

.close-btn:hover {
  color: var(--lattice-text-primary, #e5e5e5);
  background: var(--lattice-surface-3, #222);
}

.dialog-body {
  padding: 20px;
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.info-section {
  background: var(--lattice-surface-1, #121212);
  border-radius: var(--lattice-radius-md, 4px);
  padding: 12px;
}

.info-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 4px 0;
}

.info-row.highlight {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.1));
  padding: 8px 12px;
  border-radius: var(--lattice-radius-md, 4px);
  margin: 4px 0;
}

.info-label {
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 13px;
}

.info-value {
  color: var(--lattice-text-primary, #e5e5e5);
  font-family: monospace;
  font-size: 13px;
}

.control-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.control-row {
  display: flex;
  align-items: center;
  gap: 12px;
}

.control-row label {
  width: 120px;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 13px;
  flex-shrink: 0;
}

.input-group {
  display: flex;
  align-items: center;
  gap: 4px;
}

.stretch-input {
  width: 80px;
  padding: 6px 10px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-sm, 2px);
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 14px;
  text-align: right;
}

.stretch-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8b5cf6);
}

.unit {
  color: var(--lattice-text-muted, #6b7280);
  font-size: 13px;
}

.select-input {
  flex: 1;
  padding: 6px 10px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-sm, 2px);
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 13px;
  cursor: pointer;
}

.select-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8b5cf6);
}

.hint {
  font-size: 11px;
  color: var(--lattice-text-muted, #6b7280);
  margin: 0;
  font-style: italic;
}

.presets {
  display: flex;
  gap: 8px;
  flex-wrap: wrap;
}

.preset-btn {
  padding: 4px 12px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-pill, 999px);
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 12px;
  cursor: pointer;
  transition: all 0.15s ease;
}

.preset-btn:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.preset-btn.active {
  background: var(--lattice-accent, #8b5cf6);
  border-color: var(--lattice-accent, #8b5cf6);
  color: white;
}

.preview-section {
  background: var(--lattice-surface-1, #121212);
  border-radius: var(--lattice-radius-md, 4px);
  padding: 12px;
}

.checkbox-row {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 13px;
}

.checkbox-row input {
  width: 16px;
  height: 16px;
  accent-color: var(--lattice-accent, #8b5cf6);
}

.dialog-footer {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 16px 20px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.spacer {
  flex: 1;
}

.btn {
  padding: 8px 16px;
  border-radius: var(--lattice-radius-md, 4px);
  font-size: 13px;
  font-weight: 500;
  cursor: pointer;
  transition: all 0.15s ease;
}

.btn-secondary {
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  color: var(--lattice-text-secondary, #9ca3af);
}

.btn-secondary:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.btn-primary {
  background: var(--lattice-accent, #8b5cf6);
  border: 1px solid var(--lattice-accent, #8b5cf6);
  color: white;
}

.btn-primary:hover {
  background: var(--lattice-accent-hover, #a78bfa);
  border-color: var(--lattice-accent-hover, #a78bfa);
}
</style>
