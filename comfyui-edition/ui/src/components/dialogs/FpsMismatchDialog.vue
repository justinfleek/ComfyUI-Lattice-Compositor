<!--
  @component FpsMismatchDialog
  @description Dialog shown when importing video/sequence with different fps than composition.
  Provides three options: Match (precomp existing, change fps), Conform (time-stretch), Cancel.
-->
<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="cancel">
      <div class="dialog-container">
        <div class="dialog-header">
          <h2>Frame Rate Mismatch</h2>
          <button class="close-btn" @click="cancel" title="Close">&times;</button>
        </div>

        <div class="dialog-body">
          <!-- Info Section -->
          <div class="info-section">
            <p class="info-text">
              <strong>{{ fileName }}</strong> has a different frame rate than the composition.
            </p>
            <div class="fps-comparison">
              <div class="fps-item">
                <span class="fps-label">Imported content:</span>
                <span class="fps-value">{{ importedFps }} fps</span>
              </div>
              <div class="fps-item">
                <span class="fps-label">Composition:</span>
                <span class="fps-value">{{ compositionFps }} fps</span>
              </div>
            </div>
          </div>

          <!-- Options Section -->
          <div class="options-section">
            <button
              class="option-btn match-btn"
              @click="handleMatch"
              :title="`Change composition to ${importedFps} fps. Existing layers will be precomposed at ${compositionFps} fps.`"
            >
              <div class="option-content">
                <span class="option-title">Match composition to {{ importedFps }} fps</span>
                <span class="option-desc">
                  Existing layers will be precomposed at {{ compositionFps }} fps.
                  All {{ importedFps }} video frames will be shown.
                </span>
              </div>
            </button>

            <button
              class="option-btn conform-btn"
              @click="handleConform"
              :title="`Keep composition at ${compositionFps} fps. Video will be time-stretched.`"
            >
              <div class="option-content">
                <span class="option-title">Conform video to {{ compositionFps }} fps</span>
                <span class="option-desc">
                  Video will be time-stretched to match composition.
                  Duration: {{ conformedDuration }}
                </span>
              </div>
            </button>
          </div>
        </div>

        <div class="dialog-footer">
          <button class="btn btn-secondary" @click="cancel">Cancel</button>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted } from "vue";

const props = defineProps<{
  visible: boolean;
  fileName: string;
  importedFps: number;
  compositionFps: number;
  videoDuration: number; // in seconds
}>();

const emit = defineEmits<{
  (e: "match"): void;
  (e: "conform"): void;
  (e: "cancel"): void;
}>();

// Calculate what duration would be after conforming (time-stretch)
const conformedDuration = computed(() => {
  // If video is 30fps and comp is 16fps, video plays slower
  // stretchFactor = compositionFps / importedFps
  const stretchFactor = props.compositionFps / props.importedFps;
  const newDuration = props.videoDuration / stretchFactor;
  return formatDuration(newDuration);
});

function formatDuration(seconds: number): string {
  const mins = Math.floor(seconds / 60);
  const secs = (seconds % 60).toFixed(2);
  if (mins > 0) {
    return `${mins}m ${secs}s`;
  }
  return `${secs}s`;
}

function handleMatch() {
  emit("match");
}

function handleConform() {
  emit("conform");
}

function cancel() {
  emit("cancel");
}

// Keyboard handler
function handleKeyDown(e: KeyboardEvent) {
  if (!props.visible) return;

  if (e.key === "Escape") {
    cancel();
  } else if (e.key === "1") {
    handleMatch();
  } else if (e.key === "2") {
    handleConform();
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
  min-width: 420px;
  max-width: 500px;
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
  padding: 16px;
}

.info-text {
  margin: 0 0 12px 0;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 13px;
}

.info-text strong {
  color: var(--lattice-accent, #8b5cf6);
}

.fps-comparison {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.fps-item {
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.fps-label {
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 13px;
}

.fps-value {
  color: var(--lattice-text-primary, #e5e5e5);
  font-family: monospace;
  font-size: 14px;
  font-weight: 600;
}

.options-section {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.option-btn {
  display: flex;
  align-items: flex-start;
  padding: 16px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-md, 4px);
  cursor: pointer;
  text-align: left;
  transition: all 0.15s ease;
}

.option-btn:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  border-color: var(--lattice-border-default, #333);
}

.option-btn:focus {
  outline: none;
  border-color: var(--lattice-accent, #8b5cf6);
}

.match-btn:hover {
  border-color: var(--lattice-accent, #8b5cf6);
}

.conform-btn:hover {
  border-color: var(--lattice-warning, #f59e0b);
}

.option-content {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.option-title {
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 14px;
  font-weight: 500;
}

.option-desc {
  color: var(--lattice-text-muted, #6b7280);
  font-size: 12px;
  line-height: 1.4;
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  padding: 16px 20px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
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
</style>
