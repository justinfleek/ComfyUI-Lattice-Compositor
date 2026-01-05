<!--
  @component FpsSelectDialog
  @description Dialog shown when video fps cannot be detected.
  User must select the correct fps for the imported video.
-->
<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="cancel">
      <div class="dialog-container">
        <div class="dialog-header">
          <h2>Select Video Frame Rate</h2>
          <button class="close-btn" @click="cancel" title="Close">&times;</button>
        </div>

        <div class="dialog-body">
          <!-- Info Section -->
          <div class="info-section">
            <p class="info-text">
              Unable to detect frame rate for <strong>{{ fileName }}</strong>.
            </p>
            <p class="info-subtext">
              Please select the correct frame rate for this video.
            </p>
          </div>

          <!-- FPS Options -->
          <div class="fps-options">
            <button
              v-for="fps in fpsOptions"
              :key="fps.value"
              class="fps-btn"
              :class="{ selected: selectedFps === fps.value }"
              @click="selectedFps = fps.value"
            >
              <span class="fps-value">{{ fps.value }}</span>
              <span class="fps-label">{{ fps.label }}</span>
            </button>
          </div>

          <!-- Custom FPS -->
          <div class="custom-fps">
            <label>
              <input
                type="checkbox"
                v-model="useCustomFps"
                @change="onCustomToggle"
              />
              Custom frame rate
            </label>
            <input
              v-if="useCustomFps"
              type="number"
              v-model.number="customFpsValue"
              min="1"
              max="120"
              step="0.001"
              class="custom-input"
              placeholder="e.g., 23.976"
            />
          </div>
        </div>

        <div class="dialog-footer">
          <button class="btn btn-secondary" @click="cancel">Cancel</button>
          <button
            class="btn btn-primary"
            @click="confirm"
            :disabled="!effectiveFps"
          >
            Import at {{ effectiveFps || '?' }} fps
          </button>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref, watch } from "vue";

const props = defineProps<{
  visible: boolean;
  fileName: string;
  videoDuration: number;
}>();

const emit = defineEmits<{
  (e: "confirm", fps: number): void;
  (e: "cancel"): void;
}>();

// Common fps options with descriptions
const fpsOptions = [
  { value: 8, label: "AnimateDiff" },
  { value: 16, label: "WAN / Mochi" },
  { value: 24, label: "Film" },
  { value: 30, label: "Standard" },
  { value: 60, label: "High FR" },
];

const selectedFps = ref<number>(16); // Default to WAN standard
const useCustomFps = ref(false);
const customFpsValue = ref<number>(30);

const effectiveFps = computed(() => {
  if (useCustomFps.value) {
    return customFpsValue.value > 0 ? customFpsValue.value : null;
  }
  return selectedFps.value;
});

// Frame count preview
const _frameCountPreview = computed(() => {
  if (!effectiveFps.value || !props.videoDuration) return null;
  return Math.ceil(props.videoDuration * effectiveFps.value);
});

function _onCustomToggle() {
  if (useCustomFps.value) {
    customFpsValue.value = selectedFps.value;
  }
}

function confirm() {
  if (effectiveFps.value) {
    emit("confirm", effectiveFps.value);
  }
}

function cancel() {
  emit("cancel");
}

// Keyboard handler
function handleKeyDown(e: KeyboardEvent) {
  if (!props.visible) return;

  if (e.key === "Escape") {
    cancel();
  } else if (e.key === "Enter" && effectiveFps.value) {
    confirm();
  } else if (e.key >= "1" && e.key <= "5" && !useCustomFps.value) {
    const index = parseInt(e.key, 10) - 1;
    if (fpsOptions[index]) {
      selectedFps.value = fpsOptions[index].value;
    }
  }
}

// Reset selection when dialog opens
watch(
  () => props.visible,
  (visible) => {
    if (visible) {
      selectedFps.value = 16;
      useCustomFps.value = false;
      customFpsValue.value = 30;
    }
  },
);

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
  max-width: 450px;
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
  margin: 0 0 4px 0;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 13px;
}

.info-text strong {
  color: var(--lattice-warning, #f59e0b);
}

.info-subtext {
  margin: 0;
  color: var(--lattice-text-muted, #6b7280);
  font-size: 12px;
}

.fps-options {
  display: grid;
  grid-template-columns: repeat(5, 1fr);
  gap: 8px;
}

.fps-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 2px;
  padding: 12px 8px;
  background: var(--lattice-surface-3, #222);
  border: 2px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-md, 4px);
  cursor: pointer;
  transition: all 0.15s ease;
}

.fps-btn:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  border-color: var(--lattice-border-default, #333);
}

.fps-btn.selected {
  background: var(--lattice-accent-subtle, rgba(139, 92, 246, 0.15));
  border-color: var(--lattice-accent, #8b5cf6);
}

.fps-value {
  font-size: 18px;
  font-weight: 600;
  color: var(--lattice-text-primary, #e5e5e5);
  font-family: monospace;
}

.fps-label {
  font-size: 10px;
  color: var(--lattice-text-muted, #6b7280);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.fps-btn.selected .fps-value {
  color: var(--lattice-accent, #8b5cf6);
}

.custom-fps {
  display: flex;
  align-items: center;
  gap: 12px;
}

.custom-fps label {
  display: flex;
  align-items: center;
  gap: 8px;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 13px;
  cursor: pointer;
}

.custom-fps input[type="checkbox"] {
  width: 16px;
  height: 16px;
  cursor: pointer;
}

.custom-input {
  flex: 1;
  max-width: 120px;
  padding: 8px 12px;
  background: var(--lattice-surface-1, #121212);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-md, 4px);
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 13px;
  font-family: monospace;
}

.custom-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8b5cf6);
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

.btn-primary {
  background: var(--lattice-accent, #8b5cf6);
  border: none;
  color: white;
}

.btn-primary:hover:not(:disabled) {
  background: var(--lattice-accent-hover, #7c3aed);
}

.btn-primary:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}
</style>
