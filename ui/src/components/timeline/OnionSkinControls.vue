<!--
  @component OnionSkinControls
  @description Compact controls for onion skinning animation preview.
  Shows semi-transparent overlays of previous/next frames.

  @features
  - Toggle enable/disable
  - Preset selection (Traditional, Keyframes, Light, Heavy, etc.)
  - Frames before/after sliders
  - Opacity falloff mode
  - Color tint customization
-->
<template>
  <div class="onion-skin-controls" ref="containerRef">
    <button
      class="onion-toggle-btn"
      :class="{ active: config.enabled }"
      @click="toggleDropdown"
      :title="config.enabled ? 'Onion Skinning On (click to configure)' : 'Onion Skinning Off (click to configure)'"
    >
      <span class="onion-icon">🧅</span>
      <span v-if="config.enabled" class="status-dot active"></span>
    </button>

    <Teleport to="body">
      <div
        v-if="showDropdown"
        class="onion-dropdown"
        :style="dropdownStyle"
        @click.stop
      >
        <div class="dropdown-header">
          <span class="dropdown-title">Onion Skinning</span>
          <label class="enable-toggle">
            <input type="checkbox" v-model="config.enabled" @change="updateConfig" />
            <span>{{ config.enabled ? 'On' : 'Off' }}</span>
          </label>
        </div>

        <div class="dropdown-body" :class="{ disabled: !config.enabled }">
          <!-- Presets -->
          <div class="control-row">
            <label>Preset</label>
            <select v-model="selectedPreset" @change="applyPreset" :disabled="!config.enabled">
              <option value="">Custom</option>
              <option value="traditional">Traditional</option>
              <option value="keyframes">Keyframes Only</option>
              <option value="light">Light</option>
              <option value="heavy">Heavy</option>
              <option value="motionArc">Motion Arc</option>
              <option value="cycle">Cycle Preview</option>
            </select>
          </div>

          <!-- Frames Before/After -->
          <div class="control-row dual">
            <div class="control-half">
              <label>Before</label>
              <div class="value-input">
                <input
                  type="range"
                  min="0"
                  max="10"
                  v-model.number="config.framesBefore"
                  @input="updateConfig"
                  :disabled="!config.enabled"
                />
                <span class="value">{{ config.framesBefore }}</span>
              </div>
            </div>
            <div class="control-half">
              <label>After</label>
              <div class="value-input">
                <input
                  type="range"
                  min="0"
                  max="10"
                  v-model.number="config.framesAfter"
                  @input="updateConfig"
                  :disabled="!config.enabled"
                />
                <span class="value">{{ config.framesAfter }}</span>
              </div>
            </div>
          </div>

          <!-- Opacity -->
          <div class="control-row">
            <label>Max Opacity</label>
            <div class="value-input">
              <input
                type="range"
                min="0.1"
                max="1"
                step="0.05"
                v-model.number="config.maxOpacity"
                @input="updateConfig"
                :disabled="!config.enabled"
              />
              <span class="value">{{ Math.round(config.maxOpacity * 100) }}%</span>
            </div>
          </div>

          <!-- Falloff -->
          <div class="control-row">
            <label>Falloff</label>
            <select v-model="config.opacityFalloff" @change="updateConfig" :disabled="!config.enabled">
              <option value="linear">Linear</option>
              <option value="exponential">Exponential</option>
              <option value="constant">Constant</option>
            </select>
          </div>

          <!-- Colors -->
          <div class="control-row dual">
            <div class="control-half">
              <label>Past</label>
              <input
                type="color"
                v-model="config.beforeColor"
                @input="updateConfig"
                :disabled="!config.enabled"
                class="color-input"
              />
            </div>
            <div class="control-half">
              <label>Future</label>
              <input
                type="color"
                v-model="config.afterColor"
                @input="updateConfig"
                :disabled="!config.enabled"
                class="color-input"
              />
            </div>
          </div>

          <!-- Tint Intensity -->
          <div class="control-row">
            <label>Tint</label>
            <div class="value-input">
              <input
                type="range"
                min="0"
                max="1"
                step="0.05"
                v-model.number="config.tintIntensity"
                @input="updateConfig"
                :disabled="!config.enabled"
              />
              <span class="value">{{ Math.round(config.tintIntensity * 100) }}%</span>
            </div>
          </div>

          <!-- Spacing -->
          <div class="control-row">
            <label>Frame Spacing</label>
            <div class="value-input">
              <input
                type="range"
                min="1"
                max="5"
                v-model.number="config.spacing"
                @input="updateConfig"
                :disabled="!config.enabled"
              />
              <span class="value">{{ config.spacing }}</span>
            </div>
          </div>

          <!-- Keyframes Only Toggle -->
          <div class="control-row checkbox-row">
            <label>
              <input
                type="checkbox"
                v-model="config.keyframesOnly"
                @change="updateConfig"
                :disabled="!config.enabled"
              />
              <span>Keyframes only</span>
            </label>
          </div>
        </div>
      </div>
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import {
  type CSSProperties,
  computed,
  onMounted,
  onUnmounted,
  reactive,
  ref,
  watch,
} from "vue";
import {
  DEFAULT_ONION_SKIN_CONFIG,
  type OnionSkinConfig,
  onionSkinning,
} from "@/services/onionSkinning";

// Emit for parent components
const emit =
  defineEmits<(e: "configChanged", config: OnionSkinConfig) => void>();

// Refs
const containerRef = ref<HTMLElement | null>(null);
const showDropdown = ref(false);
const selectedPreset = ref("");

// Local config copy (reactive)
const config = reactive<OnionSkinConfig>({ ...DEFAULT_ONION_SKIN_CONFIG });

// Dropdown position
// Explicitly typed to satisfy Vue's style binding requirements
const dropdownStyle = computed((): CSSProperties => {
  if (!containerRef.value) return {};

  const rect = containerRef.value.getBoundingClientRect();
  return {
    position: "fixed",
    top: `${rect.bottom + 4}px`,
    left: `${rect.left}px`,
    zIndex: 10000,
  };
});

// Toggle dropdown
function toggleDropdown() {
  showDropdown.value = !showDropdown.value;
}

// Close dropdown when clicking outside
function handleClickOutside(e: MouseEvent) {
  if (
    showDropdown.value &&
    containerRef.value &&
    !containerRef.value.contains(e.target as Node)
  ) {
    // Check if click is inside dropdown
    const dropdown = document.querySelector(".onion-dropdown");
    if (dropdown && !dropdown.contains(e.target as Node)) {
      showDropdown.value = false;
    }
  }
}

// Update service config
function updateConfig() {
  onionSkinning.setConfig(config);
  selectedPreset.value = ""; // Clear preset when manually editing
  emit("configChanged", { ...config });
}

// Apply preset
function applyPreset() {
  if (selectedPreset.value) {
    onionSkinning.applyPreset(selectedPreset.value);
    Object.assign(config, onionSkinning.getConfig());
    emit("configChanged", { ...config });
  }
}

// Sync local config with service on mount
onMounted(() => {
  Object.assign(config, onionSkinning.getConfig());
  document.addEventListener("click", handleClickOutside);
});

onUnmounted(() => {
  document.removeEventListener("click", handleClickOutside);
});

// Watch for external config changes
watch(
  () => onionSkinning.getConfig(),
  (newConfig) => {
    Object.assign(config, newConfig);
  },
  { deep: true },
);
</script>

<style scoped>
.onion-skin-controls {
  position: relative;
  display: inline-flex;
  align-items: center;
}

.onion-toggle-btn {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-md, 4px);
  color: var(--lattice-text-secondary, #9ca3af);
  cursor: pointer;
  transition: all 0.15s ease;
  font-size: 12px;
}

.onion-toggle-btn:hover {
  background: var(--lattice-surface-3, #222222);
  border-color: var(--lattice-border-hover, #444444);
}

.onion-toggle-btn.active {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
  border-color: var(--lattice-accent, #8b5cf6);
  color: var(--lattice-text-primary, #e5e5e5);
}

.onion-icon {
  font-size: 14px;
}

.status-dot {
  width: 6px;
  height: 6px;
  border-radius: 50%;
  background: var(--lattice-accent, #8b5cf6);
}

.status-dot.active {
  animation: pulse 2s infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.5; }
}

/* Dropdown */
.onion-dropdown {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #333333);
  border-radius: var(--lattice-radius-lg, 8px);
  box-shadow: var(--lattice-shadow-dropdown, 0 4px 12px rgba(0,0,0,0.3));
  min-width: 280px;
  overflow: hidden;
}

.dropdown-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 10px 12px;
  background: var(--lattice-surface-3, #222222);
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.dropdown-title {
  font-weight: 600;
  font-size: 13px;
  color: var(--lattice-text-primary, #e5e5e5);
}

.enable-toggle {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  font-size: 12px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.enable-toggle input {
  width: 14px;
  height: 14px;
  accent-color: var(--lattice-accent, #8b5cf6);
}

.dropdown-body {
  padding: 12px;
  display: flex;
  flex-direction: column;
  gap: 10px;
}

.dropdown-body.disabled {
  opacity: 0.5;
  pointer-events: none;
}

.control-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.control-row > label {
  flex: 0 0 80px;
  font-size: 11px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.control-row select {
  flex: 1;
  padding: 4px 8px;
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-sm, 2px);
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 11px;
}

.control-row.dual {
  gap: 12px;
}

.control-half {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 6px;
}

.control-half label {
  flex: 0 0 40px;
  font-size: 11px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.value-input {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 6px;
}

.value-input input[type="range"] {
  flex: 1;
  height: 4px;
  accent-color: var(--lattice-accent, #8b5cf6);
}

.value-input .value {
  flex: 0 0 30px;
  text-align: right;
  font-size: 10px;
  color: var(--lattice-text-muted, #6b7280);
  font-variant-numeric: tabular-nums;
}

.color-input {
  width: 24px;
  height: 24px;
  padding: 0;
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: var(--lattice-radius-sm, 2px);
  cursor: pointer;
}

.checkbox-row {
  padding-top: 4px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.checkbox-row label {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
}

.checkbox-row input[type="checkbox"] {
  width: 14px;
  height: 14px;
  accent-color: var(--lattice-accent, #8b5cf6);
}

.checkbox-row span {
  font-size: 11px;
  color: var(--lattice-text-secondary, #9ca3af);
}
</style>
