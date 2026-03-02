<!--
  @component CurveEditorHeader
  @description Header toolbar for the Curve Editor with mode toggle, presets, and tools.
  Extracted from CurveEditor.vue to reduce file size.
-->
<template>
  <div class="curve-header">
    <span class="curve-title">Curve Editor</span>

    <!-- Mode toggle -->
    <div class="mode-toggle">
      <button
        :class="{ active: mode === 'value' }"
        @click="$emit('update:mode', 'value')"
        title="Value Graph"
      >
        Value
      </button>
      <button
        :class="{ active: mode === 'speed' }"
        @click="$emit('update:mode', 'speed')"
        title="Speed Graph"
      >
        Speed
      </button>
    </div>

    <!-- Easing presets -->
    <div class="preset-buttons">
      <button
        v-for="preset in presetList"
        :key="preset.key"
        class="preset-btn"
        :class="{ active: isPresetActive(preset.key) }"
        @click="$emit('applyPreset', preset.key)"
        :title="preset.label"
      >
        {{ preset.shortLabel }}
      </button>
    </div>

    <!-- Tools -->
    <div class="toolbar">
      <button @click="$emit('fitToView')" title="Fit to View">
        <span class="icon">[ ]</span>
      </button>
      <button
        @click="$emit('update:autoSelectNearby', !autoSelectNearby)"
        :class="{ active: autoSelectNearby }"
        title="Auto-select Nearby Keyframes"
      >
        <span class="icon">A</span>
      </button>
      <button
        @click="$emit('update:snapEnabled', !snapEnabled)"
        :class="{ active: snapEnabled }"
        title="Snap to Grid"
      >
        <span class="icon">#</span>
      </button>
    </div>

    <button class="close-btn" @click="$emit('close')">
      <span class="icon">X</span>
    </button>
  </div>
</template>

<script setup lang="ts">
export type CurveMode = "value" | "speed";

export interface EasingPreset {
  key: string;
  label: string;
  shortLabel: string;
}

defineProps<{
  mode: CurveMode;
  presetList: EasingPreset[];
  autoSelectNearby: boolean;
  snapEnabled: boolean;
  isPresetActive: (key: string) => boolean;
}>();

defineEmits<{
  "update:mode": [mode: CurveMode];
  "update:autoSelectNearby": [value: boolean];
  "update:snapEnabled": [value: boolean];
  applyPreset: [key: string];
  fitToView: [];
  close: [];
}>();
</script>

<style scoped>
.curve-header {
  display: flex;
  align-items: center;
  gap: 12px;
  padding: 6px 12px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border, #333);
}

.curve-title {
  font-size: 12px;
  font-weight: 600;
  color: var(--lattice-accent, #8b5cf6);
}

.mode-toggle {
  display: flex;
  gap: 2px;
  background: var(--lattice-surface-1, #121212);
  border-radius: 4px;
  padding: 2px;
}

.mode-toggle button {
  padding: 4px 8px;
  background: transparent;
  border: none;
  color: var(--lattice-text-secondary, #888);
  cursor: pointer;
  font-size: 10px;
  border-radius: 3px;
  transition: all 0.15s ease;
}

.mode-toggle button.active {
  background: var(--lattice-accent-dim, rgba(139, 92, 246, 0.2));
  color: var(--lattice-accent, #8b5cf6);
}

.mode-toggle button:hover:not(.active) {
  color: var(--lattice-text-primary, #e5e5e5);
}

.preset-buttons {
  display: flex;
  gap: 4px;
}

.preset-btn {
  padding: 4px 6px;
  background: var(--lattice-surface-3, #252525);
  border: 1px solid var(--lattice-border, #333);
  color: var(--lattice-text-secondary, #888);
  font-size: 9px;
  cursor: pointer;
  border-radius: 3px;
  transition: all 0.15s ease;
}

.preset-btn:hover {
  border-color: var(--lattice-accent, #8b5cf6);
  color: var(--lattice-text-primary, #e5e5e5);
}

.preset-btn.active {
  background: var(--lattice-accent-dim, rgba(139, 92, 246, 0.2));
  border-color: var(--lattice-accent, #8b5cf6);
  color: var(--lattice-accent, #8b5cf6);
}

.toolbar {
  display: flex;
  gap: 4px;
  margin-left: auto;
}

.toolbar button {
  width: 28px;
  height: 24px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--lattice-surface-3, #252525);
  border: 1px solid var(--lattice-border, #333);
  color: var(--lattice-text-secondary, #888);
  cursor: pointer;
  border-radius: 4px;
  font-size: 12px;
  transition: all 0.15s ease;
}

.toolbar button:hover {
  border-color: var(--lattice-accent, #8b5cf6);
  color: var(--lattice-text-primary, #e5e5e5);
}

.toolbar button.active {
  background: var(--lattice-accent-dim, rgba(139, 92, 246, 0.2));
  border-color: var(--lattice-accent, #8b5cf6);
  color: var(--lattice-accent, #8b5cf6);
}

.close-btn {
  width: 24px;
  height: 24px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: transparent;
  border: none;
  color: var(--lattice-text-secondary, #888);
  cursor: pointer;
  border-radius: 4px;
  font-size: 14px;
  transition: all 0.15s ease;
}

.close-btn:hover {
  background: var(--lattice-error, #f43f5e);
  color: white;
}

.icon {
  font-family: monospace;
  font-weight: bold;
}
</style>
