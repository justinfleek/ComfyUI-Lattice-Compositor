<template>
  <div class="style-editor">
    <div class="property-row">
      <label>Blend Mode</label>
      <select :value="style.blendMode" @change="emit('update', { blendMode: ($event.target as HTMLSelectElement).value })">
        <option v-for="mode in blendModes" :key="mode" :value="mode">{{ formatMode(mode) }}</option>
      </select>
    </div>

    <div class="property-row">
      <label>Opacity</label>
      <input type="range" min="0" max="100" :value="style.opacity.value"
        @input="emit('update', { opacity: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.opacity.value }}%</span>
    </div>

    <div class="property-row">
      <label>Size</label>
      <input type="range" min="1" max="50" :value="style.size.value"
        @input="emit('update', { size: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.size.value }}px</span>
    </div>

    <div class="property-row">
      <label>Position</label>
      <select :value="style.position" @change="emit('update', { position: ($event.target as HTMLSelectElement).value })">
        <option value="outside">Outside</option>
        <option value="inside">Inside</option>
        <option value="center">Center</option>
      </select>
    </div>

    <div class="property-row">
      <label>Fill Type</label>
      <select :value="style.fillType" @change="emit('update', { fillType: ($event.target as HTMLSelectElement).value })">
        <option value="color">Color</option>
        <option value="gradient">Gradient</option>
      </select>
    </div>

    <div class="property-row" v-if="style.fillType === 'color'">
      <label>Color</label>
      <input type="color" :value="rgbaToHex(style.color.value)"
        @input="emit('update', { color: hexToRgba(($event.target as HTMLInputElement).value) })" />
      <div class="color-preview" :style="{ backgroundColor: rgbaToHex(style.color.value) }"></div>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { StrokeStyle, StrokeStyleUpdate, RGBA } from '@/types/layerStyles';

defineProps<{
  style: StrokeStyle;
}>();

const emit = defineEmits<{
  (e: 'update', updates: StrokeStyleUpdate): void;
}>();

const blendModes = ['normal', 'multiply', 'screen', 'overlay', 'darken', 'lighten'];

function formatMode(mode: string): string {
  return mode.split('-').map(w => w.charAt(0).toUpperCase() + w.slice(1)).join(' ');
}

function rgbaToHex(color: RGBA): string {
  const r = Math.round(color.r).toString(16).padStart(2, '0');
  const g = Math.round(color.g).toString(16).padStart(2, '0');
  const b = Math.round(color.b).toString(16).padStart(2, '0');
  return `#${r}${g}${b}`;
}

function hexToRgba(hex: string): RGBA {
  const r = parseInt(hex.slice(1, 3), 16);
  const g = parseInt(hex.slice(3, 5), 16);
  const b = parseInt(hex.slice(5, 7), 16);
  return { r, g, b, a: 1 };
}
</script>

<style scoped>
.style-editor {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.property-row label {
  min-width: 80px;
  font-size: var(--lattice-font-size-xs);
  color: var(--lattice-text-secondary);
}

.property-row input[type="range"] {
  flex: 1;
  height: 4px;
  accent-color: var(--lattice-accent);
}

.property-row input[type="color"] {
  width: 32px;
  height: 24px;
  padding: 0;
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  cursor: pointer;
}

.property-row select {
  flex: 1;
  padding: 4px 8px;
  background: var(--lattice-surface-2);
  border: 1px solid var(--lattice-border-default);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-primary);
  font-size: var(--lattice-font-size-xs);
}

.color-preview {
  width: 60px;
  height: 24px;
  border-radius: var(--lattice-radius-sm);
  border: 1px solid var(--lattice-border-default);
}

.value {
  min-width: 40px;
  text-align: right;
  font-size: var(--lattice-font-size-xs);
  color: var(--lattice-text-muted);
  font-family: monospace;
}
</style>
