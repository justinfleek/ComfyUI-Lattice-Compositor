<template>
  <div class="style-editor">
    <div class="property-row">
      <label>Style</label>
      <select :value="style.style" @change="emit('update', { style: ($event.target as HTMLSelectElement).value })">
        <option value="outer-bevel">Outer Bevel</option>
        <option value="inner-bevel">Inner Bevel</option>
        <option value="emboss">Emboss</option>
        <option value="pillow-emboss">Pillow Emboss</option>
        <option value="stroke-emboss">Stroke Emboss</option>
      </select>
    </div>

    <div class="property-row">
      <label>Technique</label>
      <select :value="style.technique" @change="emit('update', { technique: ($event.target as HTMLSelectElement).value })">
        <option value="smooth">Smooth</option>
        <option value="chisel-hard">Chisel Hard</option>
        <option value="chisel-soft">Chisel Soft</option>
      </select>
    </div>

    <div class="property-row">
      <label>Depth</label>
      <input type="range" min="1" max="1000" :value="style.depth.value"
        @input="emit('update', { depth: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.depth.value }}%</span>
    </div>

    <div class="property-row">
      <label>Direction</label>
      <select :value="style.direction" @change="emit('update', { direction: ($event.target as HTMLSelectElement).value })">
        <option value="up">Up</option>
        <option value="down">Down</option>
      </select>
    </div>

    <div class="property-row">
      <label>Size</label>
      <input type="range" min="0" max="100" :value="style.size.value"
        @input="emit('update', { size: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.size.value }}px</span>
    </div>

    <div class="property-row">
      <label>Soften</label>
      <input type="range" min="0" max="16" :value="style.soften.value"
        @input="emit('update', { soften: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.soften.value }}px</span>
    </div>

    <div class="section-header">Shading</div>

    <div class="property-row">
      <label>Angle</label>
      <input type="range" min="0" max="360" :value="style.angle.value"
        @input="emit('update', { angle: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.angle.value }}°</span>
    </div>

    <div class="property-row">
      <label>
        <input type="checkbox" :checked="style.useGlobalLight"
          @change="emit('update', { useGlobalLight: ($event.target as HTMLInputElement).checked })" />
        Use Global Light
      </label>
    </div>

    <div class="property-row">
      <label>Altitude</label>
      <input type="range" min="0" max="90" :value="style.altitude.value"
        @input="emit('update', { altitude: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.altitude.value }}°</span>
    </div>

    <div class="section-header">Highlight</div>

    <div class="property-row">
      <label>Mode</label>
      <select :value="style.highlightMode" @change="emit('update', { highlightMode: ($event.target as HTMLSelectElement).value })">
        <option v-for="mode in blendModes" :key="mode" :value="mode">{{ formatMode(mode) }}</option>
      </select>
    </div>

    <div class="property-row">
      <label>Color</label>
      <input type="color" :value="rgbaToHex(style.highlightColor.value)"
        @input="emit('update', { highlightColor: hexToRgba(($event.target as HTMLInputElement).value) })" />
    </div>

    <div class="property-row">
      <label>Opacity</label>
      <input type="range" min="0" max="100" :value="style.highlightOpacity.value"
        @input="emit('update', { highlightOpacity: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.highlightOpacity.value }}%</span>
    </div>

    <div class="section-header">Shadow</div>

    <div class="property-row">
      <label>Mode</label>
      <select :value="style.shadowMode" @change="emit('update', { shadowMode: ($event.target as HTMLSelectElement).value })">
        <option v-for="mode in blendModes" :key="mode" :value="mode">{{ formatMode(mode) }}</option>
      </select>
    </div>

    <div class="property-row">
      <label>Color</label>
      <input type="color" :value="rgbaToHex(style.shadowColor.value)"
        @input="emit('update', { shadowColor: hexToRgba(($event.target as HTMLInputElement).value) })" />
    </div>

    <div class="property-row">
      <label>Opacity</label>
      <input type="range" min="0" max="100" :value="style.shadowOpacity.value"
        @input="emit('update', { shadowOpacity: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.shadowOpacity.value }}%</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { BevelEmbossStyle, RGBA } from '@/types/layerStyles';

defineProps<{
  style: BevelEmbossStyle;
}>();

const emit = defineEmits<{
  (e: 'update', updates: Partial<BevelEmbossStyle>): void;
}>();

const blendModes = ['normal', 'multiply', 'screen', 'overlay', 'soft-light', 'hard-light'];

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

.section-header {
  margin-top: 8px;
  padding: 4px 0;
  font-size: var(--weyl-font-size-xs);
  font-weight: 600;
  color: var(--weyl-text-secondary);
  border-bottom: 1px solid var(--weyl-border-subtle);
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.property-row label {
  min-width: 80px;
  font-size: var(--weyl-font-size-xs);
  color: var(--weyl-text-secondary);
}

.property-row input[type="range"] {
  flex: 1;
  height: 4px;
  accent-color: var(--weyl-accent);
}

.property-row input[type="color"] {
  width: 32px;
  height: 24px;
  padding: 0;
  border: 1px solid var(--weyl-border-default);
  border-radius: var(--weyl-radius-sm);
  cursor: pointer;
}

.property-row input[type="checkbox"] {
  accent-color: var(--weyl-accent);
}

.property-row select {
  flex: 1;
  padding: 4px 8px;
  background: var(--weyl-surface-2);
  border: 1px solid var(--weyl-border-default);
  border-radius: var(--weyl-radius-sm);
  color: var(--weyl-text-primary);
  font-size: var(--weyl-font-size-xs);
}

.value {
  min-width: 40px;
  text-align: right;
  font-size: var(--weyl-font-size-xs);
  color: var(--weyl-text-muted);
  font-family: monospace;
}
</style>
