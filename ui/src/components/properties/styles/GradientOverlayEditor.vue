<template>
  <div class="style-editor">
    <div class="property-row">
      <label>Blend Mode</label>
      <select :value="style.blendMode" @change="emit('update', { blendMode: ($event.target as HTMLSelectElement).value as BlendMode })">
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
      <label>Style</label>
      <select :value="style.style" @change="emit('update', { style: ($event.target as HTMLSelectElement).value as GradientOverlayType })">
        <option value="linear">Linear</option>
        <option value="radial">Radial</option>
        <option value="angle">Angle</option>
        <option value="reflected">Reflected</option>
        <option value="diamond">Diamond</option>
      </select>
    </div>

    <div class="property-row">
      <label>Angle</label>
      <input type="range" min="0" max="360" :value="style.angle.value"
        @input="emit('update', { angle: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.angle.value }}°</span>
    </div>

    <div class="property-row">
      <label>Scale</label>
      <input type="range" min="10" max="150" :value="style.scale.value"
        @input="emit('update', { scale: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ style.scale.value }}%</span>
    </div>

    <div class="property-row">
      <label>
        <input type="checkbox" :checked="style.reverse"
          @change="emit('update', { reverse: ($event.target as HTMLInputElement).checked })" />
        Reverse
      </label>
    </div>

    <div class="property-row">
      <label>
        <input type="checkbox" :checked="style.alignWithLayer"
          @change="emit('update', { alignWithLayer: ($event.target as HTMLInputElement).checked })" />
        Align with Layer
      </label>
    </div>

    <div class="gradient-preview" :style="{ background: gradientCSS }"></div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import type {
  GradientOverlayStyle,
  GradientOverlayType,
  GradientOverlayUpdate,
} from "@/types/layerStyles";
import type { BlendMode } from "@/types/project";

const props = defineProps<{
  style: GradientOverlayStyle;
}>();

const emit =
  defineEmits<(e: "update", updates: GradientOverlayUpdate) => void>();

const blendModes: BlendMode[] = [
  "normal",
  "multiply",
  "screen",
  "overlay",
  "darken",
  "lighten",
  "color-dodge",
  "color-burn",
  "hard-light",
  "soft-light",
];

function formatMode(mode: string): string {
  return mode
    .split("-")
    .map((w) => w.charAt(0).toUpperCase() + w.slice(1))
    .join(" ");
}

const gradientCSS = computed(() => {
  const grad = props.style.gradient.value;
  if (!grad || !grad.stops) {
    return "linear-gradient(90deg, #000, #fff)";
  }

  const stops = grad.stops
    .map(
      (s) =>
        `rgba(${s.color.r}, ${s.color.g}, ${s.color.b}, ${s.color.a}) ${s.position * 100}%`,
    )
    .join(", ");

  return `linear-gradient(${props.style.angle.value}deg, ${stops})`;
});
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

.property-row input[type="checkbox"] {
  accent-color: var(--lattice-accent);
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

.gradient-preview {
  height: 24px;
  border-radius: var(--lattice-radius-sm);
  border: 1px solid var(--lattice-border-default);
  margin-top: 4px;
}

.value {
  min-width: 40px;
  text-align: right;
  font-size: var(--lattice-font-size-xs);
  color: var(--lattice-text-muted);
  font-family: monospace;
}
</style>
