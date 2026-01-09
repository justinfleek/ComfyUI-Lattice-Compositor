<template>
  <div class="style-editor">
    <div class="property-row">
      <label>Fill Opacity</label>
      <input type="range" min="0" max="100" :value="options.fillOpacity.value"
        @input="emit('update', { fillOpacity: Number(($event.target as HTMLInputElement).value) })" />
      <span class="value">{{ options.fillOpacity.value }}%</span>
    </div>

    <div class="property-row">
      <label>
        <input type="checkbox" :checked="options.blendInteriorStylesAsGroup"
          @change="emit('update', { blendInteriorStylesAsGroup: ($event.target as HTMLInputElement).checked })" />
        Blend Interior Effects as Group
      </label>
    </div>

    <div class="property-row" v-if="options.blendClippedLayersAsGroup !== undefined">
      <label>
        <input type="checkbox" :checked="options.blendClippedLayersAsGroup"
          @change="emit('update', { blendClippedLayersAsGroup: ($event.target as HTMLInputElement).checked })" />
        Blend Clipped Layers as Group
      </label>
    </div>

    <div class="property-row" v-if="options.transparencyShapesLayer !== undefined">
      <label>
        <input type="checkbox" :checked="options.transparencyShapesLayer"
          @change="emit('update', { transparencyShapesLayer: ($event.target as HTMLInputElement).checked })" />
        Transparency Shapes Layer
      </label>
    </div>

    <div class="property-row" v-if="options.layerMaskHidesEffects !== undefined">
      <label>
        <input type="checkbox" :checked="options.layerMaskHidesEffects"
          @change="emit('update', { layerMaskHidesEffects: ($event.target as HTMLInputElement).checked })" />
        Layer Mask Hides Effects
      </label>
    </div>

    <div class="property-row" v-if="options.vectorMaskHidesEffects !== undefined">
      <label>
        <input type="checkbox" :checked="options.vectorMaskHidesEffects"
          @change="emit('update', { vectorMaskHidesEffects: ($event.target as HTMLInputElement).checked })" />
        Vector Mask Hides Effects
      </label>
    </div>
  </div>
</template>

<script setup lang="ts">
import type {
  StyleBlendingOptions,
  StyleBlendingOptionsUpdate,
} from "@/types/layerStyles";

defineProps<{
  options: StyleBlendingOptions;
}>();

const emit =
  defineEmits<(e: "update", updates: StyleBlendingOptionsUpdate) => void>();
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

.value {
  min-width: 40px;
  text-align: right;
  font-size: var(--lattice-font-size-xs);
  color: var(--lattice-text-muted);
  font-family: monospace;
}
</style>
