<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Mode</label>
      <select :value="operator.mode" @change="updateMode">
        <option value="add">Add (Union)</option>
        <option value="subtract">Subtract</option>
        <option value="intersect">Intersect</option>
        <option value="exclude">Exclude Intersection</option>
        <option value="minusFront">Minus Front</option>
        <option value="minusBack">Minus Back</option>
      </select>
    </div>
    <div class="mode-preview">
      <div class="mode-icon" :class="operator.mode">
        <template v-if="operator.mode === 'add'">⊕</template>
        <template v-else-if="operator.mode === 'subtract'">⊖</template>
        <template v-else-if="operator.mode === 'intersect'">⊗</template>
        <template v-else-if="operator.mode === 'exclude'">⊘</template>
        <template v-else>⊛</template>
      </div>
      <span class="mode-desc">{{ modeDescription }}</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import type { MergePathsOperator, MergeMode } from '@/types/shapes';

const props = defineProps<{ operator: MergePathsOperator; layerId: string }>();
const emit = defineEmits(['update']);

const modeDescription = computed(() => {
  const descs: Record<MergeMode, string> = {
    add: 'Combines all paths into one',
    subtract: 'Removes overlapping areas',
    intersect: 'Keeps only overlapping areas',
    exclude: 'Removes overlapping, keeps the rest',
    minusFront: 'Back shape minus front shapes',
    minusBack: 'Front shape minus back shapes',
  };
  return descs[props.operator.mode];
});

function updateMode(e: Event) {
  const updated = { ...props.operator };
  updated.mode = (e.target as HTMLSelectElement).value as MergeMode;
  emit('update', updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--lattice-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.property-row select { flex: 1; padding: 3px 6px; background: var(--lattice-surface-0, #0a0a0a); border: 1px solid var(--lattice-border-default, #333); border-radius: 3px; color: var(--lattice-text-primary, #e0e0e0); font-size: 11px; }
.mode-preview { display: flex; align-items: center; gap: 8px; padding: 8px; background: var(--lattice-surface-0, #0a0a0a); border-radius: 4px; }
.mode-icon { font-size: 20px; width: 28px; text-align: center; color: var(--lattice-accent, #8B5CF6); }
.mode-desc { font-size: 11px; color: var(--lattice-text-muted, #888); }
</style>
