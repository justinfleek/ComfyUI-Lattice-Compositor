<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Name</label>
      <input type="text" :value="group.name" @change="updateName" class="name-input" />
    </div>
    <div class="property-row">
      <label>Blend Mode</label>
      <select :value="group.blendMode" @change="updateBlendMode">
        <option value="normal">Normal</option>
        <option value="multiply">Multiply</option>
        <option value="screen">Screen</option>
        <option value="overlay">Overlay</option>
        <option value="darken">Darken</option>
        <option value="lighten">Lighten</option>
      </select>
    </div>

    <div class="subsection-header">Transform</div>
    <TransformEditor :transform="group.transform" @update="updateTransform" />

    <div class="subsection-header">Contents ({{ group.contents?.length || 0 }})</div>
    <div class="contents-info">
      <span v-if="!group.contents?.length">No contents in this group</span>
      <span v-else>{{ group.contents.length }} item(s)</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { ShapeGroup, ShapeTransform } from '@/types/shapes';
import TransformEditor from './TransformEditor.vue';

const props = defineProps<{ group: ShapeGroup }>();
const emit = defineEmits(['update']);

function updateName(e: Event) {
  const updated = { ...props.group };
  updated.name = (e.target as HTMLInputElement).value;
  emit('update', updated);
}

function updateBlendMode(e: Event) {
  const updated = { ...props.group };
  updated.blendMode = (e.target as HTMLSelectElement).value;
  emit('update', updated);
}

function updateTransform(transform: ShapeTransform) {
  const updated = { ...props.group, transform };
  emit('update', updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--weyl-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.property-row select, .name-input { flex: 1; padding: 3px 6px; background: var(--weyl-surface-0, #0a0a0a); border: 1px solid var(--weyl-border-default, #333); border-radius: 3px; color: var(--weyl-text-primary, #e0e0e0); font-size: 11px; }
.name-input:focus { outline: none; border-color: var(--weyl-accent, #8B5CF6); }
.subsection-header { font-size: 10px; font-weight: 600; color: var(--weyl-text-muted, #666); text-transform: uppercase; letter-spacing: 0.05em; margin-top: 8px; padding-bottom: 4px; border-bottom: 1px solid var(--weyl-border-subtle, #2a2a2a); }
.contents-info { font-size: 11px; color: var(--weyl-text-muted, #888); padding: 4px 0; }
</style>
