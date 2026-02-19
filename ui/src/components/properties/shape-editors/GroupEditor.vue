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
    <TransformEditor :transform="group.transform" :layerId="layerId" @update="updateTransform" />

    <div class="subsection-header">Contents ({{ getContentsCount() }})</div>
    <div class="contents-info">
      <!-- Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?. -->
      <span v-if="getContentsCount() === 0">No contents in this group</span>
      <span v-else>{{ getContentsCount() }} item(s)</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { safeNonNegativeDefault } from "@/utils/typeGuards";
import type { ShapeGroup, ShapeTransform } from "@/types/shapes";

const props = defineProps<{ group: ShapeGroup; layerId: string }>();
const emit = defineEmits(["update"]);

// Type proof: contents.length ∈ number | undefined → number (≥ 0, count)
function getContentsCount(): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const groupContents = (props.group != null && typeof props.group === "object" && "contents" in props.group && props.group.contents != null && Array.isArray(props.group.contents)) ? props.group.contents : undefined;
  const contentsLength = (groupContents != null && Array.isArray(groupContents)) ? groupContents.length : undefined;
  return safeNonNegativeDefault(contentsLength, 0, "group.contents.length");
}

function updateName(e: Event) {
  const updated = { ...props.group };
  updated.name = (e.target as HTMLInputElement).value;
  emit("update", updated);
}

function updateBlendMode(e: Event) {
  const updated = { ...props.group };
  updated.blendMode = (e.target as HTMLSelectElement).value;
  emit("update", updated);
}

function updateTransform(transform: ShapeTransform) {
  const updated = { ...props.group, transform };
  emit("update", updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--lattice-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.property-row select, .name-input { flex: 1; padding: 3px 6px; background: var(--lattice-surface-0, #0a0a0a); border: 1px solid var(--lattice-border-default, #333); border-radius: 3px; color: var(--lattice-text-primary, #e0e0e0); font-size: 11px; }
.name-input:focus { outline: none; border-color: var(--lattice-accent, #8B5CF6); }
.subsection-header { font-size: 10px; font-weight: 600; color: var(--lattice-text-muted, #666); text-transform: uppercase; letter-spacing: 0.05em; margin-top: 8px; padding-bottom: 4px; border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a); }
.contents-info { font-size: 11px; color: var(--lattice-text-muted, #888); padding: 4px 0; }
</style>
