<template>
  <div class="shape-editor">
    <div class="info-row">
      <span class="info-label">Edit path in canvas to modify vertices</span>
    </div>
    <div class="property-row">
      <label>Direction</label>
      <select :value="shape.direction" @change="updateDirection">
        <option :value="1">Clockwise</option>
        <option :value="-1">Counter-Clockwise</option>
      </select>
    </div>
    <div class="info-row">
      <span class="info-label">Vertices:</span>
      <span class="info-value">{{ getVertexCount() }}</span>
    </div>
    <div class="info-row">
      <span class="info-label">Closed:</span>
      <span class="info-value">{{ shape.path.value.closed ? 'Yes' : 'No' }}</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { safeNonNegativeDefault } from "@/utils/typeGuards";
import type { PathShape } from "@/types/shapes";

const props = defineProps<{ shape: PathShape; layerId: string }>();
const emit = defineEmits(["update"]);

// Type proof: vertices.length ∈ number | undefined → number (≥ 0, count)
function getVertexCount(): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const pathValue = (props.shape != null && typeof props.shape === "object" && "path" in props.shape && props.shape.path != null && typeof props.shape.path === "object" && "value" in props.shape.path && props.shape.path.value != null && typeof props.shape.path.value === "object") ? props.shape.path.value : undefined;
  const vertices = (pathValue != null && typeof pathValue === "object" && "vertices" in pathValue && pathValue.vertices != null && Array.isArray(pathValue.vertices)) ? pathValue.vertices : undefined;
  const verticesLength = (vertices != null && Array.isArray(vertices)) ? vertices.length : undefined;
  return safeNonNegativeDefault(verticesLength, 0, "shape.path.value.vertices.length");
}

function updateDirection(e: Event) {
  const updated = { ...props.shape };
  updated.direction = parseInt((e.target as HTMLSelectElement).value, 10) as
    | 1
    | -1;
  emit("update", updated);
}
</script>

<style scoped>
.shape-editor {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.property-row label {
  width: 70px;
  color: var(--lattice-text-muted, #888);
  font-size: 11px;
  flex-shrink: 0;
}

.property-row select {
  flex: 1;
  padding: 3px 6px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 11px;
}

.info-row {
  display: flex;
  gap: 6px;
  font-size: 11px;
  color: var(--lattice-text-muted, #888);
}

.info-label {
  color: var(--lattice-text-muted, #666);
}

.info-value {
  color: var(--lattice-text-secondary, #aaa);
}
</style>
