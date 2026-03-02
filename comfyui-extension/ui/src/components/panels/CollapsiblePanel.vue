<template>
  <div class="collapsible-panel" :class="{ collapsed: !isExpanded }">
    <div class="panel-header" @click="toggle">
      <span class="expand-icon">{{ isExpanded ? '▼' : '►' }}</span>
      <span class="panel-title">{{ title }}</span>
      <span v-if="badge" class="panel-badge">{{ badge }}</span>
    </div>
    <div v-show="isExpanded" class="panel-body">
      <slot></slot>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, watch } from "vue";

const props = defineProps<{
  title: string;
  expanded?: boolean;
  badge?: string | number;
}>();

const emit = defineEmits<(e: "toggle", expanded: boolean) => void>();

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
const isExpanded = ref((typeof props.expanded === "boolean") ? props.expanded : true);

watch(
  () => props.expanded,
  (val) => {
    if (val !== undefined) {
      isExpanded.value = val;
    }
  },
);

function toggle() {
  isExpanded.value = !isExpanded.value;
  emit("toggle", isExpanded.value);
}
</script>

<style scoped>
.collapsible-panel {
  border-bottom: 1px solid var(--lattice-border-default, #2a2a2a);
  margin-bottom: 4px;
}

.collapsible-panel:last-child {
  border-bottom: none;
  margin-bottom: 0;
}

.panel-header {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 10px 14px;
  background: var(--lattice-surface-0, #0a0a0a);
  border-left: 3px solid transparent;
  cursor: pointer;
  user-select: none;
  transition: all 0.15s ease;
}

.panel-header:hover {
  background: var(--lattice-surface-3, #222222);
  border-left-color: var(--lattice-accent-muted, rgba(139, 92, 246, 0.3));
}

.collapsible-panel:not(.collapsed) .panel-header {
  border-left-color: var(--lattice-accent, #8B5CF6);
  background: var(--lattice-surface-2, #1a1a1a);
}

.expand-icon {
  font-size: 10px;
  color: var(--lattice-text-muted, #6B7280);
  width: 12px;
  transition: color 0.15s ease;
}

.collapsible-panel:not(.collapsed) .expand-icon {
  color: var(--lattice-accent, #8B5CF6);
}

.panel-title {
  flex: 1;
  font-size: 13px;
  font-weight: 600;
  color: var(--lattice-text-secondary, #9CA3AF);
}

.collapsible-panel:not(.collapsed) .panel-title {
  color: var(--lattice-text-primary, #E5E5E5);
}

.panel-badge {
  font-size: 11px;
  padding: 2px 6px;
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
  color: var(--lattice-accent, #8B5CF6);
  border-radius: 10px;
}

.panel-body {
  max-height: 400px;
  overflow-y: auto;
}

.collapsed .panel-header {
  background: var(--lattice-surface-1, #121212);
  border-left-color: transparent;
}
</style>
