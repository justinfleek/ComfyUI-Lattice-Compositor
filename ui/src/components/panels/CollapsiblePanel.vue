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
import { ref, watch } from 'vue';

const props = defineProps<{
  title: string;
  expanded?: boolean;
  badge?: string | number;
}>();

const emit = defineEmits<{
  (e: 'toggle', expanded: boolean): void;
}>();

const isExpanded = ref(props.expanded ?? true);

watch(() => props.expanded, (val) => {
  if (val !== undefined) {
    isExpanded.value = val;
  }
});

function toggle() {
  isExpanded.value = !isExpanded.value;
  emit('toggle', isExpanded.value);
}
</script>

<style scoped>
.collapsible-panel {
  border-bottom: 1px solid var(--weyl-border-subtle, #1a1a1a);
}

.collapsible-panel:last-child {
  border-bottom: none;
}

.panel-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 10px 12px;
  background: var(--weyl-surface-2, #1a1a1a);
  cursor: pointer;
  user-select: none;
}

.panel-header:hover {
  background: var(--weyl-surface-3, #222222);
}

.expand-icon {
  font-size: 10px;
  color: var(--weyl-text-muted, #6B7280);
  width: 12px;
}

.panel-title {
  flex: 1;
  font-size: 13px;
  font-weight: 500;
  color: var(--weyl-text-primary, #E5E5E5);
}

.panel-badge {
  font-size: 11px;
  padding: 2px 6px;
  background: var(--weyl-accent-muted, rgba(139, 92, 246, 0.15));
  color: var(--weyl-accent, #8B5CF6);
  border-radius: 10px;
}

.panel-body {
  max-height: 400px;
  overflow-y: auto;
}

.collapsed .panel-header {
  background: var(--weyl-surface-1, #141414);
}
</style>
