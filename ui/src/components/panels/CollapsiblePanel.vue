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
  border-bottom: 1px solid var(--weyl-border-default, #2a2a2a);
}

.collapsible-panel:last-child {
  border-bottom: none;
}

.panel-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 12px 14px;
  background: var(--weyl-surface-0, #0a0a0a);
  border-left: 3px solid transparent;
  cursor: pointer;
  user-select: none;
  transition: all 0.15s ease;
}

.panel-header:hover {
  background: var(--weyl-surface-3, #222222);
  border-left-color: var(--weyl-accent-muted, rgba(139, 92, 246, 0.3));
}

.collapsible-panel:not(.collapsed) .panel-header {
  border-left-color: var(--weyl-accent, #8B5CF6);
  background: var(--weyl-surface-2, #1a1a1a);
}

.expand-icon {
  font-size: 10px;
  color: var(--weyl-text-muted, #6B7280);
  width: 12px;
  transition: color 0.15s ease;
}

.collapsible-panel:not(.collapsed) .expand-icon {
  color: var(--weyl-accent, #8B5CF6);
}

.panel-title {
  flex: 1;
  font-size: 13px;
  font-weight: 600;
  color: var(--weyl-text-secondary, #9CA3AF);
}

.collapsible-panel:not(.collapsed) .panel-title {
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
  background: var(--weyl-surface-1, #121212);
  border-left-color: transparent;
}
</style>
