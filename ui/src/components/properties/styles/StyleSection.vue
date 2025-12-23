<template>
  <div class="style-section" :class="{ enabled, expanded }">
    <div class="section-header" @click="toggleExpand">
      <label class="enable-toggle" @click.stop>
        <input
          type="checkbox"
          :checked="enabled"
          @change="$emit('toggle', ($event.target as HTMLInputElement).checked)"
        />
      </label>
      <span class="section-title">{{ title }}</span>
      <span class="expand-icon">{{ expanded ? '&#x25BC;' : '&#x25B6;' }}</span>
    </div>
    <div class="section-content" v-show="expanded && enabled">
      <slot />
    </div>
  </div>
</template>

<script setup lang="ts">
const props = defineProps<{
  title: string;
  enabled: boolean;
  expanded: boolean;
}>();

const emit = defineEmits<{
  (e: 'toggle', enabled: boolean): void;
  (e: 'expand', expanded: boolean): void;
}>();

function toggleExpand() {
  emit('expand', !props.expanded);
}
</script>

<style scoped>
.style-section {
  border-bottom: 1px solid var(--weyl-border-subtle);
}

.style-section.enabled .section-header {
  background: var(--weyl-surface-2);
}

.style-section.expanded .section-header {
  border-left: 2px solid var(--weyl-accent);
}

.section-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 12px;
  cursor: pointer;
  transition: background 0.15s ease;
  border-left: 2px solid transparent;
}

.section-header:hover {
  background: var(--weyl-surface-2);
}

.enable-toggle {
  display: flex;
  align-items: center;
}

.enable-toggle input {
  width: 12px;
  height: 12px;
  accent-color: var(--weyl-accent);
}

.section-title {
  flex: 1;
  font-size: var(--weyl-font-size-sm);
  color: var(--weyl-text-primary);
}

.style-section:not(.enabled) .section-title {
  color: var(--weyl-text-muted);
}

.expand-icon {
  font-size: 8px;
  color: var(--weyl-text-muted);
  transition: transform 0.15s ease;
}

.style-section.expanded .expand-icon {
  color: var(--weyl-accent);
}

.section-content {
  padding: 8px 12px 12px 24px;
  background: var(--weyl-surface-1);
}
</style>
