<!--
  @component LeftSidebar
  @description Left sidebar panel with Project/Effects/Assets tabs.
  Extracted from WorkspaceLayout.vue to reduce file size.
-->
<template>
  <div class="panel left-panel">
    <div class="panel-tabs" role="tablist" aria-label="Left panel tabs">
      <button
        role="tab"
        :aria-selected="modelValue === 'project'"
        aria-controls="left-panel-project"
        :class="{ active: modelValue === 'project' }"
        @click="$emit('update:modelValue', 'project')"
      >
        Project
      </button>
      <button
        role="tab"
        :aria-selected="modelValue === 'effects'"
        aria-controls="left-panel-effects"
        :class="{ active: modelValue === 'effects' }"
        @click="$emit('update:modelValue', 'effects')"
      >
        Effects
      </button>
      <button
        role="tab"
        :aria-selected="modelValue === 'assets'"
        aria-controls="left-panel-assets"
        :class="{ active: modelValue === 'assets' }"
        @click="$emit('update:modelValue', 'assets')"
      >
        Assets
      </button>
    </div>
    <div class="panel-content" role="tabpanel" :id="`left-panel-${modelValue}`">
      <ProjectPanel
        v-if="modelValue === 'project'"
        @openCompositionSettings="$emit('openCompositionSettings')"
      />
      <EffectsPanel v-else-if="modelValue === 'effects'" />
      <AssetsPanel
        v-else-if="modelValue === 'assets'"
        @create-layers-from-svg="$emit('createLayersFromSvg', $event)"
        @use-mesh-as-emitter="$emit('useMeshAsEmitter', $event)"
        @environment-update="$emit('environmentUpdate', $event)"
        @environment-load="$emit('environmentLoad', $event)"
        @environment-clear="$emit('environmentClear')"
      />
    </div>
  </div>
</template>

<script setup lang="ts">
import type { EnvironmentState } from "@/stores/assetStore";

export type LeftTab = "project" | "effects" | "assets";

defineProps<{
  modelValue: LeftTab;
}>();

defineEmits<{
  "update:modelValue": [tab: LeftTab];
  openCompositionSettings: [];
  createLayersFromSvg: [svgId: string];
  useMeshAsEmitter: [meshId: string];
  environmentUpdate: [settings: Partial<EnvironmentState>];
  environmentLoad: [settings: Partial<EnvironmentState>];
  environmentClear: [];
}>();
</script>

<style scoped>
.left-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #121212);
}

.panel-tabs {
  display: flex;
  gap: 0;
  padding: 0;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border, #333);
}

.panel-tabs button {
  flex: 1;
  padding: 6px 8px;
  background: transparent;
  border: none;
  color: var(--lattice-text-secondary, #888);
  cursor: pointer;
  font-size: 11px;
  font-weight: 500;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  transition: all 0.15s ease;
}

.panel-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
  background: var(--lattice-surface-3, #252525);
}

.panel-tabs button.active {
  color: var(--lattice-accent, #8b5cf6);
  background: var(--lattice-surface-1, #121212);
  border-bottom: 2px solid var(--lattice-accent, #8b5cf6);
}

.panel-content {
  flex: 1;
  overflow: auto;
}
</style>
