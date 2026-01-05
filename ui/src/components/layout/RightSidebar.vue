<!--
  @component RightSidebar
  @description Right sidebar with collapsible property panels and AI tools.
  Extracted from WorkspaceLayout.vue to reduce file size.
-->
<template>
  <Splitpanes horizontal class="default-theme right-splitpanes">
    <!-- Main Properties Section -->
    <Pane :size="45" :min-size="25">
      <div class="panel right-panel stacked-panels">
        <div class="panel-content">
          <!-- Properties Panel -->
          <CollapsiblePanel
            title="Properties"
            :expanded="expandedPanels.properties"
            @toggle="updatePanel('properties', $event)"
          >
            <PropertiesPanel />
          </CollapsiblePanel>

          <!-- Effects Panel -->
          <CollapsiblePanel
            title="Effects"
            :expanded="expandedPanels.effects"
            @toggle="updatePanel('effects', $event)"
          >
            <EffectControlsPanel />
          </CollapsiblePanel>

          <!-- Drivers Panel -->
          <CollapsiblePanel
            title="Drivers"
            :expanded="expandedPanels.drivers"
            @toggle="updatePanel('drivers', $event)"
          >
            <DriverList :layerId="selectedLayerId" />
          </CollapsiblePanel>

          <!-- Scopes Panel -->
          <CollapsiblePanel
            title="Scopes"
            :expanded="expandedPanels.scopes"
            @toggle="updatePanel('scopes', $event)"
          >
            <ScopesPanel />
          </CollapsiblePanel>

          <!-- Camera Panel -->
          <CollapsiblePanel
            title="Camera"
            :expanded="expandedPanels.camera"
            @toggle="updatePanel('camera', $event)"
          >
            <CameraProperties
              :camera="camera"
              @update:camera="$emit('updateCamera', $event)"
            />
          </CollapsiblePanel>

          <!-- Audio Panel -->
          <CollapsiblePanel
            title="Audio"
            :expanded="expandedPanels.audio"
            @toggle="updatePanel('audio', $event)"
          >
            <AudioPanel />
          </CollapsiblePanel>

          <!-- Align Panel -->
          <CollapsiblePanel
            title="Align"
            :expanded="expandedPanels.align"
            @toggle="updatePanel('align', $event)"
          >
            <AlignPanel />
          </CollapsiblePanel>

          <!-- Preview Panel -->
          <CollapsiblePanel
            title="Preview"
            :expanded="expandedPanels.preview"
            @toggle="updatePanel('preview', $event)"
          >
            <PreviewPanel :engine="engine" />
          </CollapsiblePanel>
        </div>
      </div>
    </Pane>

    <!-- AI Section (Bottom) -->
    <Pane :size="55" :min-size="30">
      <div class="panel ai-section">
        <div class="ai-section-header">
          <span class="ai-section-title">AI Tools</span>
        </div>
        <div class="ai-section-tabs">
          <button
            :class="{ active: aiTab === 'chat' }"
            @click="$emit('update:aiTab', 'chat')"
            title="AI Compositor Agent"
          >
            Chat
          </button>
          <button
            :class="{ active: aiTab === 'generate' }"
            @click="$emit('update:aiTab', 'generate')"
            title="AI Generation (Depth, Normal, Segment)"
          >
            Generate
          </button>
          <button
            :class="{ active: aiTab === 'flow' }"
            @click="$emit('update:aiTab', 'flow')"
            title="Generative Flow Trajectories for Wan-Move"
          >
            Flow
          </button>
          <button
            :class="{ active: aiTab === 'decompose' }"
            @click="$emit('update:aiTab', 'decompose')"
            title="AI Layer Decomposition"
          >
            Decompose
          </button>
        </div>
        <div class="ai-section-content">
          <AIChatPanel v-if="aiTab === 'chat'" />
          <AIGeneratePanel v-else-if="aiTab === 'generate'" />
          <GenerativeFlowPanel v-else-if="aiTab === 'flow'" />
          <LayerDecompositionPanel v-else-if="aiTab === 'decompose'" />
        </div>
      </div>
    </Pane>
  </Splitpanes>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import type { Camera3D } from "@/types/camera";

const store = useCompositorStore();
const _selectedLayerId = computed(() => store.selectedLayerIds[0] || "");

export type AITab = "chat" | "generate" | "flow" | "decompose";

export interface ExpandedPanels {
  properties: boolean;
  effects: boolean;
  drivers: boolean;
  scopes: boolean;
  camera: boolean;
  audio: boolean;
  align: boolean;
  preview: boolean;
  renderQueue: boolean;
  physics: boolean;
  styles: boolean;
}

const props = defineProps<{
  expandedPanels: ExpandedPanels;
  aiTab: AITab;
  camera: Camera3D;
  engine: any;
}>();

const emit = defineEmits<{
  "update:expandedPanels": [panels: ExpandedPanels];
  "update:aiTab": [tab: AITab];
  updateCamera: [camera: Camera3D];
}>();

function _updatePanel(panel: keyof ExpandedPanels, expanded: boolean) {
  emit("update:expandedPanels", {
    ...props.expandedPanels,
    [panel]: expanded,
  });
}
</script>

<style scoped>
.right-splitpanes {
  height: 100%;
}

.right-panel {
  height: 100%;
  display: flex;
  flex-direction: column;
  background: var(--lattice-surface-1, #121212);
}

.stacked-panels .panel-content {
  flex: 1;
  overflow-y: auto;
  overflow-x: hidden;
}

.ai-section {
  height: 100%;
  display: flex;
  flex-direction: column;
  background: var(--lattice-surface-1, #121212);
}

.ai-section-header {
  padding: 6px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border, #333);
}

.ai-section-title {
  font-size: 11px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--lattice-text-secondary, #888);
}

.ai-section-tabs {
  display: flex;
  gap: 0;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border, #333);
}

.ai-section-tabs button {
  flex: 1;
  padding: 6px 4px;
  background: transparent;
  border: none;
  color: var(--lattice-text-secondary, #888);
  cursor: pointer;
  font-size: 10px;
  font-weight: 500;
  transition: all 0.15s ease;
}

.ai-section-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
  background: var(--lattice-surface-3, #252525);
}

.ai-section-tabs button.active {
  color: var(--lattice-accent, #8b5cf6);
  background: var(--lattice-surface-1, #121212);
  border-bottom: 2px solid var(--lattice-accent, #8b5cf6);
}

.ai-section-content {
  flex: 1;
  overflow: auto;
}
</style>
