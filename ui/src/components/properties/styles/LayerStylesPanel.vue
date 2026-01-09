<template>
  <div class="layer-styles-panel">
    <div class="panel-header">
      <div class="header-left">
        <label class="master-toggle">
          <input
            type="checkbox"
            :checked="stylesEnabled"
            @change="toggleStyles"
          />
          <span class="toggle-label">Layer Styles</span>
        </label>
      </div>
      <div class="header-actions">
        <button
          class="action-btn"
          title="Copy Layer Style"
          @click="copyStyles"
          :disabled="!hasStyles"
        >
          <span class="icon">&#x2398;</span>
        </button>
        <button
          class="action-btn"
          title="Paste Layer Style"
          @click="pasteStyles"
          :disabled="!canPaste"
        >
          <span class="icon">&#x2399;</span>
        </button>
        <button
          class="action-btn"
          title="Clear Layer Style"
          @click="clearStyles"
          :disabled="!hasStyles"
        >
          <span class="icon">&#x2715;</span>
        </button>
        <select
          class="preset-select"
          @change="applyPreset"
          title="Style Presets"
        >
          <option value="">Presets...</option>
          <option v-for="preset in presetNames" :key="preset" :value="preset">
            {{ formatPresetName(preset) }}
          </option>
        </select>
      </div>
    </div>

    <div class="styles-list" v-if="selectedLayer">
      <!-- Drop Shadow -->
      <StyleSection
        title="Drop Shadow"
        :enabled="dropShadowEnabled"
        @toggle="toggleStyle('dropShadow', $event)"
        :expanded="expandedSections.dropShadow"
        @expand="expandedSections.dropShadow = $event"
      >
        <DropShadowEditor
          v-if="layerStyles?.dropShadow"
          :style="layerStyles.dropShadow"
          @update="updateDropShadow"
        />
      </StyleSection>

      <!-- Inner Shadow -->
      <StyleSection
        title="Inner Shadow"
        :enabled="innerShadowEnabled"
        @toggle="toggleStyle('innerShadow', $event)"
        :expanded="expandedSections.innerShadow"
        @expand="expandedSections.innerShadow = $event"
      >
        <InnerShadowEditor
          v-if="layerStyles?.innerShadow"
          :style="layerStyles.innerShadow"
          @update="updateInnerShadow"
        />
      </StyleSection>

      <!-- Outer Glow -->
      <StyleSection
        title="Outer Glow"
        :enabled="outerGlowEnabled"
        @toggle="toggleStyle('outerGlow', $event)"
        :expanded="expandedSections.outerGlow"
        @expand="expandedSections.outerGlow = $event"
      >
        <OuterGlowEditor
          v-if="layerStyles?.outerGlow"
          :style="layerStyles.outerGlow"
          @update="updateOuterGlow"
        />
      </StyleSection>

      <!-- Inner Glow -->
      <StyleSection
        title="Inner Glow"
        :enabled="innerGlowEnabled"
        @toggle="toggleStyle('innerGlow', $event)"
        :expanded="expandedSections.innerGlow"
        @expand="expandedSections.innerGlow = $event"
      >
        <InnerGlowEditor
          v-if="layerStyles?.innerGlow"
          :style="layerStyles.innerGlow"
          @update="updateInnerGlow"
        />
      </StyleSection>

      <!-- Bevel and Emboss -->
      <StyleSection
        title="Bevel and Emboss"
        :enabled="bevelEmbossEnabled"
        @toggle="toggleStyle('bevelEmboss', $event)"
        :expanded="expandedSections.bevelEmboss"
        @expand="expandedSections.bevelEmboss = $event"
      >
        <BevelEmbossEditor
          v-if="layerStyles?.bevelEmboss"
          :style="layerStyles.bevelEmboss"
          @update="updateBevelEmboss"
        />
      </StyleSection>

      <!-- Satin -->
      <StyleSection
        title="Satin"
        :enabled="satinEnabled"
        @toggle="toggleStyle('satin', $event)"
        :expanded="expandedSections.satin"
        @expand="expandedSections.satin = $event"
      >
        <SatinEditor
          v-if="layerStyles?.satin"
          :style="layerStyles.satin"
          @update="updateSatin"
        />
      </StyleSection>

      <!-- Color Overlay -->
      <StyleSection
        title="Color Overlay"
        :enabled="colorOverlayEnabled"
        @toggle="toggleStyle('colorOverlay', $event)"
        :expanded="expandedSections.colorOverlay"
        @expand="expandedSections.colorOverlay = $event"
      >
        <ColorOverlayEditor
          v-if="layerStyles?.colorOverlay"
          :style="layerStyles.colorOverlay"
          @update="updateColorOverlay"
        />
      </StyleSection>

      <!-- Gradient Overlay -->
      <StyleSection
        title="Gradient Overlay"
        :enabled="gradientOverlayEnabled"
        @toggle="toggleStyle('gradientOverlay', $event)"
        :expanded="expandedSections.gradientOverlay"
        @expand="expandedSections.gradientOverlay = $event"
      >
        <GradientOverlayEditor
          v-if="layerStyles?.gradientOverlay"
          :style="layerStyles.gradientOverlay"
          @update="updateGradientOverlay"
        />
      </StyleSection>

      <!-- Stroke -->
      <StyleSection
        title="Stroke"
        :enabled="strokeEnabled"
        @toggle="toggleStyle('stroke', $event)"
        :expanded="expandedSections.stroke"
        @expand="expandedSections.stroke = $event"
      >
        <StrokeEditor
          v-if="layerStyles?.stroke"
          :style="layerStyles.stroke"
          @update="updateStroke"
        />
      </StyleSection>

      <!-- Blending Options -->
      <StyleSection
        title="Blending Options"
        :enabled="blendingOptionsEnabled"
        @toggle="toggleBlendingOptions"
        :expanded="expandedSections.blendingOptions"
        @expand="expandedSections.blendingOptions = $event"
      >
        <BlendingOptionsEditor
          v-if="layerStyles?.blendingOptions"
          :options="layerStyles.blendingOptions"
          @update="updateBlendingOptions"
        />
      </StyleSection>
    </div>

    <div class="no-layer" v-else>
      <p>Select a layer to edit styles</p>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, reactive } from "vue";
import {
  applyStylePreset,
  clearLayerStyles,
  copyLayerStyles,
  getStylePresetNames,
  hasStylesInClipboard,
  pasteLayerStyles,
  setLayerStylesEnabled,
  setStyleEnabled,
  updateStyleProperty,
} from "@/stores/actions/layerStyleActions";
import { useCompositorStore } from "@/stores/compositorStore";
import type { LayerStyles } from "@/types/layerStyles";

const store = useCompositorStore();

// Track expanded sections
const expandedSections = reactive({
  dropShadow: false,
  innerShadow: false,
  outerGlow: false,
  innerGlow: false,
  bevelEmboss: false,
  satin: false,
  colorOverlay: false,
  gradientOverlay: false,
  stroke: false,
  blendingOptions: false,
});

// Computed properties
const selectedLayer = computed(() => {
  const layers = store.getActiveCompLayers();
  const selected = store.selectedLayerIds[0];
  return layers.find((l) => l.id === selected) ?? null;
});

const layerStyles = computed(() => selectedLayer.value?.layerStyles);

const stylesEnabled = computed(() => layerStyles.value?.enabled ?? false);

const hasStyles = computed(() => !!layerStyles.value);

const canPaste = computed(() => hasStylesInClipboard());

const presetNames = computed(() => getStylePresetNames());

// Individual style enabled states
const dropShadowEnabled = computed(
  () => layerStyles.value?.dropShadow?.enabled ?? false,
);
const innerShadowEnabled = computed(
  () => layerStyles.value?.innerShadow?.enabled ?? false,
);
const outerGlowEnabled = computed(
  () => layerStyles.value?.outerGlow?.enabled ?? false,
);
const innerGlowEnabled = computed(
  () => layerStyles.value?.innerGlow?.enabled ?? false,
);
const bevelEmbossEnabled = computed(
  () => layerStyles.value?.bevelEmboss?.enabled ?? false,
);
const satinEnabled = computed(
  () => layerStyles.value?.satin?.enabled ?? false,
);
const colorOverlayEnabled = computed(
  () => layerStyles.value?.colorOverlay?.enabled ?? false,
);
const gradientOverlayEnabled = computed(
  () => layerStyles.value?.gradientOverlay?.enabled ?? false,
);
const strokeEnabled = computed(
  () => layerStyles.value?.stroke?.enabled ?? false,
);
const blendingOptionsEnabled = computed(
  () => !!layerStyles.value?.blendingOptions,
);

// Actions
function toggleStyles() {
  if (!selectedLayer.value) return;
  setLayerStylesEnabled(store, selectedLayer.value.id, !stylesEnabled.value);
}

function toggleStyle(styleType: keyof LayerStyles, enabled: boolean) {
  if (!selectedLayer.value) return;
  setStyleEnabled(store, selectedLayer.value.id, styleType, enabled);

  // Auto-expand when enabling
  if (enabled && styleType in expandedSections) {
    (expandedSections as any)[styleType] = true;
  }
}

function toggleBlendingOptions() {
  if (!selectedLayer.value) return;
  setStyleEnabled(
    store,
    selectedLayer.value.id,
    "blendingOptions",
    !blendingOptionsEnabled.value,
  );
}

function copyStyles() {
  if (!selectedLayer.value) return;
  copyLayerStyles(store, selectedLayer.value.id);
}

function pasteStyles() {
  if (!selectedLayer.value) return;
  pasteLayerStyles(store, selectedLayer.value.id);
}

function clearStyles() {
  if (!selectedLayer.value) return;
  clearLayerStyles(store, selectedLayer.value.id);
}

function applyPreset(event: Event) {
  const select = event.target as HTMLSelectElement;
  const preset = select.value;
  if (!preset || !selectedLayer.value) return;

  applyStylePreset(store, selectedLayer.value.id, preset);
  select.value = "";
}

function formatPresetName(name: string): string {
  return name
    .split("-")
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
    .join(" ");
}

// Style update handlers
function updateDropShadow(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "dropShadow",
      key as any,
      value,
    );
  });
}

function updateInnerShadow(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "innerShadow",
      key as any,
      value,
    );
  });
}

function updateOuterGlow(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "outerGlow",
      key as any,
      value,
    );
  });
}

function updateInnerGlow(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "innerGlow",
      key as any,
      value,
    );
  });
}

function updateBevelEmboss(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "bevelEmboss",
      key as any,
      value,
    );
  });
}

function updateSatin(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "satin",
      key as any,
      value,
    );
  });
}

function updateColorOverlay(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "colorOverlay",
      key as any,
      value,
    );
  });
}

function updateGradientOverlay(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "gradientOverlay",
      key as any,
      value,
    );
  });
}

function updateStroke(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "stroke",
      key as any,
      value,
    );
  });
}

function updateBlendingOptions(updates: any) {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  Object.entries(updates).forEach(([key, value]) => {
    updateStyleProperty(
      store,
      layerId,
      "blendingOptions",
      key as any,
      value,
    );
  });
}
</script>

<style scoped>
.layer-styles-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1);
  color: var(--lattice-text-primary);
  font-size: var(--lattice-font-size-sm);
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 12px;
  background: var(--lattice-surface-0);
  border-bottom: 1px solid var(--lattice-border-subtle);
}

.header-left {
  display: flex;
  align-items: center;
}

.master-toggle {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
}

.master-toggle input {
  width: 14px;
  height: 14px;
  accent-color: var(--lattice-accent);
}

.toggle-label {
  font-weight: 600;
  font-size: var(--lattice-font-size-base);
}

.header-actions {
  display: flex;
  align-items: center;
  gap: 4px;
}

.action-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  width: 24px;
  height: 24px;
  background: var(--lattice-surface-2);
  border: 1px solid var(--lattice-border-subtle);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-secondary);
  cursor: pointer;
  transition: all 0.15s ease;
}

.action-btn:hover:not(:disabled) {
  background: var(--lattice-surface-3);
  border-color: var(--lattice-accent);
  color: var(--lattice-text-primary);
}

.action-btn:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.action-btn .icon {
  font-size: 12px;
}

.preset-select {
  padding: 4px 8px;
  background: var(--lattice-surface-2);
  border: 1px solid var(--lattice-border-subtle);
  border-radius: var(--lattice-radius-sm);
  color: var(--lattice-text-secondary);
  font-size: var(--lattice-font-size-xs);
  cursor: pointer;
}

.preset-select:hover {
  border-color: var(--lattice-accent);
}

.styles-list {
  flex: 1;
  overflow-y: auto;
  padding: 4px 0;
}

.no-layer {
  display: flex;
  align-items: center;
  justify-content: center;
  height: 100%;
  color: var(--lattice-text-muted);
  font-size: var(--lattice-font-size-sm);
}
</style>
