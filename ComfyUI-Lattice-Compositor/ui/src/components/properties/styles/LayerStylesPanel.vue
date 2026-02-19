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
          v-if="hasDropShadow"
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
          v-if="hasInnerShadow"
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
          v-if="hasOuterGlow"
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
          v-if="hasInnerGlow"
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
          v-if="hasBevelEmboss"
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
          v-if="hasSatin"
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
          v-if="hasColorOverlay"
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
          v-if="hasGradientOverlay"
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
          v-if="hasStroke"
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
          v-if="hasBlendingOptions"
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
import { useEffectStore } from "@/stores/effectStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import type {
  BevelEmbossUpdate,
  ColorOverlayUpdate,
  DropShadowUpdate,
  GradientOverlayUpdate,
  InnerGlowUpdate,
  InnerShadowUpdate,
  LayerStyles,
  OuterGlowUpdate,
  SatinUpdate,
  StrokeStyleUpdate,
  StyleBlendingOptionsUpdate,
  RGBA,
  ContourCurve,
  GradientStop,
} from "@/types/layerStyles";
import type { BlendMode } from "@/types/project";

const projectStore = useProjectStore();
const selectionStore = useSelectionStore();

// Track expanded sections - subset of LayerStyles that can be expanded
type ExpandableStyleType =
  | "dropShadow"
  | "innerShadow"
  | "outerGlow"
  | "innerGlow"
  | "bevelEmboss"
  | "satin"
  | "colorOverlay"
  | "gradientOverlay"
  | "stroke"
  | "blendingOptions";

const expandedSections = reactive<Record<ExpandableStyleType, boolean>>({
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

function isExpandableStyleType(
  styleType: keyof LayerStyles,
): styleType is ExpandableStyleType {
  return styleType in expandedSections;
}

// Computed properties
const selectedLayer = computed(() => {
  const layers = projectStore.getActiveCompLayers();
  const selected = selectionStore.selectedLayerIds[0];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing
  // Pattern match: layers.find(...) ∈ Layer | undefined → Layer | null
  const foundLayer = layers.find((l) => l.id === selected);
  return (foundLayer !== undefined) ? foundLayer : null;
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
const layerStyles = computed(() => {
  const selectedLayerVal = selectedLayer.value;
  return (selectedLayerVal != null && typeof selectedLayerVal === "object" && "layerStyles" in selectedLayerVal && selectedLayerVal.layerStyles != null) ? selectedLayerVal.layerStyles : undefined;
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing
// Pattern match: layerStyles.value.enabled ∈ boolean | undefined → boolean (default false)
const stylesEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  return (layerStylesValue !== null && typeof layerStylesValue === "object" && "enabled" in layerStylesValue && typeof layerStylesValue.enabled === "boolean") ? layerStylesValue.enabled : false;
});

const hasStyles = computed(() => !!layerStyles.value);

const effectStore = useEffectStore();

const canPaste = computed(() => effectStore.hasStylesInClipboard());

const presetNames = computed(() => effectStore.getStylePresetNames());

// Individual style enabled states
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy nullish coalescing
// Pattern match: layerStyles.value.dropShadow.enabled ∈ boolean | undefined → boolean (default false)
const dropShadowEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "dropShadow" in layerStylesValue && layerStylesValue.dropShadow !== null && typeof layerStylesValue.dropShadow === "object" && "enabled" in layerStylesValue.dropShadow && typeof layerStylesValue.dropShadow.enabled === "boolean") {
    return layerStylesValue.dropShadow.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.innerShadow.enabled ∈ boolean | undefined → boolean (default false)
const innerShadowEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "innerShadow" in layerStylesValue && layerStylesValue.innerShadow !== null && typeof layerStylesValue.innerShadow === "object" && "enabled" in layerStylesValue.innerShadow && typeof layerStylesValue.innerShadow.enabled === "boolean") {
    return layerStylesValue.innerShadow.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.outerGlow.enabled ∈ boolean | undefined → boolean (default false)
const outerGlowEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "outerGlow" in layerStylesValue && layerStylesValue.outerGlow !== null && typeof layerStylesValue.outerGlow === "object" && "enabled" in layerStylesValue.outerGlow && typeof layerStylesValue.outerGlow.enabled === "boolean") {
    return layerStylesValue.outerGlow.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.innerGlow.enabled ∈ boolean | undefined → boolean (default false)
const innerGlowEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "innerGlow" in layerStylesValue && layerStylesValue.innerGlow !== null && typeof layerStylesValue.innerGlow === "object" && "enabled" in layerStylesValue.innerGlow && typeof layerStylesValue.innerGlow.enabled === "boolean") {
    return layerStylesValue.innerGlow.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.bevelEmboss.enabled ∈ boolean | undefined → boolean (default false)
const bevelEmbossEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "bevelEmboss" in layerStylesValue && layerStylesValue.bevelEmboss !== null && typeof layerStylesValue.bevelEmboss === "object" && "enabled" in layerStylesValue.bevelEmboss && typeof layerStylesValue.bevelEmboss.enabled === "boolean") {
    return layerStylesValue.bevelEmboss.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.satin.enabled ∈ boolean | undefined → boolean (default false)
const satinEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "satin" in layerStylesValue && layerStylesValue.satin !== null && typeof layerStylesValue.satin === "object" && "enabled" in layerStylesValue.satin && typeof layerStylesValue.satin.enabled === "boolean") {
    return layerStylesValue.satin.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.colorOverlay.enabled ∈ boolean | undefined → boolean (default false)
const colorOverlayEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "colorOverlay" in layerStylesValue && layerStylesValue.colorOverlay !== null && typeof layerStylesValue.colorOverlay === "object" && "enabled" in layerStylesValue.colorOverlay && typeof layerStylesValue.colorOverlay.enabled === "boolean") {
    return layerStylesValue.colorOverlay.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.gradientOverlay.enabled ∈ boolean | undefined → boolean (default false)
const gradientOverlayEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "gradientOverlay" in layerStylesValue && layerStylesValue.gradientOverlay !== null && typeof layerStylesValue.gradientOverlay === "object" && "enabled" in layerStylesValue.gradientOverlay && typeof layerStylesValue.gradientOverlay.enabled === "boolean") {
    return layerStylesValue.gradientOverlay.enabled;
  }
  return false;
});
// Pattern match: layerStyles.value.stroke.enabled ∈ boolean | undefined → boolean (default false)
const strokeEnabled = computed(() => {
  const layerStylesValue = layerStyles.value;
  if (layerStylesValue !== null && typeof layerStylesValue === "object" && "stroke" in layerStylesValue && layerStylesValue.stroke !== null && typeof layerStylesValue.stroke === "object" && "enabled" in layerStylesValue.stroke && typeof layerStylesValue.stroke.enabled === "boolean") {
    return layerStylesValue.stroke.enabled;
  }
  return false;
});
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
const blendingOptionsEnabled = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "blendingOptions" in layerStylesVal && layerStylesVal.blendingOptions != null);
});

// Computed properties for template v-if checks (explicit pattern matching - no lazy ?.)
const hasDropShadow = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "dropShadow" in layerStylesVal && layerStylesVal.dropShadow != null);
});
const hasInnerShadow = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "innerShadow" in layerStylesVal && layerStylesVal.innerShadow != null);
});
const hasOuterGlow = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "outerGlow" in layerStylesVal && layerStylesVal.outerGlow != null);
});
const hasInnerGlow = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "innerGlow" in layerStylesVal && layerStylesVal.innerGlow != null);
});
const hasBevelEmboss = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "bevelEmboss" in layerStylesVal && layerStylesVal.bevelEmboss != null);
});
const hasSatin = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "satin" in layerStylesVal && layerStylesVal.satin != null);
});
const hasColorOverlay = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "colorOverlay" in layerStylesVal && layerStylesVal.colorOverlay != null);
});
const hasGradientOverlay = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "gradientOverlay" in layerStylesVal && layerStylesVal.gradientOverlay != null);
});
const hasStroke = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "stroke" in layerStylesVal && layerStylesVal.stroke != null);
});
const hasBlendingOptions = computed(() => {
  const layerStylesVal = layerStyles.value;
  return !!(layerStylesVal != null && typeof layerStylesVal === "object" && "blendingOptions" in layerStylesVal && layerStylesVal.blendingOptions != null);
});

// Actions
function toggleStyles() {
  if (!selectedLayer.value) return;
  effectStore.setLayerStylesEnabled(selectedLayer.value.id, !stylesEnabled.value);
}

function toggleStyle(styleType: keyof LayerStyles, enabled: boolean) {
  if (!selectedLayer.value) return;
  effectStore.setStyleEnabled(selectedLayer.value.id, styleType, enabled);

  // Auto-expand when enabling
  if (enabled && isExpandableStyleType(styleType)) {
    expandedSections[styleType] = true;
  }
}

function toggleBlendingOptions() {
  if (!selectedLayer.value) return;
  effectStore.setStyleEnabled(
    selectedLayer.value.id,
    "blendingOptions",
    !blendingOptionsEnabled.value,
  );
}

function copyStyles() {
  if (!selectedLayer.value) return;
  effectStore.copyLayerStyles(selectedLayer.value.id);
}

function pasteStyles() {
  if (!selectedLayer.value) return;
  effectStore.pasteLayerStyles(selectedLayer.value.id);
}

function clearStyles() {
  if (!selectedLayer.value) return;
  effectStore.clearLayerStyles(selectedLayer.value.id);
}

function applyPreset(event: Event) {
  const select = event.target as HTMLSelectElement;
  const preset = select.value;
  if (!preset || !selectedLayer.value) return;

  effectStore.applyStylePreset(selectedLayer.value.id, preset);
  select.value = "";
}

function formatPresetName(name: string): string {
  return name
    .split("-")
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
    .join(" ");
}

// Style update handlers - generic helper to reduce duplication
function applyStyleUpdates<T extends keyof LayerStyles>(
  styleType: T,
  updates: Partial<NonNullable<LayerStyles[T]>>,
): void {
  if (!selectedLayer.value) return;
  const layerId = selectedLayer.value.id;
  for (const [key, value] of Object.entries(updates)) {
    // Type assertion needed because Object.entries loses key type info
    // The updateStyleProperty function validates keys at runtime
    effectStore.updateStyleProperty(
      layerId,
      styleType,
      key as keyof NonNullable<LayerStyles[T]>,
      value as string | number | boolean | RGBA | BlendMode | ContourCurve | GradientStop[] | null | undefined,
    );
  }
}

function updateDropShadow(updates: DropShadowUpdate) {
  applyStyleUpdates("dropShadow", updates);
}

function updateInnerShadow(updates: InnerShadowUpdate) {
  applyStyleUpdates("innerShadow", updates);
}

function updateOuterGlow(updates: OuterGlowUpdate) {
  applyStyleUpdates("outerGlow", updates);
}

function updateInnerGlow(updates: InnerGlowUpdate) {
  applyStyleUpdates("innerGlow", updates);
}

function updateBevelEmboss(updates: BevelEmbossUpdate) {
  applyStyleUpdates("bevelEmboss", updates);
}

function updateSatin(updates: SatinUpdate) {
  applyStyleUpdates("satin", updates);
}

function updateColorOverlay(updates: ColorOverlayUpdate) {
  applyStyleUpdates("colorOverlay", updates);
}

function updateGradientOverlay(updates: GradientOverlayUpdate) {
  applyStyleUpdates("gradientOverlay", updates);
}

function updateStroke(updates: StrokeStyleUpdate) {
  applyStyleUpdates("stroke", updates);
}

function updateBlendingOptions(updates: StyleBlendingOptionsUpdate) {
  applyStyleUpdates("blendingOptions", updates);
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
