<template>
  <div class="effect-controls">
    <div class="panel-header">
      <div class="header-row">
        <h3>Effect Controls</h3>
        <div class="layer-badge" v-if="layer">
          <span class="layer-type-icon">{{ getLayerIcon(layer.type) }}</span>
          {{ layer.name }}
        </div>
      </div>

      <div class="add-effect-wrapper" ref="menuRef">
        <button class="add-btn" @click="showAddMenu = !showAddMenu" :disabled="!layer">
          <span class="icon">+</span> Add Effect
        </button>

        <div v-if="showAddMenu" class="effect-menu">
          <div v-for="(catInfo, catKey) in categories" :key="catKey" class="effect-category">
            <div class="category-label">
              <span class="cat-icon">{{ catInfo.icon }}</span> {{ catInfo.label }}
            </div>
            <div class="category-items">
              <button
                v-for="def in getEffectsByCategory(catKey)"
                :key="def.key"
                @click="addEffect(def.key)"
              >
                {{ def.name }}
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>

    <div class="panel-content">
      <div v-if="!layer" class="empty-state">
        Select a layer to edit effects
      </div>

      <div v-else-if="!layer.effects || layer.effects.length === 0" class="empty-state">
        No effects applied
      </div>

      <div v-else class="effects-list">
        <div
          v-for="(effect, index) in layer.effects"
          :key="effect.id"
          class="effect-item"
          :class="{ collapsed: !effect.expanded, 'drag-over': dragOverEffectId === effect.id }"
          draggable="true"
          @dragstart="onDragStart($event, index)"
          @dragend="onDragEnd"
          @dragover.prevent="onDragOver($event, effect.id)"
          @dragleave="onDragLeave"
          @drop="onDrop($event, index)"
        >
          <div class="effect-header" @click="toggleExpand(effect)">
            <div class="header-left">
              <span class="arrow">{{ effect.expanded ? '▼' : '▶' }}</span>
              <button class="icon-btn" @click.stop="toggleEffect(effect)">
                <span class="fx-icon" :class="{ disabled: !effect.enabled }">fx</span>
              </button>
              <span class="effect-name">{{ effect.name }}</span>
            </div>
            <div class="header-right">
              <button class="icon-btn delete" @click.stop="removeEffect(effect)" title="Remove Effect">×</button>
            </div>
          </div>

          <div v-if="effect.expanded" class="effect-params">
            <div
              v-for="(param, key) in effect.parameters"
              :key="key"
              class="param-row"
            >
              <div class="param-header">
                <span class="param-name" :title="String(key)">{{ param.name }}</span>
                <button
                  class="keyframe-toggle"
                  :class="{ active: param.animated }"
                  @click="toggleParamAnim(effect.id, String(key))"
                  title="Toggle Animation"
                >◆</button>
              </div>

              <div class="param-control">
                <!-- Angle parameters (stored as 'number' type but originally 'angle') -->
                <template v-if="param.type === 'number' && isAngleParam(effect.effectKey, String(key))">
                  <div class="control-group">
                    <AngleDial
                      :modelValue="param.value"
                      @update:modelValue="(v: number) => updateParam(effect.id, String(key), v)"
                      :size="32"
                      :showValue="false"
                    />
                    <ScrubableNumber
                      :modelValue="param.value"
                      @update:modelValue="(v: number) => updateParam(effect.id, String(key), v)"
                      unit="°"
                    />
                  </div>
                </template>

                <!-- Regular number parameters -->
                <template v-else-if="param.type === 'number'">
                  <div class="control-group">
                    <SliderInput
                      v-if="hasRange(effect.effectKey, String(key))"
                      :modelValue="param.value"
                      @update:modelValue="(v: number) => updateParam(effect.id, String(key), v)"
                      :min="getParamDefMin(effect.effectKey, String(key))"
                      :max="getParamDefMax(effect.effectKey, String(key))"
                      :step="getParamDefStep(effect.effectKey, String(key), 1)"
                      :showValue="false"
                    />
                    <ScrubableNumber
                      :modelValue="param.value"
                      @update:modelValue="(v: number) => updateParam(effect.id, String(key), v)"
                      :step="getParamDefStep(effect.effectKey, String(key), 0.1)"
                    />
                  </div>
                </template>

                <template v-else-if="param.type === 'position'">
                  <div class="control-group point-group">
                    <ScrubableNumber
                      :modelValue="param.value.x"
                      @update:modelValue="(v: number) => updatePoint(effect.id, String(key), 'x', v)"
                      label="X"
                    />
                    <ScrubableNumber
                      :modelValue="param.value.y"
                      @update:modelValue="(v: number) => updatePoint(effect.id, String(key), 'y', v)"
                      label="Y"
                    />
                  </div>
                </template>

                <template v-else-if="param.type === 'color'">
                  <ColorPicker
                    :modelValue="formatColor(param.value)"
                    @update:modelValue="(v: string) => updateColor(effect.id, String(key), v)"
                    :alpha="true"
                  />
                </template>

                <template v-else-if="param.type === 'enum' && isCheckbox(effect.effectKey, String(key))">
                  <input
                    type="checkbox"
                    :checked="param.value"
                    @change="(e) => updateParam(effect.id, String(key), (e.target as HTMLInputElement).checked)"
                  />
                </template>

                <template v-else-if="param.type === 'enum'">
                  <select
                    :value="param.value"
                    @change="(e) => updateParam(effect.id, String(key), (e.target as HTMLSelectElement).value)"
                    class="param-select"
                  >
                    <option
                      v-for="opt in getParamOptions(effect.effectKey, String(key))"
                      :key="opt.value"
                      :value="opt.value"
                    >
                      {{ opt.label }}
                    </option>
                  </select>
                </template>

                <!-- Layer picker for displacement map sources -->
                <template v-else-if="isLayerParam(effect.effectKey, String(key))">
                  <select
                    :value="param.value"
                    @change="(e) => updateParam(effect.id, String(key), (e.target as HTMLSelectElement).value || null)"
                    class="param-select layer-select"
                  >
                    <option value="">None</option>
                    <option
                      v-for="availableLayer in getAvailableLayers()"
                      :key="availableLayer.id"
                      :value="availableLayer.id"
                    >
                      {{ availableLayer.name }}
                    </option>
                  </select>
                </template>
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref } from "vue";
import { useEffectStore, type EffectStoreAccess } from "@/stores/effectStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { EFFECT_CATEGORIES, EFFECT_DEFINITIONS } from "@/types/effects";
import { hexToRgba, rgbaToHex } from "@/utils/colorUtils";

const projectStore = useProjectStore();
const selectionStore = useSelectionStore();
const effectStore = useEffectStore();
const showAddMenu = ref(false);
const menuRef = ref<HTMLDivElement | null>(null);

// Drag state
const dragOverEffectId = ref<string | null>(null);
const draggedIndex = ref<number | null>(null);

// Get selected layer from selectionStore and projectStore
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
const layer = computed(() => {
  const selectedId = selectionStore.selectedLayerIds[0];
  if (!selectedId) return null;
  const layers = projectStore.getActiveCompLayers();
  const found = layers.find((l) => l.id === selectedId);
  return found !== undefined ? found : null;
});
const categories = EFFECT_CATEGORIES;

// Helper function to create EffectStoreAccess interface
function getEffectStoreAccess(): EffectStoreAccess {
  return {
    project: {
      meta: projectStore.project.meta,
    },
    currentFrame: 0, // Not used by effect methods
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    getActiveComp: () => projectStore.getActiveComp(),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// ── Helpers ───────────────────────────────────────────────────────────────

function getEffectsByCategory(cat: string) {
  return Object.entries(EFFECT_DEFINITIONS)
    .filter(([_, def]) => def.category === cat)
    .map(([key, def]) => ({ key, ...def }));
}

function getParamDef(effectKey: string, paramKey: string) {
  const def = EFFECT_DEFINITIONS[effectKey];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (def == null || typeof def !== "object" || !("parameters" in def) || !Array.isArray(def.parameters)) return undefined;
  return def.parameters.find((p) => formatParamKey(p.name) === paramKey);
}

// Utility to match the key generation in createEffectInstance
function formatParamKey(name: string) {
  return name
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_|_$/g, "");
}

function hasRange(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  return def && (def.min !== undefined || def.max !== undefined);
}

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
// Helper functions for optional paramDef properties
function getParamDefMin(effectKey: string, paramKey: string): number {
  const def = getParamDef(effectKey, paramKey);
  return (def !== null && def !== undefined && typeof def === "object" && "min" in def && typeof def.min === "number" && Number.isFinite(def.min)) ? def.min : 0;
}
function getParamDefMax(effectKey: string, paramKey: string): number {
  const def = getParamDef(effectKey, paramKey);
  return (def !== null && def !== undefined && typeof def === "object" && "max" in def && typeof def.max === "number" && Number.isFinite(def.max)) ? def.max : 100;
}
function getParamDefStep(effectKey: string, paramKey: string, defaultStep: number = 1): number {
  const def = getParamDef(effectKey, paramKey);
  return (def !== null && def !== undefined && typeof def === "object" && "step" in def && typeof def.step === "number" && Number.isFinite(def.step) && def.step > 0) ? def.step : defaultStep;
}

function isCheckbox(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  return (def != null && typeof def === "object" && "type" in def && typeof def.type === "string" && def.type === "checkbox") ? true : false;
}

function isAngleParam(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  return (def != null && typeof def === "object" && "type" in def && typeof def.type === "string" && def.type === "angle") ? true : false;
}

function isLayerParam(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  return (def != null && typeof def === "object" && "type" in def && typeof def.type === "string" && def.type === "layer") ? true : false;
}

function getAvailableLayers() {
  const comp = projectStore.getActiveComp();
  if (!comp) return [];
  // Return all layers except the currently selected one (can't use self as displacement map)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layerValue = layer.value;
  const layerId = (layerValue != null && typeof layerValue === "object" && "id" in layerValue && typeof layerValue.id === "string") ? layerValue.id : undefined;
  return comp.layers.filter((l) => l.id !== layerId);
}

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
function getParamOptions(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  const options = (def !== null && def !== undefined && typeof def === "object" && "options" in def && Array.isArray(def.options)) ? def.options : [];
  return options;
}

function getLayerIcon(type: string) {
  const icons: Record<string, string> = {
    solid: "■",
    text: "T",
    spline: "~",
    null: "□",
    camera: "📷",
    light: "💡",
    particles: "✦",
    image: "🖼",
  };
  return icons[type] || "•";
}

// ── Actions ───────────────────────────────────────────────────────────────

function addEffect(key: string) {
  if (layer.value) {
    effectStore.addEffectToLayer(layer.value.id, key);
    showAddMenu.value = false;
  }
}

function removeEffect(effect: { id: string }) {
  if (layer.value) effectStore.removeEffectFromLayer(layer.value.id, effect.id);
}

function toggleEffect(effect: { id: string }) {
  if (layer.value) effectStore.toggleEffect(layer.value.id, effect.id);
}

function toggleExpand(effect: { expanded?: boolean }) {
  effect.expanded = !effect.expanded;
}

function updateParam(
  effectId: string,
  paramKey: string,
  value: import("@/types/effects").EffectParameterValue,
) {
  if (layer.value)
    effectStore.updateEffectParameter(layer.value.id, effectId, paramKey, value);
}

function updatePoint(
  effectId: string,
  paramKey: string,
  axis: "x" | "y",
  val: number,
) {
  if (!layer.value) return;
  const effect = layer.value.effects.find(
    (e): e is import("@/types/effects").EffectInstance => e.id === effectId,
  );
  if (!effect) return;

  const current = effect.parameters[paramKey].value;
  const newValue = { ...current, [axis]: val };
  effectStore.updateEffectParameter(layer.value.id, effectId, paramKey, newValue);
}

// Color handling: Store uses RGBA object {r,g,b,a}, Picker uses Hex string
function formatColor(
  val: import("@/types/effects").EffectParameterValue,
): string {
  if (typeof val === "string") return val;
  if (
    typeof val === "object" &&
    val !== null &&
    "r" in val &&
    "g" in val &&
    "b" in val
  ) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const rgba = val as { r: number; g: number; b: number; a?: number };
    const alpha = (typeof rgba.a === "number" && Number.isFinite(rgba.a)) ? rgba.a : 1;
    return rgbaToHex(rgba.r, rgba.g, rgba.b, alpha);
  }
  return "#ffffff"; // Fallback
}

function updateColor(effectId: string, paramKey: string, hex: string) {
  const rgba = hexToRgba(hex);
  if (rgba && layer.value) {
    const val = { r: rgba[0], g: rgba[1], b: rgba[2], a: rgba[3] };
    effectStore.updateEffectParameter(layer.value.id, effectId, paramKey, val);
  }
}

function toggleParamAnim(effectId: string, paramKey: string) {
  if (!layer.value) return;
  const effect = layer.value.effects.find(
    (e): e is import("@/types/effects").EffectInstance => e.id === effectId,
  );
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const parameters = (effect != null && typeof effect === "object" && "parameters" in effect && effect.parameters != null && typeof effect.parameters === "object") ? effect.parameters : undefined;
  const param = (parameters != null && typeof parameters === "object" && paramKey in parameters) ? parameters[paramKey] : undefined;
  if (param) {
    effectStore.setEffectParamAnimated(
      store,
      layer.value.id,
      effectId,
      paramKey,
      !param.animated,
    );
  }
}

// ── Drag & Drop ───────────────────────────────────────────────────────────

function onDragStart(event: DragEvent, index: number) {
  if (!event.dataTransfer) return;
  draggedIndex.value = index;
  event.dataTransfer.setData("application/effect-reorder", String(index));
  event.dataTransfer.effectAllowed = "move";
}

function onDragEnd() {
  draggedIndex.value = null;
  dragOverEffectId.value = null;
}

function onDragOver(event: DragEvent, effectId: string) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  const types = (dataTransfer != null && typeof dataTransfer === "object" && "types" in dataTransfer && dataTransfer.types != null && Array.isArray(dataTransfer.types)) ? dataTransfer.types : undefined;
  const data = (types != null && types.includes("application/effect-reorder")) ? true : false;
  if (data) {
    dragOverEffectId.value = effectId;
  }
}

function onDragLeave() {
  dragOverEffectId.value = null;
}

function onDrop(event: DragEvent, targetIndex: number) {
  dragOverEffectId.value = null;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  const fromIndexStr = (dataTransfer != null && typeof dataTransfer === "object" && typeof dataTransfer.getData === "function") ? dataTransfer.getData("application/effect-reorder") : undefined;
  if (!fromIndexStr || !layer.value) return;

  const fromIndex = parseInt(fromIndexStr, 10);
  if (fromIndex !== targetIndex && !Number.isNaN(fromIndex)) {
    effectStore.reorderEffects(layer.value.id, fromIndex, targetIndex);
  }
}

// Click outside menu
function onClickOutside(e: MouseEvent) {
  if (menuRef.value && !menuRef.value.contains(e.target as Node)) {
    showAddMenu.value = false;
  }
}

onMounted(() => window.addEventListener("mousedown", onClickOutside));
onUnmounted(() => window.removeEventListener("mousedown", onClickOutside));
</script>

<style scoped>
.effect-controls {
  height: 100%;
  display: flex;
  flex-direction: column;
  background: #1e1e1e;
  color: #ccc;
  font-size: 13px;
}

.panel-header {
  padding: 8px;
  background: #252525;
  border-bottom: 1px solid #111;
}

.header-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 8px;
}

h3 { margin: 0; font-size: 13px; font-weight: 600; color: #888; text-transform: uppercase; }

.layer-badge {
  background: #333;
  padding: 2px 6px;
  border-radius: 3px;
  color: #fff;
  font-size: 12px;
  display: flex;
  align-items: center;
  gap: 4px;
}

.add-effect-wrapper { position: relative; }

.add-btn {
  width: 100%;
  background: #333;
  border: 1px solid #444;
  color: #eee;
  padding: 4px;
  cursor: pointer;
  border-radius: 3px;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
}
.add-btn:hover:not(:disabled) { background: #444; }
.add-btn:disabled { opacity: 0.5; cursor: default; }

.effect-menu {
  position: absolute;
  top: 100%;
  left: 0;
  right: 0;
  background: #2a2a2a;
  border: 1px solid #000;
  box-shadow: 0 4px 12px rgba(0,0,0,0.5);
  z-index: 1000;
  max-height: 400px;
  overflow-y: auto;
  margin-top: 2px;
}

.category-label {
  padding: 4px 8px;
  background: #222;
  color: #888;
  font-weight: 600;
  border-bottom: 1px solid #333;
  position: sticky;
  top: 0;
}

.category-items button {
  display: block;
  width: 100%;
  text-align: left;
  padding: 6px 12px;
  background: transparent;
  border: none;
  color: #ccc;
  cursor: pointer;
  border-bottom: 1px solid #333;
}
.category-items button:hover { background: #4a90d9; color: #fff; }

.panel-content { flex: 1; overflow-y: auto; overflow-x: hidden; }

.empty-state {
  padding: 20px;
  text-align: center;
  color: #666;
  font-style: italic;
}

.effect-item {
  border-bottom: 1px solid #111;
  background: #222;
  cursor: grab;
}
.effect-item:active { cursor: grabbing; }
.effect-item.drag-over {
  background: #2a4a6a;
  border-top: 2px solid #4a90d9;
  margin-top: -2px;
}

.effect-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 4px 2px;
  cursor: pointer;
  background: #2a2a2a;
  border-bottom: 1px solid #333;
}
.effect-header:hover { background: #333; }

.header-left { display: flex; align-items: center; gap: 4px; }
.arrow { font-size: 11px; width: 12px; text-align: center; color: #888; }
.fx-icon { font-family: serif; font-weight: bold; font-size: 12px; color: #4a90d9; }
.fx-icon.disabled { color: #555; }
.effect-name { font-weight: 600; color: #eee; }

.icon-btn {
  background: transparent;
  border: none;
  color: #888;
  cursor: pointer;
  padding: 2px;
  display: flex;
  align-items: center;
  justify-content: center;
}
.icon-btn:hover { color: #fff; }
.icon-btn.delete:hover { color: #ff4444; }

.effect-params {
  padding: 4px 0;
  background: #1e1e1e;
}

.param-row {
  padding: 4px 8px;
  display: flex;
  flex-direction: column;
  gap: 2px;
  border-bottom: 1px solid #252525;
}

.param-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.param-name { color: #aaa; }

.keyframe-toggle {
  background: transparent;
  border: none;
  color: #444;
  cursor: pointer;
  font-size: 12px;
  padding: 0;
}
.keyframe-toggle:hover { color: #888; }
.keyframe-toggle.active { color: #4a90d9; }

.control-group {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-top: 2px;
}

.point-group {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 8px;
}

.param-select {
  width: 100%;
  background: #111;
  border: 1px solid #333;
  color: #ccc;
  padding: 2px 4px;
  border-radius: 2px;
  font-size: 12px;
}

.layer-select {
  background: #1a1a2a;
  border-color: #4a4a6a;
}

.layer-select:focus {
  border-color: #6a6aaa;
  outline: none;
}
</style>
