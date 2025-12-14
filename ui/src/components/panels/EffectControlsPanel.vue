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
          :class="{ collapsed: !effect.expanded }"
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
                  class="stopwatch"
                  :class="{ active: param.animated }"
                  @click="toggleParamAnim(effect.id, String(key))"
                  title="Toggle Animation"
                >⏱</button>
              </div>

              <div class="param-control">
                <template v-if="param.type === 'number'">
                  <div class="control-group">
                    <SliderInput
                      v-if="hasRange(effect.effectKey, String(key))"
                      :modelValue="param.value"
                      @update:modelValue="(v) => updateParam(effect.id, String(key), v)"
                      :min="getParamDef(effect.effectKey, String(key))?.min ?? 0"
                      :max="getParamDef(effect.effectKey, String(key))?.max ?? 100"
                      :step="getParamDef(effect.effectKey, String(key))?.step ?? 1"
                      :showValue="false"
                    />
                    <ScrubableNumber
                      :modelValue="param.value"
                      @update:modelValue="(v) => updateParam(effect.id, String(key), v)"
                      :step="getParamDef(effect.effectKey, String(key))?.step ?? 0.1"
                    />
                  </div>
                </template>

                <template v-else-if="param.type === 'angle'">
                  <div class="control-group">
                    <AngleDial
                      :modelValue="param.value"
                      @update:modelValue="(v) => updateParam(effect.id, String(key), v)"
                      :size="32"
                      :showValue="false"
                    />
                    <ScrubableNumber
                      :modelValue="param.value"
                      @update:modelValue="(v) => updateParam(effect.id, String(key), v)"
                      unit="°"
                    />
                  </div>
                </template>

                <template v-else-if="param.type === 'position'">
                  <div class="control-group point-group">
                    <ScrubableNumber
                      :modelValue="param.value.x"
                      @update:modelValue="(v) => updatePoint(effect.id, String(key), 'x', v)"
                      label="X"
                    />
                    <ScrubableNumber
                      :modelValue="param.value.y"
                      @update:modelValue="(v) => updatePoint(effect.id, String(key), 'y', v)"
                      label="Y"
                    />
                  </div>
                </template>

                <template v-else-if="param.type === 'color'">
                  <ColorPicker
                    :modelValue="formatColor(param.value)"
                    @update:modelValue="(v) => updateColor(effect.id, String(key), v)"
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
              </div>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { EFFECT_DEFINITIONS, EFFECT_CATEGORIES, type EffectCategory } from '@/types/effects';
import ScrubableNumber from '@/components/controls/ScrubableNumber.vue';
import SliderInput from '@/components/controls/SliderInput.vue';
import AngleDial from '@/components/controls/AngleDial.vue';
import ColorPicker from '@/components/controls/ColorPicker.vue';
import { rgbaToHex, hexToRgba } from '@/utils/colorUtils';

const store = useCompositorStore();
const showAddMenu = ref(false);
const menuRef = ref<HTMLDivElement | null>(null);

const layer = computed(() => store.selectedLayer);
const categories = EFFECT_CATEGORIES;

// --- Helpers ---

function getEffectsByCategory(cat: string) {
  return Object.entries(EFFECT_DEFINITIONS)
    .filter(([_, def]) => def.category === cat)
    .map(([key, def]) => ({ key, ...def }));
}

function getParamDef(effectKey: string, paramKey: string) {
  const def = EFFECT_DEFINITIONS[effectKey];
  return def?.parameters.find(p => formatParamKey(p.name) === paramKey);
}

// Utility to match the key generation in createEffectInstance
function formatParamKey(name: string) {
  return name.toLowerCase().replace(/[^a-z0-9]+/g, '_').replace(/^_|_$/g, '');
}

function hasRange(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  return def && (def.min !== undefined || def.max !== undefined);
}

function isCheckbox(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  return def?.type === 'checkbox';
}

function getParamOptions(effectKey: string, paramKey: string) {
  const def = getParamDef(effectKey, paramKey);
  return def?.options || [];
}

function getLayerIcon(type: string) {
  const icons: Record<string, string> = {
    solid: '■', text: 'T', spline: '~', null: '□',
    camera: '📷', light: '💡', particles: '✦', image: '🖼'
  };
  return icons[type] || '•';
}

// --- Actions ---

function addEffect(key: string) {
  if(layer.value) {
    store.addEffectToLayer(layer.value.id, key);
    showAddMenu.value = false;
  }
}

function removeEffect(effect: any) {
  if(layer.value) store.removeEffectFromLayer(layer.value.id, effect.id);
}

function toggleEffect(effect: any) {
  if(layer.value) store.toggleEffect(layer.value.id, effect.id);
}

function toggleExpand(effect: any) {
  effect.expanded = !effect.expanded;
}

function updateParam(effectId: string, paramKey: string, value: any) {
  if(layer.value) store.updateEffectParameter(layer.value.id, effectId, paramKey, value);
}

function updatePoint(effectId: string, paramKey: string, axis: 'x'|'y', val: number) {
  if(!layer.value) return;
  const effect = layer.value.effects.find((e: any) => e.id === effectId);
  if(!effect) return;

  const current = effect.parameters[paramKey].value;
  const newValue = { ...current, [axis]: val };
  store.updateEffectParameter(layer.value.id, effectId, paramKey, newValue);
}

// Color handling: Store uses RGBA object {r,g,b,a}, Picker uses Hex string
function formatColor(val: any) {
  if(typeof val === 'string') return val;
  return rgbaToHex(val.r, val.g, val.b, val.a ?? 1);
}

function updateColor(effectId: string, paramKey: string, hex: string) {
  const rgba = hexToRgba(hex);
  if(rgba && layer.value) {
    const val = { r: rgba[0], g: rgba[1], b: rgba[2], a: rgba[3] };
    store.updateEffectParameter(layer.value.id, effectId, paramKey, val);
  }
}

function toggleParamAnim(effectId: string, paramKey: string) {
  if(!layer.value) return;
  const effect = layer.value.effects.find((e: any) => e.id === effectId);
  const param = effect?.parameters[paramKey];
  if(param) {
    param.animated = !param.animated;
    if(param.animated && param.keyframes.length === 0) {
      store.addKeyframe(layer.value.id, param.id, param.value);
    }
  }
}

// Click outside menu
function onClickOutside(e: MouseEvent) {
  if (menuRef.value && !menuRef.value.contains(e.target as Node)) {
    showAddMenu.value = false;
  }
}

onMounted(() => window.addEventListener('mousedown', onClickOutside));
onUnmounted(() => window.removeEventListener('mousedown', onClickOutside));
</script>

<style scoped>
.effect-controls {
  height: 100%;
  display: flex;
  flex-direction: column;
  background: #1e1e1e;
  color: #ccc;
  font-size: 11px;
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

h3 { margin: 0; font-size: 11px; font-weight: 600; color: #888; text-transform: uppercase; }

.layer-badge {
  background: #333;
  padding: 2px 6px;
  border-radius: 3px;
  color: #fff;
  font-size: 10px;
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
.arrow { font-size: 8px; width: 12px; text-align: center; color: #888; }
.fx-icon { font-family: serif; font-weight: bold; font-size: 10px; color: #4a90d9; }
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

.stopwatch {
  background: transparent;
  border: none;
  color: #444;
  cursor: pointer;
  font-size: 12px;
  padding: 0;
}
.stopwatch:hover { color: #888; }
.stopwatch.active { color: #4a90d9; }

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
  font-size: 10px;
}
</style>
