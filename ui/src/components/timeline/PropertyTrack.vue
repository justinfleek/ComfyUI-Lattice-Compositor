<template>
  <div class="prop-wrapper">
    <div v-if="layoutMode === 'sidebar'" class="prop-sidebar" :class="{ selected: isSelected }" :style="gridStyle" @click="selectProp">
      <div class="indent-spacer"></div>

      <div class="icon-box" @click.stop="addKeyframeAtCurrent">
        <span class="kf-btn" :class="{ active: hasKeyframeAtCurrent }">◇</span>
      </div>

      <div class="icon-box" @click.stop="toggleAnim">
        <span class="stopwatch" :class="{ active: property.animated }">⏱</span>
      </div>

      <div class="prop-content">
        <span class="prop-name">{{ name }}</span>

        <div class="prop-inputs">
          <!-- Number type -->
          <template v-if="typeof property.value === 'number'">
             <ScrubableNumber :modelValue="property.value" @update:modelValue="updateValDirect" :precision="1" />
          </template>

          <!-- Object type (X/Y or X/Y/Z) -->
          <template v-else-if="typeof property.value === 'object' && property.value !== null">
             <div class="vec-item">
               <span class="label x-label">X</span>
               <ScrubableNumber :modelValue="property.value.x" @update:modelValue="v => updateValByIndex('x', v)" />
             </div>
             <div class="vec-item">
               <span class="label y-label">Y</span>
               <ScrubableNumber :modelValue="property.value.y" @update:modelValue="v => updateValByIndex('y', v)" />
             </div>
             <div class="vec-item" v-if="property.value.z !== undefined">
               <span class="label z-label">Z</span>
               <ScrubableNumber :modelValue="property.value.z" @update:modelValue="v => updateValByIndex('z', v)" />
             </div>
          </template>

          <!-- Color type -->
          <template v-else-if="property.type === 'color'">
             <input type="color" :value="property.value" @input="e => updateValDirect((e.target as HTMLInputElement).value)" class="color-input" />
             <span class="color-text">{{ property.value }}</span>
          </template>

          <!-- Fallback -->
          <template v-else>
             <span class="val-display">{{ formatValue(property.value) }}</span>
          </template>
        </div>
      </div>
    </div>

    <div v-else class="prop-track">
       <div v-for="kf in property.keyframes" :key="kf.id"
            class="keyframe" :style="{ left: `${kf.frame * pixelsPerFrame}px` }">
       </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import ScrubableNumber from '@/components/controls/ScrubableNumber.vue';

const props = defineProps(['name', 'property', 'layerId', 'propertyPath', 'layoutMode', 'pixelsPerFrame', 'gridStyle']);
const store = useCompositorStore();

const hasKeyframeAtCurrent = computed(() => props.property.keyframes?.some((k: any) => k.frame === store.currentFrame));
const isSelected = false;

function formatValue(v: any) {
  if (typeof v === 'number') return v.toFixed(1);
  if (typeof v === 'object' && v !== null) {
    if (v.z !== undefined) return `${v.x?.toFixed(0)}, ${v.y?.toFixed(0)}, ${v.z?.toFixed(0)}`;
    if (v.x !== undefined) return `${v.x?.toFixed(0)}, ${v.y?.toFixed(0)}`;
  }
  return String(v);
}

function toggleAnim() { store.setPropertyAnimated(props.layerId, props.propertyPath, !props.property.animated); }
function addKeyframeAtCurrent() { store.addKeyframe(props.layerId, props.propertyPath, props.property.value); }
function updateValDirect(v: any) { store.setPropertyValue(props.layerId, props.propertyPath, v); }
function updateValByIndex(axis: string, v: number) {
  const newVal = { ...props.property.value, [axis]: v };
  store.setPropertyValue(props.layerId, props.propertyPath, newVal);
}
function selectProp() {}
</script>

<style scoped>
.prop-wrapper { width: 100%; display: flex; flex-direction: column; }

.prop-sidebar {
  display: grid;
  /* Must match parent grid: 24 24 30 24 24 24 1fr 70 70 */
  grid-template-columns: 24px 24px 30px 24px 24px 24px 1fr 70px 70px;
  align-items: center;
  height: 32px;
  border-bottom: 1px solid #2a2a2a;
  background: #1a1a1a;
  font-size: 13px;
  color: #ccc;
}
.prop-sidebar:hover { background: #222; }
.prop-sidebar.selected { background: #2a2a2a; border-left: 2px solid #3ea6ff; }

.indent-spacer { grid-column: span 3; }

.icon-box { display: flex; justify-content: center; cursor: pointer; font-size: 14px; }
.kf-btn { color: #555; }
.kf-btn:hover { color: #fff; }
.kf-btn.active { color: #f1c40f; }
.stopwatch { color: #555; }
.stopwatch:hover { color: #fff; }
.stopwatch.active { color: #3498db; }

/* Content spans from column 7 (Name) to the end */
.prop-content {
  grid-column: 7 / -1;
  display: flex;
  align-items: center;
  padding-right: 10px;
  overflow: hidden;
  gap: 12px;
}

.prop-name { min-width: 100px; color: #999; font-size: 13px; white-space: nowrap; }

.prop-inputs { display: flex; gap: 10px; flex: 1; align-items: center; }

.vec-item { display: flex; align-items: center; gap: 4px; }
.label { font-size: 11px; font-weight: bold; width: 14px; text-align: center; }
.x-label { color: #e74c3c; }
.y-label { color: #2ecc71; }
.z-label { color: #3498db; }

.color-input { width: 32px; height: 24px; border: 1px solid #444; cursor: pointer; }
.color-text { font-family: monospace; font-size: 12px; color: #888; }

.val-display { color: #3ea6ff; font-family: monospace; font-size: 13px; }

/* Override ScrubableNumber for compact display */
.prop-inputs :deep(.scrubable-number) { gap: 0; }
.prop-inputs :deep(.scrub-input) {
  width: 55px;
  padding: 3px 4px;
  font-size: 13px;
  background: #111;
  border: 1px solid #333;
  color: #3ea6ff;
  font-family: 'Consolas', monospace;
  border-radius: 2px;
}
.prop-inputs :deep(.scrub-input):hover { background: #1a1a1a; border-color: #4a90d9; }
.prop-inputs :deep(.scrub-input):focus { border-color: #4a90d9; outline: none; }
.prop-inputs :deep(.scrub-label) { display: none; }

.prop-track { height: 32px; background: #151515; border-bottom: 1px solid #2a2a2a; position: relative; }
.keyframe {
  position: absolute;
  width: 10px;
  height: 10px;
  background: #f1c40f;
  transform: rotate(45deg);
  top: 11px;
  border: 1px solid #000;
  cursor: pointer;
}
.keyframe:hover { background: #fff; transform: rotate(45deg) scale(1.2); }
</style>
