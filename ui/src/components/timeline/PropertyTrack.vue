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
          <template v-if="typeof property.value === 'number'">
             <ScrubableNumber :modelValue="property.value" @update:modelValue="updateValDirect" :precision="1" />
          </template>
          <template v-else-if="typeof property.value === 'object'">
             <div class="vec-item"><span class="label x-label">X</span>
               <ScrubableNumber :modelValue="property.value.x" @update:modelValue="v => updateValByIndex('x', v)" />
             </div>
             <div class="vec-item"><span class="label y-label">Y</span>
               <ScrubableNumber :modelValue="property.value.y" @update:modelValue="v => updateValByIndex('y', v)" />
             </div>
             <div class="vec-item" v-if="property.value.z !== undefined"><span class="label z-label">Z</span>
               <ScrubableNumber :modelValue="property.value.z" @update:modelValue="v => updateValByIndex('z', v)" />
             </div>
          </template>
          <template v-else-if="property.type === 'color'">
             <input type="color" :value="property.value" @input="e => updateValDirect((e.target as HTMLInputElement).value)" />
             <span class="color-text">{{ property.value }}</span>
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

const hasKeyframeAtCurrent = computed(() => props.property.keyframes?.some((k:any) => k.frame === store.currentFrame));
const isSelected = false; // Simplified

function toggleAnim() { store.setPropertyAnimated(props.layerId, props.propertyPath, !props.property.animated); }
function addKeyframeAtCurrent() { store.addKeyframe(props.layerId, props.propertyPath, props.property.value); }
function updateValDirect(v: any) { store.setPropertyValue(props.layerId, props.propertyPath, v); }
function updateValByIndex(axis: string, v: number) {
  const newVal = { ...props.property.value, [axis]: v };
  store.setPropertyValue(props.layerId, props.propertyPath, newVal);
}
function selectProp() {} // TODO
</script>

<style scoped>
.prop-wrapper { width: 100%; display: flex; flex-direction: column; }
.prop-sidebar {
  display: grid;
  /* Must match parent grid. Columns: 24 24 30 24 24 24 1fr 70 70 */
  grid-template-columns: 24px 24px 30px 24px 24px 24px 1fr 70px 70px;
  align-items: center;
  height: 32px; /* Taller */
  border-bottom: 1px solid #2a2a2a;
  background: #1a1a1a;
  font-size: 13px; /* Readable font */
  color: #ccc;
}
.indent-spacer { grid-column: span 3; }
.icon-box { display: flex; justify-content: center; cursor: pointer; }
.kf-btn.active { color: #f1c40f; }
.stopwatch.active { color: #3498db; }

/* Content spans from column 7 (Name) to the end */
.prop-content {
  grid-column: 7 / -1;
  display: flex;
  align-items: center;
  padding-right: 10px;
  overflow: hidden;
}
.prop-name { min-width: 100px; color: #999; font-size: 13px; }
.prop-inputs { display: flex; gap: 8px; flex: 1; align-items: center; }

.vec-item { display: flex; align-items: center; gap: 4px; }
.label { font-size: 10px; font-weight: bold; }
.x-label { color: #e74c3c; } .y-label { color: #2ecc71; } .z-label { color: #3498db; }

.prop-track { height: 32px; background: #151515; border-bottom: 1px solid #2a2a2a; position: relative; }
.keyframe { position: absolute; width: 10px; height: 10px; background: #f1c40f; transform: rotate(45deg); top: 11px; border: 1px solid #000; }
</style>
