<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Angle</label>
      <ScrubableNumber :modelValue="operator.angle.value" @update:modelValue="v => updateNumber('angle', v)" :min="-720" :max="720" unit="°" />
      <KeyframeToggle :property="operator.angle" @toggle="toggleKeyframe('angle')" />
    </div>
    <div class="property-row">
      <label>Center</label>
      <div class="xy-inputs">
        <ScrubableNumber :modelValue="operator.center.value.x" @update:modelValue="v => updatePoint('center', 'x', v)" unit="px" />
        <ScrubableNumber :modelValue="operator.center.value.y" @update:modelValue="v => updatePoint('center', 'y', v)" unit="px" />
      </div>
      <KeyframeToggle :property="operator.center" @toggle="toggleKeyframe('center')" />
    </div>
  </div>
</template>

<script setup lang="ts">
import type { TwistOperator } from '@/types/shapes';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from '../KeyframeToggle.vue';
import { useCompositorStore } from '@/stores/compositorStore';

const props = defineProps<{ operator: TwistOperator }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

function updateNumber(prop: 'angle', value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit('update', updated);
}

function updatePoint(prop: 'center', axis: 'x' | 'y', value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value: { ...updated[prop].value, [axis]: value } };
  emit('update', updated);
}

function toggleKeyframe(prop: 'angle' | 'center') {
  const updated = { ...props.operator };
  const animProp = updated[prop];
  const frame = store.currentFrame;
  const hasKf = animProp.keyframes.some(k => k.frame === frame);
  if (hasKf) { animProp.keyframes = animProp.keyframes.filter(k => k.frame !== frame); }
  else { animProp.keyframes.push({ id: `kf_${Date.now()}`, frame, value: animProp.value, easing: 'linear' }); }
  animProp.animated = animProp.keyframes.length > 0;
  emit('update', updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--weyl-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.xy-inputs { display: flex; gap: 4px; flex: 1; }
.xy-inputs > * { flex: 1; }
</style>
