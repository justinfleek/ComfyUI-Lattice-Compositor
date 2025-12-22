<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Radius</label>
      <ScrubableNumber :modelValue="operator.radius.value" @update:modelValue="v => updateNumber('radius', v)" :min="0" :max="500" unit="px" />
      <KeyframeToggle :property="operator.radius" @toggle="toggleKeyframe" />
    </div>
  </div>
</template>

<script setup lang="ts">
import type { RoundedCornersOperator } from '@/types/shapes';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from '../KeyframeToggle.vue';
import { useCompositorStore } from '@/stores/compositorStore';

const props = defineProps<{ operator: RoundedCornersOperator }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

function updateNumber(prop: 'radius', value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit('update', updated);
}

function toggleKeyframe() {
  const updated = { ...props.operator };
  const animProp = updated.radius;
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
</style>
