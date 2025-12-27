<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Amount</label>
      <ScrubableNumber
        :modelValue="operator.amount.value"
        @update:modelValue="v => updateNumber('amount', v)"
        :min="-100"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="operator.amount" :layerId="layerId" @toggle="toggleKeyframe" />
    </div>
    <div class="hint">
      <span>Negative = Pucker (inward)</span>
      <span>Positive = Bloat (outward)</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { PuckerBloatOperator } from '@/types/shapes';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from '../KeyframeToggle.vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { createKeyframe } from '@/types/animation';

const props = defineProps<{ operator: PuckerBloatOperator; layerId: string }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

function updateNumber(prop: 'amount', value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit('update', updated);
}

function toggleKeyframe() {
  const updated = { ...props.operator };
  const animProp = updated.amount;
  const frame = store.currentFrame;
  const hasKf = animProp.keyframes.some(k => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter(k => k.frame !== frame);
  } else {
    animProp.keyframes.push(createKeyframe(frame, animProp.value, 'linear'));
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit('update', updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--lattice-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.hint { display: flex; flex-direction: column; gap: 2px; font-size: 10px; color: var(--lattice-text-muted, #666); padding-top: 4px; }
</style>
