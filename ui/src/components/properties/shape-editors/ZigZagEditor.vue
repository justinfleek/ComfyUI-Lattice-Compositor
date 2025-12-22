<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Size</label>
      <ScrubableNumber :modelValue="operator.size.value" @update:modelValue="v => updateNumber('size', v)" :min="0" :max="200" unit="px" />
      <KeyframeToggle :property="operator.size" @toggle="toggleKeyframe('size')" />
    </div>
    <div class="property-row">
      <label>Ridges/Segment</label>
      <ScrubableNumber :modelValue="operator.ridgesPerSegment.value" @update:modelValue="v => updateNumber('ridgesPerSegment', v)" :min="1" :max="20" :step="1" />
      <KeyframeToggle :property="operator.ridgesPerSegment" @toggle="toggleKeyframe('ridgesPerSegment')" />
    </div>
    <div class="property-row">
      <label>Points</label>
      <div class="icon-toggle-group">
        <button :class="{ active: operator.points === 'corner' }" @click="updateMeta('points', 'corner')">Corner</button>
        <button :class="{ active: operator.points === 'smooth' }" @click="updateMeta('points', 'smooth')">Smooth</button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { ZigZagOperator, ZigZagPointType } from '@/types/shapes';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from '../KeyframeToggle.vue';
import { useCompositorStore } from '@/stores/compositorStore';

const props = defineProps<{ operator: ZigZagOperator }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

function updateNumber(prop: 'size' | 'ridgesPerSegment', value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit('update', updated);
}

function updateMeta(key: string, value: any) {
  const updated = { ...props.operator, [key]: value };
  emit('update', updated);
}

function toggleKeyframe(prop: 'size' | 'ridgesPerSegment') {
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
.property-row label { width: 90px; color: var(--weyl-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.icon-toggle-group { display: flex; background: var(--weyl-surface-0, #0a0a0a); border-radius: 3px; border: 1px solid var(--weyl-border-default, #333); }
.icon-toggle-group button { background: transparent; border: none; color: var(--weyl-text-muted, #666); padding: 4px 10px; cursor: pointer; font-size: 11px; border-right: 1px solid var(--weyl-border-default, #333); }
.icon-toggle-group button:last-child { border-right: none; }
.icon-toggle-group button.active { background: var(--weyl-accent, #8B5CF6); color: #fff; }
</style>
