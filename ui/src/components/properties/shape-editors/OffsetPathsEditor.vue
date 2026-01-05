<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Amount</label>
      <ScrubableNumber
        :modelValue="operator.amount.value"
        @update:modelValue="v => updateNumber('amount', v)"
        :min="-100"
        :max="100"
        unit="px"
      />
      <KeyframeToggle :property="operator.amount" :layerId="layerId" @toggle="toggleKeyframe('amount')" />
    </div>
    <div class="property-row">
      <label>Line Join</label>
      <div class="icon-toggle-group">
        <button :class="{ active: operator.lineJoin === 'miter' }" @click="updateJoin('miter')" title="Miter">⟨</button>
        <button :class="{ active: operator.lineJoin === 'round' }" @click="updateJoin('round')" title="Round">◠</button>
        <button :class="{ active: operator.lineJoin === 'bevel' }" @click="updateJoin('bevel')" title="Bevel">∠</button>
      </div>
    </div>
    <div class="property-row">
      <label>Miter Limit</label>
      <ScrubableNumber
        :modelValue="operator.miterLimit.value"
        @update:modelValue="v => updateNumber('miterLimit', v)"
        :min="1"
        :max="100"
      />
      <KeyframeToggle :property="operator.miterLimit" :layerId="layerId" @toggle="toggleKeyframe('miterLimit')" />
    </div>
    <div class="property-row">
      <label>Copies</label>
      <ScrubableNumber
        :modelValue="operator.copies.value"
        @update:modelValue="v => updateNumber('copies', v)"
        :min="1"
        :max="20"
        :step="1"
      />
      <KeyframeToggle :property="operator.copies" :layerId="layerId" @toggle="toggleKeyframe('copies')" />
    </div>
    <div class="property-row">
      <label>Copy Offset</label>
      <ScrubableNumber
        :modelValue="operator.copyOffset.value"
        @update:modelValue="v => updateNumber('copyOffset', v)"
        unit="px"
      />
      <KeyframeToggle :property="operator.copyOffset" :layerId="layerId" @toggle="toggleKeyframe('copyOffset')" />
    </div>
  </div>
</template>

<script setup lang="ts">
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { OffsetJoin, OffsetPathsOperator } from "@/types/shapes";

const props = defineProps<{ operator: OffsetPathsOperator; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

function _updateNumber(
  prop: "amount" | "miterLimit" | "copies" | "copyOffset",
  value: number,
) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function _updateJoin(join: OffsetJoin) {
  const updated = { ...props.operator, lineJoin: join };
  emit("update", updated);
}

function _toggleKeyframe(
  prop: "amount" | "miterLimit" | "copies" | "copyOffset",
) {
  const updated = { ...props.operator };
  const animProp = updated[prop];
  const frame = store.currentFrame;
  const hasKf = animProp.keyframes.some((k) => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter((k) => k.frame !== frame);
  } else {
    animProp.keyframes.push(createKeyframe(frame, animProp.value, "linear"));
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit("update", updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--lattice-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.icon-toggle-group { display: flex; background: var(--lattice-surface-0, #0a0a0a); border-radius: 3px; border: 1px solid var(--lattice-border-default, #333); }
.icon-toggle-group button { background: transparent; border: none; color: var(--lattice-text-muted, #666); padding: 4px 8px; cursor: pointer; font-size: 12px; border-right: 1px solid var(--lattice-border-default, #333); }
.icon-toggle-group button:last-child { border-right: none; }
.icon-toggle-group button.active { background: var(--lattice-accent, #8B5CF6); color: #fff; }
.icon-toggle-group button:hover:not(.active) { background: var(--lattice-surface-3, #333); }
</style>
