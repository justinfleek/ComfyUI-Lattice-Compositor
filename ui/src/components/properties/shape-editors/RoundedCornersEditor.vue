<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Radius</label>
      <ScrubableNumber :modelValue="operator.radius.value" @update:modelValue="v => updateNumber('radius', v)" :min="0" :max="500" unit="px" />
      <KeyframeToggle :property="operator.radius" :layerId="layerId" @toggle="toggleKeyframe" />
    </div>
  </div>
</template>

<script setup lang="ts">
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { RoundedCornersOperator } from "@/types/shapes";

const props = defineProps<{
  operator: RoundedCornersOperator;
  layerId: string;
}>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

function _updateNumber(prop: "radius", value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function _toggleKeyframe() {
  const updated = { ...props.operator };
  const animProp = updated.radius;
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
</style>
