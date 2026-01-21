<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Angle</label>
      <ScrubableNumber :modelValue="operator.angle.value" @update:modelValue="(v: number) => updateNumber('angle', v)" :min="-720" :max="720" unit="°" />
      <KeyframeToggle :property="operator.angle" :layerId="layerId" @toggle="toggleKeyframe('angle')" />
    </div>
    <div class="property-row">
      <label>Center</label>
      <div class="xy-inputs">
        <ScrubableNumber :modelValue="operator.center.value.x" @update:modelValue="(v: number) => updatePoint('center', 'x', v)" unit="px" />
        <ScrubableNumber :modelValue="operator.center.value.y" @update:modelValue="(v: number) => updatePoint('center', 'y', v)" unit="px" />
      </div>
      <KeyframeToggle :property="operator.center" :layerId="layerId" @toggle="toggleKeyframe('center')" />
    </div>
  </div>
</template>

<script setup lang="ts">
import { useAnimationStore } from "@/stores/animationStore";
import { createKeyframe } from "@/types/animation";
import type { TwistOperator } from "@/types/shapes";

const props = defineProps<{ operator: TwistOperator; layerId: string }>();
const emit = defineEmits(["update"]);
const animationStore = useAnimationStore();

function updateNumber(prop: "angle", value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function updatePoint(prop: "center", axis: "x" | "y", value: number) {
  const updated = { ...props.operator };
  updated[prop] = {
    ...updated[prop],
    value: { ...updated[prop].value, [axis]: value },
  };
  emit("update", updated);
}

function toggleKeyframe(prop: "angle" | "center") {
  const updated = { ...props.operator };
  const animProp = updated[prop];
  const frame = animationStore.currentFrame;
  const hasKf = animProp.keyframes.some((k) => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter(
      (k) => k.frame !== frame,
    ) as typeof animProp.keyframes;
  } else {
    // createKeyframe returns Keyframe<T> matching the value type
    animProp.keyframes.push(
      createKeyframe(frame, animProp.value, "linear") as typeof animProp.keyframes[0],
    );
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit("update", updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--lattice-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.xy-inputs { display: flex; gap: 4px; flex: 1; }
.xy-inputs > * { flex: 1; }
</style>
