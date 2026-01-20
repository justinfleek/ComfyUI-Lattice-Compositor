<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Anchor</label>
      <div class="xy-inputs">
        <ScrubableNumber :modelValue="transform.anchorPoint.value.x" @update:modelValue="(v: number) => updatePoint('anchorPoint', 'x', v)" unit="px" />
        <ScrubableNumber :modelValue="transform.anchorPoint.value.y" @update:modelValue="(v: number) => updatePoint('anchorPoint', 'y', v)" unit="px" />
      </div>
      <KeyframeToggle :property="transform.anchorPoint" :layerId="layerId" @toggle="toggleKeyframe('anchorPoint')" />
    </div>
    <div class="property-row">
      <label>Position</label>
      <div class="xy-inputs">
        <ScrubableNumber :modelValue="transform.position.value.x" @update:modelValue="(v: number) => updatePoint('position', 'x', v)" unit="px" />
        <ScrubableNumber :modelValue="transform.position.value.y" @update:modelValue="(v: number) => updatePoint('position', 'y', v)" unit="px" />
      </div>
      <KeyframeToggle :property="transform.position" :layerId="layerId" @toggle="toggleKeyframe('position')" />
    </div>
    <div class="property-row">
      <label>Scale</label>
      <div class="xy-inputs">
        <ScrubableNumber :modelValue="transform.scale.value.x" @update:modelValue="(v: number) => updatePoint('scale', 'x', v)" :min="0" :max="500" unit="%" />
        <ScrubableNumber :modelValue="transform.scale.value.y" @update:modelValue="(v: number) => updatePoint('scale', 'y', v)" :min="0" :max="500" unit="%" />
      </div>
      <KeyframeToggle :property="transform.scale" :layerId="layerId" @toggle="toggleKeyframe('scale')" />
    </div>
    <div class="property-row">
      <label>Rotation</label>
      <ScrubableNumber :modelValue="transform.rotation.value" @update:modelValue="(v: number) => updateNumber('rotation', v)" unit="°" />
      <KeyframeToggle :property="transform.rotation" :layerId="layerId" @toggle="toggleKeyframe('rotation')" />
    </div>
    <div class="property-row">
      <label>Skew</label>
      <ScrubableNumber :modelValue="transform.skew.value" @update:modelValue="(v: number) => updateNumber('skew', v)" :min="-90" :max="90" unit="°" />
      <KeyframeToggle :property="transform.skew" :layerId="layerId" @toggle="toggleKeyframe('skew')" />
    </div>
    <div class="property-row">
      <label>Skew Axis</label>
      <ScrubableNumber :modelValue="transform.skewAxis.value" @update:modelValue="(v: number) => updateNumber('skewAxis', v)" :min="-180" :max="180" unit="°" />
      <KeyframeToggle :property="transform.skewAxis" :layerId="layerId" @toggle="toggleKeyframe('skewAxis')" />
    </div>
    <div class="property-row">
      <label>Opacity</label>
      <ScrubableNumber :modelValue="transform.opacity.value" @update:modelValue="(v: number) => updateNumber('opacity', v)" :min="0" :max="100" unit="%" />
      <KeyframeToggle :property="transform.opacity" :layerId="layerId" @toggle="toggleKeyframe('opacity')" />
    </div>
  </div>
</template>

<script setup lang="ts">
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { ShapeTransform } from "@/types/shapes";

const props = defineProps<{ transform: ShapeTransform; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

function updatePoint(
  prop: "anchorPoint" | "position" | "scale",
  axis: "x" | "y",
  value: number,
) {
  const updated = { ...props.transform };
  updated[prop] = {
    ...updated[prop],
    value: { ...updated[prop].value, [axis]: value },
  };
  emit("update", updated);
}

function updateNumber(
  prop: "rotation" | "skew" | "skewAxis" | "opacity",
  value: number,
) {
  const updated = { ...props.transform };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function toggleKeyframe(
  prop:
    | "anchorPoint"
    | "position"
    | "scale"
    | "rotation"
    | "skew"
    | "skewAxis"
    | "opacity",
) {
  const updated = { ...props.transform };
  const animProp = updated[prop];
  const frame = store.currentFrame;
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
