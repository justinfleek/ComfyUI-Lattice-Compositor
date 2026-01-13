<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Position</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="shape.position.value.x"
          @update:modelValue="(v: number) => updatePoint('position', 'x', v)"
          unit="px"
        />
        <ScrubableNumber
          :modelValue="shape.position.value.y"
          @update:modelValue="(v: number) => updatePoint('position', 'y', v)"
          unit="px"
        />
      </div>
      <KeyframeToggle :property="shape.position" :layerId="layerId" @toggle="toggleKeyframe('position')" />
    </div>
    <div class="property-row">
      <label>Points</label>
      <ScrubableNumber
        :modelValue="shape.points.value"
        @update:modelValue="(v: number) => updateNumber('points', v)"
        :min="3"
        :max="100"
        :step="1"
      />
      <KeyframeToggle :property="shape.points" :layerId="layerId" @toggle="toggleKeyframe('points')" />
    </div>
    <div class="property-row">
      <label>Outer Radius</label>
      <ScrubableNumber
        :modelValue="shape.outerRadius.value"
        @update:modelValue="(v: number) => updateNumber('outerRadius', v)"
        :min="0"
        unit="px"
      />
      <KeyframeToggle :property="shape.outerRadius" :layerId="layerId" @toggle="toggleKeyframe('outerRadius')" />
    </div>
    <div class="property-row">
      <label>Inner Radius</label>
      <ScrubableNumber
        :modelValue="shape.innerRadius.value"
        @update:modelValue="(v: number) => updateNumber('innerRadius', v)"
        :min="0"
        unit="px"
      />
      <KeyframeToggle :property="shape.innerRadius" :layerId="layerId" @toggle="toggleKeyframe('innerRadius')" />
    </div>
    <div class="property-row">
      <label>Outer Round</label>
      <ScrubableNumber
        :modelValue="shape.outerRoundness.value"
        @update:modelValue="(v: number) => updateNumber('outerRoundness', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="shape.outerRoundness" :layerId="layerId" @toggle="toggleKeyframe('outerRoundness')" />
    </div>
    <div class="property-row">
      <label>Inner Round</label>
      <ScrubableNumber
        :modelValue="shape.innerRoundness.value"
        @update:modelValue="(v: number) => updateNumber('innerRoundness', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="shape.innerRoundness" :layerId="layerId" @toggle="toggleKeyframe('innerRoundness')" />
    </div>
    <div class="property-row">
      <label>Rotation</label>
      <ScrubableNumber
        :modelValue="shape.rotation.value"
        @update:modelValue="(v: number) => updateNumber('rotation', v)"
        unit="°"
      />
      <KeyframeToggle :property="shape.rotation" :layerId="layerId" @toggle="toggleKeyframe('rotation')" />
    </div>
    <div class="property-row">
      <label>Direction</label>
      <select :value="shape.direction" @change="updateDirection">
        <option :value="1">Clockwise</option>
        <option :value="-1">Counter-Clockwise</option>
      </select>
    </div>
  </div>
</template>

<script setup lang="ts">
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { StarShape } from "@/types/shapes";

const props = defineProps<{ shape: StarShape; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

function updatePoint(prop: "position", axis: "x" | "y", value: number) {
  const updated = { ...props.shape };
  updated[prop] = {
    ...updated[prop],
    value: { ...updated[prop].value, [axis]: value },
  };
  emit("update", updated);
}

function updateNumber(
  prop:
    | "points"
    | "outerRadius"
    | "innerRadius"
    | "outerRoundness"
    | "innerRoundness"
    | "rotation",
  value: number,
) {
  const updated = { ...props.shape };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function updateDirection(e: Event) {
  const updated = { ...props.shape };
  updated.direction = parseInt((e.target as HTMLSelectElement).value, 10) as
    | 1
    | -1;
  emit("update", updated);
}

function toggleKeyframe(
  prop:
    | "position"
    | "points"
    | "outerRadius"
    | "innerRadius"
    | "outerRoundness"
    | "innerRoundness"
    | "rotation",
) {
  const updated = { ...props.shape };
  const animProp = updated[prop];
  const frame = store.currentFrame;

  const hasKf = animProp.keyframes.some((k) => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter(
      (k) => k.frame !== frame,
    ) as typeof animProp.keyframes;
  } else {
    (animProp.keyframes as unknown[]).push(
      createKeyframe(frame, animProp.value, "linear"),
    );
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit("update", updated);
}
</script>

<style scoped>
.shape-editor {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.property-row label {
  width: 70px;
  color: var(--lattice-text-muted, #888);
  font-size: 11px;
  flex-shrink: 0;
}

.property-row select {
  flex: 1;
  padding: 3px 6px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 11px;
}

.xy-inputs {
  display: flex;
  gap: 4px;
  flex: 1;
}

.xy-inputs > * {
  flex: 1;
}
</style>
