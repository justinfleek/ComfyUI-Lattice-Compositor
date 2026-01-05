<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Position</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="shape.position.value.x"
          @update:modelValue="v => updatePoint('position', 'x', v)"
          unit="px"
        />
        <ScrubableNumber
          :modelValue="shape.position.value.y"
          @update:modelValue="v => updatePoint('position', 'y', v)"
          unit="px"
        />
      </div>
      <KeyframeToggle :property="shape.position" :layerId="layerId" @toggle="toggleKeyframe('position')" />
    </div>
    <div class="property-row">
      <label>Size</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="shape.size.value.x"
          @update:modelValue="v => updatePoint('size', 'x', v)"
          :min="0"
          unit="px"
        />
        <ScrubableNumber
          :modelValue="shape.size.value.y"
          @update:modelValue="v => updatePoint('size', 'y', v)"
          :min="0"
          unit="px"
        />
      </div>
      <KeyframeToggle :property="shape.size" :layerId="layerId" @toggle="toggleKeyframe('size')" />
    </div>
    <div class="property-row">
      <label>Roundness</label>
      <ScrubableNumber
        :modelValue="shape.roundness.value"
        @update:modelValue="v => updateNumber('roundness', v)"
        :min="0"
        :max="500"
        unit="px"
      />
      <KeyframeToggle :property="shape.roundness" :layerId="layerId" @toggle="toggleKeyframe('roundness')" />
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
import type { RectangleShape } from "@/types/shapes";

const props = defineProps<{ shape: RectangleShape; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

function _updatePoint(
  prop: "position" | "size",
  axis: "x" | "y",
  value: number,
) {
  const updated = { ...props.shape };
  updated[prop] = {
    ...updated[prop],
    value: { ...updated[prop].value, [axis]: value },
  };
  emit("update", updated);
}

function _updateNumber(prop: "roundness", value: number) {
  const updated = { ...props.shape };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function _updateDirection(e: Event) {
  const updated = { ...props.shape };
  updated.direction = parseInt((e.target as HTMLSelectElement).value, 10) as
    | 1
    | -1;
  emit("update", updated);
}

function _toggleKeyframe(prop: "position" | "size" | "roundness") {
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
