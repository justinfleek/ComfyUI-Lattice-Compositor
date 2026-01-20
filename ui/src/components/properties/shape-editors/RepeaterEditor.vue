<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Copies</label>
      <ScrubableNumber
        :modelValue="operator.copies.value"
        @update:modelValue="(v: number) => updateNumber('copies', v)"
        :min="1"
        :max="100"
        :step="1"
      />
      <KeyframeToggle :property="operator.copies" :layerId="layerId" @toggle="toggleKeyframe('copies')" />
    </div>
    <div class="property-row">
      <label>Offset</label>
      <ScrubableNumber
        :modelValue="operator.offset.value"
        @update:modelValue="(v: number) => updateNumber('offset', v)"
        :min="-10"
        :max="10"
        :step="0.1"
      />
      <KeyframeToggle :property="operator.offset" :layerId="layerId" @toggle="toggleKeyframe('offset')" />
    </div>
    <div class="property-row">
      <label>Composite</label>
      <select :value="operator.composite" @change="updateComposite">
        <option value="below">Below</option>
        <option value="above">Above</option>
      </select>
    </div>

    <div class="subsection-header">Transform</div>

    <div class="property-row">
      <label>Position</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="operator.transform.position.value.x"
          @update:modelValue="(v: number) => updateTransformPoint('position', 'x', v)"
          unit="px"
        />
        <ScrubableNumber
          :modelValue="operator.transform.position.value.y"
          @update:modelValue="(v: number) => updateTransformPoint('position', 'y', v)"
          unit="px"
        />
      </div>
      <KeyframeToggle :property="operator.transform.position" :layerId="layerId" @toggle="toggleTransformKeyframe('position')" />
    </div>
    <div class="property-row">
      <label>Scale</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="operator.transform.scale.value.x"
          @update:modelValue="(v: number) => updateTransformPoint('scale', 'x', v)"
          :min="0"
          :max="500"
          unit="%"
        />
        <ScrubableNumber
          :modelValue="operator.transform.scale.value.y"
          @update:modelValue="(v: number) => updateTransformPoint('scale', 'y', v)"
          :min="0"
          :max="500"
          unit="%"
        />
      </div>
      <KeyframeToggle :property="operator.transform.scale" :layerId="layerId" @toggle="toggleTransformKeyframe('scale')" />
    </div>
    <div class="property-row">
      <label>Rotation</label>
      <ScrubableNumber
        :modelValue="operator.transform.rotation.value"
        @update:modelValue="(v: number) => updateTransformNumber('rotation', v)"
        unit="°"
      />
      <KeyframeToggle :property="operator.transform.rotation" :layerId="layerId" @toggle="toggleTransformKeyframe('rotation')" />
    </div>
    <div class="property-row">
      <label>Start Opacity</label>
      <ScrubableNumber
        :modelValue="operator.transform.startOpacity.value"
        @update:modelValue="(v: number) => updateTransformNumber('startOpacity', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="operator.transform.startOpacity" :layerId="layerId" @toggle="toggleTransformKeyframe('startOpacity')" />
    </div>
    <div class="property-row">
      <label>End Opacity</label>
      <ScrubableNumber
        :modelValue="operator.transform.endOpacity.value"
        @update:modelValue="(v: number) => updateTransformNumber('endOpacity', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="operator.transform.endOpacity" :layerId="layerId" @toggle="toggleTransformKeyframe('endOpacity')" />
    </div>
  </div>
</template>

<script setup lang="ts">
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { RepeaterComposite, RepeaterOperator } from "@/types/shapes";

const props = defineProps<{ operator: RepeaterOperator; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

function updateNumber(prop: "copies" | "offset", value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function updateComposite(e: Event) {
  const updated = { ...props.operator };
  updated.composite = (e.target as HTMLSelectElement)
    .value as RepeaterComposite;
  emit("update", updated);
}

function updateTransformPoint(
  prop: "position" | "scale" | "anchorPoint",
  axis: "x" | "y",
  value: number,
) {
  const updated = { ...props.operator };
  updated.transform = { ...updated.transform };
  updated.transform[prop] = {
    ...updated.transform[prop],
    value: { ...updated.transform[prop].value, [axis]: value },
  };
  emit("update", updated);
}

function updateTransformNumber(
  prop: "rotation" | "startOpacity" | "endOpacity",
  value: number,
) {
  const updated = { ...props.operator };
  updated.transform = { ...updated.transform };
  updated.transform[prop] = { ...updated.transform[prop], value };
  emit("update", updated);
}

function toggleKeyframe(prop: "copies" | "offset") {
  const updated = { ...props.operator };
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

function toggleTransformKeyframe(
  prop:
    | "position"
    | "scale"
    | "anchorPoint"
    | "rotation"
    | "startOpacity"
    | "endOpacity",
) {
  const updated = { ...props.operator };
  updated.transform = { ...updated.transform };
  const animProp = updated.transform[prop];
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
  width: 80px;
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

.subsection-header {
  font-size: 10px;
  font-weight: 600;
  color: var(--lattice-text-muted, #666);
  text-transform: uppercase;
  letter-spacing: 0.05em;
  margin-top: 6px;
  padding-bottom: 4px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}
</style>
