<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Start</label>
      <ScrubableNumber
        :modelValue="operator.start.value"
        @update:modelValue="v => updateNumber('start', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="operator.start" :layerId="layerId" @toggle="toggleKeyframe('start')" />
    </div>
    <div class="property-row">
      <label>End</label>
      <ScrubableNumber
        :modelValue="operator.end.value"
        @update:modelValue="v => updateNumber('end', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="operator.end" :layerId="layerId" @toggle="toggleKeyframe('end')" />
    </div>
    <div class="property-row">
      <label>Offset</label>
      <ScrubableNumber
        :modelValue="operator.offset.value"
        @update:modelValue="v => updateNumber('offset', v)"
        :min="-360"
        :max="360"
        unit="°"
      />
      <KeyframeToggle :property="operator.offset" :layerId="layerId" @toggle="toggleKeyframe('offset')" />
    </div>
    <div class="property-row">
      <label>Trim Mode</label>
      <select :value="operator.mode" @change="updateMode">
        <option value="simultaneously">Simultaneously</option>
        <option value="individually">Individually</option>
      </select>
    </div>
  </div>
</template>

<script setup lang="ts">
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { TrimMode, TrimPathsOperator } from "@/types/shapes";

const props = defineProps<{ operator: TrimPathsOperator; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

function _updateNumber(prop: "start" | "end" | "offset", value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function _updateMode(e: Event) {
  const updated = { ...props.operator };
  updated.mode = (e.target as HTMLSelectElement).value as TrimMode;
  emit("update", updated);
}

function _toggleKeyframe(prop: "start" | "end" | "offset") {
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
</style>
