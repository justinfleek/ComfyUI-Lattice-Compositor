<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Color</label>
      <div class="color-input-wrapper">
        <input
          type="color"
          :value="colorHex"
          @input="updateColor"
        />
        <span class="color-value">{{ colorHex }}</span>
      </div>
      <KeyframeToggle :property="shape.color" :layerId="layerId" @toggle="toggleKeyframe('color')" />
    </div>
    <div class="property-row">
      <label>Opacity</label>
      <ScrubableNumber
        :modelValue="shape.opacity.value"
        @update:modelValue="(v: number) => updateNumber('opacity', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="shape.opacity" :layerId="layerId" @toggle="toggleKeyframe('opacity')" />
    </div>
    <div class="property-row">
      <label>Fill Rule</label>
      <select :value="shape.fillRule" @change="updateFillRule">
        <option value="nonzero">Non-Zero</option>
        <option value="evenodd">Even-Odd</option>
      </select>
    </div>
    <div class="property-row">
      <label>Blend Mode</label>
      <select :value="shape.blendMode" @change="updateBlendMode">
        <option value="normal">Normal</option>
        <option value="multiply">Multiply</option>
        <option value="screen">Screen</option>
        <option value="overlay">Overlay</option>
        <option value="darken">Darken</option>
        <option value="lighten">Lighten</option>
        <option value="color-dodge">Color Dodge</option>
        <option value="color-burn">Color Burn</option>
        <option value="hard-light">Hard Light</option>
        <option value="soft-light">Soft Light</option>
        <option value="difference">Difference</option>
        <option value="exclusion">Exclusion</option>
      </select>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { FillShape } from "@/types/shapes";

const props = defineProps<{ shape: FillShape; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

const colorHex = computed(() => {
  const c = props.shape.color.value;
  const r = Math.round(c.r).toString(16).padStart(2, "0");
  const g = Math.round(c.g).toString(16).padStart(2, "0");
  const b = Math.round(c.b).toString(16).padStart(2, "0");
  return `#${r}${g}${b}`;
});

function updateColor(e: Event) {
  const hex = (e.target as HTMLInputElement).value;
  const r = parseInt(hex.slice(1, 3), 16);
  const g = parseInt(hex.slice(3, 5), 16);
  const b = parseInt(hex.slice(5, 7), 16);

  const updated = { ...props.shape };
  updated.color = {
    ...updated.color,
    value: { r, g, b, a: updated.color.value.a },
  };
  emit("update", updated);
}

function updateNumber(prop: "opacity", value: number) {
  const updated = { ...props.shape };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function updateFillRule(e: Event) {
  const updated = { ...props.shape };
  updated.fillRule = (e.target as HTMLSelectElement).value as
    | "nonzero"
    | "evenodd";
  emit("update", updated);
}

function updateBlendMode(e: Event) {
  const updated = { ...props.shape };
  updated.blendMode = (e.target as HTMLSelectElement).value;
  emit("update", updated);
}

function toggleKeyframe(prop: "color" | "opacity") {
  const updated = { ...props.shape };
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

.color-input-wrapper {
  display: flex;
  align-items: center;
  gap: 8px;
  flex: 1;
}

.color-input-wrapper input[type="color"] {
  width: 32px;
  height: 24px;
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 3px;
  padding: 0;
  cursor: pointer;
}

.color-value {
  font-size: 11px;
  color: var(--lattice-text-muted, #888);
  font-family: monospace;
}
</style>
