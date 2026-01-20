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
      <label>Width</label>
      <ScrubableNumber
        :modelValue="shape.width.value"
        @update:modelValue="(v: number) => updateNumber('width', v)"
        :min="0"
        :max="500"
        unit="px"
      />
      <KeyframeToggle :property="shape.width" :layerId="layerId" @toggle="toggleKeyframe('width')" />
    </div>
    <div class="property-row">
      <label>Line Cap</label>
      <div class="icon-toggle-group">
        <button :class="{ active: shape.lineCap === 'butt' }" @click="updateMeta('lineCap', 'butt')" title="Butt">┃</button>
        <button :class="{ active: shape.lineCap === 'round' }" @click="updateMeta('lineCap', 'round')" title="Round">◯</button>
        <button :class="{ active: shape.lineCap === 'square' }" @click="updateMeta('lineCap', 'square')" title="Square">□</button>
      </div>
    </div>
    <div class="property-row">
      <label>Line Join</label>
      <div class="icon-toggle-group">
        <button :class="{ active: shape.lineJoin === 'miter' }" @click="updateMeta('lineJoin', 'miter')" title="Miter">⟨</button>
        <button :class="{ active: shape.lineJoin === 'round' }" @click="updateMeta('lineJoin', 'round')" title="Round">◠</button>
        <button :class="{ active: shape.lineJoin === 'bevel' }" @click="updateMeta('lineJoin', 'bevel')" title="Bevel">∠</button>
      </div>
    </div>
    <div class="property-row">
      <label>Dashes</label>
      <input
        type="text"
        class="dash-input"
        :value="dashString"
        @change="updateDashes"
        placeholder="e.g. 10, 5"
      />
    </div>
    <div class="property-row" v-if="hasDashes">
      <label>Dash Offset</label>
      <ScrubableNumber
        :modelValue="shape.dashOffset.value"
        @update:modelValue="(v: number) => updateNumber('dashOffset', v)"
      />
      <KeyframeToggle :property="shape.dashOffset" :layerId="layerId" @toggle="toggleKeyframe('dashOffset')" />
    </div>
    <div class="property-row">
      <label>Blend Mode</label>
      <select :value="shape.blendMode" @change="e => updateMeta('blendMode', (e.target as HTMLSelectElement).value)">
        <option value="normal">Normal</option>
        <option value="multiply">Multiply</option>
        <option value="screen">Screen</option>
        <option value="overlay">Overlay</option>
        <option value="darken">Darken</option>
        <option value="lighten">Lighten</option>
      </select>
    </div>

    <!-- Taper Section -->
    <div class="subsection-header" @click="toggleTaper">
      <span class="expand-icon">{{ taperExpanded ? '▼' : '►' }}</span>
      <span class="section-title">Taper</span>
      <input
        type="checkbox"
        :checked="shape.taperEnabled"
        @click.stop="updateMeta('taperEnabled', !shape.taperEnabled)"
      />
    </div>
    <template v-if="taperExpanded && shape.taperEnabled">
      <div class="property-row">
        <label>Start Length</label>
        <ScrubableNumber
          :modelValue="shape.taperStartLength.value"
          @update:modelValue="(v: number) => updateTaper('taperStartLength', v)"
          :min="0"
          :max="100"
          unit="%"
        />
        <KeyframeToggle :property="shape.taperStartLength" :layerId="layerId" @toggle="toggleKeyframe('taperStartLength')" />
      </div>
      <div class="property-row">
        <label>Start Width</label>
        <ScrubableNumber
          :modelValue="shape.taperStartWidth.value"
          @update:modelValue="(v: number) => updateTaper('taperStartWidth', v)"
          :min="0"
          :max="100"
          unit="%"
        />
        <KeyframeToggle :property="shape.taperStartWidth" :layerId="layerId" @toggle="toggleKeyframe('taperStartWidth')" />
      </div>
      <div class="property-row">
        <label>Start Ease</label>
        <ScrubableNumber
          :modelValue="shape.taperStartEase.value"
          @update:modelValue="(v: number) => updateTaper('taperStartEase', v)"
          :min="0"
          :max="100"
          unit="%"
        />
        <KeyframeToggle :property="shape.taperStartEase" :layerId="layerId" @toggle="toggleKeyframe('taperStartEase')" />
      </div>
      <div class="property-row">
        <label>End Length</label>
        <ScrubableNumber
          :modelValue="shape.taperEndLength.value"
          @update:modelValue="(v: number) => updateTaper('taperEndLength', v)"
          :min="0"
          :max="100"
          unit="%"
        />
        <KeyframeToggle :property="shape.taperEndLength" :layerId="layerId" @toggle="toggleKeyframe('taperEndLength')" />
      </div>
      <div class="property-row">
        <label>End Width</label>
        <ScrubableNumber
          :modelValue="shape.taperEndWidth.value"
          @update:modelValue="(v: number) => updateTaper('taperEndWidth', v)"
          :min="0"
          :max="100"
          unit="%"
        />
        <KeyframeToggle :property="shape.taperEndWidth" :layerId="layerId" @toggle="toggleKeyframe('taperEndWidth')" />
      </div>
      <div class="property-row">
        <label>End Ease</label>
        <ScrubableNumber
          :modelValue="shape.taperEndEase.value"
          @update:modelValue="(v: number) => updateTaper('taperEndEase', v)"
          :min="0"
          :max="100"
          unit="%"
        />
        <KeyframeToggle :property="shape.taperEndEase" :layerId="layerId" @toggle="toggleKeyframe('taperEndEase')" />
      </div>
    </template>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type { StrokeShape } from "@/types/shapes";

const props = defineProps<{ shape: StrokeShape; layerId: string }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

const taperExpanded = ref(false);

function toggleTaper() {
  taperExpanded.value = !taperExpanded.value;
}

const colorHex = computed(() => {
  const c = props.shape.color.value;
  const r = Math.round(c.r).toString(16).padStart(2, "0");
  const g = Math.round(c.g).toString(16).padStart(2, "0");
  const b = Math.round(c.b).toString(16).padStart(2, "0");
  return `#${r}${g}${b}`;
});

const dashString = computed(() => {
  return props.shape.dashPattern.value.join(", ");
});

const hasDashes = computed(() => {
  return props.shape.dashPattern.value.length > 0;
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

function updateNumber(
  prop: "opacity" | "width" | "dashOffset",
  value: number,
) {
  const updated = { ...props.shape };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function updateMeta(key: string, value: unknown) {
  const updated = { ...props.shape, [key]: value };
  emit("update", updated);
}

// Type-safe taper property accessor
function updateTaper(
  prop:
    | "taperStartLength"
    | "taperStartWidth"
    | "taperStartEase"
    | "taperEndLength"
    | "taperEndWidth"
    | "taperEndEase",
  value: number,
) {
  const updated = { ...props.shape };
  // Type-safe property access - all taper properties are AnimatableProperty<number>
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function updateDashes(e: Event) {
  const input = (e.target as HTMLInputElement).value;
  const values = input.trim()
    ? input
        .split(",")
        .map((v) => parseFloat(v.trim()))
        .filter((v) => !Number.isNaN(v) && v >= 0)
    : [];

  const updated = { ...props.shape };
  updated.dashPattern = { ...updated.dashPattern, value: values };
  emit("update", updated);
}

// Type-safe property accessor for StrokeShape animatable properties
function getAnimatableProperty(
  shape: StrokeShape,
  prop:
    | "color"
    | "opacity"
    | "width"
    | "dashOffset"
    | "taperStartLength"
    | "taperStartWidth"
    | "taperStartEase"
    | "taperEndLength"
    | "taperEndWidth"
    | "taperEndEase",
): import("@/types/animation").AnimatableProperty<unknown> {
  // Type-safe property access - all these properties are AnimatableProperty
  if (prop === "color") return shape.color as import("@/types/animation").AnimatableProperty<unknown>;
  if (prop === "opacity") return shape.opacity;
  if (prop === "width") return shape.width;
  if (prop === "dashOffset") return shape.dashOffset;
  if (prop === "taperStartLength") return shape.taperStartLength;
  if (prop === "taperStartWidth") return shape.taperStartWidth;
  if (prop === "taperStartEase") return shape.taperStartEase;
  if (prop === "taperEndLength") return shape.taperEndLength;
  if (prop === "taperEndWidth") return shape.taperEndWidth;
  return shape.taperEndEase;
}

function toggleKeyframe(
  prop:
    | "color"
    | "opacity"
    | "width"
    | "dashOffset"
    | "taperStartLength"
    | "taperStartWidth"
    | "taperStartEase"
    | "taperEndLength"
    | "taperEndWidth"
    | "taperEndEase",
) {
  const updated = { ...props.shape };
  const animProp = getAnimatableProperty(updated, prop);
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

.icon-toggle-group {
  display: flex;
  background: var(--lattice-surface-0, #0a0a0a);
  border-radius: 3px;
  border: 1px solid var(--lattice-border-default, #333);
}

.icon-toggle-group button {
  background: transparent;
  border: none;
  color: var(--lattice-text-muted, #666);
  padding: 4px 8px;
  cursor: pointer;
  font-size: 12px;
  border-right: 1px solid var(--lattice-border-default, #333);
}

.icon-toggle-group button:last-child {
  border-right: none;
}

.icon-toggle-group button.active {
  background: var(--lattice-accent, #8B5CF6);
  color: #fff;
}

.icon-toggle-group button:hover:not(.active) {
  background: var(--lattice-surface-3, #333);
}

.dash-input {
  flex: 1;
  padding: 3px 6px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 11px;
}

.dash-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.subsection-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 0;
  cursor: pointer;
  user-select: none;
  margin-top: 8px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.subsection-header .expand-icon {
  width: 10px;
  font-size: 10px;
  color: var(--lattice-text-muted, #666);
}

.subsection-header .section-title {
  flex: 1;
  font-size: 11px;
  font-weight: 600;
  color: var(--lattice-text-secondary, #ccc);
  text-transform: uppercase;
  letter-spacing: 0.05em;
}

.subsection-header input[type="checkbox"] {
  margin: 0;
  cursor: pointer;
}
</style>
