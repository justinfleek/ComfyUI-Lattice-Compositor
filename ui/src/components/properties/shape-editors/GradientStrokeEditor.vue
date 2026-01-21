<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Gradient Type</label>
      <select :value="shape.gradient.value.type" @change="updateGradientType">
        <option value="linear">Linear</option>
        <option value="radial">Radial</option>
      </select>
    </div>

    <div class="property-row">
      <label>Width</label>
      <ScrubableNumber
        :modelValue="shape.width.value"
        @update:modelValue="(v: number) => updateNumber('width', v)"
        :min="0"
        :max="100"
        unit="px"
      />
      <KeyframeToggle :property="shape.width" :layerId="layerId" @toggle="toggleKeyframe('width')" />
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
      <label>Line Cap</label>
      <select :value="shape.lineCap" @change="updateLineCap">
        <option value="butt">Butt</option>
        <option value="round">Round</option>
        <option value="square">Square</option>
      </select>
    </div>

    <div class="property-row">
      <label>Line Join</label>
      <select :value="shape.lineJoin" @change="updateLineJoin">
        <option value="miter">Miter</option>
        <option value="round">Round</option>
        <option value="bevel">Bevel</option>
      </select>
    </div>

    <div class="property-row">
      <label>Miter Limit</label>
      <ScrubableNumber
        :modelValue="shape.miterLimit"
        @update:modelValue="updateMiterLimit"
        :min="1"
        :max="100"
      />
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
      </select>
    </div>

    <!-- Gradient Stops -->
    <div class="subsection-header">Gradient Stops</div>
    <div class="gradient-preview" :style="gradientPreviewStyle"></div>
    <div class="stops-list">
      <div v-for="(stop, index) in shape.gradient.value.stops" :key="index" class="stop-row">
        <input
          type="color"
          :value="colorToHex(stop.color)"
          @input="e => updateStopColor(index, (e.target as HTMLInputElement).value)"
          class="color-input"
        />
        <ScrubableNumber
          :modelValue="stop.position * 100"
          @update:modelValue="(v: number) => updateStopPosition(index, v / 100)"
          :min="0"
          :max="100"
          unit="%"
        />
        <button class="remove-stop" @click="removeStop(index)" :disabled="shape.gradient.value.stops.length <= 2">-</button>
      </div>
      <button class="add-stop" @click="addStop">+ Add Stop</button>
    </div>

    <!-- Dash Pattern -->
    <div class="subsection-header">Dashes</div>
    <div class="property-row">
      <label>Dash Offset</label>
      <ScrubableNumber
        :modelValue="shape.dashOffset.value"
        @update:modelValue="(v: number) => updateNumber('dashOffset', v)"
        :min="0"
        :max="100"
        unit="px"
      />
      <KeyframeToggle :property="shape.dashOffset" :layerId="layerId" @toggle="toggleKeyframe('dashOffset')" />
    </div>
    <div class="dash-info">
      <span>{{ dashPatternDisplay }}</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useAnimationStore } from "@/stores/animationStore";
import { createKeyframe } from "@/types/animation";
import type {
  GradientStrokeShape,
  LineCap,
  LineJoin,
  ShapeColor,
} from "@/types/shapes";

const props = defineProps<{ shape: GradientStrokeShape; layerId: string }>();
const emit = defineEmits(["update"]);
const animationStore = useAnimationStore();

// Gradient preview CSS
const gradientPreviewStyle = computed(() => {
  const g = props.shape.gradient.value;
  const stops = g.stops
    .map(
      (s) =>
        `rgba(${s.color.r}, ${s.color.g}, ${s.color.b}, ${s.color.a}) ${s.position * 100}%`,
    )
    .join(", ");

  if (g.type === "linear") {
    return { background: `linear-gradient(90deg, ${stops})` };
  } else {
    return { background: `radial-gradient(circle, ${stops})` };
  }
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
const dashPatternDisplay = computed(() => {
  const dashPattern = props.shape.dashPattern;
  const value = (dashPattern !== null && dashPattern !== undefined && typeof dashPattern === "object" && "value" in dashPattern) ? dashPattern.value : undefined;
  const pattern = (value !== null && value !== undefined && Array.isArray(value)) ? value : [];
  return pattern.length > 0 ? pattern.join(", ") : "No dashes";
});

function colorToHex(color: ShapeColor): string {
  const r = Math.round(color.r).toString(16).padStart(2, "0");
  const g = Math.round(color.g).toString(16).padStart(2, "0");
  const b = Math.round(color.b).toString(16).padStart(2, "0");
  return `#${r}${g}${b}`;
}

function hexToColor(hex: string): ShapeColor {
  const r = parseInt(hex.slice(1, 3), 16);
  const g = parseInt(hex.slice(3, 5), 16);
  const b = parseInt(hex.slice(5, 7), 16);
  return { r, g, b, a: 1 };
}

function updateGradientType(e: Event) {
  const updated = { ...props.shape };
  updated.gradient = {
    ...updated.gradient,
    value: {
      ...updated.gradient.value,
      type: (e.target as HTMLSelectElement).value as "linear" | "radial",
    },
  };
  emit("update", updated);
}

function updateNumber(
  prop: "width" | "opacity" | "dashOffset",
  value: number,
) {
  const updated = { ...props.shape };
  updated[prop] = { ...updated[prop], value };
  emit("update", updated);
}

function toggleKeyframe(prop: "width" | "opacity" | "dashOffset") {
  const updated = { ...props.shape };
  const animProp = updated[prop];
  const frame = animationStore.currentFrame;
  const hasKf = animProp.keyframes.some((k) => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter((k) => k.frame !== frame);
  } else {
    animProp.keyframes.push(createKeyframe(frame, animProp.value, "linear"));
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit("update", updated);
}

function updateLineCap(e: Event) {
  const updated = { ...props.shape };
  updated.lineCap = (e.target as HTMLSelectElement).value as LineCap;
  emit("update", updated);
}

function updateLineJoin(e: Event) {
  const updated = { ...props.shape };
  updated.lineJoin = (e.target as HTMLSelectElement).value as LineJoin;
  emit("update", updated);
}

function updateMiterLimit(value: number) {
  const updated = { ...props.shape };
  updated.miterLimit = value;
  emit("update", updated);
}

function updateBlendMode(e: Event) {
  const updated = { ...props.shape };
  updated.blendMode = (e.target as HTMLSelectElement).value;
  emit("update", updated);
}

function updateStopColor(index: number, hex: string) {
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops[index] = { ...stops[index], color: hexToColor(hex) };
  updated.gradient = {
    ...updated.gradient,
    value: { ...updated.gradient.value, stops },
  };
  emit("update", updated);
}

function updateStopPosition(index: number, position: number) {
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops[index] = { ...stops[index], position };
  updated.gradient = {
    ...updated.gradient,
    value: { ...updated.gradient.value, stops },
  };
  emit("update", updated);
}

function addStop() {
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops.push({ position: 0.5, color: { r: 128, g: 128, b: 128, a: 1 } });
  stops.sort((a, b) => a.position - b.position);
  updated.gradient = {
    ...updated.gradient,
    value: { ...updated.gradient.value, stops },
  };
  emit("update", updated);
}

function removeStop(index: number) {
  if (props.shape.gradient.value.stops.length <= 2) return;
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops.splice(index, 1);
  updated.gradient = {
    ...updated.gradient,
    value: { ...updated.gradient.value, stops },
  };
  emit("update", updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--lattice-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.property-row select { flex: 1; padding: 3px 6px; background: var(--lattice-surface-0, #0a0a0a); border: 1px solid var(--lattice-border-default, #333); border-radius: 3px; color: var(--lattice-text-primary, #e0e0e0); font-size: 11px; }
.subsection-header { font-size: 10px; font-weight: 600; color: var(--lattice-text-muted, #666); text-transform: uppercase; letter-spacing: 0.05em; margin-top: 8px; padding-bottom: 4px; border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a); }
.gradient-preview { height: 24px; border-radius: 4px; margin: 4px 0; border: 1px solid var(--lattice-border-default, #333); }
.stops-list { display: flex; flex-direction: column; gap: 4px; }
.stop-row { display: flex; align-items: center; gap: 6px; }
.color-input { width: 28px; height: 28px; padding: 0; border: 1px solid var(--lattice-border-default, #333); border-radius: 3px; cursor: pointer; }
.remove-stop { width: 20px; height: 20px; padding: 0; border: none; background: var(--lattice-surface-3, #333); color: #c44; border-radius: 2px; cursor: pointer; font-weight: bold; }
.remove-stop:disabled { opacity: 0.3; cursor: not-allowed; }
.add-stop { padding: 4px 8px; border: 1px dashed var(--lattice-border-default, #333); background: transparent; color: var(--lattice-text-muted, #888); border-radius: 3px; cursor: pointer; font-size: 11px; }
.add-stop:hover { border-color: var(--lattice-accent, #8B5CF6); color: var(--lattice-accent, #8B5CF6); }
.dash-info { font-size: 11px; color: var(--lattice-text-muted, #888); padding: 4px 0; }
</style>
