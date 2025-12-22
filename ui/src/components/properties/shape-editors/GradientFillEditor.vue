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
      <label>Opacity</label>
      <ScrubableNumber
        :modelValue="shape.opacity.value"
        @update:modelValue="v => updateNumber('opacity', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="shape.opacity" @toggle="toggleKeyframe('opacity')" />
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
          @update:modelValue="v => updateStopPosition(index, v / 100)"
          :min="0"
          :max="100"
          unit="%"
        />
        <button class="remove-stop" @click="removeStop(index)" :disabled="shape.gradient.value.stops.length <= 2">-</button>
      </div>
      <button class="add-stop" @click="addStop">+ Add Stop</button>
    </div>

    <!-- Start/End Points -->
    <div class="subsection-header">Position</div>
    <div class="property-row">
      <label>Start</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="shape.gradient.value.startPoint.x * 100"
          @update:modelValue="v => updateStartPoint('x', v / 100)"
          :min="0"
          :max="100"
          unit="%"
        />
        <ScrubableNumber
          :modelValue="shape.gradient.value.startPoint.y * 100"
          @update:modelValue="v => updateStartPoint('y', v / 100)"
          :min="0"
          :max="100"
          unit="%"
        />
      </div>
    </div>
    <div class="property-row">
      <label>End</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="shape.gradient.value.endPoint.x * 100"
          @update:modelValue="v => updateEndPoint('x', v / 100)"
          :min="0"
          :max="100"
          unit="%"
        />
        <ScrubableNumber
          :modelValue="shape.gradient.value.endPoint.y * 100"
          @update:modelValue="v => updateEndPoint('y', v / 100)"
          :min="0"
          :max="100"
          unit="%"
        />
      </div>
    </div>

    <!-- Radial-specific options -->
    <template v-if="shape.gradient.value.type === 'radial'">
      <div class="property-row">
        <label>Highlight</label>
        <ScrubableNumber
          :modelValue="shape.gradient.value.highlightLength || 0"
          @update:modelValue="updateHighlightLength"
          :min="0"
          :max="100"
          unit="%"
        />
      </div>
      <div class="property-row">
        <label>Highlight Angle</label>
        <ScrubableNumber
          :modelValue="shape.gradient.value.highlightAngle || 0"
          @update:modelValue="updateHighlightAngle"
          :min="-180"
          :max="180"
          unit="deg"
        />
      </div>
    </template>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import type { GradientFillShape, ShapeColor, GradientStop, FillRule } from '@/types/shapes';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from '../KeyframeToggle.vue';
import { useCompositorStore } from '@/stores/compositorStore';

const props = defineProps<{ shape: GradientFillShape }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

// Gradient preview CSS
const gradientPreviewStyle = computed(() => {
  const g = props.shape.gradient.value;
  const stops = g.stops.map(s => `rgba(${s.color.r}, ${s.color.g}, ${s.color.b}, ${s.color.a}) ${s.position * 100}%`).join(', ');

  if (g.type === 'linear') {
    const angle = Math.atan2(g.endPoint.y - g.startPoint.y, g.endPoint.x - g.startPoint.x) * 180 / Math.PI + 90;
    return { background: `linear-gradient(${angle}deg, ${stops})` };
  } else {
    return { background: `radial-gradient(circle, ${stops})` };
  }
});

function colorToHex(color: ShapeColor): string {
  const r = Math.round(color.r).toString(16).padStart(2, '0');
  const g = Math.round(color.g).toString(16).padStart(2, '0');
  const b = Math.round(color.b).toString(16).padStart(2, '0');
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
    value: { ...updated.gradient.value, type: (e.target as HTMLSelectElement).value as 'linear' | 'radial' }
  };
  emit('update', updated);
}

function updateNumber(prop: 'opacity', value: number) {
  const updated = { ...props.shape };
  updated[prop] = { ...updated[prop], value };
  emit('update', updated);
}

function toggleKeyframe(prop: 'opacity') {
  const updated = { ...props.shape };
  const animProp = updated[prop];
  const frame = store.currentFrame;
  const hasKf = animProp.keyframes.some(k => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter(k => k.frame !== frame);
  } else {
    animProp.keyframes.push({ id: `kf_${Date.now()}`, frame, value: animProp.value, easing: 'linear' });
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit('update', updated);
}

function updateFillRule(e: Event) {
  const updated = { ...props.shape };
  updated.fillRule = (e.target as HTMLSelectElement).value as FillRule;
  emit('update', updated);
}

function updateBlendMode(e: Event) {
  const updated = { ...props.shape };
  updated.blendMode = (e.target as HTMLSelectElement).value;
  emit('update', updated);
}

function updateStopColor(index: number, hex: string) {
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops[index] = { ...stops[index], color: hexToColor(hex) };
  updated.gradient = { ...updated.gradient, value: { ...updated.gradient.value, stops } };
  emit('update', updated);
}

function updateStopPosition(index: number, position: number) {
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops[index] = { ...stops[index], position };
  updated.gradient = { ...updated.gradient, value: { ...updated.gradient.value, stops } };
  emit('update', updated);
}

function addStop() {
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops.push({ position: 0.5, color: { r: 128, g: 128, b: 128, a: 1 } });
  stops.sort((a, b) => a.position - b.position);
  updated.gradient = { ...updated.gradient, value: { ...updated.gradient.value, stops } };
  emit('update', updated);
}

function removeStop(index: number) {
  if (props.shape.gradient.value.stops.length <= 2) return;
  const updated = { ...props.shape };
  const stops = [...updated.gradient.value.stops];
  stops.splice(index, 1);
  updated.gradient = { ...updated.gradient, value: { ...updated.gradient.value, stops } };
  emit('update', updated);
}

function updateStartPoint(axis: 'x' | 'y', value: number) {
  const updated = { ...props.shape };
  updated.gradient = {
    ...updated.gradient,
    value: {
      ...updated.gradient.value,
      startPoint: { ...updated.gradient.value.startPoint, [axis]: value }
    }
  };
  emit('update', updated);
}

function updateEndPoint(axis: 'x' | 'y', value: number) {
  const updated = { ...props.shape };
  updated.gradient = {
    ...updated.gradient,
    value: {
      ...updated.gradient.value,
      endPoint: { ...updated.gradient.value.endPoint, [axis]: value }
    }
  };
  emit('update', updated);
}

function updateHighlightLength(value: number) {
  const updated = { ...props.shape };
  updated.gradient = {
    ...updated.gradient,
    value: { ...updated.gradient.value, highlightLength: value }
  };
  emit('update', updated);
}

function updateHighlightAngle(value: number) {
  const updated = { ...props.shape };
  updated.gradient = {
    ...updated.gradient,
    value: { ...updated.gradient.value, highlightAngle: value }
  };
  emit('update', updated);
}
</script>

<style scoped>
.shape-editor { display: flex; flex-direction: column; gap: 6px; }
.property-row { display: flex; align-items: center; gap: 8px; }
.property-row label { width: 70px; color: var(--weyl-text-muted, #888); font-size: 11px; flex-shrink: 0; }
.property-row select { flex: 1; padding: 3px 6px; background: var(--weyl-surface-0, #0a0a0a); border: 1px solid var(--weyl-border-default, #333); border-radius: 3px; color: var(--weyl-text-primary, #e0e0e0); font-size: 11px; }
.xy-inputs { display: flex; gap: 4px; flex: 1; }
.xy-inputs > * { flex: 1; }
.subsection-header { font-size: 10px; font-weight: 600; color: var(--weyl-text-muted, #666); text-transform: uppercase; letter-spacing: 0.05em; margin-top: 8px; padding-bottom: 4px; border-bottom: 1px solid var(--weyl-border-subtle, #2a2a2a); }
.gradient-preview { height: 24px; border-radius: 4px; margin: 4px 0; border: 1px solid var(--weyl-border-default, #333); }
.stops-list { display: flex; flex-direction: column; gap: 4px; }
.stop-row { display: flex; align-items: center; gap: 6px; }
.color-input { width: 28px; height: 28px; padding: 0; border: 1px solid var(--weyl-border-default, #333); border-radius: 3px; cursor: pointer; }
.remove-stop { width: 20px; height: 20px; padding: 0; border: none; background: var(--weyl-surface-3, #333); color: #c44; border-radius: 2px; cursor: pointer; font-weight: bold; }
.remove-stop:disabled { opacity: 0.3; cursor: not-allowed; }
.add-stop { padding: 4px 8px; border: 1px dashed var(--weyl-border-default, #333); background: transparent; color: var(--weyl-text-muted, #888); border-radius: 3px; cursor: pointer; font-size: 11px; }
.add-stop:hover { border-color: var(--weyl-accent, #8B5CF6); color: var(--weyl-accent, #8B5CF6); }
</style>
