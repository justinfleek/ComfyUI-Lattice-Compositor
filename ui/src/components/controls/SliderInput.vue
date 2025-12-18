<template>
  <div class="slider-input" :class="{ disabled }">
    <label
      v-if="label"
      class="slider-label"
      :class="{ scrubbing: isScrubbing }"
      @mousedown="startScrub"
    >
      {{ label }}
    </label>
    <div class="slider-track" ref="trackRef" @mousedown="onTrackClick">
      <div
        class="slider-fill"
        :style="{ width: fillPercent + '%', background: gradient || undefined }"
      />
      <div
        class="slider-thumb"
        :style="{ left: fillPercent + '%' }"
        @mousedown.stop="startThumbDrag"
      />
    </div>
    <input
      v-if="showValue"
      type="number"
      class="slider-value"
      :value="displayValue"
      :min="min"
      :max="max"
      :step="step"
      :disabled="disabled"
      @input="onInput"
      @blur="onBlur"
    />
    <span v-if="unit" class="slider-unit">{{ unit }}</span>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from 'vue';

interface Props {
  modelValue: number;
  label?: string;
  min: number;
  max: number;
  step?: number;
  unit?: string;
  showValue?: boolean;
  gradient?: string;
  disabled?: boolean;
  precision?: number;
}

const props = withDefaults(defineProps<Props>(), {
  step: 1,
  showValue: true,
  disabled: false,
  precision: 2
});

const emit = defineEmits<{
  (e: 'update:modelValue', value: number): void;
}>();

const trackRef = ref<HTMLDivElement | null>(null);
const isScrubbing = ref(false);
const isDragging = ref(false);
const scrubStartX = ref(0);
const scrubStartValue = ref(0);

const fillPercent = computed(() => {
  const range = props.max - props.min;
  if (range === 0) return 0;
  return ((props.modelValue - props.min) / range) * 100;
});

const displayValue = computed(() => {
  if (Number.isInteger(props.step) && props.precision === 0) {
    return props.modelValue;
  }
  return Number(props.modelValue.toFixed(props.precision));
});

function clamp(value: number): number {
  return Math.max(props.min, Math.min(props.max, value));
}

function round(value: number): number {
  const factor = Math.pow(10, props.precision);
  return Math.round(value * factor) / factor;
}

function startScrub(e: MouseEvent): void {
  if (props.disabled) return;

  isScrubbing.value = true;
  scrubStartX.value = e.clientX;
  scrubStartValue.value = props.modelValue;

  document.addEventListener('mousemove', onScrubMove);
  document.addEventListener('mouseup', stopScrub);
  document.body.style.cursor = 'ew-resize';
  document.body.style.userSelect = 'none';
}

function onScrubMove(e: MouseEvent): void {
  const deltaX = e.clientX - scrubStartX.value;
  const range = props.max - props.min;

  let multiplier = 1;
  if (e.shiftKey) multiplier *= 10;
  if (e.ctrlKey || e.metaKey) multiplier *= 0.1;

  const deltaValue = (deltaX / 200) * range * multiplier;
  const newValue = round(clamp(scrubStartValue.value + deltaValue));

  if (newValue !== props.modelValue) {
    emit('update:modelValue', newValue);
  }
}

function stopScrub(): void {
  isScrubbing.value = false;
  document.removeEventListener('mousemove', onScrubMove);
  document.removeEventListener('mouseup', stopScrub);
  document.body.style.cursor = '';
  document.body.style.userSelect = '';
}

function onTrackClick(e: MouseEvent): void {
  if (props.disabled || !trackRef.value) return;

  const rect = trackRef.value.getBoundingClientRect();
  const percent = (e.clientX - rect.left) / rect.width;
  const value = props.min + percent * (props.max - props.min);

  emit('update:modelValue', round(clamp(value)));
}

function startThumbDrag(_e: MouseEvent): void {
  if (props.disabled) return;

  isDragging.value = true;
  document.addEventListener('mousemove', onThumbDrag);
  document.addEventListener('mouseup', stopThumbDrag);
  document.body.style.cursor = 'grabbing';
  document.body.style.userSelect = 'none';
}

function onThumbDrag(e: MouseEvent): void {
  if (!trackRef.value) return;

  const rect = trackRef.value.getBoundingClientRect();
  const percent = (e.clientX - rect.left) / rect.width;
  const value = props.min + Math.max(0, Math.min(1, percent)) * (props.max - props.min);

  emit('update:modelValue', round(clamp(value)));
}

function stopThumbDrag(): void {
  isDragging.value = false;
  document.removeEventListener('mousemove', onThumbDrag);
  document.removeEventListener('mouseup', stopThumbDrag);
  document.body.style.cursor = '';
  document.body.style.userSelect = '';
}

function onInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (!isNaN(value)) {
    emit('update:modelValue', round(clamp(value)));
  }
}

function onBlur(e: FocusEvent): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (isNaN(value)) {
    input.value = displayValue.value.toString();
  }
}
</script>

<style scoped>
.slider-input {
  display: flex;
  align-items: center;
  gap: 8px;
}

.slider-input.disabled {
  opacity: 0.5;
  pointer-events: none;
}

.slider-label {
  min-width: 70px;
  font-size: 13px;
  color: #888;
  cursor: ew-resize;
  user-select: none;
  transition: color 0.1s;
}

.slider-label:hover,
.slider-label.scrubbing {
  color: #7c9cff;
}

.slider-track {
  flex: 1;
  height: 4px;
  background: #3a3a3a;
  border-radius: 2px;
  position: relative;
  cursor: pointer;
  min-width: 80px;
}

.slider-fill {
  height: 100%;
  background: #7c9cff;
  border-radius: 2px;
  pointer-events: none;
}

.slider-thumb {
  position: absolute;
  top: 50%;
  width: 12px;
  height: 12px;
  background: #e0e0e0;
  border: 2px solid #7c9cff;
  border-radius: 50%;
  transform: translate(-50%, -50%);
  cursor: grab;
  transition: transform 0.1s;
}

.slider-thumb:hover {
  transform: translate(-50%, -50%) scale(1.2);
}

.slider-thumb:active {
  cursor: grabbing;
}

.slider-value {
  width: 50px;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #e0e0e0;
  font-size: 13px;
  text-align: right;
}

.slider-value:focus {
  outline: none;
  border-color: #7c9cff;
}

.slider-value::-webkit-inner-spin-button,
.slider-value::-webkit-outer-spin-button {
  -webkit-appearance: none;
  margin: 0;
}

.slider-value[type=number] {
  -moz-appearance: textfield;
}

.slider-unit {
  font-size: 12px;
  color: #666;
  min-width: 16px;
}
</style>
