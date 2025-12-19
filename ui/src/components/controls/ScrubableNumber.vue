<template>
  <div class="scrubable-number" :class="{ disabled }">
    <label
      v-if="label"
      class="scrub-label"
      :class="{ scrubbing: isScrubbing }"
      @mousedown="startScrub"
    >
      {{ label }}
    </label>
    <input
      type="number"
      class="scrub-input"
      :value="displayValue"
      :min="min"
      :max="max"
      :step="step"
      :disabled="disabled"
      @input="onInput"
      @keydown="onKeyDown"
      @blur="onBlur"
    />
    <span v-if="unit" class="scrub-unit">{{ unit }}</span>
    <button
      v-if="showReset && modelValue !== defaultValue"
      class="reset-btn"
      @click="reset"
      title="Reset to default"
    >
      <i class="pi pi-refresh" />
    </button>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from 'vue';

interface Props {
  modelValue: number;
  label?: string;
  min?: number;
  max?: number;
  step?: number;
  precision?: number;
  unit?: string;
  default?: number;
  sensitivity?: number;
  disabled?: boolean;
}

const props = withDefaults(defineProps<Props>(), {
  min: -Infinity,
  max: Infinity,
  step: 1,
  precision: 2,
  sensitivity: 1,
  disabled: false
});

const emit = defineEmits<{
  (e: 'update:modelValue', value: number): void;
}>();

const isScrubbing = ref(false);
const scrubStartX = ref(0);
const scrubStartValue = ref(0);

const defaultValue = computed(() => props.default ?? props.modelValue);
const showReset = computed(() => props.default !== undefined);

const displayValue = computed(() => {
  if (Number.isInteger(props.modelValue) && props.precision === 0) {
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

  // Modifier keys affect sensitivity
  let multiplier = props.sensitivity;
  if (e.shiftKey) multiplier *= 10;
  if (e.ctrlKey || e.metaKey) multiplier *= 0.1;

  const deltaValue = deltaX * props.step * multiplier * 0.5;
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

function onInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (!isNaN(value)) {
    emit('update:modelValue', round(clamp(value)));
  }
}

function onKeyDown(e: KeyboardEvent): void {
  if (props.disabled) return;

  let delta = 0;
  if (e.key === 'ArrowUp') delta = props.step;
  else if (e.key === 'ArrowDown') delta = -props.step;

  if (delta !== 0) {
    e.preventDefault();
    if (e.shiftKey) delta *= 10;
    if (e.ctrlKey || e.metaKey) delta *= 0.1;

    emit('update:modelValue', round(clamp(props.modelValue + delta)));
  }
}

function onBlur(e: FocusEvent): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (isNaN(value)) {
    // Reset to current model value if invalid
    input.value = displayValue.value.toString();
  }
}

function reset(): void {
  if (props.default !== undefined) {
    emit('update:modelValue', props.default);
  }
}
</script>

<style scoped>
.scrubable-number {
  display: flex;
  align-items: center;
  gap: 6px;
}

.scrubable-number.disabled {
  opacity: 0.5;
  pointer-events: none;
}

.scrub-label {
  min-width: 70px;
  font-size: 13px;
  color: #888;
  cursor: ew-resize;
  user-select: none;
  transition: color 0.1s;
}

.scrub-label:hover {
  color: #7c9cff;
}

.scrub-label.scrubbing {
  color: #7c9cff;
}

.scrub-input {
  width: 60px;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #3498db; /* Cyan color for numeric values */
  font-size: 13px;
  font-family: inherit;
  text-align: right;
}

.scrub-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.scrub-input::-webkit-inner-spin-button,
.scrub-input::-webkit-outer-spin-button {
  -webkit-appearance: none;
  margin: 0;
}

.scrub-input[type=number] {
  -moz-appearance: textfield;
}

.scrub-unit {
  font-size: 12px;
  color: #666;
  min-width: 16px;
}

.reset-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  border-radius: 3px;
  background: transparent;
  color: #666;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  opacity: 0;
  transition: opacity 0.1s;
}

.scrubable-number:hover .reset-btn {
  opacity: 1;
}

.reset-btn:hover {
  background: #333;
  color: #7c9cff;
}

.reset-btn i {
  font-size: 12px;
}
</style>
