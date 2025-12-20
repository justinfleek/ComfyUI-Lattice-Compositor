<template>
  <div class="scrubable-number" :class="{ disabled, scrubbing: isScrubbing }">
    <label
      v-if="label"
      class="scrub-label"
      :class="{ scrubbing: isScrubbing }"
      @mousedown="startScrub"
    >
      {{ label }}
    </label>
    <!-- Scrub handle for when there's no label - appears on hover -->
    <div
      v-if="!label"
      class="scrub-handle"
      :class="{ scrubbing: isScrubbing }"
      @mousedown="startScrub"
      title="Drag to scrub value"
    >
      ⋮⋮
    </div>
    <input
      ref="inputRef"
      type="number"
      class="scrub-input"
      :class="{ scrubbing: isScrubbing }"
      :value="displayValue"
      :min="min"
      :max="max"
      :step="step"
      :disabled="disabled"
      @input="onInput"
      @keydown="onKeyDown"
      @blur="onBlur"
      @mousedown="onInputMouseDown"
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

const inputRef = ref<HTMLInputElement | null>(null);
const isScrubbing = ref(false);
const scrubStartX = ref(0);
const scrubStartValue = ref(0);
const isDragging = ref(false);
const dragThreshold = 3; // pixels before considering it a drag vs click

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
  e.preventDefault();

  isScrubbing.value = true;
  scrubStartX.value = e.clientX;
  scrubStartValue.value = props.modelValue;

  document.addEventListener('mousemove', onScrubMove);
  document.addEventListener('mouseup', stopScrub);
  document.body.style.cursor = 'ew-resize';
  document.body.style.userSelect = 'none';
}

// Handle mousedown on input - detect drag vs click
function onInputMouseDown(e: MouseEvent): void {
  if (props.disabled) return;

  // Only trigger on left mouse button
  if (e.button !== 0) return;

  const startX = e.clientX;
  const startY = e.clientY;
  isDragging.value = false;

  const onMouseMove = (moveEvent: MouseEvent) => {
    const deltaX = Math.abs(moveEvent.clientX - startX);
    const deltaY = Math.abs(moveEvent.clientY - startY);

    // If moved beyond threshold, start scrubbing
    if (!isDragging.value && (deltaX > dragThreshold || deltaY > dragThreshold)) {
      isDragging.value = true;
      isScrubbing.value = true;
      scrubStartX.value = startX;
      scrubStartValue.value = props.modelValue;
      document.body.style.cursor = 'ew-resize';
      document.body.style.userSelect = 'none';

      // Blur the input to prevent text selection issues
      inputRef.value?.blur();
    }

    if (isDragging.value) {
      onScrubMove(moveEvent);
    }
  };

  const onMouseUp = () => {
    document.removeEventListener('mousemove', onMouseMove);
    document.removeEventListener('mouseup', onMouseUp);

    if (isDragging.value) {
      isScrubbing.value = false;
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
    }
    // If not dragging, the click will focus the input normally
    isDragging.value = false;
  };

  document.addEventListener('mousemove', onMouseMove);
  document.addEventListener('mouseup', onMouseUp);
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
  gap: 4px;
}

.scrubable-number.disabled {
  opacity: 0.5;
  pointer-events: none;
}

.scrubable-number.scrubbing {
  /* Visual feedback when scrubbing */
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

/* Scrub handle - visible drag target when no label */
.scrub-handle {
  display: flex;
  align-items: center;
  justify-content: center;
  width: 12px;
  height: 20px;
  color: #555;
  cursor: ew-resize;
  user-select: none;
  font-size: 10px;
  letter-spacing: -2px;
  transition: color 0.1s, background 0.1s;
  border-radius: 2px;
  flex-shrink: 0;
}

.scrub-handle:hover {
  color: #7c9cff;
  background: rgba(124, 156, 255, 0.1);
}

.scrub-handle.scrubbing {
  color: #7c9cff;
  background: rgba(124, 156, 255, 0.2);
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
  cursor: text;
  transition: border-color 0.1s;
}

/* Change cursor to indicate scrubbing is possible */
.scrub-input:not(:focus) {
  cursor: ew-resize;
}

.scrub-input:focus {
  outline: none;
  border-color: #7c9cff;
  cursor: text;
}

.scrub-input.scrubbing {
  border-color: #7c9cff;
  background: #252530;
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
