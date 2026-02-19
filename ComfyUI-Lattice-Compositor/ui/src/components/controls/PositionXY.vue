<template>
  <div class="position-xy" :class="{ disabled }">
    <div class="position-row">
      <label class="axis-label">X</label>
      <input
        type="number"
        class="position-input"
        :value="displayX"
        :min="min"
        :max="max"
        :step="step"
        :disabled="disabled"
        @input="onXInput"
        @blur="onBlur($event, 'x')"
      />
    </div>
    <button
      v-if="showLink"
      class="link-btn"
      :class="{ linked }"
      @click="toggleLink"
      title="Link X and Y"
    >
      <i :class="linked ? 'pi pi-link' : 'pi pi-minus'" />
    </button>
    <div class="position-row">
      <label class="axis-label">Y</label>
      <input
        type="number"
        class="position-input"
        :value="displayY"
        :min="min"
        :max="max"
        :step="step"
        :disabled="disabled"
        @input="onYInput"
        @blur="onBlur($event, 'y')"
      />
    </div>
    <div v-if="hasZ" class="position-row">
      <label class="axis-label">Z</label>
      <input
        type="number"
        class="position-input"
        :value="displayZ"
        :min="min"
        :max="max"
        :step="step"
        :disabled="disabled"
        @input="onZInput"
        @blur="onBlur($event, 'z')"
      />
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";

interface Props {
  x: number;
  y: number;
  z?: number;
  linked?: boolean;
  showLink?: boolean;
  step?: number;
  min?: number;
  max?: number;
  disabled?: boolean;
  precision?: number;
}

const props = withDefaults(defineProps<Props>(), {
  linked: false,
  showLink: true,
  step: 1,
  min: -Infinity,
  max: Infinity,
  disabled: false,
  precision: 2,
});

const emit = defineEmits<{
  (e: "update:x", value: number): void;
  (e: "update:y", value: number): void;
  (e: "update:z", value: number): void;
  (e: "update:linked", value: boolean): void;
}>();

const linked = ref(props.linked);
const previousX = ref(props.x);
const previousY = ref(props.y);

const hasZ = computed(() => props.z !== undefined);

const displayX = computed(() => round(props.x));
const displayY = computed(() => round(props.y));
const displayZ = computed(() => (props.z !== undefined ? round(props.z) : 0));

function round(value: number): number {
  const factor = 10 ** props.precision;
  return Math.round(value * factor) / factor;
}

function clamp(value: number): number {
  return Math.max(props.min, Math.min(props.max, value));
}

function toggleLink(): void {
  linked.value = !linked.value;
  emit("update:linked", linked.value);
}

function onXInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (!Number.isNaN(value)) {
    const newX = round(clamp(value));
    const deltaX = newX - previousX.value;

    emit("update:x", newX);

    if (linked.value) {
      emit("update:y", round(clamp(props.y + deltaX)));
    }

    previousX.value = newX;
  }
}

function onYInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (!Number.isNaN(value)) {
    const newY = round(clamp(value));
    const deltaY = newY - previousY.value;

    emit("update:y", newY);

    if (linked.value) {
      emit("update:x", round(clamp(props.x + deltaY)));
    }

    previousY.value = newY;
  }
}

function onZInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (!Number.isNaN(value)) {
    emit("update:z", round(clamp(value)));
  }
}

function onBlur(e: FocusEvent, axis: "x" | "y" | "z"): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (Number.isNaN(value)) {
    if (axis === "x") input.value = displayX.value.toString();
    else if (axis === "y") input.value = displayY.value.toString();
    else if (axis === "z") input.value = displayZ.value.toString();
  }
}
</script>

<style scoped>
.position-xy {
  display: flex;
  align-items: center;
  gap: 8px;
}

.position-xy.disabled {
  opacity: 0.5;
  pointer-events: none;
}

.position-row {
  display: flex;
  align-items: center;
  gap: 4px;
}

.axis-label {
  font-size: 12px;
  color: #666;
  font-weight: 500;
  min-width: 12px;
}

.position-input {
  width: 55px;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #e0e0e0;
  font-size: 13px;
  text-align: right;
}

.position-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.position-input::-webkit-inner-spin-button,
.position-input::-webkit-outer-spin-button {
  -webkit-appearance: none;
  margin: 0;
}

.position-input[type=number] {
  -moz-appearance: textfield;
}

.link-btn {
  width: 20px;
  height: 20px;
  padding: 0;
  border: none;
  border-radius: 3px;
  background: transparent;
  color: #666;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  transition: all 0.1s;
}

.link-btn:hover {
  background: #333;
  color: #888;
}

.link-btn.linked {
  color: #7c9cff;
}

.link-btn i {
  font-size: 12px;
}
</style>
