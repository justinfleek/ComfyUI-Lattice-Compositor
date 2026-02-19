<template>
  <div class="angle-dial" :class="{ disabled }">
    <div
      class="dial"
      ref="dialRef"
      :style="{ width: size + 'px', height: size + 'px' }"
      @mousedown="startDrag"
    >
      <div class="dial-ring" />
      <div class="dial-center" />
      <div
        class="dial-indicator"
        :style="{ transform: `rotate(${modelValue}deg)` }"
      />
      <div class="dial-marks">
        <div class="dial-mark" v-for="i in 8" :key="i" :style="{ transform: `rotate(${i * 45}deg)` }" />
      </div>
    </div>
    <div v-if="showValue" class="angle-value">
      <input
        type="number"
        class="angle-input"
        :value="displayValue"
        :disabled="disabled"
        @input="onInput"
        @blur="onBlur"
      />
      <span class="angle-unit">°</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";

interface Props {
  modelValue: number;
  size?: number;
  showValue?: boolean;
  disabled?: boolean;
}

const props = withDefaults(defineProps<Props>(), {
  size: 48,
  showValue: true,
  disabled: false,
});

const emit = defineEmits<(e: "update:modelValue", value: number) => void>();

const dialRef = ref<HTMLDivElement | null>(null);
const isDragging = ref(false);

const displayValue = computed(() => {
  return Math.round(props.modelValue * 10) / 10;
});

function normalizeAngle(angle: number): number {
  return ((angle % 360) + 360) % 360;
}

function startDrag(e: MouseEvent): void {
  if (props.disabled) return;

  isDragging.value = true;
  updateAngle(e);

  document.addEventListener("mousemove", onDrag);
  document.addEventListener("mouseup", stopDrag);
  document.body.style.cursor = "grabbing";
  document.body.style.userSelect = "none";
}

function onDrag(e: MouseEvent): void {
  if (!isDragging.value) return;
  updateAngle(e);
}

function updateAngle(e: MouseEvent): void {
  if (!dialRef.value) return;

  const rect = dialRef.value.getBoundingClientRect();
  const centerX = rect.left + rect.width / 2;
  const centerY = rect.top + rect.height / 2;

  const deltaX = e.clientX - centerX;
  const deltaY = e.clientY - centerY;

  // Calculate angle (0 = up, clockwise positive)
  let angle = Math.atan2(deltaX, -deltaY) * (180 / Math.PI);
  angle = normalizeAngle(angle);

  // Snap to 45° increments when Shift is held
  if (e.shiftKey) {
    angle = Math.round(angle / 45) * 45;
  }

  emit("update:modelValue", angle);
}

function stopDrag(): void {
  isDragging.value = false;
  document.removeEventListener("mousemove", onDrag);
  document.removeEventListener("mouseup", stopDrag);
  document.body.style.cursor = "";
  document.body.style.userSelect = "";
}

function onInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (!Number.isNaN(value)) {
    emit("update:modelValue", normalizeAngle(value));
  }
}

function onBlur(e: FocusEvent): void {
  const input = e.target as HTMLInputElement;
  const value = parseFloat(input.value);

  if (Number.isNaN(value)) {
    input.value = displayValue.value.toString();
  }
}
</script>

<style scoped>
.angle-dial {
  display: flex;
  align-items: center;
  gap: 8px;
}

.angle-dial.disabled {
  opacity: 0.5;
  pointer-events: none;
}

.dial {
  position: relative;
  cursor: grab;
}

.dial:active {
  cursor: grabbing;
}

.dial-ring {
  position: absolute;
  inset: 4px;
  border: 2px solid #3d3d3d;
  border-radius: 50%;
}

.dial-center {
  position: absolute;
  top: 50%;
  left: 50%;
  width: 6px;
  height: 6px;
  background: #666;
  border-radius: 50%;
  transform: translate(-50%, -50%);
}

.dial-indicator {
  position: absolute;
  top: 50%;
  left: 50%;
  width: 2px;
  height: 45%;
  background: #7c9cff;
  border-radius: 1px;
  transform-origin: center bottom;
  transform: rotate(0deg);
}

.dial-marks {
  position: absolute;
  inset: 0;
}

.dial-mark {
  position: absolute;
  top: 2px;
  left: 50%;
  width: 1px;
  height: 4px;
  background: #555;
  transform-origin: center calc(50% - 2px);
}

.angle-value {
  display: flex;
  align-items: center;
  gap: 2px;
}

.angle-input {
  width: 50px;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #e0e0e0;
  font-size: 13px;
  text-align: right;
}

.angle-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.angle-input::-webkit-inner-spin-button,
.angle-input::-webkit-outer-spin-button {
  -webkit-appearance: none;
  margin: 0;
}

.angle-input[type=number] {
  -moz-appearance: textfield;
}

.angle-unit {
  font-size: 13px;
  color: #666;
}
</style>
