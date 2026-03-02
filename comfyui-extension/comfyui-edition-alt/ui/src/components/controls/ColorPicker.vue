<template>
  <div class="color-picker" ref="containerRef">
    <!-- Color Preview Swatch -->
    <button
      class="color-swatch"
      :style="{ backgroundColor: modelValue }"
      @click="togglePicker"
    >
      <span class="checkerboard" v-if="alpha" />
    </button>

    <!-- Hex Input -->
    <input
      type="text"
      class="hex-input"
      :value="modelValue"
      @input="onHexInput"
      @blur="onHexBlur"
      @keydown.enter="($event.target as HTMLInputElement).blur()"
    />

    <!-- Picker Panel -->
    <Teleport to="body" :disabled="!teleport">
      <div
        v-if="isOpen"
        class="picker-panel"
        :style="panelStyle"
        ref="panelRef"
      >
        <!-- Mode Tabs -->
        <div class="mode-tabs">
          <button
            v-for="mode in modes"
            :key="mode"
            :class="{ active: currentMode === mode }"
            @click="currentMode = mode"
          >
            {{ mode.toUpperCase() }}
          </button>
        </div>

        <!-- HSV Mode -->
        <template v-if="currentMode === 'hsv'">
          <!-- SV Square -->
          <div
            class="sv-square"
            :style="{ backgroundColor: `hsl(${hsv[0]}, 100%, 50%)` }"
            @mousedown="startSVDrag"
            ref="svSquareRef"
          >
            <div class="sv-white" />
            <div class="sv-black" />
            <div
              class="sv-cursor"
              :style="{ left: hsv[1] * 100 + '%', top: (1 - hsv[2]) * 100 + '%' }"
            />
          </div>

          <!-- Hue Slider -->
          <div class="hue-slider" @mousedown="startHueDrag" ref="hueSliderRef">
            <div class="hue-cursor" :style="{ left: (hsv[0] / 360) * 100 + '%' }" />
          </div>
        </template>

        <!-- RGB Mode -->
        <template v-else-if="currentMode === 'rgb'">
          <div class="rgb-sliders">
            <div class="color-slider">
              <label>R</label>
              <div
                class="slider-track r-track"
                @mousedown="startSliderDrag('r', $event)"
              >
                <div class="slider-cursor" :style="{ left: (rgb[0] / 255) * 100 + '%' }" />
              </div>
              <input
                type="number"
                :value="rgb[0]"
                min="0"
                max="255"
                @input="onRgbInput(0, $event)"
              />
            </div>
            <div class="color-slider">
              <label>G</label>
              <div
                class="slider-track g-track"
                @mousedown="startSliderDrag('g', $event)"
              >
                <div class="slider-cursor" :style="{ left: (rgb[1] / 255) * 100 + '%' }" />
              </div>
              <input
                type="number"
                :value="rgb[1]"
                min="0"
                max="255"
                @input="onRgbInput(1, $event)"
              />
            </div>
            <div class="color-slider">
              <label>B</label>
              <div
                class="slider-track b-track"
                @mousedown="startSliderDrag('b', $event)"
              >
                <div class="slider-cursor" :style="{ left: (rgb[2] / 255) * 100 + '%' }" />
              </div>
              <input
                type="number"
                :value="rgb[2]"
                min="0"
                max="255"
                @input="onRgbInput(2, $event)"
              />
            </div>
          </div>
        </template>

        <!-- HSL Mode -->
        <template v-else-if="currentMode === 'hsl'">
          <div class="hsl-sliders">
            <div class="color-slider">
              <label>H</label>
              <div class="slider-track hue-track" @mousedown="startSliderDrag('h', $event)">
                <div class="slider-cursor" :style="{ left: (hsl[0] / 360) * 100 + '%' }" />
              </div>
              <input
                type="number"
                :value="Math.round(hsl[0])"
                min="0"
                max="360"
                @input="onHslInput(0, $event)"
              />
            </div>
            <div class="color-slider">
              <label>S</label>
              <div
                class="slider-track sat-track"
                :style="{ '--hue': hsl[0] }"
                @mousedown="startSliderDrag('s', $event)"
              >
                <div class="slider-cursor" :style="{ left: hsl[1] * 100 + '%' }" />
              </div>
              <input
                type="number"
                :value="Math.round(hsl[1] * 100)"
                min="0"
                max="100"
                @input="onHslInput(1, $event)"
              />
            </div>
            <div class="color-slider">
              <label>L</label>
              <div
                class="slider-track light-track"
                :style="{ '--hue': hsl[0] }"
                @mousedown="startSliderDrag('l', $event)"
              >
                <div class="slider-cursor" :style="{ left: hsl[2] * 100 + '%' }" />
              </div>
              <input
                type="number"
                :value="Math.round(hsl[2] * 100)"
                min="0"
                max="100"
                @input="onHslInput(2, $event)"
              />
            </div>
          </div>
        </template>

        <!-- Alpha Slider -->
        <div v-if="alpha" class="alpha-slider">
          <label>A</label>
          <div
            class="slider-track alpha-track"
            :style="{ '--color': modelValue }"
            @mousedown="startAlphaDrag"
            ref="alphaSliderRef"
          >
            <div class="slider-cursor" :style="{ left: alphaValue * 100 + '%' }" />
          </div>
          <input
            type="number"
            :value="Math.round(alphaValue * 100)"
            min="0"
            max="100"
            @input="onAlphaInput"
          />
        </div>

        <!-- Swatches -->
        <div class="swatches-section">
          <div class="swatches-label">Swatches</div>
          <div class="swatches-grid">
            <button
              v-for="swatch in allSwatches"
              :key="swatch"
              class="swatch"
              :style="{ backgroundColor: swatch }"
              @click="selectSwatch(swatch)"
            />
          </div>
        </div>

        <!-- Recent Colors -->
        <div v-if="recentColors.length > 0" class="recent-section">
          <div class="swatches-label">Recent</div>
          <div class="swatches-grid">
            <button
              v-for="color in recentColors"
              :key="color"
              class="swatch"
              :style="{ backgroundColor: color }"
              @click="selectSwatch(color)"
            />
          </div>
        </div>
      </div>
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref, watch } from "vue";
import { safeNonNegativeDefault, safeCoordinateDefault } from "@/utils/typeGuards";
import {
  type HSL,
  type HSV,
  hexToRgb,
  hslToRgb,
  hsvToRgb,
  type RGB,
  rgbToHex,
  rgbToHsl,
  rgbToHsv,
  STANDARD_SWATCHES,
} from "@/utils/colorUtils";

interface Props {
  modelValue: string;
  alpha?: boolean;
  swatches?: string[];
  recentCount?: number;
  teleport?: boolean;
}

const props = withDefaults(defineProps<Props>(), {
  alpha: false,
  recentCount: 8,
  teleport: true,
});

const emit = defineEmits<(e: "update:modelValue", value: string) => void>();

type ColorMode = "hsv" | "rgb" | "hsl";
const modes: ColorMode[] = ["hsv", "rgb", "hsl"];

const containerRef = ref<HTMLDivElement | null>(null);
const panelRef = ref<HTMLDivElement | null>(null);
const svSquareRef = ref<HTMLDivElement | null>(null);
const hueSliderRef = ref<HTMLDivElement | null>(null);
const alphaSliderRef = ref<HTMLDivElement | null>(null);

const isOpen = ref(false);
const currentMode = ref<ColorMode>("hsv");
const alphaValue = ref(1);
const recentColors = ref<string[]>([]);

// Derived color values
const rgb = ref<RGB>([255, 255, 255]);
const hsv = ref<HSV>([0, 0, 1]);
const hsl = ref<HSL>([0, 0, 1]);

const allSwatches = computed(() => props.swatches || STANDARD_SWATCHES);

const panelStyle = computed(() => {
  if (!containerRef.value || !props.teleport) return {};

  const rect = containerRef.value.getBoundingClientRect();
  return {
    top: `${rect.bottom + 4}px`,
    left: `${rect.left}px`,
  };
});

// Initialize from modelValue
function updateFromHex(hex: string): void {
  // System F/Omega proof: Validate hex format before calling utility
  // Type proof: hex ∈ string → void
  // Mathematical proof: Hex string must be valid format (#RGB, #RRGGBB, or #RRGGBBAA)
  const normalizedHex = hex.replace(/^#/, "");
  const isValidHex = /^([0-9a-f]{3}|[0-9a-f]{6}|[0-9a-f]{8})$/i.test(normalizedHex);
  
  if (!isValidHex) {
    // Invalid hex format - skip update
    return;
  }
  
  const parsed = hexToRgb(hex);
  rgb.value = parsed;
  hsv.value = rgbToHsv(parsed[0], parsed[1], parsed[2]);
  hsl.value = rgbToHsl(parsed[0], parsed[1], parsed[2]);
}

function emitColor(): void {
  const hex = rgbToHex(rgb.value[0], rgb.value[1], rgb.value[2]);
  emit("update:modelValue", hex);
}

function togglePicker(): void {
  isOpen.value = !isOpen.value;
}

function closePicker(): void {
  if (isOpen.value) {
    isOpen.value = false;
    addToRecent(props.modelValue);
  }
}

function addToRecent(color: string): void {
  const index = recentColors.value.indexOf(color);
  if (index !== -1) {
    recentColors.value.splice(index, 1);
  }
  recentColors.value.unshift(color);
  if (recentColors.value.length > props.recentCount) {
    recentColors.value.pop();
  }
}

function selectSwatch(color: string): void {
  emit("update:modelValue", color);
}

//                                                                   // sv // s
let isDraggingSV = false;

function startSVDrag(e: MouseEvent): void {
  isDraggingSV = true;
  updateSV(e);
  document.addEventListener("mousemove", onSVDrag);
  document.addEventListener("mouseup", stopSVDrag);
}

function onSVDrag(e: MouseEvent): void {
  if (isDraggingSV) updateSV(e);
}

function updateSV(e: MouseEvent): void {
  if (!svSquareRef.value) return;

  const rect = svSquareRef.value.getBoundingClientRect();
  const s = Math.max(0, Math.min(1, (e.clientX - rect.left) / rect.width));
  const v = Math.max(0, Math.min(1, 1 - (e.clientY - rect.top) / rect.height));

  hsv.value = [hsv.value[0], s, v];
  rgb.value = hsvToRgb(hsv.value[0], hsv.value[1], hsv.value[2]);
  hsl.value = rgbToHsl(rgb.value[0], rgb.value[1], rgb.value[2]);
  emitColor();
}

function stopSVDrag(): void {
  isDraggingSV = false;
  document.removeEventListener("mousemove", onSVDrag);
  document.removeEventListener("mouseup", stopSVDrag);
}

// Hue slider drag
let isDraggingHue = false;

function startHueDrag(e: MouseEvent): void {
  isDraggingHue = true;
  updateHue(e);
  document.addEventListener("mousemove", onHueDrag);
  document.addEventListener("mouseup", stopHueDrag);
}

function onHueDrag(e: MouseEvent): void {
  if (isDraggingHue) updateHue(e);
}

function updateHue(e: MouseEvent): void {
  if (!hueSliderRef.value) return;

  const rect = hueSliderRef.value.getBoundingClientRect();
  const h = Math.max(
    0,
    Math.min(360, ((e.clientX - rect.left) / rect.width) * 360),
  );

  hsv.value = [h, hsv.value[1], hsv.value[2]];
  rgb.value = hsvToRgb(hsv.value[0], hsv.value[1], hsv.value[2]);
  hsl.value = rgbToHsl(rgb.value[0], rgb.value[1], rgb.value[2]);
  emitColor();
}

function stopHueDrag(): void {
  isDraggingHue = false;
  document.removeEventListener("mousemove", onHueDrag);
  document.removeEventListener("mouseup", stopHueDrag);
}

// Generic slider drag
let draggingSlider: string | null = null;
let sliderRect: DOMRect | null = null;

function startSliderDrag(slider: string, e: MouseEvent): void {
  draggingSlider = slider;
  const track = (e.target as HTMLElement).closest(
    ".slider-track",
  ) as HTMLElement;
  if (track) {
    sliderRect = track.getBoundingClientRect();
    updateSlider(e);
    document.addEventListener("mousemove", onSliderDrag);
    document.addEventListener("mouseup", stopSliderDrag);
  }
}

function onSliderDrag(e: MouseEvent): void {
  if (draggingSlider) updateSlider(e);
}

function updateSlider(e: MouseEvent): void {
  if (!sliderRect || !draggingSlider) return;

  const percent = Math.max(
    0,
    Math.min(1, (e.clientX - sliderRect.left) / sliderRect.width),
  );

  switch (draggingSlider) {
    case "r":
      rgb.value = [Math.round(percent * 255), rgb.value[1], rgb.value[2]];
      hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
      hsl.value = rgbToHsl(rgb.value[0], rgb.value[1], rgb.value[2]);
      break;
    case "g":
      rgb.value = [rgb.value[0], Math.round(percent * 255), rgb.value[2]];
      hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
      hsl.value = rgbToHsl(rgb.value[0], rgb.value[1], rgb.value[2]);
      break;
    case "b":
      rgb.value = [rgb.value[0], rgb.value[1], Math.round(percent * 255)];
      hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
      hsl.value = rgbToHsl(rgb.value[0], rgb.value[1], rgb.value[2]);
      break;
    case "h":
      hsl.value = [percent * 360, hsl.value[1], hsl.value[2]];
      rgb.value = hslToRgb(hsl.value[0], hsl.value[1], hsl.value[2]);
      hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
      break;
    case "s":
      hsl.value = [hsl.value[0], percent, hsl.value[2]];
      rgb.value = hslToRgb(hsl.value[0], hsl.value[1], hsl.value[2]);
      hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
      break;
    case "l":
      hsl.value = [hsl.value[0], hsl.value[1], percent];
      rgb.value = hslToRgb(hsl.value[0], hsl.value[1], hsl.value[2]);
      hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
      break;
  }

  emitColor();
}

function stopSliderDrag(): void {
  draggingSlider = null;
  sliderRect = null;
  document.removeEventListener("mousemove", onSliderDrag);
  document.removeEventListener("mouseup", stopSliderDrag);
}

// Alpha slider
let isDraggingAlpha = false;

function startAlphaDrag(e: MouseEvent): void {
  isDraggingAlpha = true;
  updateAlpha(e);
  document.addEventListener("mousemove", onAlphaDrag);
  document.addEventListener("mouseup", stopAlphaDrag);
}

function onAlphaDrag(e: MouseEvent): void {
  if (isDraggingAlpha) updateAlpha(e);
}

function updateAlpha(e: MouseEvent): void {
  if (!alphaSliderRef.value) return;

  const rect = alphaSliderRef.value.getBoundingClientRect();
  alphaValue.value = Math.max(
    0,
    Math.min(1, (e.clientX - rect.left) / rect.width),
  );
}

function stopAlphaDrag(): void {
  isDraggingAlpha = false;
  document.removeEventListener("mousemove", onAlphaDrag);
  document.removeEventListener("mouseup", stopAlphaDrag);
}

// Input handlers
function onHexInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  let value = input.value.trim();

  if (!value.startsWith("#")) {
    value = `#${value}`;
  }

  if (/^#[0-9a-f]{6}$/i.test(value)) {
    emit("update:modelValue", value.toLowerCase());
  }
}

function onHexBlur(e: FocusEvent): void {
  const input = e.target as HTMLInputElement;
  input.value = props.modelValue;
}

function onRgbInput(index: number, e: Event): void {
  const input = e.target as HTMLInputElement;
  // Type proof: RGB value ∈ number | NaN → number (0-255 range, non-negative)
  const parsed = parseInt(input.value, 10);
  const value = Number.isInteger(parsed) && parsed >= 0 && parsed <= 255 ? parsed : 0;
  const clampedValue = Math.max(0, Math.min(255, value));

  const newRgb: RGB = [...rgb.value];
  newRgb[index] = clampedValue;
  rgb.value = newRgb;
  hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
  hsl.value = rgbToHsl(rgb.value[0], rgb.value[1], rgb.value[2]);
  emitColor();
}

function onHslInput(index: number, e: Event): void {
  const input = e.target as HTMLInputElement;
  // Type proof: HSL value ∈ number | NaN → number (coordinate-like for hue, 0-100 for saturation/lightness)
  const parsed = parseFloat(input.value);
  let value = Number.isFinite(parsed) ? parsed : 0;

  if (index === 0) {
    value = Math.max(0, Math.min(360, value));
    hsl.value = [value, hsl.value[1], hsl.value[2]];
  } else {
    value = Math.max(0, Math.min(100, value)) / 100;
    if (index === 1) hsl.value = [hsl.value[0], value, hsl.value[2]];
    else hsl.value = [hsl.value[0], hsl.value[1], value];
  }

  rgb.value = hslToRgb(hsl.value[0], hsl.value[1], hsl.value[2]);
  hsv.value = rgbToHsv(rgb.value[0], rgb.value[1], rgb.value[2]);
  emitColor();
}

function onAlphaInput(e: Event): void {
  const input = e.target as HTMLInputElement;
  // Type proof: alpha value ∈ number | NaN → number (0-100 range, non-negative)
  const parsed = parseInt(input.value, 10);
  const value = Number.isInteger(parsed) && parsed >= 0 && parsed <= 100 ? parsed : 0;
  alphaValue.value = Math.max(0, Math.min(100, value)) / 100;
}

// Click outside handler
function onClickOutside(e: MouseEvent): void {
  if (
    containerRef.value &&
    !containerRef.value.contains(e.target as Node) &&
    panelRef.value &&
    !panelRef.value.contains(e.target as Node)
  ) {
    closePicker();
  }
}

// Watch modelValue changes
watch(
  () => props.modelValue,
  (newVal) => {
    updateFromHex(newVal);
  },
  { immediate: true },
);

onMounted(() => {
  document.addEventListener("mousedown", onClickOutside);
});

onUnmounted(() => {
  document.removeEventListener("mousedown", onClickOutside);
});
</script>

<style scoped>
.color-picker {
  display: flex;
  align-items: center;
  gap: 6px;
  position: relative;
}

.color-swatch {
  width: 24px;
  height: 24px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  cursor: pointer;
  position: relative;
  padding: 0;
}

.color-swatch:hover {
  border-color: #7c9cff;
}

.checkerboard {
  position: absolute;
  inset: 0;
  background: conic-gradient(#808080 25%, #fff 25% 50%, #808080 50% 75%, #fff 75%);
  background-size: 8px 8px;
  border-radius: 2px;
  z-index: -1;
}

.hex-input {
  width: 70px;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #e0e0e0;
  font-size: 13px;
  font-family: monospace;
}

.hex-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.picker-panel {
  position: fixed;
  z-index: 1000;
  width: 240px;
  background: #1e1e1e;
  border: 1px solid #3d3d3d;
  border-radius: 6px;
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.4);
  padding: 12px;
}

.mode-tabs {
  display: flex;
  gap: 4px;
  margin-bottom: 12px;
}

.mode-tabs button {
  flex: 1;
  padding: 4px 8px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #888;
  font-size: 12px;
  cursor: pointer;
}

.mode-tabs button.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}

.sv-square {
  position: relative;
  width: 100%;
  height: 140px;
  border-radius: 4px;
  cursor: crosshair;
  margin-bottom: 12px;
}

.sv-white {
  position: absolute;
  inset: 0;
  background: linear-gradient(to right, white, transparent);
  border-radius: 4px;
}

.sv-black {
  position: absolute;
  inset: 0;
  background: linear-gradient(to bottom, transparent, black);
  border-radius: 4px;
}

.sv-cursor {
  position: absolute;
  width: 12px;
  height: 12px;
  border: 2px solid white;
  border-radius: 50%;
  box-shadow: 0 0 0 1px rgba(0, 0, 0, 0.3), inset 0 0 0 1px rgba(0, 0, 0, 0.3);
  transform: translate(-50%, -50%);
  pointer-events: none;
}

.hue-slider,
.alpha-slider .slider-track {
  height: 12px;
  border-radius: 6px;
  cursor: pointer;
  position: relative;
  margin-bottom: 12px;
}

.hue-slider {
  background: linear-gradient(to right,
    #ff0000, #ffff00, #00ff00, #00ffff, #0000ff, #ff00ff, #ff0000);
}

.hue-cursor,
.slider-cursor {
  position: absolute;
  top: 50%;
  width: 14px;
  height: 14px;
  background: white;
  border: 2px solid #333;
  border-radius: 50%;
  transform: translate(-50%, -50%);
  box-shadow: 0 1px 3px rgba(0, 0, 0, 0.3);
  pointer-events: none;
}

.rgb-sliders,
.hsl-sliders {
  display: flex;
  flex-direction: column;
  gap: 8px;
  margin-bottom: 12px;
}

.color-slider {
  display: flex;
  align-items: center;
  gap: 8px;
}

.color-slider label {
  width: 14px;
  font-size: 12px;
  color: #888;
  font-weight: 500;
}

.slider-track {
  flex: 1;
  height: 12px;
  border-radius: 6px;
  cursor: pointer;
  position: relative;
}

.r-track {
  background: linear-gradient(to right, #000, #f00);
}

.g-track {
  background: linear-gradient(to right, #000, #0f0);
}

.b-track {
  background: linear-gradient(to right, #000, #00f);
}

.hue-track {
  background: linear-gradient(to right,
    #ff0000, #ffff00, #00ff00, #00ffff, #0000ff, #ff00ff, #ff0000);
}

.sat-track {
  background: linear-gradient(to right,
    hsl(calc(var(--hue) * 1deg), 0%, 50%),
    hsl(calc(var(--hue) * 1deg), 100%, 50%));
}

.light-track {
  background: linear-gradient(to right,
    #000,
    hsl(calc(var(--hue) * 1deg), 100%, 50%),
    #fff);
}

.alpha-slider {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 12px;
}

.alpha-slider label {
  width: 14px;
  font-size: 12px;
  color: #888;
  font-weight: 500;
}

.alpha-slider .slider-track {
  flex: 1;
  background:
    linear-gradient(to right, transparent, var(--color)),
    conic-gradient(#808080 25%, #fff 25% 50%, #808080 50% 75%, #fff 75%);
  background-size: 100% 100%, 8px 8px;
}

.color-slider input,
.alpha-slider input {
  width: 40px;
  padding: 2px 4px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #e0e0e0;
  font-size: 12px;
  text-align: right;
}

.color-slider input:focus,
.alpha-slider input:focus {
  outline: none;
  border-color: #7c9cff;
}

.color-slider input::-webkit-inner-spin-button,
.color-slider input::-webkit-outer-spin-button,
.alpha-slider input::-webkit-inner-spin-button,
.alpha-slider input::-webkit-outer-spin-button {
  -webkit-appearance: none;
  margin: 0;
}

.swatches-section,
.recent-section {
  margin-top: 8px;
}

.swatches-label {
  font-size: 12px;
  color: #666;
  margin-bottom: 6px;
}

.swatches-grid {
  display: flex;
  flex-wrap: wrap;
  gap: 4px;
}

.swatch {
  width: 16px;
  height: 16px;
  border: 1px solid #3d3d3d;
  border-radius: 2px;
  cursor: pointer;
  padding: 0;
}

.swatch:hover {
  border-color: #7c9cff;
  transform: scale(1.1);
}
</style>
