<template>
  <div class="exposed-property-control">
    <div class="property-header">
      <input
        type="text"
        v-model="localName"
        class="property-name-input"
        @blur="updateName"
      />
      <div class="property-actions">
        <button class="btn-icon-tiny" @click="$emit('remove')" title="Remove">
          ×
        </button>
      </div>
    </div>

    <div class="property-value">
      <!-- Source Text -->
      <template v-if="property.type === 'sourceText'">
        <input
          type="text"
          :value="currentValue"
          @input="updateValue(($event.target as HTMLInputElement).value)"
          class="text-input"
          placeholder="Enter text..."
        />
      </template>

      <!-- Number / Slider -->
      <template v-else-if="property.type === 'number'">
        <div class="slider-control">
          <input
            type="range"
            :min="property.config.min ?? 0"
            :max="property.config.max ?? 100"
            :step="property.config.step ?? 1"
            :value="currentValue"
            @input="updateValue(parseFloat(($event.target as HTMLInputElement).value))"
            class="slider"
          />
          <input
            type="number"
            :value="currentValue"
            @input="updateValue(parseFloat(($event.target as HTMLInputElement).value))"
            class="number-input"
          />
        </div>
      </template>

      <!-- Checkbox -->
      <template v-else-if="property.type === 'checkbox'">
        <label class="checkbox-control">
          <input
            type="checkbox"
            :checked="currentValue"
            @change="updateValue(($event.target as HTMLInputElement).checked)"
          />
          <span class="checkbox-label">{{ currentValue ? 'On' : 'Off' }}</span>
        </label>
      </template>

      <!-- Dropdown -->
      <template v-else-if="property.type === 'dropdown'">
        <select
          :value="currentValue"
          @change="updateValue(($event.target as HTMLSelectElement).value)"
          class="dropdown-input"
        >
          <option
            v-for="opt in property.config.options"
            :key="opt.value"
            :value="opt.value"
          >
            {{ opt.label }}
          </option>
        </select>
      </template>

      <!-- Color -->
      <template v-else-if="property.type === 'color'">
        <div class="color-control">
          <input
            type="color"
            :value="colorToHex(currentValue)"
            @input="updateValue(hexToColor(($event.target as HTMLInputElement).value))"
            class="color-input"
          />
          <span class="color-hex">{{ colorToHex(currentValue) }}</span>
        </div>
      </template>

      <!-- Point -->
      <template v-else-if="property.type === 'point'">
        <div class="point-control">
          <label>
            X:
            <input
              type="number"
              :value="currentValue?.x ?? 0"
              @input="updatePointValue('x', parseFloat(($event.target as HTMLInputElement).value))"
              class="point-input"
            />
          </label>
          <label>
            Y:
            <input
              type="number"
              :value="currentValue?.y ?? 0"
              @input="updatePointValue('y', parseFloat(($event.target as HTMLInputElement).value))"
              class="point-input"
            />
          </label>
        </div>
      </template>

      <!-- Media -->
      <template v-else-if="property.type === 'media'">
        <div class="media-control">
          <div class="media-preview" @click="selectMedia" :title="'Click to replace media'">
            <img v-if="currentValue" :src="currentValue" alt="" />
            <span v-else class="media-placeholder">📁</span>
          </div>
          <div class="media-info">
            <span v-if="currentValue" class="media-filename">{{ getMediaFilename(currentValue) }}</span>
            <span v-else class="media-filename muted">No media selected</span>
            <button class="btn-small" @click="selectMedia">Replace...</button>
          </div>
        </div>
        <input
          ref="mediaFileInput"
          type="file"
          accept="image/*,video/*"
          style="display: none"
          @change="handleMediaSelect"
        />
      </template>

      <!-- Layer Picker -->
      <template v-else-if="property.type === 'layer'">
        <div class="layer-control">
          <select
            :value="currentValue"
            @change="updateValue(($event.target as HTMLSelectElement).value)"
            class="dropdown-input layer-picker"
          >
            <option value="">None</option>
            <option
              v-for="availableLayer in availableLayers"
              :key="availableLayer.id"
              :value="availableLayer.id"
            >
              {{ availableLayer.name }}
            </option>
          </select>
          <div v-if="selectedLayerInfo" class="layer-info">
            <span class="layer-type">{{ selectedLayerInfo.type }}</span>
          </div>
        </div>
      </template>

      <!-- Font -->
      <template v-else-if="property.type === 'font'">
        <select
          :value="currentValue"
          @change="updateValue(($event.target as HTMLSelectElement).value)"
          class="dropdown-input"
        >
          <option v-for="font in availableFonts" :key="font" :value="font">
            {{ font }}
          </option>
        </select>
      </template>

      <!-- Fallback -->
      <template v-else>
        <span class="unsupported">Unsupported type: {{ property.type }}</span>
      </template>
    </div>

    <!-- Property path info -->
    <div class="property-path">
      {{ property.sourcePropertyPath }}
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, watch } from "vue";
import { getPropertyValue, setPropertyValue } from "@/services/templateBuilder";
import { useCompositorStore } from "@/stores/compositorStore";
import type { Layer } from "@/types/project";
import type { ExposedProperty } from "@/types/templateBuilder";

const props = defineProps<{
  property: ExposedProperty;
  layer?: Layer;
}>();

const emit = defineEmits<{
  (e: "update", propertyId: string, updates: Partial<ExposedProperty>): void;
  (e: "remove"): void;
}>();

const compositorStore = useCompositorStore();

// Local state
const localName = ref(props.property.name);
const mediaFileInput = ref<HTMLInputElement | null>(null);

// Watch for external changes
watch(
  () => props.property.name,
  (newName) => {
    localName.value = newName;
  },
);

// Current value from the layer
const currentValue = computed(() => {
  if (!props.layer) return undefined;
  return getPropertyValue(props.layer, props.property.sourcePropertyPath);
});

// Available layers for layer picker (exclude current layer)
const availableLayers = computed(() => {
  const comp = compositorStore.activeComposition;
  if (!comp) return [];
  return comp.layers.filter((l) => l.id !== props.layer?.id);
});

// Selected layer info for display
const _selectedLayerInfo = computed(() => {
  if (!currentValue.value || props.property.type !== "layer") return null;
  return availableLayers.value.find((l) => l.id === currentValue.value);
});

// Available fonts
const _availableFonts = [
  "Arial",
  "Helvetica",
  "Times New Roman",
  "Georgia",
  "Verdana",
  "Courier New",
  "Inter",
  "Roboto",
  "Open Sans",
  "Lato",
  "Montserrat",
  "Poppins",
  "Source Sans Pro",
  "Nunito",
  "Raleway",
];

// Update property name
function _updateName() {
  if (localName.value !== props.property.name) {
    emit("update", props.property.id, { name: localName.value });
  }
}

// Update property value in the layer
function updateValue(value: any) {
  if (!props.layer) return;
  setPropertyValue(props.layer, props.property.sourcePropertyPath, value);
}

// Update point value
function _updatePointValue(axis: "x" | "y", value: number) {
  if (!props.layer) return;
  const current = currentValue.value || { x: 0, y: 0 };
  const updated = { ...current, [axis]: value };
  setPropertyValue(props.layer, props.property.sourcePropertyPath, updated);
}

// Color utilities
function _colorToHex(color: any): string {
  if (!color) return "#ffffff";
  if (typeof color === "string") return color;

  const r = Math.round((color.r ?? 255) * (color.r > 1 ? 1 : 255));
  const g = Math.round((color.g ?? 255) * (color.g > 1 ? 1 : 255));
  const b = Math.round((color.b ?? 255) * (color.b > 1 ? 1 : 255));

  return `#${[r, g, b].map((c) => c.toString(16).padStart(2, "0")).join("")}`;
}

function _hexToColor(hex: string): {
  r: number;
  g: number;
  b: number;
  a: number;
} {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  if (!result) return { r: 1, g: 1, b: 1, a: 1 };

  return {
    r: parseInt(result[1], 16) / 255,
    g: parseInt(result[2], 16) / 255,
    b: parseInt(result[3], 16) / 255,
    a: 1,
  };
}

// Media utilities
function _getMediaFilename(url: string): string {
  if (!url) return "";
  // Handle data URLs
  if (url.startsWith("data:")) {
    const match = url.match(/data:([^;]+)/);
    return match ? `[${match[1]}]` : "[embedded]";
  }
  // Handle regular URLs
  try {
    const urlObj = new URL(url, window.location.origin);
    const path = urlObj.pathname;
    return path.split("/").pop() || "media";
  } catch {
    return url.split("/").pop() || "media";
  }
}

// Media selection
function _selectMedia() {
  mediaFileInput.value?.click();
}

async function _handleMediaSelect(event: Event) {
  const input = event.target as HTMLInputElement;
  const file = input.files?.[0];
  if (!file) return;

  try {
    // Read file as data URL
    const dataUrl = await readFileAsDataURL(file);
    updateValue(dataUrl);
  } catch (error) {
    console.error("[ExposedPropertyControl] Failed to read media file:", error);
  }

  // Reset input for re-selection of same file
  input.value = "";
}

function readFileAsDataURL(file: File): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(reader.result as string);
    reader.onerror = () => reject(reader.error);
    reader.readAsDataURL(file);
  });
}
</script>

<style scoped>
.exposed-property-control {
  padding: 8px;
}

.property-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  margin-bottom: 6px;
}

.property-name-input {
  flex: 1;
  background: transparent;
  border: none;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
  font-weight: 500;
  padding: 2px 0;
}

.property-name-input:focus {
  outline: none;
  background: var(--lattice-surface-0, #0a0a0a);
  border-radius: 2px;
  padding: 2px 4px;
  margin: -2px -4px;
}

.property-actions {
  display: flex;
  gap: 4px;
  opacity: 0;
  transition: opacity 0.15s ease;
}

.exposed-property-control:hover .property-actions {
  opacity: 1;
}

.btn-icon-tiny {
  width: 18px;
  height: 18px;
  padding: 0;
  background: none;
  border: none;
  color: var(--lattice-text-muted, #6b7280);
  cursor: pointer;
  font-size: 14px;
}

.btn-icon-tiny:hover {
  color: var(--lattice-text-primary, #e5e5e5);
}

.property-value {
  margin-bottom: 4px;
}

.text-input,
.dropdown-input {
  width: 100%;
  padding: 6px 8px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
}

.slider-control {
  display: flex;
  align-items: center;
  gap: 8px;
}

.slider {
  flex: 1;
  height: 4px;
  -webkit-appearance: none;
  background: var(--lattice-surface-0, #0a0a0a);
  border-radius: 2px;
}

.slider::-webkit-slider-thumb {
  -webkit-appearance: none;
  width: 12px;
  height: 12px;
  background: var(--lattice-accent, #8b5cf6);
  border-radius: 50%;
  cursor: pointer;
}

.number-input {
  width: 60px;
  padding: 4px 6px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 11px;
  text-align: right;
}

.checkbox-control {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
}

.checkbox-label {
  font-size: 12px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.color-control {
  display: flex;
  align-items: center;
  gap: 8px;
}

.color-input {
  width: 32px;
  height: 24px;
  padding: 0;
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  cursor: pointer;
}

.color-hex {
  font-size: 11px;
  font-family: monospace;
  color: var(--lattice-text-secondary, #9ca3af);
}

.point-control {
  display: flex;
  gap: 12px;
}

.point-control label {
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: 11px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.point-input {
  width: 60px;
  padding: 4px 6px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 11px;
}

.media-control {
  display: flex;
  align-items: flex-start;
  gap: 10px;
}

.media-preview {
  width: 56px;
  height: 42px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  display: flex;
  align-items: center;
  justify-content: center;
  overflow: hidden;
  cursor: pointer;
  transition: border-color 0.15s ease;
  flex-shrink: 0;
}

.media-preview:hover {
  border-color: var(--lattice-accent, #8b5cf6);
}

.media-preview img {
  width: 100%;
  height: 100%;
  object-fit: cover;
}

.media-placeholder {
  font-size: 18px;
  opacity: 0.5;
}

.media-info {
  display: flex;
  flex-direction: column;
  gap: 4px;
  flex: 1;
  min-width: 0;
}

.media-filename {
  font-size: 11px;
  color: var(--lattice-text-secondary, #9ca3af);
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.media-filename.muted {
  color: var(--lattice-text-muted, #6b7280);
  font-style: italic;
}

.btn-small {
  padding: 4px 8px;
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 10px;
  cursor: pointer;
}

.btn-small:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.property-path {
  font-size: 9px;
  color: var(--lattice-text-muted, #6b7280);
  font-family: monospace;
}

.unsupported {
  font-size: 11px;
  color: var(--lattice-text-muted, #6b7280);
  font-style: italic;
}

/* Layer picker styles */
.layer-control {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.layer-picker {
  width: 100%;
}

.layer-info {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 2px 0;
}

.layer-type {
  font-size: 10px;
  color: var(--lattice-text-muted, #6b7280);
  background: var(--lattice-surface-0, #0a0a0a);
  padding: 2px 6px;
  border-radius: 3px;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}
</style>
