<template>
  <div class="texture-upload" :class="{ 'has-texture': hasTexture, 'drag-over': isDragging }">
    <div
      class="upload-zone"
      @click="openFilePicker"
      @dragover.prevent="onDragOver"
      @dragleave.prevent="onDragLeave"
      @drop.prevent="onDrop"
    >
      <div v-if="hasTexture" class="texture-preview">
        <img :src="previewUrl" :alt="mapType" />
        <div class="texture-info">
          <span class="texture-name">{{ textureName }}</span>
          <span class="texture-size">{{ textureSize }}</span>
        </div>
        <button class="remove-btn" @click.stop="removeTexture" title="Remove texture">
          <i class="pi pi-times"></i>
        </button>
      </div>
      <div v-else class="upload-placeholder">
        <i class="pi pi-image"></i>
        <span class="map-label">{{ mapLabel }}</span>
        <span class="hint">Click or drop image</span>
      </div>
    </div>

    <input
      ref="fileInput"
      type="file"
      :accept="acceptedFormats"
      @change="onFileSelected"
      style="display: none"
    />

    <!-- Texture settings (shown when texture is loaded) -->
    <div v-if="hasTexture && showSettings" class="texture-settings">
      <div class="setting-row">
        <label>Repeat</label>
        <div class="repeat-inputs">
          <ScrubableNumber
            v-model="repeatXValue"
            :min="0.01"
            :step="0.1"
          />
          <span class="separator">x</span>
          <ScrubableNumber
            v-model="repeatYValue"
            :min="0.01"
            :step="0.1"
          />
        </div>
      </div>

      <div class="setting-row">
        <label>Offset</label>
        <div class="offset-inputs">
          <ScrubableNumber
            v-model="offsetXValue"
            :step="0.01"
          />
          <span class="separator">,</span>
          <ScrubableNumber
            v-model="offsetYValue"
            :step="0.01"
          />
        </div>
      </div>

      <div class="setting-row" v-if="mapType === 'normal'">
        <label>Strength</label>
        <SliderInput
          v-model="normalScaleValue"
          :min="0"
          :max="2"
          :step="0.1"
        />
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import type { TextureMapType } from "@/types/project";

const props = defineProps<{
  mapType: TextureMapType;
  textureUrl?: string;
  textureName?: string;
  repeatX?: number;
  repeatY?: number;
  offsetX?: number;
  offsetY?: number;
  normalScale?: number;
  showSettings?: boolean;
}>();

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
// Computed properties for optional props with defaults
const repeatXValue = computed({
  get: () => (typeof props.repeatX === "number" && Number.isFinite(props.repeatX)) ? props.repeatX : 1,
  set: (value: number) => emit("update:repeatX", value),
});
const repeatYValue = computed({
  get: () => (typeof props.repeatY === "number" && Number.isFinite(props.repeatY)) ? props.repeatY : 1,
  set: (value: number) => emit("update:repeatY", value),
});
const offsetXValue = computed({
  get: () => (typeof props.offsetX === "number" && Number.isFinite(props.offsetX)) ? props.offsetX : 0,
  set: (value: number) => emit("update:offsetX", value),
});
const offsetYValue = computed({
  get: () => (typeof props.offsetY === "number" && Number.isFinite(props.offsetY)) ? props.offsetY : 0,
  set: (value: number) => emit("update:offsetY", value),
});
const normalScaleValue = computed({
  get: () => (typeof props.normalScale === "number" && Number.isFinite(props.normalScale)) ? props.normalScale : 1,
  set: (value: number) => emit("update:normalScale", value),
});

const emit = defineEmits<{
  upload: [file: File, dataUrl: string];
  remove: [];
  "update:repeatX": [value: number];
  "update:repeatY": [value: number];
  "update:offsetX": [value: number];
  "update:offsetY": [value: number];
  "update:normalScale": [value: number];
}>();

const fileInput = ref<HTMLInputElement | null>(null);
const isDragging = ref(false);
const previewUrl = ref(props.textureUrl || "");
const textureSize = ref("");

const mapLabels: Record<TextureMapType, string> = {
  albedo: "Albedo / Color",
  normal: "Normal Map",
  roughness: "Roughness",
  metalness: "Metalness",
  ao: "Ambient Occlusion",
  emissive: "Emissive",
  height: "Height / Displacement",
  opacity: "Opacity / Alpha",
  specular: "Specular",
};

const mapLabel = computed(() => mapLabels[props.mapType] || props.mapType);
const hasTexture = computed(() => !!previewUrl.value || !!props.textureUrl);

const acceptedFormats = "image/png,image/jpeg,image/webp,image/exr";

function openFilePicker() {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const fileInputValue = fileInput.value;
  if (fileInputValue != null && typeof fileInputValue === "object" && typeof fileInputValue.click === "function") {
    fileInputValue.click();
  }
}

function onDragOver(_e: DragEvent) {
  isDragging.value = true;
}

function onDragLeave(_e: DragEvent) {
  isDragging.value = false;
}

function onDrop(e: DragEvent) {
  isDragging.value = false;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (e != null && typeof e === "object" && "dataTransfer" in e && e.dataTransfer != null && typeof e.dataTransfer === "object") ? e.dataTransfer : undefined;
  const files = (dataTransfer != null && typeof dataTransfer === "object" && "files" in dataTransfer && dataTransfer.files != null) ? dataTransfer.files : null;
  if (files != null && files.length > 0) {
    handleFile(files[0]);
  }
}

function onFileSelected(e: Event) {
  const input = e.target as HTMLInputElement;
  if (input.files && input.files.length > 0) {
    handleFile(input.files[0]);
  }
}

function handleFile(file: File) {
  // Validate file type
  if (!file.type.startsWith("image/")) {
    console.warn("Invalid file type:", file.type);
    return;
  }

  // Create preview URL
  const reader = new FileReader();
  reader.onload = (e) => {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const target = (e != null && typeof e === "object" && "target" in e && e.target != null) ? e.target : undefined;
    const result = (target != null && typeof target === "object" && "result" in target && target.result != null) ? target.result : undefined;
    const dataUrl = (result != null && typeof result === "string") ? result : "";
    previewUrl.value = dataUrl;

    // Get image dimensions
    const img = new Image();
    img.onload = () => {
      textureSize.value = `${img.width} x ${img.height}`;
    };
    img.src = dataUrl;

    emit("upload", file, dataUrl);
  };
  reader.readAsDataURL(file);
}

function removeTexture() {
  previewUrl.value = "";
  textureSize.value = "";
  if (fileInput.value) {
    fileInput.value.value = "";
  }
  emit("remove");
}
</script>

<style scoped>
.texture-upload {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.upload-zone {
  position: relative;
  border: 2px dashed #333;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.2s ease;
  overflow: hidden;
  min-height: 80px;
}

.upload-zone:hover {
  border-color: #555;
  background: #252525;
}

.drag-over .upload-zone {
  border-color: #4a90d9;
  background: rgba(74, 144, 217, 0.1);
}

.has-texture .upload-zone {
  border-style: solid;
  border-color: #333;
}

.upload-placeholder {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  padding: 16px;
  gap: 4px;
}

.upload-placeholder i {
  font-size: 24px;
  color: #555;
}

.map-label {
  font-size: 13px;
  color: #888;
  font-weight: 500;
}

.hint {
  font-size: 12px;
  color: #555;
}

.texture-preview {
  position: relative;
  display: flex;
  align-items: center;
  padding: 8px;
  gap: 10px;
}

.texture-preview img {
  width: 48px;
  height: 48px;
  object-fit: cover;
  border-radius: 3px;
  background: #111;
}

.texture-info {
  flex: 1;
  display: flex;
  flex-direction: column;
  gap: 2px;
  overflow: hidden;
}

.texture-name {
  font-size: 13px;
  color: #ccc;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.texture-size {
  font-size: 12px;
  color: #666;
}

.remove-btn {
  position: absolute;
  top: 4px;
  right: 4px;
  width: 20px;
  height: 20px;
  border: none;
  background: rgba(0, 0, 0, 0.6);
  color: #aaa;
  border-radius: 50%;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  opacity: 0;
  transition: opacity 0.2s ease;
}

.texture-preview:hover .remove-btn {
  opacity: 1;
}

.remove-btn:hover {
  background: #d44;
  color: white;
}

.texture-settings {
  display: flex;
  flex-direction: column;
  gap: 8px;
  padding: 8px;
  background: #1a1a1a;
  border-radius: 4px;
}

.setting-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.setting-row label {
  width: 60px;
  font-size: 12px;
  color: #888;
}

.repeat-inputs,
.offset-inputs {
  display: flex;
  align-items: center;
  gap: 4px;
  flex: 1;
}

.separator {
  color: #555;
  font-size: 12px;
}
</style>
