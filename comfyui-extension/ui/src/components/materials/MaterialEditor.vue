<template>
  <div class="material-editor">
    <!-- Header with preset selector -->
    <div class="editor-header">
      <div class="header-title">
        <i class="pi pi-palette"></i>
        <span>Material</span>
      </div>
      <select v-model="selectedPreset" @change="applyPreset" class="preset-select">
        <option value="">Custom</option>
        <option v-for="preset in presets" :key="preset.id" :value="preset.id">
          {{ preset.name }}
        </option>
      </select>
    </div>

    <!-- Basic Properties -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('basic')">
        <i :class="['pi', sections.basic ? 'pi-chevron-down' : 'pi-chevron-right']"></i>
        <span>Basic Properties</span>
      </div>
      <div v-show="sections.basic" class="section-content">
        <div class="property-group">
          <label>Base Color</label>
          <ColorPicker
            :modelValue="material.color"
            @update:modelValue="updateMaterial('color', $event)"
          />
        </div>

        <div class="property-group">
          <label>Metalness</label>
          <SliderInput
            :modelValue="material.metalness"
            @update:modelValue="updateMaterial('metalness', $event)"
            :min="0"
            :max="1"
            :step="0.01"
          />
        </div>

        <div class="property-group">
          <label>Roughness</label>
          <SliderInput
            :modelValue="material.roughness"
            @update:modelValue="updateMaterial('roughness', $event)"
            :min="0"
            :max="1"
            :step="0.01"
          />
        </div>

        <div class="property-group">
          <label>Opacity</label>
          <SliderInput
            :modelValue="material.opacity"
            @update:modelValue="updateMaterial('opacity', $event)"
            :min="0"
            :max="1"
            :step="0.01"
          />
        </div>

        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="material.transparent"
              @change="updateMaterial('transparent', ($event.target as HTMLInputElement).checked)"
            />
            Transparent
          </label>
        </div>
      </div>
    </div>

    <!-- Emissive -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('emissive')">
        <i :class="['pi', sections.emissive ? 'pi-chevron-down' : 'pi-chevron-right']"></i>
        <span>Emissive</span>
      </div>
      <div v-show="sections.emissive" class="section-content">
        <div class="property-group">
          <label>Emissive Color</label>
          <ColorPicker
            :modelValue="material.emissive"
            @update:modelValue="updateMaterial('emissive', $event)"
          />
        </div>

        <div class="property-group">
          <label>Intensity</label>
          <SliderInput
            :modelValue="material.emissiveIntensity"
            @update:modelValue="updateMaterial('emissiveIntensity', $event)"
            :min="0"
            :max="5"
            :step="0.1"
          />
        </div>
      </div>
    </div>

    <!-- Texture Maps -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('textures')">
        <i :class="['pi', sections.textures ? 'pi-chevron-down' : 'pi-chevron-right']"></i>
        <span>Texture Maps</span>
      </div>
      <div v-show="sections.textures" class="section-content">
        <div class="texture-grid">
          <TextureUpload
            mapType="albedo"
            :textureUrl="materialMapsAlbedo"
            @upload="(file: File, dataUrl: string) => uploadTexture('albedo', file, dataUrl)"
            @remove="removeTexture('albedo')"
          />

          <TextureUpload
            mapType="normal"
            :textureUrl="materialMapsNormal"
            :normalScale="material.normalScale"
            :showSettings="!!materialMapsNormal"
            @upload="(file: File, dataUrl: string) => uploadTexture('normal', file, dataUrl)"
            @remove="removeTexture('normal')"
            @update:normalScale="updateMaterial('normalScale', $event)"
          />

          <TextureUpload
            mapType="roughness"
            :textureUrl="materialMapsRoughness"
            @upload="(file: File, dataUrl: string) => uploadTexture('roughness', file, dataUrl)"
            @remove="removeTexture('roughness')"
          />

          <TextureUpload
            mapType="metalness"
            :textureUrl="materialMapsMetalness"
            @upload="(file: File, dataUrl: string) => uploadTexture('metalness', file, dataUrl)"
            @remove="removeTexture('metalness')"
          />

          <TextureUpload
            mapType="ao"
            :textureUrl="materialMapsAo"
            @upload="(file: File, dataUrl: string) => uploadTexture('ao', file, dataUrl)"
            @remove="removeTexture('ao')"
          />

          <TextureUpload
            mapType="emissive"
            :textureUrl="materialMapsEmissive"
            @upload="(file: File, dataUrl: string) => uploadTexture('emissive', file, dataUrl)"
            @remove="removeTexture('emissive')"
          />

          <TextureUpload
            mapType="height"
            :textureUrl="materialMapsHeight"
            @upload="(file: File, dataUrl: string) => uploadTexture('height', file, dataUrl)"
            @remove="removeTexture('height')"
          />

          <TextureUpload
            mapType="opacity"
            :textureUrl="materialMapsOpacity"
            @upload="(file: File, dataUrl: string) => uploadTexture('opacity', file, dataUrl)"
            @remove="removeTexture('opacity')"
          />
        </div>

        <!-- Global texture settings -->
        <div class="texture-global-settings" v-if="hasAnyTexture">
          <div class="setting-row">
            <label>UV Repeat</label>
            <div class="repeat-inputs">
              <ScrubableNumber
                v-model="materialTextureRepeatX"
                :min="0.01"
                :step="0.1"
              />
              <span class="separator">x</span>
              <ScrubableNumber
                v-model="materialTextureRepeatY"
                :min="0.01"
                :step="0.1"
              />
            </div>
          </div>
        </div>
      </div>
    </div>

    <!-- Environment -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('environment')">
        <i :class="['pi', sections.environment ? 'pi-chevron-down' : 'pi-chevron-right']"></i>
        <span>Environment</span>
      </div>
      <div v-show="sections.environment" class="section-content">
        <div class="property-group">
          <label>Environment Intensity</label>
          <SliderInput
            :modelValue="material.envMapIntensity"
            @update:modelValue="updateMaterial('envMapIntensity', $event)"
            :min="0"
            :max="3"
            :step="0.1"
          />
        </div>

        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="material.flatShading"
              @change="updateMaterial('flatShading', ($event.target as HTMLInputElement).checked)"
            />
            Flat Shading
          </label>
        </div>

        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="material.wireframe"
              @change="updateMaterial('wireframe', ($event.target as HTMLInputElement).checked)"
            />
            Wireframe
          </label>
        </div>

        <div class="property-row">
          <label>Side</label>
          <select
            :value="material.side"
            @change="updateMaterial('side', ($event.target as HTMLSelectElement).value as 'front' | 'back' | 'double')"
            class="type-select"
          >
            <option value="front">Front</option>
            <option value="back">Back</option>
            <option value="double">Double</option>
          </select>
        </div>
      </div>
    </div>

    <!-- Actions -->
    <div class="editor-actions">
      <button class="action-btn" @click="resetMaterial">
        <i class="pi pi-refresh"></i>
        Reset
      </button>
      <button class="action-btn primary" @click="saveMaterial">
        <i class="pi pi-save"></i>
        Save as Preset
      </button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, reactive, ref, watch } from "vue";
import type { TextureMapType } from "@/types/project";

// Material configuration interface
interface MaterialConfig {
  color: string;
  metalness: number;
  roughness: number;
  opacity: number;
  transparent: boolean;
  emissive: string;
  emissiveIntensity: number;
  normalScale: number;
  envMapIntensity: number;
  flatShading: boolean;
  wireframe: boolean;
  side: "front" | "back" | "double";
  maps: Partial<Record<TextureMapType, string>>;
  textureRepeat: { x: number; y: number };
}

interface MaterialPreset {
  id: string;
  name: string;
  config: Partial<MaterialConfig>;
}

const props = defineProps<{
  modelValue?: Partial<MaterialConfig>;
  layerId?: string;
  // Props from AssetsPanel
  materialId?: string;
  config?: Partial<MaterialConfig>;
}>();

const emit = defineEmits<{
  "update:modelValue": [value: MaterialConfig];
  "save-preset": [name: string, config: MaterialConfig];
  // Events for AssetsPanel
  update: [updates: Partial<MaterialConfig>];
  "texture-upload": [textureType: string, file: File];
}>();

// Default material values
const defaultMaterial: MaterialConfig = {
  color: "#ffffff",
  metalness: 0,
  roughness: 0.5,
  opacity: 1,
  transparent: false,
  emissive: "#000000",
  emissiveIntensity: 0,
  normalScale: 1,
  envMapIntensity: 1,
  flatShading: false,
  wireframe: false,
  side: "front",
  maps: {},
  textureRepeat: { x: 1, y: 1 },
};

// Material presets
const presets: MaterialPreset[] = [
  {
    id: "chrome",
    name: "Chrome",
    config: { color: "#ffffff", metalness: 1, roughness: 0.1 },
  },
  {
    id: "gold",
    name: "Gold",
    config: { color: "#ffd700", metalness: 1, roughness: 0.2 },
  },
  {
    id: "copper",
    name: "Copper",
    config: { color: "#b87333", metalness: 1, roughness: 0.3 },
  },
  {
    id: "plastic",
    name: "Plastic",
    config: { color: "#ffffff", metalness: 0, roughness: 0.4 },
  },
  {
    id: "rubber",
    name: "Rubber",
    config: { color: "#222222", metalness: 0, roughness: 0.9 },
  },
  {
    id: "glass",
    name: "Glass",
    config: {
      color: "#ffffff",
      metalness: 0,
      roughness: 0.1,
      opacity: 0.3,
      transparent: true,
    },
  },
  {
    id: "emissive",
    name: "Emissive",
    config: {
      color: "#ffffff",
      emissive: "#00aaff",
      emissiveIntensity: 2,
      metalness: 0,
      roughness: 0.5,
    },
  },
  {
    id: "matte",
    name: "Matte",
    config: { color: "#cccccc", metalness: 0, roughness: 1 },
  },
];

// Reactive state - merge from both modelValue and config props
const material = reactive<MaterialConfig>({
  ...defaultMaterial,
  ...props.modelValue,
  ...props.config,
});
const selectedPreset = ref("");
const sections = reactive({
  basic: true,
  emissive: false,
  textures: true,
  environment: false,
});

// Computed
const hasAnyTexture = computed(() => {
  return Object.values(material.maps).some((url) => !!url);
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
// Computed properties for texture map URLs
const materialMapsAlbedo = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "albedo" in maps && typeof maps.albedo === "string") ? maps.albedo : undefined;
});

const materialMapsNormal = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "normal" in maps && typeof maps.normal === "string") ? maps.normal : undefined;
});

const materialMapsRoughness = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "roughness" in maps && typeof maps.roughness === "string") ? maps.roughness : undefined;
});

const materialMapsMetalness = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "metalness" in maps && typeof maps.metalness === "string") ? maps.metalness : undefined;
});

const materialMapsAo = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "ao" in maps && typeof maps.ao === "string") ? maps.ao : undefined;
});

const materialMapsEmissive = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "emissive" in maps && typeof maps.emissive === "string") ? maps.emissive : undefined;
});

const materialMapsHeight = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "height" in maps && typeof maps.height === "string") ? maps.height : undefined;
});

const materialMapsOpacity = computed(() => {
  const maps = (material != null && typeof material === "object" && "maps" in material && material.maps != null && typeof material.maps === "object") ? material.maps : undefined;
  return (maps != null && typeof maps === "object" && "opacity" in maps && typeof maps.opacity === "string") ? maps.opacity : undefined;
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
// Computed properties for optional textureRepeat properties
const materialTextureRepeatX = computed({
  get: () => {
    const repeat = material.textureRepeat;
    return (repeat !== null && repeat !== undefined && typeof repeat === "object" && "x" in repeat && typeof repeat.x === "number" && Number.isFinite(repeat.x)) ? repeat.x : 1;
  },
  set: (value: number) => {
    if (!material.textureRepeat) {
      material.textureRepeat = { x: value, y: materialTextureRepeatY.value };
    } else {
      material.textureRepeat.x = value;
    }
    emitUpdate();
  },
});
const materialTextureRepeatY = computed({
  get: () => {
    const repeat = material.textureRepeat;
    return (repeat !== null && repeat !== undefined && typeof repeat === "object" && "y" in repeat && typeof repeat.y === "number" && Number.isFinite(repeat.y)) ? repeat.y : 1;
  },
  set: (value: number) => {
    if (!material.textureRepeat) {
      material.textureRepeat = { x: materialTextureRepeatX.value, y: value };
    } else {
      material.textureRepeat.y = value;
    }
    emitUpdate();
  },
});

// Watch for external changes
watch(
  () => props.modelValue,
  (newVal) => {
    if (newVal) {
      Object.assign(material, { ...defaultMaterial, ...newVal });
    }
  },
  { deep: true },
);

watch(
  () => props.config,
  (newVal) => {
    if (newVal) {
      Object.assign(material, { ...defaultMaterial, ...newVal });
    }
  },
  { deep: true },
);

// Methods
function toggleSection(section: keyof typeof sections) {
  sections[section] = !sections[section];
}

function updateMaterial<K extends keyof MaterialConfig>(
  key: K,
  value: MaterialConfig[K],
) {
  material[key] = value;
  selectedPreset.value = ""; // Clear preset when manually editing
  emitUpdate();
}

function updateTextureRepeat(axis: "x" | "y", value: number) {
  material.textureRepeat[axis] = value;
  emitUpdate();
}

function uploadTexture(mapType: TextureMapType, file: File, dataUrl: string) {
  material.maps[mapType] = dataUrl;
  emitUpdate();
  emit("texture-upload", mapType, file);
}

function removeTexture(mapType: TextureMapType) {
  delete material.maps[mapType];
  emitUpdate();
}

function applyPreset() {
  if (!selectedPreset.value) return;

  const preset = presets.find((p) => p.id === selectedPreset.value);
  if (preset) {
    Object.assign(material, { ...defaultMaterial, ...preset.config });
    emitUpdate();
  }
}

function resetMaterial() {
  Object.assign(material, defaultMaterial);
  selectedPreset.value = "";
  emitUpdate();
}

function saveMaterial() {
  const name = prompt("Enter preset name:");
  if (name) {
    emit("save-preset", name, { ...material });
  }
}

function emitUpdate() {
  emit("update:modelValue", { ...material });
  emit("update", { ...material });
}
</script>

<style scoped>
.material-editor {
  display: flex;
  flex-direction: column;
  background: #1e1e1e;
  border-radius: 4px;
  overflow: hidden;
}

.editor-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 10px 12px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.header-title {
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 12px;
  font-weight: 600;
  color: #ccc;
}

.header-title i {
  color: #4a90d9;
}

.preset-select {
  background: #111;
  border: 1px solid #333;
  color: #ccc;
  padding: 4px 8px;
  border-radius: 3px;
  font-size: 13px;
  min-width: 100px;
}

.property-section {
  border-bottom: 1px solid #2a2a2a;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  background: #222;
  cursor: pointer;
  user-select: none;
  font-size: 13px;
  color: #aaa;
}

.section-header:hover {
  background: #282828;
}

.section-header i {
  font-size: 12px;
  color: #666;
}

.section-content {
  padding: 12px;
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.property-group {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.property-group label {
  color: #888;
  font-size: 12px;
}

.property-row {
  display: flex;
  align-items: center;
  justify-content: space-between;
}

.property-row label {
  color: #888;
  font-size: 13px;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  color: #ccc;
  font-size: 13px;
  cursor: pointer;
}

.type-select {
  background: #111;
  border: 1px solid #333;
  color: #ccc;
  padding: 4px 8px;
  border-radius: 3px;
  font-size: 13px;
}

.texture-grid {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 8px;
}

.texture-global-settings {
  margin-top: 8px;
  padding-top: 12px;
  border-top: 1px solid #333;
}

.setting-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.setting-row label {
  width: 70px;
  font-size: 12px;
  color: #888;
}

.repeat-inputs {
  display: flex;
  align-items: center;
  gap: 4px;
  flex: 1;
}

.separator {
  color: #555;
  font-size: 12px;
}

.editor-actions {
  display: flex;
  gap: 8px;
  padding: 12px;
  background: #1a1a1a;
  border-top: 1px solid #333;
}

.action-btn {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  padding: 8px 12px;
  background: #333;
  border: 1px solid #444;
  color: #ccc;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
  transition: all 0.2s ease;
}

.action-btn:hover {
  background: #444;
}

.action-btn.primary {
  background: #4a90d9;
  border-color: #5a9fe9;
  color: white;
}

.action-btn.primary:hover {
  background: #5a9fe9;
}
</style>
