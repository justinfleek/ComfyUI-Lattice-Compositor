<template>
  <div class="environment-settings">
    <div class="settings-header">
      <div class="header-title">
        <i class="pi pi-globe"></i>
        <span>Environment</span>
      </div>
      <label class="enable-toggle">
        <input
          type="checkbox"
          :checked="config.enabled"
          @change="updateConfig('enabled', ($event.target as HTMLInputElement).checked)"
        />
        <span class="toggle-label">Enabled</span>
      </label>
    </div>

    <div class="settings-content" v-if="config.enabled">
      <!-- HDRI Upload -->
      <div class="setting-group">
        <label class="group-label">Environment Map (HDRI)</label>
        <AssetUploader
          assetType="hdri"
          label="Upload HDRI"
          @upload="onHdriUpload"
          @remove="onHdriRemove"
        />
      </div>

      <!-- Quick presets -->
      <div class="setting-group" v-if="!config.url">
        <label class="group-label">Quick Presets</label>
        <div class="preset-grid">
          <button
            v-for="preset in presets"
            :key="preset.id"
            class="preset-btn"
            :class="{ active: selectedPreset === preset.id }"
            @click="applyPreset(preset)"
          >
            <div class="preset-preview" :style="{ background: preset.color }"></div>
            <span>{{ preset.name }}</span>
          </button>
        </div>
      </div>

      <!-- Intensity -->
      <div class="setting-group">
        <label>Intensity</label>
        <SliderInput
          :modelValue="config.intensity"
          @update:modelValue="updateConfig('intensity', $event)"
          :min="0"
          :max="3"
          :step="0.1"
        />
      </div>

      <!-- Rotation -->
      <div class="setting-group">
        <label>Rotation</label>
        <div class="rotation-control">
          <AngleDial
            :modelValue="config.rotation"
            @update:modelValue="updateConfig('rotation', $event)"
            :size="36"
          />
          <ScrubableNumber
            :modelValue="config.rotation"
            @update:modelValue="updateConfig('rotation', $event)"
            unit="°"
          />
        </div>
      </div>

      <!-- Background settings -->
      <div class="setting-group">
        <label class="checkbox-label">
          <input
            type="checkbox"
            :checked="config.useAsBackground"
            @change="updateConfig('useAsBackground', ($event.target as HTMLInputElement).checked)"
          />
          Use as Background
        </label>
      </div>

      <div class="setting-group" v-if="config.useAsBackground">
        <label>Background Blur</label>
        <SliderInput
          :modelValue="config.backgroundBlur"
          @update:modelValue="updateConfig('backgroundBlur', $event)"
          :min="0"
          :max="1"
          :step="0.05"
        />
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { reactive, ref, watch } from "vue";
import type { EnvironmentMapConfig } from "@/engine/core/SceneManager";

interface EnvironmentPreset {
  id: string;
  name: string;
  color: string;
  url?: string;
}

const props = defineProps<{
  modelValue?: Partial<EnvironmentMapConfig>;
  // Props from AssetsPanel
  config?: Partial<EnvironmentMapConfig>;
}>();

const emit = defineEmits<{
  "update:modelValue": [value: EnvironmentMapConfig];
  "load-hdri": [url: string];
  // Events for AssetsPanel
  update: [settings: Partial<EnvironmentMapConfig>];
  load: [file: File];
  clear: [];
}>();

// Default config
const defaultConfig: EnvironmentMapConfig = {
  enabled: false,
  intensity: 1,
  rotation: 0,
  backgroundBlur: 0,
  useAsBackground: true,
  toneMapping: true,
};

const configState = reactive<EnvironmentMapConfig>({
  ...defaultConfig,
  ...props.modelValue,
  ...props.config,
});
const selectedPreset = ref<string | null>(null);

// Alias for template compatibility (avoiding conflict with props.config)
const _config = configState;

// Built-in presets (these would normally link to actual HDRI files)
const _presets: EnvironmentPreset[] = [
  {
    id: "studio",
    name: "Studio",
    color: "linear-gradient(135deg, #2a2a2a 0%, #1a1a1a 100%)",
  },
  {
    id: "outdoor",
    name: "Outdoor",
    color: "linear-gradient(135deg, #87CEEB 0%, #98D8C8 100%)",
  },
  {
    id: "sunset",
    name: "Sunset",
    color: "linear-gradient(135deg, #ff6b6b 0%, #ffa600 100%)",
  },
  {
    id: "night",
    name: "Night",
    color: "linear-gradient(135deg, #1a1a3e 0%, #0d0d1a 100%)",
  },
];

// Watch for external changes
watch(
  () => props.modelValue,
  (newVal) => {
    if (newVal) {
      Object.assign(configState, { ...defaultConfig, ...newVal });
    }
  },
  { deep: true },
);

watch(
  () => props.config,
  (newVal) => {
    if (newVal) {
      Object.assign(configState, { ...defaultConfig, ...newVal });
    }
  },
  { deep: true },
);

// Methods
function _updateConfig<K extends keyof EnvironmentMapConfig>(
  key: K,
  value: EnvironmentMapConfig[K],
) {
  configState[key] = value;
  emitUpdate();
}

function _onHdriUpload(file: File, dataUrl?: string) {
  if (dataUrl) {
    configState.url = dataUrl;
    selectedPreset.value = null;
    emitUpdate();
    emit("load-hdri", dataUrl);
    emit("load", file);
  }
}

function _onHdriRemove() {
  configState.url = undefined;
  emitUpdate();
  emit("clear");
}

function _applyPreset(preset: EnvironmentPreset) {
  selectedPreset.value = preset.id;
  if (preset.url) {
    configState.url = preset.url;
    emit("load-hdri", preset.url);
  }
  emitUpdate();
}

function emitUpdate() {
  emit("update:modelValue", { ...configState });
  emit("update", { ...configState });
}
</script>

<style scoped>
.environment-settings {
  display: flex;
  flex-direction: column;
  background: #1e1e1e;
  border-radius: 4px;
  overflow: hidden;
}

.settings-header {
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

.enable-toggle {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
}

.toggle-label {
  font-size: 13px;
  color: #888;
}

.settings-content {
  padding: 12px;
  display: flex;
  flex-direction: column;
  gap: 16px;
}

.setting-group {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.setting-group > label,
.group-label {
  font-size: 12px;
  color: #888;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.preset-grid {
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  gap: 6px;
}

.preset-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 4px;
  padding: 8px 4px;
  background: #252525;
  border: 1px solid #333;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.2s ease;
}

.preset-btn:hover {
  border-color: #555;
  background: #2a2a2a;
}

.preset-btn.active {
  border-color: #4a90d9;
  background: rgba(74, 144, 217, 0.1);
}

.preset-preview {
  width: 32px;
  height: 32px;
  border-radius: 4px;
}

.preset-btn span {
  font-size: 11px;
  color: #888;
}

.rotation-control {
  display: flex;
  align-items: center;
  gap: 8px;
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 6px;
  font-size: 13px;
  color: #ccc;
  cursor: pointer;
}
</style>
