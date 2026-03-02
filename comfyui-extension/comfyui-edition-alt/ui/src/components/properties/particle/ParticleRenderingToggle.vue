<template>
  <div class="rendering-toggle">
    <div class="toggle-header">
      <span class="toggle-label">Rendering</span>
      <div class="backend-indicator" :class="backendClass">
        <span class="backend-icon">{{ backendIcon }}</span>
        <span class="backend-name">{{ backendName }}</span>
      </div>
    </div>

    <div class="toggle-options">
      <button
        v-for="option in options"
        :key="option.value"
        class="toggle-btn"
        :class="{ active: store.preferences.renderingBackend === option.value }"
        :disabled="option.disabled"
        :title="option.tooltip"
        @click="setBackend(option.value)"
      >
        {{ option.icon }}
      </button>
    </div>

    <div class="quick-settings">
      <label class="mini-toggle" :class="{ disabled: !store.hasWebGPU }">
        <input
          type="checkbox"
          v-model="store.preferences.enableGPUCompute"
          :disabled="!store.hasWebGPU"
          @change="save"
        />
        <span>GPU Physics</span>
      </label>

      <button class="settings-btn" @click="$emit('openPreferences')" title="More settings">
        ⚙️
      </button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted } from "vue";
import { useParticlePreferencesStore, type RenderingBackend } from "../../../stores/particlePreferences";

const store = useParticlePreferencesStore();

const emit = defineEmits<{
  (e: "openPreferences"): void;
}>();

onMounted(() => {
  store.detectCapabilities();
});

const options = computed(() => [
  {
    value: "auto" as RenderingBackend,
    icon: "🔄",
    tooltip: "Auto (best available)",
    disabled: false,
  },
  {
    value: "webgpu" as RenderingBackend,
    icon: "⚡",
    tooltip: store.hasWebGPU ? "WebGPU" : "WebGPU (not available)",
    disabled: !store.hasWebGPU,
  },
  {
    value: "webgl2" as RenderingBackend,
    icon: "🎮",
    tooltip: store.hasWebGL2 ? "WebGL2" : "WebGL2 (not available)",
    disabled: !store.hasWebGL2,
  },
  {
    value: "cpu" as RenderingBackend,
    icon: "🖥️",
    tooltip: "Software (slowest)",
    disabled: false,
  },
]);

const backendClass = computed(() => {
  switch (store.activeBackend) {
    case "webgpu": return "backend-webgpu";
    case "webgl2": return "backend-webgl2";
    default: return "backend-cpu";
  }
});

const backendIcon = computed(() => {
  switch (store.activeBackend) {
    case "webgpu": return "⚡";
    case "webgl2": return "🎮";
    default: return "🖥️";
  }
});

const backendName = computed(() => {
  switch (store.activeBackend) {
    case "webgpu": return "WebGPU";
    case "webgl2": return "WebGL2";
    default: return "CPU";
  }
});

function setBackend(backend: RenderingBackend) {
  store.updatePreferences({ renderingBackend: backend });
}

function save() {
  store.updatePreferences(store.preferences);
}
</script>

<style scoped>
.rendering-toggle {
  background: var(--card-bg, #252540);
  border-radius: 8px;
  padding: 10px;
  margin-bottom: 8px;
}

.toggle-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 8px;
}

.toggle-label {
  font-size: 11px;
  font-weight: 600;
  text-transform: uppercase;
  color: var(--text-muted, #888);
}

.backend-indicator {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 3px 8px;
  border-radius: 4px;
  font-size: 10px;
}

.backend-webgpu {
  background: #1a4a3a;
  color: #4ade80;
}

.backend-webgl2 {
  background: #3a3a1a;
  color: #fbbf24;
}

.backend-cpu {
  background: #3a2a2a;
  color: #f87171;
}

.backend-icon {
  font-size: 12px;
}

.toggle-options {
  display: flex;
  gap: 4px;
  margin-bottom: 8px;
}

.toggle-btn {
  flex: 1;
  padding: 6px;
  background: var(--button-bg, #2a2a4a);
  border: 2px solid transparent;
  border-radius: 6px;
  cursor: pointer;
  font-size: 14px;
  transition: all 0.15s;
}

.toggle-btn:hover:not(:disabled) {
  background: var(--button-hover, #3a3a5a);
}

.toggle-btn.active {
  border-color: var(--accent, #6c5ce7);
  background: var(--accent-bg, #2a2a5a);
}

.toggle-btn:disabled {
  opacity: 0.3;
  cursor: not-allowed;
}

.quick-settings {
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.mini-toggle {
  display: flex;
  align-items: center;
  gap: 6px;
  font-size: 11px;
  color: var(--text-secondary, #aaa);
  cursor: pointer;
}

.mini-toggle.disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.mini-toggle input {
  margin: 0;
}

.settings-btn {
  padding: 4px 8px;
  background: transparent;
  border: none;
  cursor: pointer;
  font-size: 14px;
  opacity: 0.6;
  transition: opacity 0.15s;
}

.settings-btn:hover {
  opacity: 1;
}
</style>
