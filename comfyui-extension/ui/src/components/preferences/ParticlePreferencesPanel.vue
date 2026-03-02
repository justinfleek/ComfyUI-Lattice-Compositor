<template>
  <div class="particle-preferences-panel">
    <div class="panel-header">
      <h3>Particle System Settings</h3>
      <p class="subtitle">Configure rendering and simulation behavior</p>
    </div>

    <!-- GPU Status -->
    <div class="status-card" :class="statusClass">
      <div class="status-icon">{{ statusIcon }}</div>
      <div class="status-info">
        <div class="status-title">{{ store.backendDescription }}</div>
        <div class="status-subtitle">
          <span v-if="store.hasWebGPU" class="badge success">WebGPU ✓</span>
          <span v-else class="badge warning">WebGPU ✗</span>
          <span v-if="store.hasWebGL2" class="badge success">WebGL2 ✓</span>
          <span v-else class="badge error">WebGL2 ✗</span>
        </div>
      </div>
    </div>

    <!-- Rendering Backend -->
    <div class="section">
      <div class="section-title">Rendering Backend</div>
      <div class="option-grid">
        <button
          v-for="option in backendOptions"
          :key="option.value"
          class="option-btn"
          :class="{ active: store.preferences.renderingBackend === option.value, disabled: option.disabled }"
          :disabled="option.disabled"
          @click="setBackend(option.value)"
        >
          <span class="option-icon">{{ option.icon }}</span>
          <span class="option-label">{{ option.label }}</span>
          <span v-if="option.recommended" class="recommended">Recommended</span>
        </button>
      </div>
    </div>

    <!-- Simulation Mode -->
    <div class="section">
      <div class="section-title">Simulation Mode</div>
      <div class="radio-group">
        <label class="radio-option">
          <input
            type="radio"
            name="simMode"
            value="realtime"
            v-model="store.preferences.simulationMode"
            @change="savePreferences"
          />
          <div class="radio-content">
            <span class="radio-title">Real-time</span>
            <span class="radio-desc">Simulate during playback. Fast but less precise scrubbing.</span>
          </div>
        </label>

        <label class="radio-option">
          <input
            type="radio"
            name="simMode"
            value="cached"
            v-model="store.preferences.simulationMode"
            @change="savePreferences"
          />
          <div class="radio-content">
            <span class="radio-title">Cached</span>
            <span class="radio-desc">Cache checkpoints for smooth timeline scrubbing. Recommended.</span>
          </div>
        </label>

        <label class="radio-option">
          <input
            type="radio"
            name="simMode"
            value="baked"
            v-model="store.preferences.simulationMode"
            @change="savePreferences"
          />
          <div class="radio-content">
            <span class="radio-title">Baked</span>
            <span class="radio-desc">Pre-calculate all frames. Most accurate, uses more memory.</span>
          </div>
        </label>
      </div>
    </div>

    <!-- Performance -->
    <div class="section">
      <div class="section-title">Performance</div>

      <div class="param-row">
        <label>Max Particles Per Layer</label>
        <input
          type="range"
          min="1000"
          max="500000"
          step="1000"
          v-model.number="store.preferences.maxParticlesPerLayer"
          @input="savePreferences"
        />
        <span class="value">{{ formatNumber(store.preferences.maxParticlesPerLayer) }}</span>
      </div>

      <div class="param-row">
        <label>Target FPS</label>
        <select v-model.number="store.preferences.targetFPS" @change="savePreferences">
          <option :value="30">30 FPS (Better battery)</option>
          <option :value="60">60 FPS (Smoother)</option>
        </select>
      </div>

      <div class="param-row">
        <label>Cache Memory Limit</label>
        <input
          type="range"
          min="128"
          max="2048"
          step="128"
          v-model.number="store.preferences.maxCacheMemoryMB"
          @input="savePreferences"
        />
        <span class="value">{{ store.preferences.maxCacheMemoryMB }} MB</span>
      </div>

      <div class="checkbox-row">
        <label>
          <input
            type="checkbox"
            v-model="store.preferences.enableGPUCompute"
            @change="savePreferences"
            :disabled="!store.hasWebGPU"
          />
          <span>Use GPU for physics (WebGPU only)</span>
        </label>
      </div>
    </div>

    <!-- Quality -->
    <div class="section">
      <div class="section-title">Quality</div>

      <div class="checkbox-row">
        <label>
          <input type="checkbox" v-model="store.preferences.enableMotionBlur" @change="savePreferences" />
          <span>Motion Blur</span>
        </label>
      </div>

      <div class="checkbox-row">
        <label>
          <input type="checkbox" v-model="store.preferences.enableSoftParticles" @change="savePreferences" />
          <span>Soft Particles (depth fade)</span>
        </label>
      </div>

      <div class="checkbox-row">
        <label>
          <input type="checkbox" v-model="store.preferences.enableShadows" @change="savePreferences" />
          <span>Particle Shadows</span>
        </label>
      </div>

      <div class="checkbox-row">
        <label>
          <input type="checkbox" v-model="store.preferences.lodEnabled" @change="savePreferences" />
          <span>Level of Detail (LOD)</span>
        </label>
      </div>
    </div>

    <!-- Presets -->
    <div class="section">
      <div class="section-title">Quick Presets</div>
      <div class="preset-buttons">
        <button class="preset-btn" @click="store.applyLowEndPreset()">
          <span class="preset-icon">🐢</span>
          <span>Low-End</span>
        </button>
        <button class="preset-btn" @click="store.applyHighEndPreset()">
          <span class="preset-icon">🚀</span>
          <span>High-End</span>
        </button>
        <button class="preset-btn danger" @click="store.resetToDefaults()">
          <span class="preset-icon">↺</span>
          <span>Reset</span>
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted } from "vue";
import { useParticlePreferencesStore, type RenderingBackend } from "../../stores/particlePreferences";

const store = useParticlePreferencesStore();

onMounted(() => {
  store.detectCapabilities();
});

const backendOptions = computed(() => [
  {
    value: "auto" as RenderingBackend,
    label: "Auto",
    icon: "🔄",
    recommended: true,
    disabled: false,
  },
  {
    value: "webgpu" as RenderingBackend,
    label: "WebGPU",
    icon: "⚡",
    recommended: false,
    disabled: !store.hasWebGPU,
  },
  {
    value: "webgl2" as RenderingBackend,
    label: "WebGL2",
    icon: "🎮",
    recommended: false,
    disabled: !store.hasWebGL2,
  },
  {
    value: "cpu" as RenderingBackend,
    label: "Software",
    icon: "🖥️",
    recommended: false,
    disabled: false,
  },
]);

const statusClass = computed(() => {
  if (store.activeBackend === "webgpu") return "status-excellent";
  if (store.activeBackend === "webgl2") return "status-good";
  return "status-fallback";
});

const statusIcon = computed(() => {
  if (store.activeBackend === "webgpu") return "⚡";
  if (store.activeBackend === "webgl2") return "🎮";
  return "🖥️";
});

function setBackend(backend: RenderingBackend) {
  store.updatePreferences({ renderingBackend: backend });
}

function savePreferences() {
  store.updatePreferences(store.preferences);
}

function formatNumber(n: number): string {
  if (n >= 1000000) return `${(n / 1000000).toFixed(1)}M`;
  if (n >= 1000) return `${(n / 1000).toFixed(0)}K`;
  return n.toString();
}
</script>

<style scoped>
.particle-preferences-panel {
  padding: 20px;
  background: var(--panel-bg, #1a1a2e);
  color: var(--text-primary, #fff);
  font-family: system-ui, -apple-system, sans-serif;
}

.panel-header {
  margin-bottom: 24px;
}

.panel-header h3 {
  margin: 0 0 4px 0;
  font-size: 18px;
  font-weight: 600;
}

.subtitle {
  margin: 0;
  font-size: 13px;
  color: var(--text-muted, #888);
}

/* Status Card */
.status-card {
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 16px;
  border-radius: 12px;
  margin-bottom: 24px;
}

.status-excellent {
  background: linear-gradient(135deg, #1a4a3a, #0d2a20);
  border: 1px solid #2a6a4a;
}

.status-good {
  background: linear-gradient(135deg, #3a3a1a, #2a2a0d);
  border: 1px solid #6a6a2a;
}

.status-fallback {
  background: linear-gradient(135deg, #3a2a2a, #2a1a1a);
  border: 1px solid #6a3a3a;
}

.status-icon {
  font-size: 32px;
}

.status-title {
  font-size: 14px;
  font-weight: 600;
  margin-bottom: 4px;
}

.status-subtitle {
  display: flex;
  gap: 8px;
}

.badge {
  font-size: 10px;
  padding: 2px 6px;
  border-radius: 4px;
}

.badge.success {
  background: #1a4a2a;
  color: #4ade80;
}

.badge.warning {
  background: #4a3a1a;
  color: #fbbf24;
}

.badge.error {
  background: #4a1a1a;
  color: #f87171;
}

/* Sections */
.section {
  margin-bottom: 24px;
  padding-bottom: 20px;
  border-bottom: 1px solid var(--border-color, #333);
}

.section:last-child {
  border-bottom: none;
  margin-bottom: 0;
}

.section-title {
  font-size: 12px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--text-muted, #888);
  margin-bottom: 12px;
}

/* Option Grid */
.option-grid {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 8px;
}

.option-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 4px;
  padding: 12px;
  background: var(--button-bg, #2a2a4a);
  border: 2px solid transparent;
  border-radius: 8px;
  cursor: pointer;
  transition: all 0.2s;
  position: relative;
}

.option-btn:hover:not(.disabled) {
  background: var(--button-hover, #3a3a5a);
}

.option-btn.active {
  border-color: var(--accent, #6c5ce7);
  background: var(--accent-bg, #2a2a5a);
}

.option-btn.disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.option-icon {
  font-size: 24px;
}

.option-label {
  font-size: 12px;
  color: var(--text-primary, #fff);
}

.recommended {
  position: absolute;
  top: 4px;
  right: 4px;
  font-size: 8px;
  padding: 2px 4px;
  background: var(--accent, #6c5ce7);
  border-radius: 3px;
  color: white;
}

/* Radio Group */
.radio-group {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.radio-option {
  display: flex;
  align-items: flex-start;
  gap: 12px;
  padding: 12px;
  background: var(--card-bg, #2a2a4a);
  border-radius: 8px;
  cursor: pointer;
  transition: background 0.2s;
}

.radio-option:hover {
  background: var(--card-hover, #3a3a5a);
}

.radio-option input {
  margin-top: 4px;
}

.radio-content {
  display: flex;
  flex-direction: column;
}

.radio-title {
  font-size: 13px;
  font-weight: 500;
  color: var(--text-primary, #fff);
}

.radio-desc {
  font-size: 11px;
  color: var(--text-muted, #888);
  margin-top: 2px;
}

/* Param Rows */
.param-row {
  display: flex;
  align-items: center;
  gap: 12px;
  margin-bottom: 12px;
}

.param-row label {
  min-width: 160px;
  font-size: 13px;
  color: var(--text-secondary, #aaa);
}

.param-row input[type="range"] {
  flex: 1;
  height: 4px;
}

.param-row select {
  flex: 1;
  padding: 8px;
  background: var(--input-bg, #2a2a4a);
  border: 1px solid var(--border-color, #444);
  border-radius: 6px;
  color: var(--text-primary, #fff);
  font-size: 13px;
}

.param-row .value {
  min-width: 60px;
  font-size: 13px;
  color: var(--accent, #6c5ce7);
  text-align: right;
  font-weight: 500;
}

/* Checkbox Rows */
.checkbox-row {
  margin-bottom: 8px;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 10px;
  font-size: 13px;
  color: var(--text-secondary, #aaa);
  cursor: pointer;
}

.checkbox-row label:hover {
  color: var(--text-primary, #fff);
}

/* Preset Buttons */
.preset-buttons {
  display: flex;
  gap: 8px;
}

.preset-btn {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
  padding: 10px;
  background: var(--button-bg, #2a2a4a);
  border: 1px solid var(--border-color, #444);
  border-radius: 6px;
  color: var(--text-primary, #fff);
  font-size: 12px;
  cursor: pointer;
  transition: all 0.2s;
}

.preset-btn:hover {
  background: var(--button-hover, #3a3a5a);
  border-color: var(--accent, #6c5ce7);
}

.preset-btn.danger {
  background: var(--danger-bg, #3a2020);
  border-color: var(--danger-border, #5a3030);
}

.preset-btn.danger:hover {
  background: var(--danger-hover, #4a2525);
}

.preset-icon {
  font-size: 16px;
}
</style>
