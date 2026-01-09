<template>
  <div class="sph-section">
    <div class="section-header" @click="isExpanded = !isExpanded">
      <span class="expand-icon">{{ isExpanded ? '▼' : '▶' }}</span>
      <span class="section-title">Fluid Simulation (SPH)</span>
      <label class="enable-toggle" @click.stop>
        <input type="checkbox" v-model="config.enabled" @change="emitUpdate" />
        <span class="toggle-label">Enabled</span>
      </label>
    </div>

    <div v-if="isExpanded && config.enabled" class="section-content">
      <!-- GPU Status -->
      <div class="gpu-status" :class="{ available: gpuAvailable }">
        <span class="status-icon">{{ gpuAvailable ? '⚡' : '🐢' }}</span>
        <span class="status-text">{{ gpuAvailable ? 'GPU Accelerated' : 'CPU Fallback' }}</span>
      </div>

      <!-- Fluid Presets -->
      <div class="subsection">
        <div class="subsection-title">Fluid Presets</div>
        <div class="preset-grid">
          <button
            v-for="preset in presets"
            :key="preset.id"
            class="preset-btn"
            :class="{ active: activePreset === preset.id }"
            @click="applyPreset(preset.id)"
          >
            <span class="preset-icon">{{ preset.icon }}</span>
            <span class="preset-label">{{ preset.name }}</span>
          </button>
        </div>
      </div>

      <!-- Core Parameters -->
      <div class="subsection">
        <div class="subsection-title">Fluid Properties</div>

        <div class="param-row">
          <label>Smoothing Radius</label>
          <input
            type="range"
            min="10"
            max="100"
            step="1"
            v-model.number="config.smoothingRadius"
            @input="emitUpdate"
          />
          <span class="value">{{ config.smoothingRadius }}</span>
        </div>

        <div class="param-row">
          <label>Rest Density</label>
          <input
            type="range"
            min="1"
            max="5000"
            step="10"
            v-model.number="config.restDensity"
            @input="emitUpdate"
          />
          <span class="value">{{ config.restDensity }}</span>
        </div>

        <div class="param-row">
          <label>Gas Constant (Stiffness)</label>
          <input
            type="range"
            min="100"
            max="10000"
            step="100"
            v-model.number="config.gasConstant"
            @input="emitUpdate"
          />
          <span class="value">{{ config.gasConstant }}</span>
        </div>

        <div class="param-row">
          <label>Viscosity</label>
          <input
            type="range"
            min="0"
            max="20000"
            step="100"
            v-model.number="config.viscosity"
            @input="emitUpdate"
          />
          <span class="value">{{ config.viscosity }}</span>
        </div>
      </div>

      <!-- Surface Tension -->
      <div class="subsection">
        <div class="subsection-title">Surface Tension</div>

        <div class="param-row checkbox-row">
          <label>
            <input
              type="checkbox"
              v-model="config.enableSurfaceTension"
              @change="emitUpdate"
            />
            Enable Surface Tension (expensive)
          </label>
        </div>

        <div v-if="config.enableSurfaceTension" class="param-row">
          <label>Tension Coefficient</label>
          <input
            type="range"
            min="0"
            max="1"
            step="0.01"
            v-model.number="config.surfaceTension"
            @input="emitUpdate"
          />
          <span class="value">{{ config.surfaceTension.toFixed(3) }}</span>
        </div>
      </div>

      <!-- Gravity -->
      <div class="subsection">
        <div class="subsection-title">Gravity</div>

        <div class="param-row">
          <label>X</label>
          <input
            type="number"
            v-model.number="config.gravity.x"
            @input="emitUpdate"
            step="10"
          />
        </div>

        <div class="param-row">
          <label>Y</label>
          <input
            type="number"
            v-model.number="config.gravity.y"
            @input="emitUpdate"
            step="10"
          />
        </div>

        <div class="param-row">
          <label>Z</label>
          <input
            type="number"
            v-model.number="config.gravity.z"
            @input="emitUpdate"
            step="10"
          />
        </div>
      </div>

      <!-- Performance -->
      <div class="subsection">
        <div class="subsection-title">Performance</div>

        <div class="param-row">
          <label>Max Time Step</label>
          <input
            type="range"
            min="0.001"
            max="0.016"
            step="0.001"
            v-model.number="config.maxTimeStep"
            @input="emitUpdate"
          />
          <span class="value">{{ (config.maxTimeStep * 1000).toFixed(1) }}ms</span>
        </div>

        <div class="performance-note">
          <span class="note-icon">ℹ️</span>
          <span>Smaller timesteps = more stable but slower. SPH is computationally expensive. Reduce particle count for real-time playback.</span>
        </div>
      </div>

      <!-- Visual Guide -->
      <div class="subsection">
        <div class="subsection-title">Parameter Guide</div>
        <div class="guide-item">
          <span class="guide-label">Viscosity:</span>
          <span class="guide-range">Water ~100 | Honey ~5000 | Lava ~20000</span>
        </div>
        <div class="guide-item">
          <span class="guide-label">Rest Density:</span>
          <span class="guide-range">Air ~1 | Water ~1000 | Lava ~3000</span>
        </div>
        <div class="guide-item">
          <span class="guide-label">Gas Constant:</span>
          <span class="guide-range">Higher = stiffer, less compressible</span>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, watch } from "vue";

interface SPHConfig {
  enabled: boolean;
  smoothingRadius: number;
  restDensity: number;
  gasConstant: number;
  viscosity: number;
  surfaceTension: number;
  enableSurfaceTension: boolean;
  gravity: { x: number; y: number; z: number };
  maxTimeStep: number;
}

interface Props {
  modelValue: SPHConfig;
  gpuAvailable?: boolean;
}

interface Emits {
  (e: "update:modelValue", value: SPHConfig): void;
}

const props = withDefaults(defineProps<Props>(), {
  gpuAvailable: false,
});

const emit = defineEmits<Emits>();

const isExpanded = ref(true);
const activePreset = ref<string | null>(null);

const config = ref<SPHConfig>({ ...props.modelValue });

const presets = [
  { id: "water", name: "Water", icon: "💧" },
  { id: "honey", name: "Honey", icon: "🍯" },
  { id: "lava", name: "Lava", icon: "🌋" },
  { id: "gas", name: "Gas/Smoke", icon: "💨" },
  { id: "blood", name: "Blood", icon: "🩸" },
  { id: "slime", name: "Slime", icon: "🦠" },
];

watch(
  () => props.modelValue,
  (val) => {
    config.value = { ...val };
  },
  { deep: true }
);

function emitUpdate() {
  activePreset.value = null; // Clear preset indicator when manually editing
  emit("update:modelValue", { ...config.value });
}

function applyPreset(presetId: string) {
  activePreset.value = presetId;

  switch (presetId) {
    case "water":
      config.value = {
        ...config.value,
        smoothingRadius: 40,
        restDensity: 1000,
        gasConstant: 3000,
        viscosity: 100,
        surfaceTension: 0.0728,
        enableSurfaceTension: true,
        gravity: { x: 0, y: -980, z: 0 },
      };
      break;
    case "honey":
      config.value = {
        ...config.value,
        smoothingRadius: 50,
        restDensity: 1400,
        gasConstant: 2000,
        viscosity: 5000,
        surfaceTension: 0.05,
        enableSurfaceTension: true,
        gravity: { x: 0, y: -500, z: 0 },
      };
      break;
    case "lava":
      config.value = {
        ...config.value,
        smoothingRadius: 60,
        restDensity: 3000,
        gasConstant: 1500,
        viscosity: 20000,
        surfaceTension: 0.1,
        enableSurfaceTension: false,
        gravity: { x: 0, y: -200, z: 0 },
      };
      break;
    case "gas":
      config.value = {
        ...config.value,
        smoothingRadius: 80,
        restDensity: 1.2,
        gasConstant: 50,
        viscosity: 2,
        surfaceTension: 0,
        enableSurfaceTension: false,
        gravity: { x: 0, y: 100, z: 0 }, // Rises!
      };
      break;
    case "blood":
      config.value = {
        ...config.value,
        smoothingRadius: 45,
        restDensity: 1060,
        gasConstant: 2500,
        viscosity: 300,
        surfaceTension: 0.056,
        enableSurfaceTension: true,
        gravity: { x: 0, y: -980, z: 0 },
      };
      break;
    case "slime":
      config.value = {
        ...config.value,
        smoothingRadius: 55,
        restDensity: 1200,
        gasConstant: 1000,
        viscosity: 10000,
        surfaceTension: 0.2,
        enableSurfaceTension: true,
        gravity: { x: 0, y: -400, z: 0 },
      };
      break;
  }

  emit("update:modelValue", { ...config.value });
}
</script>

<style scoped>
.sph-section {
  background: var(--panel-bg, #1a1a2e);
  border-radius: 8px;
  margin-bottom: 8px;
  overflow: hidden;
}

.section-header {
  display: flex;
  align-items: center;
  padding: 10px 12px;
  background: linear-gradient(135deg, #1e3a5f, #2d4a6f);
  cursor: pointer;
  user-select: none;
}

.expand-icon {
  font-size: 10px;
  margin-right: 8px;
  color: var(--text-muted, #888);
}

.section-title {
  flex: 1;
  font-weight: 600;
  color: var(--text-primary, #fff);
}

.enable-toggle {
  display: flex;
  align-items: center;
  gap: 6px;
  font-size: 12px;
  color: var(--text-secondary, #aaa);
}

.section-content {
  padding: 12px;
}

.gpu-status {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  background: var(--warning-bg, #3a3020);
  border-radius: 6px;
  margin-bottom: 12px;
  font-size: 12px;
}

.gpu-status.available {
  background: var(--success-bg, #203a20);
}

.status-icon {
  font-size: 16px;
}

.status-text {
  color: var(--text-primary, #fff);
}

.subsection {
  margin-bottom: 16px;
  padding-bottom: 12px;
  border-bottom: 1px solid var(--border-color, #333);
}

.subsection:last-child {
  border-bottom: none;
  margin-bottom: 0;
}

.subsection-title {
  font-size: 11px;
  font-weight: 600;
  text-transform: uppercase;
  color: var(--text-muted, #888);
  margin-bottom: 10px;
}

.preset-grid {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 8px;
}

.preset-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 4px;
  padding: 10px 8px;
  background: var(--card-bg, #2a2a4a);
  border: 2px solid var(--border-color, #444);
  border-radius: 8px;
  cursor: pointer;
  transition: all 0.2s;
}

.preset-btn:hover {
  background: var(--card-hover, #3a3a5a);
  border-color: var(--accent, #3498db);
}

.preset-btn.active {
  background: var(--accent-bg, #1e3a5f);
  border-color: var(--accent, #3498db);
}

.preset-icon {
  font-size: 20px;
}

.preset-label {
  font-size: 10px;
  color: var(--text-secondary, #aaa);
}

.param-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.param-row label {
  min-width: 140px;
  font-size: 12px;
  color: var(--text-secondary, #aaa);
}

.param-row input[type="range"] {
  flex: 1;
  height: 4px;
}

.param-row input[type="number"] {
  width: 80px;
  padding: 4px 8px;
  background: var(--input-bg, #2a2a4a);
  border: 1px solid var(--border-color, #444);
  border-radius: 4px;
  color: var(--text-primary, #fff);
  font-size: 12px;
}

.param-row .value {
  min-width: 50px;
  font-size: 12px;
  color: var(--accent, #3498db);
  text-align: right;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 8px;
  min-width: auto;
  cursor: pointer;
}

.performance-note {
  display: flex;
  align-items: flex-start;
  gap: 8px;
  padding: 10px;
  background: var(--info-bg, #1a2a4a);
  border-radius: 6px;
  font-size: 11px;
  color: var(--text-secondary, #aaa);
  line-height: 1.4;
}

.note-icon {
  font-size: 14px;
}

.guide-item {
  display: flex;
  justify-content: space-between;
  font-size: 11px;
  margin-bottom: 6px;
  padding: 4px 0;
}

.guide-label {
  color: var(--text-secondary, #aaa);
}

.guide-range {
  color: var(--text-muted, #666);
  font-style: italic;
}
</style>
