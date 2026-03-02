<template>
  <div class="spring-section">
    <div class="section-header" @click="isExpanded = !isExpanded">
      <span class="expand-icon">{{ isExpanded ? '▼' : '▶' }}</span>
      <span class="section-title">Spring/Soft Body Physics</span>
      <label class="enable-toggle" @click.stop>
        <input type="checkbox" v-model="config.enabled" @change="emitUpdate" />
        <span class="toggle-label">Enabled</span>
      </label>
    </div>

    <div v-if="isExpanded && config.enabled" class="section-content">
      <!-- Global Settings -->
      <div class="subsection">
        <div class="subsection-title">Global Settings</div>

        <div class="param-row">
          <label>Global Stiffness</label>
          <input
            type="range"
            min="1"
            max="500"
            step="1"
            v-model.number="config.globalStiffness"
            @input="emitUpdate"
          />
          <span class="value">{{ config.globalStiffness }}</span>
        </div>

        <div class="param-row">
          <label>Global Damping</label>
          <input
            type="range"
            min="0"
            max="50"
            step="0.5"
            v-model.number="config.globalDamping"
            @input="emitUpdate"
          />
          <span class="value">{{ config.globalDamping }}</span>
        </div>

        <div class="param-row">
          <label>Solver Iterations</label>
          <input
            type="range"
            min="1"
            max="16"
            step="1"
            v-model.number="config.solverIterations"
            @input="emitUpdate"
          />
          <span class="value">{{ config.solverIterations }}</span>
        </div>

        <div class="param-row checkbox-row">
          <label>
            <input type="checkbox" v-model="config.useVerlet" @change="emitUpdate" />
            Use Verlet Integration (more stable)
          </label>
        </div>

        <div class="param-row checkbox-row">
          <label>
            <input type="checkbox" v-model="config.enableBreaking" @change="emitUpdate" />
            Enable Spring Breaking
          </label>
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

        <div class="preset-buttons">
          <button @click="setGravityPreset('earth')">Earth</button>
          <button @click="setGravityPreset('moon')">Moon</button>
          <button @click="setGravityPreset('zero')">Zero-G</button>
          <button @click="setGravityPreset('inverted')">Inverted</button>
        </div>
      </div>

      <!-- Presets -->
      <div class="subsection">
        <div class="subsection-title">Quick Setup</div>

        <div class="preset-grid">
          <button class="preset-btn" @click="createClothPreset">
            <span class="preset-icon">🏳️</span>
            <span class="preset-label">Cloth</span>
          </button>
          <button class="preset-btn" @click="createRopePreset">
            <span class="preset-icon">🪢</span>
            <span class="preset-label">Rope</span>
          </button>
          <button class="preset-btn" @click="createSoftBodyPreset">
            <span class="preset-icon">🧊</span>
            <span class="preset-label">Soft Body</span>
          </button>
          <button class="preset-btn" @click="createChainPreset">
            <span class="preset-icon">⛓️</span>
            <span class="preset-label">Chain</span>
          </button>
        </div>
      </div>

      <!-- Spring Info -->
      <div class="subsection">
        <div class="subsection-title">Current Springs</div>
        <div class="info-row">
          <span>Active Springs:</span>
          <span class="value">{{ springCount }}</span>
        </div>
        <div class="info-row">
          <span>Pinned Particles:</span>
          <span class="value">{{ pinCount }}</span>
        </div>
        <button class="danger-btn" @click="clearAllSprings">Clear All Springs</button>
      </div>

      <!-- Manual Spring Creation -->
      <div class="subsection collapsible">
        <div class="subsection-title" @click="showManual = !showManual">
          {{ showManual ? '▼' : '▶' }} Manual Spring Creation
        </div>
        <div v-if="showManual" class="manual-spring">
          <div class="param-row">
            <label>Particle A</label>
            <input type="number" v-model.number="newSpring.particleA" min="0" />
          </div>
          <div class="param-row">
            <label>Particle B</label>
            <input type="number" v-model.number="newSpring.particleB" min="0" />
          </div>
          <div class="param-row">
            <label>Rest Length</label>
            <input type="number" v-model.number="newSpring.restLength" min="0.001" step="1" />
          </div>
          <div class="param-row">
            <label>Stiffness</label>
            <input type="number" v-model.number="newSpring.stiffness" min="0" step="10" />
          </div>
          <div class="param-row">
            <label>Break Threshold</label>
            <input type="number" v-model.number="newSpring.breakThreshold" min="0" max="10" step="0.1" />
            <span class="hint">(0 = unbreakable)</span>
          </div>
          <button @click="addManualSpring">Add Spring</button>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch } from "vue";

interface SpringConfig {
  enabled: boolean;
  globalStiffness: number;
  globalDamping: number;
  solverIterations: number;
  useVerlet: boolean;
  enableBreaking: boolean;
  gravity: { x: number; y: number; z: number };
}

interface Props {
  modelValue: SpringConfig;
  springCount?: number;
  pinCount?: number;
}

interface Emits {
  (e: "update:modelValue", value: SpringConfig): void;
  (e: "createCloth", params: { width: number; height: number; spacing: number; stiffness: number }): void;
  (e: "createRope", params: { length: number; segments: number; stiffness: number }): void;
  (e: "createSoftBody", params: { width: number; height: number; depth: number; spacing: number; stiffness: number }): void;
  (e: "createChain", params: { length: number; stiffness: number }): void;
  (e: "addSpring", params: { particleA: number; particleB: number; restLength: number; stiffness: number; breakThreshold: number }): void;
  (e: "clearSprings"): void;
}

const props = withDefaults(defineProps<Props>(), {
  springCount: 0,
  pinCount: 0,
});

const emit = defineEmits<Emits>();

const isExpanded = ref(true);
const showManual = ref(false);

const config = ref<SpringConfig>({ ...props.modelValue });

const newSpring = ref({
  particleA: 0,
  particleB: 1,
  restLength: 20,
  stiffness: 100,
  breakThreshold: 0,
});

watch(
  () => props.modelValue,
  (val) => {
    config.value = { ...val };
  },
  { deep: true }
);

function emitUpdate() {
  emit("update:modelValue", { ...config.value });
}

function setGravityPreset(preset: "earth" | "moon" | "zero" | "inverted") {
  switch (preset) {
    case "earth":
      config.value.gravity = { x: 0, y: -980, z: 0 };
      break;
    case "moon":
      config.value.gravity = { x: 0, y: -162, z: 0 };
      break;
    case "zero":
      config.value.gravity = { x: 0, y: 0, z: 0 };
      break;
    case "inverted":
      config.value.gravity = { x: 0, y: 980, z: 0 };
      break;
  }
  emitUpdate();
}

function createClothPreset() {
  emit("createCloth", {
    width: 20,
    height: 20,
    spacing: 15,
    stiffness: config.value.globalStiffness,
  });
}

function createRopePreset() {
  emit("createRope", {
    length: 500,
    segments: 25,
    stiffness: config.value.globalStiffness,
  });
}

function createSoftBodyPreset() {
  emit("createSoftBody", {
    width: 5,
    height: 5,
    depth: 5,
    spacing: 20,
    stiffness: config.value.globalStiffness,
  });
}

function createChainPreset() {
  emit("createChain", {
    length: 10,
    stiffness: config.value.globalStiffness * 2,
  });
}

function addManualSpring() {
  emit("addSpring", { ...newSpring.value });
}

function clearAllSprings() {
  if (confirm("Remove all springs? This cannot be undone.")) {
    emit("clearSprings");
  }
}
</script>

<style scoped>
.spring-section {
  background: var(--panel-bg, #1a1a2e);
  border-radius: 8px;
  margin-bottom: 8px;
  overflow: hidden;
}

.section-header {
  display: flex;
  align-items: center;
  padding: 10px 12px;
  background: var(--header-bg, #252540);
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

.param-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.param-row label {
  min-width: 120px;
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
  min-width: 40px;
  font-size: 12px;
  color: var(--accent, #6c5ce7);
  text-align: right;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 8px;
  min-width: auto;
  cursor: pointer;
}

.preset-buttons {
  display: flex;
  gap: 6px;
  margin-top: 8px;
}

.preset-buttons button {
  flex: 1;
  padding: 6px 8px;
  background: var(--button-bg, #3a3a5a);
  border: none;
  border-radius: 4px;
  color: var(--text-primary, #fff);
  font-size: 11px;
  cursor: pointer;
  transition: background 0.2s;
}

.preset-buttons button:hover {
  background: var(--button-hover, #4a4a6a);
}

.preset-grid {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: 8px;
}

.preset-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 4px;
  padding: 12px;
  background: var(--card-bg, #2a2a4a);
  border: 1px solid var(--border-color, #444);
  border-radius: 8px;
  cursor: pointer;
  transition: all 0.2s;
}

.preset-btn:hover {
  background: var(--card-hover, #3a3a5a);
  border-color: var(--accent, #6c5ce7);
}

.preset-icon {
  font-size: 24px;
}

.preset-label {
  font-size: 11px;
  color: var(--text-secondary, #aaa);
}

.info-row {
  display: flex;
  justify-content: space-between;
  font-size: 12px;
  margin-bottom: 8px;
  color: var(--text-secondary, #aaa);
}

.info-row .value {
  color: var(--accent, #6c5ce7);
  font-weight: 600;
}

.danger-btn {
  width: 100%;
  padding: 8px;
  background: var(--danger-bg, #4a2020);
  border: 1px solid var(--danger-border, #6a3030);
  border-radius: 4px;
  color: var(--danger-text, #ff6b6b);
  font-size: 12px;
  cursor: pointer;
  transition: background 0.2s;
}

.danger-btn:hover {
  background: var(--danger-hover, #5a2525);
}

.collapsible .subsection-title {
  cursor: pointer;
}

.manual-spring {
  margin-top: 10px;
}

.manual-spring button {
  width: 100%;
  padding: 8px;
  background: var(--accent, #6c5ce7);
  border: none;
  border-radius: 4px;
  color: white;
  font-size: 12px;
  cursor: pointer;
  margin-top: 8px;
}

.hint {
  font-size: 10px;
  color: var(--text-muted, #666);
}
</style>
