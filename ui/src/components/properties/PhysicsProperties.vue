<!--
  @component PhysicsProperties
  @description Physics configuration panel for Newton Physics Simulation.

  Features:
  - Rigid body settings (type, mass, shape, material)
  - Soft body configuration
  - Cloth parameters
  - Ragdoll presets
  - Force field setup
  - Collision groups
  - Keyframe export (bake simulation)
-->
<template>
  <div class="physics-properties">
    <!-- Enable Physics Toggle -->
    <div class="toggle-row">
      <label class="toggle-label">
        <input
          type="checkbox"
          v-model="physicsEnabled"
          @change="togglePhysics"
        />
        Enable Physics
      </label>
    </div>

    <template v-if="physicsEnabled">
      <!-- Physics Type Selector -->
      <div class="form-group">
        <label>Physics Type</label>
        <select v-model="physicsType" @change="onPhysicsTypeChange">
          <option value="rigid">Rigid Body</option>
          <option value="soft">Soft Body</option>
          <option value="cloth">Cloth</option>
          <option value="ragdoll">Ragdoll</option>
        </select>
      </div>

      <!-- Rigid Body Settings -->
      <template v-if="physicsType === 'rigid'">
        <div class="section-header">Rigid Body</div>

        <div class="form-group">
          <label>Body Type</label>
          <select v-model="rigidBody.type" @change="updateRigidBody">
            <option value="dynamic">Dynamic</option>
            <option value="static">Static</option>
            <option value="kinematic">Kinematic</option>
            <option value="AEmatic">AEmatic (Follow Keyframes)</option>
          </select>
        </div>

        <div class="form-group" v-if="rigidBody.type === 'dynamic'">
          <label>Mass</label>
          <input
            type="number"
            v-model.number="rigidBody.mass"
            min="0.01"
            step="0.1"
            @change="updateRigidBody"
          />
        </div>

        <div class="form-group">
          <label>Shape</label>
          <select v-model="rigidBody.shapeType" @change="updateRigidBody">
            <option value="circle">Circle</option>
            <option value="box">Rectangle</option>
            <option value="capsule">Capsule</option>
            <option value="polygon">Polygon (From Layer)</option>
          </select>
        </div>

        <div class="form-group" v-if="rigidBody.shapeType === 'circle'">
          <label>Radius</label>
          <input
            type="number"
            v-model.number="rigidBody.radius"
            min="1"
            @change="updateRigidBody"
          />
        </div>

        <div class="form-group" v-if="rigidBody.shapeType === 'box'">
          <label>Width</label>
          <input
            type="number"
            v-model.number="rigidBody.width"
            min="1"
            @change="updateRigidBody"
          />
        </div>

        <div class="form-group" v-if="rigidBody.shapeType === 'box'">
          <label>Height</label>
          <input
            type="number"
            v-model.number="rigidBody.height"
            min="1"
            @change="updateRigidBody"
          />
        </div>

        <!-- Material Preset -->
        <div class="section-header">Material</div>

        <div class="form-group">
          <label>Preset</label>
          <select v-model="materialPreset" @change="applyMaterialPreset">
            <option value="default">Default</option>
            <option value="rubber">Rubber (Bouncy)</option>
            <option value="ice">Ice (Slippery)</option>
            <option value="metal">Metal</option>
            <option value="wood">Wood</option>
            <option value="stone">Stone</option>
            <option value="bouncy">Super Bouncy</option>
            <option value="sticky">Sticky</option>
            <option value="custom">Custom</option>
          </select>
        </div>

        <template v-if="materialPreset === 'custom'">
          <div class="form-group">
            <label>Bounciness</label>
            <input
              type="range"
              v-model.number="rigidBody.restitution"
              min="0"
              max="1"
              step="0.05"
              @input="updateRigidBody"
            />
            <span class="value-label">{{ rigidBody.restitution.toFixed(2) }}</span>
          </div>

          <div class="form-group">
            <label>Friction</label>
            <input
              type="range"
              v-model.number="rigidBody.friction"
              min="0"
              max="1"
              step="0.05"
              @input="updateRigidBody"
            />
            <span class="value-label">{{ rigidBody.friction.toFixed(2) }}</span>
          </div>
        </template>

        <div class="form-group">
          <label>Linear Damping</label>
          <input
            type="range"
            v-model.number="rigidBody.linearDamping"
            min="0"
            max="1"
            step="0.01"
            @input="updateRigidBody"
          />
          <span class="value-label">{{ rigidBody.linearDamping.toFixed(2) }}</span>
        </div>

        <div class="form-group">
          <label>Angular Damping</label>
          <input
            type="range"
            v-model.number="rigidBody.angularDamping"
            min="0"
            max="1"
            step="0.01"
            @input="updateRigidBody"
          />
          <span class="value-label">{{ rigidBody.angularDamping.toFixed(2) }}</span>
        </div>

        <div class="toggle-row">
          <label class="toggle-label">
            <input
              type="checkbox"
              v-model="rigidBody.fixedRotation"
              @change="updateRigidBody"
            />
            Fixed Rotation
          </label>
        </div>
      </template>

      <!-- Cloth Settings -->
      <template v-if="physicsType === 'cloth'">
        <div class="section-header">Cloth Simulation</div>

        <div class="form-group">
          <label>Grid Width</label>
          <input
            type="number"
            v-model.number="cloth.gridWidth"
            min="2"
            max="50"
            @change="updateCloth"
          />
        </div>

        <div class="form-group">
          <label>Grid Height</label>
          <input
            type="number"
            v-model.number="cloth.gridHeight"
            min="2"
            max="50"
            @change="updateCloth"
          />
        </div>

        <div class="form-group">
          <label>Spacing</label>
          <input
            type="number"
            v-model.number="cloth.spacing"
            min="1"
            max="50"
            @change="updateCloth"
          />
        </div>

        <div class="form-group">
          <label>Pinning</label>
          <select v-model="cloth.pinning" @change="updateCloth">
            <option value="none">None (Falls)</option>
            <option value="top">Pin Top Edge</option>
            <option value="corners">Pin Corners</option>
            <option value="left">Pin Left Edge</option>
            <option value="custom">Custom Pins</option>
          </select>
        </div>

        <div class="form-group">
          <label>Stiffness</label>
          <input
            type="range"
            v-model.number="cloth.stiffness"
            min="0"
            max="1"
            step="0.05"
            @input="updateCloth"
          />
          <span class="value-label">{{ cloth.stiffness.toFixed(2) }}</span>
        </div>

        <div class="form-group">
          <label>Damping</label>
          <input
            type="range"
            v-model.number="cloth.damping"
            min="0.9"
            max="1"
            step="0.005"
            @input="updateCloth"
          />
          <span class="value-label">{{ cloth.damping.toFixed(3) }}</span>
        </div>

        <div class="toggle-row">
          <label class="toggle-label">
            <input
              type="checkbox"
              v-model="cloth.tearable"
              @change="updateCloth"
            />
            Allow Tearing
          </label>
        </div>

        <div class="form-group" v-if="cloth.tearable">
          <label>Tear Threshold</label>
          <input
            type="range"
            v-model.number="cloth.tearThreshold"
            min="1.5"
            max="5"
            step="0.1"
            @input="updateCloth"
          />
          <span class="value-label">{{ cloth.tearThreshold.toFixed(1) }}x</span>
        </div>
      </template>

      <!-- Ragdoll Settings -->
      <template v-if="physicsType === 'ragdoll'">
        <div class="section-header">Ragdoll</div>

        <div class="form-group">
          <label>Preset</label>
          <select v-model="ragdoll.preset" @change="updateRagdoll">
            <option value="adult">Adult Human</option>
            <option value="child">Child</option>
            <option value="cartoon">Cartoon Character</option>
            <option value="custom">Custom</option>
          </select>
        </div>

        <div class="form-group">
          <label>Scale</label>
          <input
            type="range"
            v-model.number="ragdoll.scale"
            min="50"
            max="300"
            @input="updateRagdoll"
          />
          <span class="value-label">{{ ragdoll.scale }}%</span>
        </div>

        <div class="form-group">
          <label>Joint Stiffness</label>
          <input
            type="range"
            v-model.number="ragdoll.jointStiffness"
            min="0"
            max="1"
            step="0.05"
            @input="updateRagdoll"
          />
          <span class="value-label">{{ ragdoll.jointStiffness.toFixed(2) }}</span>
        </div>

        <div class="toggle-row">
          <label class="toggle-label">
            <input
              type="checkbox"
              v-model="ragdoll.selfCollision"
              @change="updateRagdoll"
            />
            Self Collision
          </label>
        </div>
      </template>

      <!-- Collision Settings -->
      <div class="section-header">Collision</div>

      <div class="form-group">
        <label>Collision Group</label>
        <select v-model="collision.group" @change="updateCollision">
          <option :value="1">Group 1 (Default)</option>
          <option :value="2">Group 2</option>
          <option :value="3">Group 3</option>
          <option :value="4">Group 4</option>
        </select>
      </div>

      <div class="form-group">
        <label>Collides With</label>
        <div class="checkbox-group">
          <label v-for="g in [1,2,3,4]" :key="g">
            <input
              type="checkbox"
              :checked="!!(collision.mask & (1 << (g-1)))"
              @change="toggleCollisionMask(g)"
            />
            Group {{ g }}
          </label>
        </div>
      </div>

      <!-- Global Settings -->
      <div class="section-header">World Settings</div>

      <div class="form-group">
        <label>Gravity X</label>
        <input
          type="number"
          v-model.number="world.gravityX"
          step="10"
          @change="updateWorld"
        />
      </div>

      <div class="form-group">
        <label>Gravity Y</label>
        <input
          type="number"
          v-model.number="world.gravityY"
          step="10"
          @change="updateWorld"
        />
      </div>

      <!-- Actions -->
      <div class="section-header">Actions</div>

      <div class="button-group">
        <button class="action-btn" @click="bakeToKeyframes">
          <i class="pi pi-key" />
          Bake to Keyframes
        </button>
        <button class="action-btn" @click="resetSimulation">
          <i class="pi pi-refresh" />
          Reset
        </button>
      </div>

      <div class="form-group">
        <label>Bake Range</label>
        <div class="range-inputs">
          <input
            type="number"
            v-model.number="bakeSettings.startFrame"
            min="0"
            placeholder="Start"
          />
          <span>to</span>
          <input
            type="number"
            v-model.number="bakeSettings.endFrame"
            min="0"
            placeholder="End"
          />
        </div>
      </div>

      <div class="toggle-row">
        <label class="toggle-label">
          <input
            type="checkbox"
            v-model="bakeSettings.simplify"
          />
          Simplify Keyframes
        </label>
      </div>
    </template>
  </div>
</template>

<script setup lang="ts">
import { onMounted, ref, watch } from "vue";
import { usePhysicsStore } from "@/stores/physicsStore";
import { useLayerStore } from "@/stores/layerStore";
import { MATERIAL_PRESETS } from "@/types/physics";

const props = defineProps<{
  layerId: string;
}>();

const emit = defineEmits<(e: "update") => void>();

const layerStore = useLayerStore();

// State
const physicsEnabled = ref(false);
const physicsType = ref<"rigid" | "soft" | "cloth" | "ragdoll">("rigid");
const materialPreset = ref("default");

const rigidBody = ref({
  type: "dynamic" as "dynamic" | "static" | "kinematic" | "AEmatic",
  mass: 1,
  shapeType: "box" as "circle" | "box" | "capsule" | "polygon",
  radius: 20,
  width: 100,
  height: 100,
  restitution: 0.3,
  friction: 0.5,
  linearDamping: 0.1,
  angularDamping: 0.1,
  fixedRotation: false,
});

const cloth = ref({
  gridWidth: 20,
  gridHeight: 20,
  spacing: 10,
  pinning: "top" as "none" | "top" | "corners" | "left" | "custom",
  stiffness: 0.8,
  damping: 0.98,
  tearable: false,
  tearThreshold: 2.0,
});

const ragdoll = ref({
  preset: "adult" as "adult" | "child" | "cartoon" | "custom",
  scale: 100,
  jointStiffness: 0.5,
  selfCollision: false,
});

const collision = ref({
  group: 1,
  mask: 0xf, // All groups by default
});

const world = ref({
  gravityX: 0,
  gravityY: 980,
});

const bakeSettings = ref({
  startFrame: 0,
  endFrame: 80,
  simplify: true,
});

// Load layer physics data
function loadLayerPhysics() {
  const layer = layerStore.getLayerById(props.layerId);
  if (!layer || !layer.data) return;

  // Check if layer data has physics property
  const layerData = layer.data as { physics?: import("@/types/physics").PhysicsLayerData };
  const data = layerData.physics;
  if (data) {
    physicsEnabled.value = data.physicsEnabled ?? false;
    
    // Determine physics type based on which config exists
    if (data.ragdoll) {
      physicsType.value = "ragdoll";
    } else if (data.cloth) {
      physicsType.value = "cloth";
    } else if (data.softBody) {
      physicsType.value = "soft";
    } else if (data.rigidBody) {
      physicsType.value = "rigid";
    }

    if (data.rigidBody) {
      Object.assign(rigidBody.value, data.rigidBody);
    }
    if (data.cloth) {
      Object.assign(cloth.value, data.cloth);
    }
    if (data.ragdoll) {
      Object.assign(ragdoll.value, data.ragdoll);
    }
    // Note: collision and world are not part of PhysicsLayerData
    // They may be stored elsewhere or need to be handled differently
  }
}

// Save physics data to layer
function saveLayerPhysics() {
  const layer = layerStore.getLayerById(props.layerId);
  if (!layer) return;

  const physicsData: import("@/types/physics").PhysicsLayerData = {
    physicsEnabled: physicsEnabled.value,
    rigidBody:
      physicsType.value === "rigid" ? { ...rigidBody.value } : undefined,
    cloth: physicsType.value === "cloth" ? { ...cloth.value } : undefined,
    ragdoll: physicsType.value === "ragdoll" ? { ...ragdoll.value } : undefined,
    // Note: collision and world are not part of PhysicsLayerData
    // They may need to be stored in rigidBody.filter or spaceConfig
  };

  layerStore.updateLayerData(props.layerId, { physics: physicsData });
  emit("update");
}

// Handlers
function togglePhysics() {
  saveLayerPhysics();
}

function onPhysicsTypeChange() {
  saveLayerPhysics();
}

function updateRigidBody() {
  saveLayerPhysics();
}

function updateCloth() {
  saveLayerPhysics();
}

function updateRagdoll() {
  saveLayerPhysics();
}

function updateCollision() {
  saveLayerPhysics();
}

function updateWorld() {
  saveLayerPhysics();
}

function applyMaterialPreset() {
  if (materialPreset.value !== "custom") {
    const preset =
      MATERIAL_PRESETS[materialPreset.value as keyof typeof MATERIAL_PRESETS];
    if (preset) {
      rigidBody.value.restitution = preset.restitution;
      rigidBody.value.friction = preset.friction;
      saveLayerPhysics();
    }
  }
}

function toggleCollisionMask(group: number) {
  collision.value.mask ^= 1 << (group - 1);
  saveLayerPhysics();
}

async function bakeToKeyframes() {
  const physicsStore = usePhysicsStore();
  try {
    await physicsStore.bakePhysicsToKeyframes(props.layerId, {
      startFrame: bakeSettings.value.startFrame,
      endFrame: bakeSettings.value.endFrame,
      simplify: bakeSettings.value.simplify,
    });
    // Refresh layer data after baking
    loadLayerPhysics();
  } catch (error) {
    console.error("Failed to bake physics to keyframes:", error);
  }
}

function resetSimulation() {
  const physicsStore = usePhysicsStore();
  try {
    physicsStore.resetPhysicsSimulation();
    // Refresh layer data after reset
    loadLayerPhysics();
  } catch (error) {
    console.error("Failed to reset physics simulation:", error);
  }
}

// Watch for layer changes
watch(
  () => props.layerId,
  () => {
    loadLayerPhysics();
  },
  { immediate: true },
);

onMounted(() => {
  loadLayerPhysics();
});
</script>

<style scoped>
.physics-properties {
  display: flex;
  flex-direction: column;
  gap: 12px;
  padding: 8px;
  font-size: var(--lattice-font-size-sm, 12px);
  color: var(--lattice-text-primary, #E5E5E5);
}

.section-header {
  font-size: var(--lattice-font-size-xs, 11px);
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--lattice-text-secondary, #9CA3AF);
  padding-top: 8px;
  border-top: 1px solid var(--lattice-border-subtle, #2A2A2A);
  margin-top: 4px;
}

.form-group {
  display: flex;
  align-items: center;
  gap: 8px;
}

.form-group > label:first-child {
  flex: 0 0 100px;
  color: var(--lattice-text-secondary, #9CA3AF);
  font-size: var(--lattice-font-size-sm, 12px);
}

.form-group select,
.form-group input[type="text"],
.form-group input[type="number"] {
  flex: 1;
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1A1A1A);
  border: 1px solid var(--lattice-border-default, #333333);
  border-radius: 4px;
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: var(--lattice-font-size-sm, 12px);
}

.form-group select:focus,
.form-group input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.form-group input[type="range"] {
  flex: 1;
  height: 4px;
  appearance: none;
  background: var(--lattice-surface-3, #222222);
  border-radius: 2px;
}

.form-group input[type="range"]::-webkit-slider-thumb {
  appearance: none;
  width: 14px;
  height: 14px;
  border-radius: 50%;
  background: var(--lattice-accent, #8B5CF6);
  cursor: pointer;
}

.value-label {
  min-width: 45px;
  text-align: right;
  color: var(--lattice-text-secondary, #9CA3AF);
  font-family: monospace;
  font-size: var(--lattice-font-size-xs, 11px);
}

.toggle-row {
  display: flex;
  align-items: center;
}

.toggle-label {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  color: var(--lattice-text-primary, #E5E5E5);
}

.toggle-label input[type="checkbox"] {
  width: 14px;
  height: 14px;
  accent-color: var(--lattice-accent, #8B5CF6);
}

.checkbox-group {
  display: flex;
  flex-wrap: wrap;
  gap: 12px;
  flex: 1;
}

.checkbox-group label {
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: var(--lattice-font-size-xs, 11px);
  color: var(--lattice-text-secondary, #9CA3AF);
}

.checkbox-group input[type="checkbox"] {
  width: 12px;
  height: 12px;
  accent-color: var(--lattice-accent, #8B5CF6);
}

.range-inputs {
  display: flex;
  align-items: center;
  gap: 8px;
  flex: 1;
}

.range-inputs input {
  width: 70px;
  flex: 0 0 auto;
}

.range-inputs span {
  color: var(--lattice-text-muted, #6B7280);
}

.button-group {
  display: flex;
  gap: 8px;
  margin-top: 4px;
}

.action-btn {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  padding: 8px 12px;
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-default, #333333);
  border-radius: 4px;
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: var(--lattice-font-size-sm, 12px);
  cursor: pointer;
  transition: all 0.15s ease;
}

.action-btn:hover {
  background: var(--lattice-surface-4, #2A2A2A);
  border-color: var(--lattice-accent, #8B5CF6);
}

.action-btn i {
  font-size: 14px;
}
</style>
