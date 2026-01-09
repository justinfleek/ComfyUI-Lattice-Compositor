<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Force Fields</span>
    </div>
    <div v-if="expanded" class="section-content">
      <!-- Tabs -->
      <div class="force-tabs">
        <button
          :class="{ active: activeTab === 'wells' }"
          @click="activeTab = 'wells'"
        >
          Gravity Wells
        </button>
        <button
          :class="{ active: activeTab === 'vortices' }"
          @click="activeTab = 'vortices'"
        >
          Vortices
        </button>
      </div>

      <!-- Gravity Wells -->
      <div v-if="activeTab === 'wells'" class="force-list">
        <button class="add-btn full-width" @click="$emit('addWell')">
          <i class="pi pi-plus" /> Add Gravity Well
        </button>
        <div
          v-for="well in gravityWells"
          :key="well.id"
          class="force-item"
        >
          <div class="force-header">
            <input
              type="text"
              :value="well.name"
              @input="$emit('updateWell', well.id, 'name', ($event.target as HTMLInputElement).value)"
              class="force-name"
            />
            <label class="enabled-toggle">
              <input
                type="checkbox"
                :checked="well.enabled"
                @change="$emit('updateWell', well.id, 'enabled', ($event.target as HTMLInputElement).checked)"
              />
            </label>
            <button class="remove-btn" @click="$emit('removeWell', well.id)">
              <i class="pi pi-trash" />
            </button>
          </div>
          <div class="property-row">
            <label title="Horizontal position of the gravity well. 0 = left edge, 0.5 = center, 1 = right edge.">Position X</label>
            <input
              type="range"
              :value="well.x"
              min="0"
              max="1"
              step="0.01"
              @input="$emit('updateWell', well.id, 'x', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ well.x.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label title="Vertical position of the gravity well. 0 = top edge, 0.5 = center, 1 = bottom edge.">Position Y</label>
            <input
              type="range"
              :value="well.y"
              min="0"
              max="1"
              step="0.01"
              @input="$emit('updateWell', well.id, 'y', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ well.y.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label title="Attraction force strength. Positive = attract particles toward center, negative = repel particles away.">Strength</label>
            <input
              type="range"
              :value="well.strength"
              min="-1000"
              max="1000"
              step="10"
              @input="$emit('updateWell', well.id, 'strength', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ well.strength }}</span>
          </div>
          <div class="property-row">
            <label title="Area of influence as a fraction of composition size. Particles outside this radius are unaffected.">Radius</label>
            <input
              type="range"
              :value="well.radius"
              min="0.01"
              max="1"
              step="0.01"
              @input="$emit('updateWell', well.id, 'radius', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ well.radius.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label title="How force decreases with distance. Linear = gradual, Quadratic = realistic physics, Constant = uniform force.">Falloff</label>
            <select
              :value="well.falloff"
              @change="$emit('updateWell', well.id, 'falloff', ($event.target as HTMLSelectElement).value)"
            >
              <option value="linear">Linear</option>
              <option value="quadratic">Quadratic</option>
              <option value="constant">Constant</option>
            </select>
          </div>
        </div>
      </div>

      <!-- Vortices -->
      <div v-if="activeTab === 'vortices'" class="force-list">
        <button class="add-btn full-width" @click="$emit('addVortex')">
          <i class="pi pi-plus" /> Add Vortex
        </button>
        <div
          v-for="vortex in vortices"
          :key="vortex.id"
          class="force-item"
        >
          <div class="force-header">
            <input
              type="text"
              :value="vortex.name"
              @input="$emit('updateVortex', vortex.id, 'name', ($event.target as HTMLInputElement).value)"
              class="force-name"
            />
            <label class="enabled-toggle">
              <input
                type="checkbox"
                :checked="vortex.enabled"
                @change="$emit('updateVortex', vortex.id, 'enabled', ($event.target as HTMLInputElement).checked)"
              />
            </label>
            <button class="remove-btn" @click="$emit('removeVortex', vortex.id)">
              <i class="pi pi-trash" />
            </button>
          </div>
          <div class="property-row">
            <label title="Horizontal position of the vortex center. 0 = left edge, 0.5 = center, 1 = right edge.">Position X</label>
            <input
              type="range"
              :value="vortex.x"
              min="0"
              max="1"
              step="0.01"
              @input="$emit('updateVortex', vortex.id, 'x', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ vortex.x.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label title="Vertical position of the vortex center. 0 = top edge, 0.5 = center, 1 = bottom edge.">Position Y</label>
            <input
              type="range"
              :value="vortex.y"
              min="0"
              max="1"
              step="0.01"
              @input="$emit('updateVortex', vortex.id, 'y', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ vortex.y.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label title="Overall strength of the vortex force applied to particles.">Strength</label>
            <input
              type="range"
              :value="vortex.strength"
              min="0"
              max="1000"
              step="10"
              @input="$emit('updateVortex', vortex.id, 'strength', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ vortex.strength }}</span>
          </div>
          <div class="property-row">
            <label title="Area of influence as a fraction of composition size. Particles outside this radius are unaffected.">Radius</label>
            <input
              type="range"
              :value="vortex.radius"
              min="0.01"
              max="1"
              step="0.01"
              @input="$emit('updateVortex', vortex.id, 'radius', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ vortex.radius.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label title="Angular velocity of the swirl in degrees per frame. Higher values create faster spinning.">Rotation Speed</label>
            <input
              type="range"
              :value="vortex.rotationSpeed"
              min="0"
              max="50"
              step="1"
              @input="$emit('updateVortex', vortex.id, 'rotationSpeed', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ vortex.rotationSpeed }}°/f</span>
          </div>
          <div class="property-row">
            <label title="Force pulling particles toward the vortex center. Creates a spiral effect when combined with rotation.">Inward Pull</label>
            <input
              type="range"
              :value="vortex.inwardPull"
              min="0"
              max="100"
              step="1"
              @input="$emit('updateVortex', vortex.id, 'inwardPull', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ vortex.inwardPull }}</span>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref } from "vue";
import type { GravityWellConfig, VortexConfig } from "@/types/project";

interface Props {
  gravityWells: GravityWellConfig[];
  vortices: VortexConfig[];
  expanded: boolean;
}

defineProps<Props>();

defineEmits<{
  (e: "toggle"): void;
  (e: "addWell"): void;
  (e: "removeWell", id: string): void;
  (e: "updateWell", id: string, key: keyof GravityWellConfig, value: any): void;
  (e: "addVortex"): void;
  (e: "removeVortex", id: string): void;
  (e: "updateVortex", id: string, key: keyof VortexConfig, value: any): void;
}>();

const activeTab = ref<"wells" | "vortices">("wells");
</script>

<style scoped>
.force-tabs {
  display: flex;
  gap: 4px;
  margin-bottom: 8px;
}

.force-tabs button {
  flex: 1;
  padding: 6px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #888;
  border-radius: 3px;
  font-size: 13px;
  cursor: pointer;
}

.force-tabs button.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.force-list {
  max-height: 300px;
  overflow-y: auto;
}

.add-btn.full-width {
  width: 100%;
  padding: 8px;
  margin-bottom: 8px;
  border: 1px dashed #3d3d3d;
  background: transparent;
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
}

.add-btn.full-width:hover {
  border-color: #4a90d9;
  color: #4a90d9;
}

.force-name {
  flex: 1;
  padding: 2px 4px;
  border: 1px solid transparent;
  background: transparent;
  color: #e0e0e0;
  font-size: 13px;
}

.force-name:focus {
  border-color: #4a90d9;
  background: #1e1e1e;
  outline: none;
}
</style>
