<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Sub-Emitters</span>
      <button class="add-btn" @click.stop="$emit('add')" title="Add Sub-Emitter">
        <i class="pi pi-plus" />
      </button>
    </div>
    <div v-if="expanded" class="section-content">
      <div
        v-for="sub in subEmitters"
        :key="sub.id"
        class="force-item"
      >
        <div class="force-header">
          <select
            :value="sub.parentEmitterId"
            @change="$emit('update', sub.id, 'parentEmitterId', ($event.target as HTMLSelectElement).value)"
            class="sub-emitter-parent"
          >
            <option value="*">All Emitters</option>
            <option v-for="e in emitters" :key="e.id" :value="e.id">{{ e.name }}</option>
          </select>
          <label class="enabled-toggle">
            <input
              type="checkbox"
              :checked="sub.enabled"
              @change="$emit('update', sub.id, 'enabled', ($event.target as HTMLInputElement).checked)"
            />
          </label>
          <button class="remove-btn" @click="$emit('remove', sub.id)">
            <i class="pi pi-trash" />
          </button>
        </div>
        <div class="property-row">
          <label title="Event that triggers sub-particle emission. 'On Death' spawns particles when parent particles expire.">Trigger</label>
          <select
            :value="sub.trigger"
            @change="$emit('update', sub.id, 'trigger', ($event.target as HTMLSelectElement).value)"
          >
            <option value="death">On Death</option>
          </select>
        </div>
        <div class="property-row">
          <label title="Number of sub-particles spawned when the trigger event occurs.">Spawn Count</label>
          <input
            type="range"
            :value="sub.spawnCount"
            min="1"
            max="10"
            step="1"
            @input="$emit('update', sub.id, 'spawnCount', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ sub.spawnCount }}</span>
        </div>
        <div class="property-row">
          <label title="How much of the parent particle's velocity is passed to sub-particles. 0% = independent, 100% = same direction.">Inherit Velocity</label>
          <input
            type="range"
            :value="sub.inheritVelocity"
            min="0"
            max="1"
            step="0.1"
            @input="$emit('update', sub.id, 'inheritVelocity', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ (sub.inheritVelocity * 100).toFixed(0) }}%</span>
        </div>
        <div class="property-row">
          <label title="Diameter of sub-particles in pixels. Often smaller than parent particles for sparks/debris effects.">Size</label>
          <input
            type="range"
            :value="sub.size"
            min="1"
            max="100"
            step="1"
            @input="$emit('update', sub.id, 'size', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ sub.size }}px</span>
        </div>
        <div class="property-row">
          <label title="How long sub-particles live in frames. Usually shorter than parent particles.">Lifetime</label>
          <input
            type="range"
            :value="sub.lifetime"
            min="1"
            max="120"
            step="1"
            @input="$emit('update', sub.id, 'lifetime', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ sub.lifetime }}f</span>
        </div>
        <div class="property-row">
          <label title="Initial velocity of sub-particles in pixels per second.">Speed</label>
          <input
            type="range"
            :value="sub.speed"
            min="1"
            max="500"
            step="10"
            @input="$emit('update', sub.id, 'speed', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ sub.speed }}</span>
        </div>
        <div class="property-row">
          <label title="Angular spread of sub-particle emission. 360° = emit in all directions (explosion), 0° = emit in inherited direction.">Spread</label>
          <input
            type="range"
            :value="sub.spread"
            min="0"
            max="360"
            step="5"
            @input="$emit('update', sub.id, 'spread', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ sub.spread }}°</span>
        </div>
        <div class="property-row">
          <label title="Color of sub-particles. Can differ from parent for visual variety.">Color</label>
          <input
            type="color"
            :value="rgbToHex(sub.color)"
            @input="$emit('updateColor', sub.id, ($event.target as HTMLInputElement).value)"
          />
        </div>
      </div>

      <div v-if="subEmitters.length === 0" class="empty-message">
        No sub-emitters. Add one for particle death effects.
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { ParticleEmitterConfig, SubEmitterConfig } from "@/types/project";

interface Props {
  subEmitters: SubEmitterConfig[];
  emitters: ParticleEmitterConfig[];
  expanded: boolean;
}

defineProps<Props>();

defineEmits<{
  (e: "toggle"): void;
  (e: "add"): void;
  (e: "remove", id: string): void;
  (e: "update", id: string, key: keyof SubEmitterConfig, value: any): void;
  (e: "updateColor", id: string, hex: string): void;
}>();

function rgbToHex(rgb: [number, number, number]): string {
  return `#${rgb.map((c) => c.toString(16).padStart(2, "0")).join("")}`;
}
</script>

<style scoped>
.sub-emitter-parent {
  flex: 1;
  padding: 2px 4px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 13px;
}
</style>
