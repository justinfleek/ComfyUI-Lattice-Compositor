<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Modulations</span>
      <button class="add-btn" @click.stop="$emit('add')" title="Add Modulation">
        <i class="pi pi-plus" />
      </button>
    </div>
    <div v-if="expanded" class="section-content">
      <div
        v-for="mod in modulations"
        :key="mod.id"
        class="modulation-item"
      >
        <div class="modulation-header">
          <select
            :value="mod.emitterId"
            @change="$emit('update', mod.id, 'emitterId', ($event.target as HTMLSelectElement).value)"
          >
            <option value="*">All Emitters</option>
            <option v-for="e in emitters" :key="e.id" :value="e.id">{{ e.name }}</option>
          </select>
          <button class="remove-btn" @click="$emit('remove', mod.id)">
            <i class="pi pi-trash" />
          </button>
        </div>
        <div class="property-row">
          <label title="Which particle property to animate over the particle's lifetime.">Property</label>
          <select
            :value="mod.property"
            @change="$emit('update', mod.id, 'property', ($event.target as HTMLSelectElement).value)"
          >
            <option value="size">Size</option>
            <option value="speed">Speed</option>
            <option value="opacity">Opacity</option>
            <option value="colorR">Color R</option>
            <option value="colorG">Color G</option>
            <option value="colorB">Color B</option>
          </select>
        </div>
        <div class="property-row">
          <label title="Value of the property when the particle is born.">Start Value</label>
          <input
            type="number"
            :value="mod.startValue"
            step="0.1"
            @input="$emit('update', mod.id, 'startValue', Number(($event.target as HTMLInputElement).value))"
          />
        </div>
        <div class="property-row">
          <label title="Value of the property when the particle dies.">End Value</label>
          <input
            type="number"
            :value="mod.endValue"
            step="0.1"
            @input="$emit('update', mod.id, 'endValue', Number(($event.target as HTMLInputElement).value))"
          />
        </div>
        <div class="property-row">
          <label title="Interpolation curve between start and end values. Linear = constant rate, Ease Out = fast then slow.">Easing</label>
          <select
            :value="mod.easing"
            @change="$emit('update', mod.id, 'easing', ($event.target as HTMLSelectElement).value)"
          >
            <option value="linear">Linear</option>
            <option value="easeIn">Ease In</option>
            <option value="easeOut">Ease Out</option>
            <option value="easeInOut">Ease In Out</option>
            <option value="bounce">Bounce</option>
            <option value="elastic">Elastic</option>
          </select>
        </div>
      </div>

      <div v-if="modulations.length === 0" class="empty-message">
        No modulations. Add one to animate particle properties over lifetime.
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { ParticleModulationConfig, ParticleEmitterConfig } from '@/types/project';

interface Props {
  modulations: ParticleModulationConfig[];
  emitters: ParticleEmitterConfig[];
  expanded: boolean;
}

defineProps<Props>();

defineEmits<{
  (e: 'toggle'): void;
  (e: 'add'): void;
  (e: 'remove', id: string): void;
  (e: 'update', id: string, key: keyof ParticleModulationConfig, value: any): void;
}>();
</script>

<style scoped>
.modulation-item {
  background: #1e1e1e;
  border-radius: 4px;
  margin-bottom: 8px;
  overflow: hidden;
}

.modulation-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
  background: #2a2a2a;
}

.modulation-header select {
  flex: 1;
  padding: 2px 4px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 13px;
}
</style>
