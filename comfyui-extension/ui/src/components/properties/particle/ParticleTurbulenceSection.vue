<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Turbulence</span>
      <button class="add-btn" @click.stop="$emit('add')" title="Add Turbulence Field">
        <i class="pi pi-plus" />
      </button>
    </div>
    <div v-if="expanded" class="section-content">
      <div
        v-for="turb in turbulenceFields"
        :key="turb.id"
        class="force-item"
      >
        <div class="force-header">
          <span class="force-label">Turbulence Field</span>
          <label class="enabled-toggle">
            <input
              type="checkbox"
              :checked="turb.enabled"
              @change="$emit('update', turb.id, 'enabled', ($event.target as HTMLInputElement).checked)"
            />
          </label>
          <button class="remove-btn" @click="$emit('remove', turb.id)">
            <i class="pi pi-trash" />
          </button>
        </div>
        <div class="property-row">
          <label title="Size of the noise pattern. Smaller values = fine, detailed turbulence. Larger values = broad, sweeping motion.">Scale</label>
          <input
            type="range"
            :value="turb.scale"
            min="0.001"
            max="0.02"
            step="0.001"
            @input="$emit('update', turb.id, 'scale', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ turb.scale.toFixed(3) }}</span>
        </div>
        <div class="property-row">
          <label title="How strongly turbulence affects particle movement. Higher values create more chaotic motion.">Strength</label>
          <input
            type="range"
            :value="turb.strength"
            min="0"
            max="500"
            step="10"
            @input="$emit('update', turb.id, 'strength', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ turb.strength }}</span>
        </div>
        <div class="property-row">
          <label title="How fast the turbulence pattern changes over time. 0 = static noise, higher = animated turbulence.">Evolution</label>
          <input
            type="range"
            :value="turb.evolutionSpeed"
            min="0"
            max="1"
            step="0.01"
            @input="$emit('update', turb.id, 'evolutionSpeed', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ turb.evolutionSpeed.toFixed(2) }}</span>
        </div>
      </div>

      <div v-if="turbulenceFields.length === 0" class="empty-message">
        No turbulence fields. Add one for organic particle motion.
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { TurbulenceFieldConfig } from "@/types/project";

interface Props {
  turbulenceFields: TurbulenceFieldConfig[];
  expanded: boolean;
}

defineProps<Props>();

defineEmits<{
  (e: "toggle"): void;
  (e: "add"): void;
  (e: "remove", id: string): void;
  (
    e: "update",
    id: string,
    key: keyof TurbulenceFieldConfig,
    value: TurbulenceFieldConfig[keyof TurbulenceFieldConfig],
  ): void;
}>();
</script>
