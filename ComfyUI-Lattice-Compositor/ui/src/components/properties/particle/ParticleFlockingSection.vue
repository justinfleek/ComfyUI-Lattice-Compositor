<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Flocking</span>
    </div>
    <div v-if="expanded" class="section-content">
      <div class="property-row">
        <label title="Enable flocking (boids) behavior. Particles will exhibit collective movement patterns.">Enabled</label>
        <input
          type="checkbox"
          :checked="flocking.enabled"
          @change="update('enabled', ($event.target as HTMLInputElement).checked)"
        />
      </div>

      <template v-if="flocking.enabled">
        <div class="subsection-label">Separation</div>
        <div class="property-row">
          <label title="How strongly particles avoid crowding each other.">Weight</label>
          <input
            type="range"
            :value="flocking.separationWeight"
            min="0"
            max="100"
            step="1"
            @input="update('separationWeight', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.separationWeight }}</span>
        </div>
        <div class="property-row">
          <label title="Distance at which particles start avoiding each other.">Radius</label>
          <input
            type="range"
            :value="flocking.separationRadius"
            min="1"
            max="100"
            step="1"
            @input="update('separationRadius', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.separationRadius }}px</span>
        </div>

        <div class="subsection-label">Alignment</div>
        <div class="property-row">
          <label title="How strongly particles try to match their neighbors' direction.">Weight</label>
          <input
            type="range"
            :value="flocking.alignmentWeight"
            min="0"
            max="100"
            step="1"
            @input="update('alignmentWeight', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.alignmentWeight }}</span>
        </div>
        <div class="property-row">
          <label title="Distance to look for neighbors to align with.">Radius</label>
          <input
            type="range"
            :value="flocking.alignmentRadius"
            min="1"
            max="200"
            step="1"
            @input="update('alignmentRadius', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.alignmentRadius }}px</span>
        </div>

        <div class="subsection-label">Cohesion</div>
        <div class="property-row">
          <label title="How strongly particles are attracted to the center of nearby particles.">Weight</label>
          <input
            type="range"
            :value="flocking.cohesionWeight"
            min="0"
            max="100"
            step="1"
            @input="update('cohesionWeight', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.cohesionWeight }}</span>
        </div>
        <div class="property-row">
          <label title="Distance to look for neighbors for cohesion.">Radius</label>
          <input
            type="range"
            :value="flocking.cohesionRadius"
            min="1"
            max="200"
            step="1"
            @input="update('cohesionRadius', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.cohesionRadius }}px</span>
        </div>

        <div class="subsection-label">Limits</div>
        <div class="property-row">
          <label title="Maximum speed particles can achieve.">Max Speed</label>
          <input
            type="range"
            :value="flocking.maxSpeed"
            min="10"
            max="500"
            step="10"
            @input="update('maxSpeed', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.maxSpeed }}</span>
        </div>
        <div class="property-row">
          <label title="Maximum steering force applied to particles.">Max Force</label>
          <input
            type="range"
            :value="flocking.maxForce"
            min="1"
            max="100"
            step="1"
            @input="update('maxForce', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.maxForce }}</span>
        </div>
        <div class="property-row">
          <label title="Field of view for detecting neighbors (degrees).">Perception</label>
          <input
            type="range"
            :value="flocking.perceptionAngle"
            min="30"
            max="360"
            step="10"
            @input="update('perceptionAngle', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ flocking.perceptionAngle }}°</span>
        </div>
      </template>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { FlockingConfig } from "@/types/project";

interface Props {
  flocking: FlockingConfig;
  expanded: boolean;
}

defineProps<Props>();

const emit = defineEmits<{
  (e: "toggle"): void;
  (e: "update", key: keyof FlockingConfig, value: FlockingConfig[keyof FlockingConfig]): void;
}>();

function update(
  key: keyof FlockingConfig,
  value: FlockingConfig[keyof FlockingConfig],
): void {
  emit("update", key, value);
}
</script>
