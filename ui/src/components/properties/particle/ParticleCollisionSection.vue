<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Collision</span>
    </div>
    <div v-if="expanded" class="section-content">
      <div class="property-row">
        <label title="Enable collision detection for particles.">Enabled</label>
        <input
          type="checkbox"
          :checked="collision.enabled"
          @change="update('enabled', ($event.target as HTMLInputElement).checked)"
        />
      </div>

      <template v-if="collision.enabled">
        <div class="subsection-label">Particle Collisions</div>
        <div class="property-row">
          <label title="Enable particle-to-particle collision (performance intensive).">P2P Collision</label>
          <input
            type="checkbox"
            :checked="collision.particleCollision"
            @change="update('particleCollision', ($event.target as HTMLInputElement).checked)"
          />
        </div>
        <div class="property-row">
          <label title="Collision radius around each particle.">Radius</label>
          <input
            type="range"
            :value="collision.particleRadius"
            min="1"
            max="50"
            step="1"
            @input="update('particleRadius', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ collision.particleRadius }}px</span>
        </div>
        <div class="property-row">
          <label title="How much velocity is retained after collision (0 = none, 1 = full).">Bounciness</label>
          <input
            type="range"
            :value="collision.bounciness"
            min="0"
            max="1"
            step="0.05"
            @input="update('bounciness', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ collision.bounciness.toFixed(2) }}</span>
        </div>
        <div class="property-row">
          <label title="Velocity reduction on collision (0 = none, 1 = full stop).">Friction</label>
          <input
            type="range"
            :value="collision.friction"
            min="0"
            max="1"
            step="0.05"
            @input="update('friction', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ collision.friction.toFixed(2) }}</span>
        </div>

        <div class="subsection-label">Boundary</div>
        <div class="property-row">
          <label title="Enable boundary collision at composition edges.">Boundary</label>
          <input
            type="checkbox"
            :checked="collision.boundaryEnabled"
            @change="update('boundaryEnabled', ($event.target as HTMLInputElement).checked)"
          />
        </div>
        <div class="property-row">
          <label title="What happens when particles hit the boundary.">Behavior</label>
          <select
            :value="collision.boundaryBehavior"
            @change="update('boundaryBehavior', ($event.target as HTMLSelectElement).value)"
          >
            <option value="none">None</option>
            <option value="bounce">Bounce</option>
            <option value="stick">Stick</option>
            <option value="wrap">Wrap Around</option>
            <option value="kill">Kill</option>
          </select>
        </div>
        <div class="property-row">
          <label title="Distance from composition edge for boundary.">Padding</label>
          <input
            type="range"
            :value="collision.boundaryPadding"
            min="0"
            max="100"
            step="5"
            @input="update('boundaryPadding', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ collision.boundaryPadding }}px</span>
        </div>

        <div class="subsection-label">Floor (CC Particle World)</div>
        <div class="property-row">
          <label title="Enable floor collision plane for particles.">Floor Enabled</label>
          <input
            type="checkbox"
            :checked="collision.floorEnabled"
            @change="update('floorEnabled', ($event.target as HTMLInputElement).checked)"
          />
        </div>
        <template v-if="collision.floorEnabled">
          <div class="property-row">
            <label title="Vertical position of floor (0=top, 1=bottom of composition).">Floor Y</label>
            <input
              type="range"
              :value="collision.floorY ?? 1.0"
              min="0"
              max="1"
              step="0.01"
              @input="update('floorY', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ ((collision.floorY ?? 1.0) * 100).toFixed(0) }}%</span>
          </div>
          <div class="property-row">
            <label title="What happens when particles hit the floor.">Floor Action</label>
            <select
              :value="collision.floorBehavior ?? 'bounce'"
              @change="update('floorBehavior', ($event.target as HTMLSelectElement).value)"
            >
              <option value="none">None (Pass Through)</option>
              <option value="bounce">Bounce</option>
              <option value="stick">Stick</option>
              <option value="kill">Kill</option>
            </select>
          </div>
          <div v-if="collision.floorBehavior === 'bounce' || collision.floorBehavior === 'stick'" class="property-row">
            <label title="Surface friction when particles hit the floor (0=slippery, 1=sticky).">Floor Friction</label>
            <input
              type="range"
              :value="collision.floorFriction ?? 0.3"
              min="0"
              max="1"
              step="0.05"
              @input="update('floorFriction', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ ((collision.floorFriction ?? 0.3)).toFixed(2) }}</span>
          </div>
        </template>

        <div class="subsection-label">Ceiling</div>
        <div class="property-row">
          <label title="Enable ceiling collision plane for particles.">Ceiling Enabled</label>
          <input
            type="checkbox"
            :checked="collision.ceilingEnabled"
            @change="update('ceilingEnabled', ($event.target as HTMLInputElement).checked)"
          />
        </div>
        <div v-if="collision.ceilingEnabled" class="property-row">
          <label title="Vertical position of ceiling (0=top, 1=bottom of composition).">Ceiling Y</label>
          <input
            type="range"
            :value="collision.ceilingY ?? 0"
            min="0"
            max="1"
            step="0.01"
            @input="update('ceilingY', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ ((collision.ceilingY ?? 0) * 100).toFixed(0) }}%</span>
        </div>
      </template>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { CollisionConfig } from "@/types/project";

interface Props {
  collision: CollisionConfig;
  expanded: boolean;
}

defineProps<Props>();

const emit = defineEmits<{
  (e: "toggle"): void;
  (e: "update", key: keyof CollisionConfig, value: CollisionConfig[keyof CollisionConfig]): void;
}>();

function update(
  key: keyof CollisionConfig,
  value: CollisionConfig[keyof CollisionConfig],
): void {
  emit("update", key, value);
}
</script>
