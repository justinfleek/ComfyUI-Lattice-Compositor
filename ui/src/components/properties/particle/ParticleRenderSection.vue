<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Render Options</span>
    </div>
    <div v-if="expanded" class="section-content">
      <div class="property-row">
        <label title="How particles blend with the background. Additive = bright/glowing, Multiply = darken, Screen = lighten.">Blend Mode</label>
        <select
          :value="renderOptions.blendMode"
          @change="update('blendMode', ($event.target as HTMLSelectElement).value)"
        >
          <option value="normal">Normal</option>
          <option value="additive">Additive</option>
          <option value="multiply">Multiply</option>
          <option value="screen">Screen</option>
        </select>
      </div>
      <div class="property-row">
        <label title="Visual shape used to render each particle (CC Particle World compatible).">Shape</label>
        <select
          :value="renderOptions.particleShape"
          @change="update('particleShape', ($event.target as HTMLSelectElement).value)"
        >
          <option value="circle">Circle</option>
          <option value="square">Square</option>
          <option value="triangle">Triangle</option>
          <option value="star">Star</option>
          <option value="line">Line</option>
          <option value="shadedSphere">Shaded Sphere</option>
          <option value="fadedSphere">Faded Sphere</option>
          <option value="ring">Ring</option>
        </select>
      </div>

      <!-- Sprite Sheet Settings -->
      <div class="property-row checkbox-row">
        <label title="Use a custom image or sprite sheet instead of procedural shapes.">
          <input
            type="checkbox"
            :checked="renderOptions.spriteEnabled"
            @change="update('spriteEnabled', ($event.target as HTMLInputElement).checked)"
          />
          Use Sprite
        </label>
      </div>
      <div v-if="renderOptions.spriteEnabled" class="property-row">
        <label title="URL or data URI of the sprite image.">Sprite URL</label>
        <input
          type="text"
          :value="renderOptions.spriteImageUrl"
          placeholder="https://... or data:..."
          @change="update('spriteImageUrl', ($event.target as HTMLInputElement).value)"
        />
      </div>
      <div v-if="renderOptions.spriteEnabled" class="property-row">
        <label title="Number of columns in the sprite sheet (1 for single image).">Columns</label>
        <input
          type="number"
          :value="renderOptions.spriteColumns"
          min="1"
          max="16"
          @change="update('spriteColumns', Number(($event.target as HTMLInputElement).value))"
        />
      </div>
      <div v-if="renderOptions.spriteEnabled" class="property-row">
        <label title="Number of rows in the sprite sheet (1 for single image).">Rows</label>
        <input
          type="number"
          :value="renderOptions.spriteRows"
          min="1"
          max="16"
          @change="update('spriteRows', Number(($event.target as HTMLInputElement).value))"
        />
      </div>
      <div v-if="renderOptions.spriteEnabled && ((renderOptions.spriteColumns ?? 1) > 1 || (renderOptions.spriteRows ?? 1) > 1)" class="property-row checkbox-row">
        <label title="Animate through sprite sheet frames over time.">
          <input
            type="checkbox"
            :checked="renderOptions.spriteAnimate"
            @change="update('spriteAnimate', ($event.target as HTMLInputElement).checked)"
          />
          Animate Frames
        </label>
      </div>
      <div v-if="renderOptions.spriteEnabled && renderOptions.spriteAnimate" class="property-row">
        <label title="Frames per second for sprite animation.">Frame Rate</label>
        <input
          type="range"
          :value="renderOptions.spriteFrameRate"
          min="1"
          max="60"
          step="1"
          @input="update('spriteFrameRate', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ renderOptions.spriteFrameRate }} fps</span>
      </div>
      <div v-if="renderOptions.spriteEnabled && ((renderOptions.spriteColumns ?? 1) > 1 || (renderOptions.spriteRows ?? 1) > 1)" class="property-row checkbox-row">
        <label title="Each particle starts at a random frame in the sprite sheet.">
          <input
            type="checkbox"
            :checked="renderOptions.spriteRandomStart"
            @change="update('spriteRandomStart', ($event.target as HTMLInputElement).checked)"
          />
          Random Start Frame
        </label>
      </div>

      <div class="property-row checkbox-row">
        <label title="Draw a trail behind moving particles showing their recent path.">
          <input
            type="checkbox"
            :checked="renderOptions.renderTrails"
            @change="update('renderTrails', ($event.target as HTMLInputElement).checked)"
          />
          Render Trails
        </label>
      </div>
      <div v-if="renderOptions.renderTrails" class="property-row">
        <label title="Number of historical positions to show in the trail.">Trail Length</label>
        <input
          type="range"
          :value="renderOptions.trailLength"
          min="1"
          max="20"
          step="1"
          @input="update('trailLength', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ renderOptions.trailLength }}</span>
      </div>
      <div v-if="renderOptions.renderTrails" class="property-row">
        <label title="How quickly trail opacity decreases. Higher values = faster fade.">Trail Falloff</label>
        <input
          type="range"
          :value="renderOptions.trailOpacityFalloff"
          min="0"
          max="1"
          step="0.05"
          @input="update('trailOpacityFalloff', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ renderOptions.trailOpacityFalloff.toFixed(2) }}</span>
      </div>
      <div class="property-row checkbox-row">
        <label title="Add a soft glow effect around particles. Great for fire, magic, and light effects.">
          <input
            type="checkbox"
            :checked="renderOptions.glowEnabled"
            @change="update('glowEnabled', ($event.target as HTMLInputElement).checked)"
          />
          Enable Glow
        </label>
      </div>
      <div v-if="renderOptions.glowEnabled" class="property-row">
        <label title="Size of the glow area around each particle.">Glow Radius</label>
        <input
          type="range"
          :value="renderOptions.glowRadius"
          min="1"
          max="50"
          step="1"
          @input="update('glowRadius', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ renderOptions.glowRadius }}px</span>
      </div>
      <div v-if="renderOptions.glowEnabled" class="property-row">
        <label title="Brightness of the glow effect. 0 = no glow, 1 = maximum glow.">Glow Intensity</label>
        <input
          type="range"
          :value="renderOptions.glowIntensity"
          min="0"
          max="1"
          step="0.05"
          @input="update('glowIntensity', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ renderOptions.glowIntensity.toFixed(2) }}</span>
      </div>

      <!-- Motion Blur -->
      <div class="subsection-divider">Motion Blur</div>
      <div class="property-row checkbox-row">
        <label title="Blur fast-moving particles to simulate camera motion blur.">
          <input
            type="checkbox"
            :checked="renderOptions.motionBlur"
            @change="update('motionBlur', ($event.target as HTMLInputElement).checked)"
          />
          Enable Motion Blur
        </label>
      </div>
      <div v-if="renderOptions.motionBlur" class="property-row">
        <label title="How much blur to apply based on particle velocity.">Blur Strength</label>
        <input
          type="range"
          :value="renderOptions.motionBlurStrength"
          min="0"
          max="1"
          step="0.05"
          @input="update('motionBlurStrength', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ renderOptions.motionBlurStrength.toFixed(2) }}</span>
      </div>
      <div v-if="renderOptions.motionBlur" class="property-row">
        <label title="Number of samples for blur quality. Higher = smoother but slower.">Blur Samples</label>
        <input
          type="range"
          :value="renderOptions.motionBlurSamples"
          min="1"
          max="16"
          step="1"
          @input="update('motionBlurSamples', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ renderOptions.motionBlurSamples }}</span>
      </div>

      <!-- Particle Connections -->
      <div class="subsection-divider">Particle Connections</div>
      <div class="property-row checkbox-row">
        <label title="Draw lines between nearby particles. Creates web/network/constellation effects.">
          <input
            type="checkbox"
            :checked="connections.enabled"
            @change="$emit('updateConnection', 'enabled', ($event.target as HTMLInputElement).checked)"
          />
          Enable Connections
        </label>
      </div>
      <div v-if="connections.enabled" class="property-row">
        <label title="Maximum distance in pixels between particles to draw a connection.">Max Distance</label>
        <input
          type="range"
          :value="connections.maxDistance"
          min="10"
          max="300"
          step="10"
          @input="$emit('updateConnection', 'maxDistance', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ connections.maxDistance }}px</span>
      </div>
      <div v-if="connections.enabled" class="property-row">
        <label title="Maximum number of connections each particle can have.">Max Connections</label>
        <input
          type="range"
          :value="connections.maxConnections"
          min="1"
          max="5"
          step="1"
          @input="$emit('updateConnection', 'maxConnections', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ connections.maxConnections }}</span>
      </div>
      <div v-if="connections.enabled" class="property-row">
        <label title="Thickness of connection lines in pixels.">Line Width</label>
        <input
          type="range"
          :value="connections.lineWidth"
          min="0.5"
          max="3"
          step="0.1"
          @input="$emit('updateConnection', 'lineWidth', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ connections.lineWidth.toFixed(1) }}</span>
      </div>
      <div v-if="connections.enabled" class="property-row">
        <label title="Transparency of connection lines. 0 = invisible, 1 = fully opaque.">Line Opacity</label>
        <input
          type="range"
          :value="connections.lineOpacity"
          min="0"
          max="1"
          step="0.05"
          @input="$emit('updateConnection', 'lineOpacity', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ connections.lineOpacity.toFixed(2) }}</span>
      </div>
      <div v-if="connections.enabled" class="property-row checkbox-row">
        <label title="Make connection lines more transparent as particles get farther apart.">
          <input
            type="checkbox"
            :checked="connections.fadeByDistance"
            @change="$emit('updateConnection', 'fadeByDistance', ($event.target as HTMLInputElement).checked)"
          />
          Fade by Distance
        </label>
      </div>
      <div v-if="connections.enabled" class="property-row checkbox-row">
        <label title="Override connection line color instead of blending particle colors.">
          <input
            type="checkbox"
            :checked="connections.color !== undefined"
            @change="$emit('updateConnection', 'color', ($event.target as HTMLInputElement).checked ? [1, 1, 1] : undefined)"
          />
          Custom Color
        </label>
      </div>
      <div v-if="connections.enabled && connections.color !== undefined" class="property-row">
        <label title="Color for connection lines (RGB).">Line Color</label>
        <input
          type="color"
          :value="rgbToHex(connections.color)"
          @input="$emit('updateConnection', 'color', hexToRgb(($event.target as HTMLInputElement).value))"
        />
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import type {
  ConnectionRenderConfig,
  ParticleRenderOptions,
} from "@/types/project";

interface Props {
  renderOptions: ParticleRenderOptions;
  connections: ConnectionRenderConfig;
  expanded: boolean;
}

defineProps<Props>();

const emit = defineEmits<{
  (e: "toggle"): void;
  (e: "update", key: keyof ParticleRenderOptions, value: any): void;
  (e: "updateConnection", key: keyof ConnectionRenderConfig, value: any): void;
}>();

function update(key: keyof ParticleRenderOptions, value: any): void {
  emit("update", key, value);
}

// Color conversion helpers (engine uses 0-1 range)
function rgbToHex(rgb: [number, number, number]): string {
  const r = Math.round(rgb[0] * 255)
    .toString(16)
    .padStart(2, "0");
  const g = Math.round(rgb[1] * 255)
    .toString(16)
    .padStart(2, "0");
  const b = Math.round(rgb[2] * 255)
    .toString(16)
    .padStart(2, "0");
  return `#${r}${g}${b}`;
}

function hexToRgb(hex: string): [number, number, number] {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  return result
    ? [
        parseInt(result[1], 16) / 255,
        parseInt(result[2], 16) / 255,
        parseInt(result[3], 16) / 255,
      ]
    : [1, 1, 1];
}
</script>

<style scoped>
.subsection-divider {
  margin: 12px 0 8px;
  padding: 6px 0;
  border-top: 1px solid #3d3d3d;
  font-size: 13px;
  color: #888;
  font-weight: 500;
}
</style>
