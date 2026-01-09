<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Visualization</span>
    </div>
    <div v-if="expanded" class="section-content">
      <div class="property-row checkbox-row">
        <label title="Show horizon line at floor position (CC Particle World style).">
          <input
            type="checkbox"
            :checked="visualization.showHorizon"
            @change="update('showHorizon', ($event.target as HTMLInputElement).checked)"
          />
          Show Horizon
        </label>
      </div>
      <div class="property-row checkbox-row">
        <label title="Show 3D perspective grid for particle space visualization.">
          <input
            type="checkbox"
            :checked="visualization.showGrid"
            @change="update('showGrid', ($event.target as HTMLInputElement).checked)"
          />
          Show Grid
        </label>
      </div>
      <div v-if="visualization.showGrid" class="property-row">
        <label title="Grid cell size in pixels.">Grid Size</label>
        <input
          type="range"
          :value="visualization.gridSize ?? 100"
          min="25"
          max="200"
          step="25"
          @input="update('gridSize', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ visualization.gridSize ?? 100 }}px</span>
      </div>
      <div v-if="visualization.showGrid" class="property-row">
        <label title="Grid depth into Z axis.">Grid Depth</label>
        <input
          type="range"
          :value="visualization.gridDepth ?? 500"
          min="100"
          max="2000"
          step="100"
          @input="update('gridDepth', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ visualization.gridDepth ?? 500 }}px</span>
      </div>
      <div class="property-row checkbox-row">
        <label title="Show XYZ axis at origin.">
          <input
            type="checkbox"
            :checked="visualization.showAxis"
            @change="update('showAxis', ($event.target as HTMLInputElement).checked)"
          />
          Show Axis
        </label>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
interface VisualizationConfig {
  showHorizon: boolean;
  showGrid: boolean;
  showAxis: boolean;
  gridSize: number;
  gridDepth: number;
}

interface Props {
  visualization: VisualizationConfig;
  expanded: boolean;
}

defineProps<Props>();

const emit = defineEmits<{
  (e: "toggle"): void;
  (e: "update", key: keyof VisualizationConfig, value: any): void;
}>();

function update(key: keyof VisualizationConfig, value: any): void {
  emit("update", key, value);
}
</script>
