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
          :value="visualizationGridSize"
          min="25"
          max="200"
          step="25"
          @input="update('gridSize', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ visualizationGridSize }}px</span>
      </div>
      <div v-if="visualization.showGrid" class="property-row">
        <label title="Grid depth into Z axis.">Grid Depth</label>
        <input
          type="range"
          :value="visualizationGridDepth"
          min="100"
          max="2000"
          step="100"
          @input="update('gridDepth', Number(($event.target as HTMLInputElement).value))"
        />
        <span class="value-display">{{ visualizationGridDepth }}px</span>
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
import { computed } from "vue";

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

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: "toggle"): void;
  (e: "update", key: keyof VisualizationConfig, value: VisualizationConfig[keyof VisualizationConfig]): void;
}>();

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
// Computed properties for optional visualization properties
const visualizationGridSize = computed(() => {
  const viz = props.visualization;
  return (typeof viz === "object" && viz !== null && "gridSize" in viz && typeof viz.gridSize === "number" && Number.isFinite(viz.gridSize)) ? viz.gridSize : 100;
});
const visualizationGridDepth = computed(() => {
  const viz = props.visualization;
  return (typeof viz === "object" && viz !== null && "gridDepth" in viz && typeof viz.gridDepth === "number" && Number.isFinite(viz.gridDepth)) ? viz.gridDepth : 500;
});

function update(key: keyof VisualizationConfig, value: VisualizationConfig[keyof VisualizationConfig]): void {
  emit("update", key, value);
}
</script>
