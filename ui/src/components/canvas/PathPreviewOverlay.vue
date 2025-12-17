<template>
  <div
    ref="overlayRef"
    class="path-preview-overlay"
    :style="overlayStyle"
  >
    <svg
      class="preview-svg"
      :viewBox="`0 0 ${width} ${height}`"
      preserveAspectRatio="xMidYMid meet"
    >
      <!-- Grid for reference -->
      <defs>
        <pattern
          id="preview-grid"
          :width="gridSize"
          :height="gridSize"
          patternUnits="userSpaceOnUse"
        >
          <path
            :d="`M ${gridSize} 0 L 0 0 0 ${gridSize}`"
            fill="none"
            stroke="rgba(255,255,255,0.05)"
            stroke-width="1"
          />
        </pattern>

        <!-- Glow filter for paths -->
        <filter id="path-glow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur in="SourceGraphic" stdDeviation="3" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>

        <!-- Arrow marker for direction -->
        <marker
          id="arrow"
          viewBox="0 0 10 10"
          refX="5"
          refY="5"
          markerWidth="6"
          markerHeight="6"
          orient="auto-start-reverse"
        >
          <path d="M 0 0 L 10 5 L 0 10 z" fill="#4a90d9" />
        </marker>
      </defs>

      <!-- Background grid -->
      <rect
        v-if="showGrid"
        width="100%"
        height="100%"
        fill="url(#preview-grid)"
      />

      <!-- Suggested paths -->
      <g
        v-for="(suggestion, index) in suggestions"
        :key="index"
        :class="['path-group', { selected: selectedIndex === index }]"
        @click="emit('select', index)"
      >
        <!-- Path shadow/glow -->
        <path
          v-if="suggestion.pathData"
          :d="suggestion.pathData"
          fill="none"
          :stroke="getPathColor(index, 0.3)"
          stroke-width="8"
          stroke-linecap="round"
          stroke-linejoin="round"
          filter="url(#path-glow)"
        />

        <!-- Main path -->
        <path
          v-if="suggestion.pathData"
          :d="suggestion.pathData"
          fill="none"
          :stroke="getPathColor(index, 1)"
          stroke-width="2"
          stroke-linecap="round"
          stroke-linejoin="round"
          :stroke-dasharray="selectedIndex === index ? 'none' : '8,4'"
          marker-end="url(#arrow)"
        />

        <!-- Control points -->
        <g v-if="suggestion.points && showPoints">
          <g
            v-for="(point, pIndex) in suggestion.points"
            :key="pIndex"
            class="control-point"
          >
            <!-- Point outer ring -->
            <circle
              :cx="point.x"
              :cy="point.y"
              r="8"
              fill="none"
              :stroke="getPathColor(index, 0.5)"
              stroke-width="2"
            />
            <!-- Point inner -->
            <circle
              :cx="point.x"
              :cy="point.y"
              r="4"
              :fill="getPathColor(index, 1)"
            />
            <!-- Point index label -->
            <text
              v-if="showLabels"
              :x="point.x + 12"
              :y="point.y + 4"
              class="point-label"
              :fill="getPathColor(index, 0.8)"
            >
              {{ pIndex + 1 }}
            </text>
            <!-- Depth indicator -->
            <text
              v-if="point.depth !== undefined && showDepth"
              :x="point.x + 12"
              :y="point.y + 16"
              class="depth-label"
            >
              z: {{ point.depth.toFixed(2) }}
            </text>
          </g>
        </g>
      </g>

      <!-- Camera motion indicators -->
      <g v-for="(suggestion, index) in cameraSuggestions" :key="`cam-${index}`">
        <g :class="['camera-indicator', { selected: selectedIndex === index }]">
          <!-- Camera icon -->
          <rect
            :x="suggestion.startX - 12"
            :y="suggestion.startY - 8"
            width="24"
            height="16"
            rx="2"
            :fill="getPathColor(index, 0.8)"
          />
          <circle
            :cx="suggestion.startX + 8"
            :cy="suggestion.startY"
            r="4"
            fill="none"
            :stroke="getPathColor(index, 1)"
            stroke-width="2"
          />

          <!-- Motion arrow -->
          <line
            :x1="suggestion.startX"
            :y1="suggestion.startY"
            :x2="suggestion.endX"
            :y2="suggestion.endY"
            :stroke="getPathColor(index, 1)"
            stroke-width="2"
            stroke-dasharray="4,2"
            marker-end="url(#arrow)"
          />

          <!-- Motion label -->
          <text
            :x="(suggestion.startX + suggestion.endX) / 2"
            :y="(suggestion.startY + suggestion.endY) / 2 - 10"
            class="motion-label"
            :fill="getPathColor(index, 1)"
          >
            {{ suggestion.type }}
          </text>
        </g>
      </g>

      <!-- Animated position indicator -->
      <g v-if="animatedPosition && showAnimation">
        <circle
          :cx="animatedPosition.x"
          :cy="animatedPosition.y"
          r="6"
          fill="#fff"
          class="animated-dot"
        />
        <circle
          :cx="animatedPosition.x"
          :cy="animatedPosition.y"
          r="12"
          fill="none"
          stroke="#fff"
          stroke-width="2"
          opacity="0.5"
          class="animated-ring"
        />
      </g>
    </svg>

    <!-- Legend -->
    <div v-if="suggestions.length > 0 && showLegend" class="legend">
      <div
        v-for="(suggestion, index) in suggestions"
        :key="index"
        class="legend-item"
        :class="{ selected: selectedIndex === index }"
        @click="emit('select', index)"
      >
        <span
          class="legend-color"
          :style="{ backgroundColor: getPathColor(index, 1) }"
        ></span>
        <span class="legend-text">{{ suggestion.description || `Path ${index + 1}` }}</span>
      </div>
    </div>

    <!-- Instructions -->
    <div v-if="suggestions.length > 0" class="instructions">
      Click a path to select it. Press Enter to accept.
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted } from 'vue';

interface PathPoint {
  x: number;
  y: number;
  depth?: number;
}

interface PathSuggestion {
  type: 'camera' | 'spline' | 'particle' | 'layer';
  description?: string;
  points?: PathPoint[];
  pathData?: string;
  confidence: number;
}

interface CameraSuggestion {
  type: string;
  startX: number;
  startY: number;
  endX: number;
  endY: number;
}

const props = withDefaults(defineProps<{
  width: number;
  height: number;
  suggestions: PathSuggestion[];
  selectedIndex: number | null;
  showGrid?: boolean;
  showPoints?: boolean;
  showLabels?: boolean;
  showDepth?: boolean;
  showLegend?: boolean;
  showAnimation?: boolean;
  gridSize?: number;
}>(), {
  showGrid: true,
  showPoints: true,
  showLabels: true,
  showDepth: true,
  showLegend: true,
  showAnimation: true,
  gridSize: 50,
});

const emit = defineEmits<{
  (e: 'select', index: number): void;
}>();

const overlayRef = ref<HTMLElement | null>(null);
const animatedPosition = ref<{ x: number; y: number } | null>(null);
let animationFrame = 0;
let animationId: number | null = null;

// Colors for different paths
const pathColors = [
  '#4a90d9', // Blue
  '#d94a4a', // Red
  '#4ad94a', // Green
  '#d9d94a', // Yellow
  '#d94ad9', // Magenta
  '#4ad9d9', // Cyan
];

// Computed
const overlayStyle = computed(() => ({
  width: `${props.width}px`,
  height: `${props.height}px`,
}));

const cameraSuggestions = computed<CameraSuggestion[]>(() => {
  return props.suggestions
    .filter(s => s.type === 'camera' && s.points && s.points.length >= 2)
    .map(s => ({
      type: s.description?.split(' ')[0] || 'Camera',
      startX: s.points![0].x,
      startY: s.points![0].y,
      endX: s.points![s.points!.length - 1].x,
      endY: s.points![s.points!.length - 1].y,
    }));
});

// Methods
function getPathColor(index: number, opacity: number): string {
  const baseColor = pathColors[index % pathColors.length];
  if (opacity === 1) return baseColor;

  // Convert hex to rgba
  const r = parseInt(baseColor.slice(1, 3), 16);
  const g = parseInt(baseColor.slice(3, 5), 16);
  const b = parseInt(baseColor.slice(5, 7), 16);
  return `rgba(${r}, ${g}, ${b}, ${opacity})`;
}

function pointsToPathData(points: PathPoint[]): string {
  if (points.length < 2) return '';

  // Create smooth cubic bezier path
  let d = `M ${points[0].x} ${points[0].y}`;

  if (points.length === 2) {
    d += ` L ${points[1].x} ${points[1].y}`;
  } else {
    // Use cubic bezier curves for smooth path
    for (let i = 0; i < points.length - 1; i++) {
      const p0 = points[Math.max(0, i - 1)];
      const p1 = points[i];
      const p2 = points[i + 1];
      const p3 = points[Math.min(points.length - 1, i + 2)];

      // Calculate control points
      const tension = 0.3;
      const cp1x = p1.x + (p2.x - p0.x) * tension;
      const cp1y = p1.y + (p2.y - p0.y) * tension;
      const cp2x = p2.x - (p3.x - p1.x) * tension;
      const cp2y = p2.y - (p3.y - p1.y) * tension;

      d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p2.x} ${p2.y}`;
    }
  }

  return d;
}

// Animate a dot along the selected path
function startAnimation() {
  if (props.selectedIndex === null) {
    animatedPosition.value = null;
    return;
  }

  const suggestion = props.suggestions[props.selectedIndex];
  if (!suggestion.points || suggestion.points.length < 2) {
    animatedPosition.value = null;
    return;
  }

  const points = suggestion.points;
  const totalLength = points.length - 1;

  function animate() {
    animationFrame = (animationFrame + 0.5) % (totalLength * 60);
    const t = animationFrame / (totalLength * 60);
    const segmentIndex = Math.min(Math.floor(t * totalLength), totalLength - 1);
    const segmentT = (t * totalLength) - segmentIndex;

    const p1 = points[segmentIndex];
    const p2 = points[segmentIndex + 1];

    animatedPosition.value = {
      x: p1.x + (p2.x - p1.x) * segmentT,
      y: p1.y + (p2.y - p1.y) * segmentT,
    };

    animationId = requestAnimationFrame(animate);
  }

  animate();
}

function stopAnimation() {
  if (animationId !== null) {
    cancelAnimationFrame(animationId);
    animationId = null;
  }
  animatedPosition.value = null;
}

// Watch for changes to generate path data
watch(() => props.suggestions, (newSuggestions) => {
  for (const suggestion of newSuggestions) {
    if (suggestion.points && !suggestion.pathData) {
      suggestion.pathData = pointsToPathData(suggestion.points);
    }
  }
}, { immediate: true, deep: true });

// Watch for selection changes to animate
watch(() => props.selectedIndex, () => {
  stopAnimation();
  if (props.showAnimation) {
    startAnimation();
  }
});

onMounted(() => {
  if (props.showAnimation && props.selectedIndex !== null) {
    startAnimation();
  }
});

onUnmounted(() => {
  stopAnimation();
});
</script>

<style scoped>
.path-preview-overlay {
  position: absolute;
  top: 0;
  left: 0;
  pointer-events: none;
  z-index: 100;
}

.preview-svg {
  width: 100%;
  height: 100%;
  pointer-events: all;
}

.path-group {
  cursor: pointer;
  transition: opacity 0.2s;
}

.path-group:hover {
  opacity: 0.8;
}

.path-group.selected path {
  stroke-width: 3;
}

.control-point {
  cursor: pointer;
}

.point-label {
  font-size: 10px;
  font-weight: 600;
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
}

.depth-label {
  font-size: 9px;
  fill: #888;
  font-family: 'SF Mono', Monaco, monospace;
}

.camera-indicator {
  cursor: pointer;
}

.motion-label {
  font-size: 10px;
  font-weight: 600;
  text-transform: uppercase;
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  text-anchor: middle;
}

.animated-dot {
  animation: pulse 1s ease-in-out infinite;
}

.animated-ring {
  animation: ring-pulse 1s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { r: 6; }
  50% { r: 8; }
}

@keyframes ring-pulse {
  0%, 100% { r: 12; opacity: 0.5; }
  50% { r: 16; opacity: 0.3; }
}

/* Legend */
.legend {
  position: absolute;
  bottom: 40px;
  left: 12px;
  background: rgba(0, 0, 0, 0.8);
  border-radius: 4px;
  padding: 8px;
  pointer-events: all;
}

.legend-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 8px;
  cursor: pointer;
  border-radius: 3px;
  transition: background 0.15s;
}

.legend-item:hover {
  background: rgba(255, 255, 255, 0.1);
}

.legend-item.selected {
  background: rgba(74, 144, 217, 0.3);
}

.legend-color {
  width: 12px;
  height: 12px;
  border-radius: 50%;
}

.legend-text {
  font-size: 11px;
  color: #e0e0e0;
}

/* Instructions */
.instructions {
  position: absolute;
  bottom: 12px;
  left: 50%;
  transform: translateX(-50%);
  background: rgba(0, 0, 0, 0.8);
  color: #888;
  font-size: 11px;
  padding: 6px 12px;
  border-radius: 4px;
  pointer-events: none;
}
</style>
