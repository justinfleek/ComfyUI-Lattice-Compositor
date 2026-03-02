<template>
  <svg class="node-connection-layer" :viewBox="viewBox" preserveAspectRatio="none">
    <defs>
      <!-- Gradient for visual flow connections -->
      <linearGradient
        v-for="conn in visualConnections"
        :key="`grad-${conn.id}`"
        :id="`gradient-${conn.id}`"
        :x1="conn.start.x"
        :y1="conn.start.y"
        :x2="conn.end.x"
        :y2="conn.end.y"
        gradientUnits="userSpaceOnUse"
      >
        <stop offset="0%" :stop-color="gradientStart" />
        <stop offset="100%" :stop-color="gradientEnd" />
      </linearGradient>
    </defs>

    <!-- Visual flow connections (thick gradient lines) -->
    <path
      v-for="conn in visualConnections"
      :key="conn.id"
      class="connection visual-flow"
      :d="generateBezierPath(conn.start, conn.end)"
      :stroke="`url(#gradient-${conn.id})`"
      stroke-width="3"
      fill="none"
    />

    <!-- Parameter connections (thin colored lines) -->
    <path
      v-for="conn in parameterConnections"
      :key="conn.id"
      class="connection parameter-link"
      :d="generateBezierPath(conn.start, conn.end)"
      :stroke="conn.color || parameterColor"
      stroke-width="1.5"
      fill="none"
    />

    <!-- Modifier connections (dashed lines) -->
    <path
      v-for="conn in modifierConnections"
      :key="conn.id"
      class="connection modifier-link"
      :d="generateBezierPath(conn.start, conn.end)"
      :stroke="conn.color || modifierColor"
      stroke-width="1"
      stroke-dasharray="4,4"
      fill="none"
    />
  </svg>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useThemeStore } from "@/stores/themeStore";

interface ConnectionPoint {
  x: number;
  y: number;
}

interface Connection {
  id: string;
  start: ConnectionPoint;
  end: ConnectionPoint;
  type: "visual" | "parameter" | "modifier";
  color?: string;
}

const props = defineProps<{
  connections: Connection[];
  width: number;
  height: number;
}>();

const themeStore = useThemeStore();

const viewBox = computed(() => `0 0 ${props.width} ${props.height}`);

// Theme-aware colors
const gradientStart = computed(() => "var(--lattice-accent, #8B5CF6)");
const gradientEnd = computed(() => "var(--lattice-accent-secondary, #EC4899)");
const parameterColor = computed(() => "var(--lattice-info, #3B82F6)");
const modifierColor = computed(() => "var(--lattice-warning, #F59E0B)");

// Categorize connections by type
const visualConnections = computed(() =>
  props.connections.filter((c) => c.type === "visual"),
);

const parameterConnections = computed(() =>
  props.connections.filter((c) => c.type === "parameter"),
);

const modifierConnections = computed(() =>
  props.connections.filter((c) => c.type === "modifier"),
);

/**
 * Generate a smooth bezier curve path between two points
 */
function generateBezierPath(
  start: ConnectionPoint,
  end: ConnectionPoint,
): string {
  // Calculate control points for a smooth S-curve
  const dx = end.x - start.x;
  const dy = end.y - start.y;

  // Horizontal control point offset (creates the curve shape)
  const controlOffset = Math.abs(dx) * 0.4;

  // For vertical connections, use a different curve style
  if (Math.abs(dy) > Math.abs(dx) * 2) {
    // Vertical-dominant: curve sideways then down
    const cp1x = start.x + controlOffset;
    const cp1y = start.y;
    const cp2x = end.x - controlOffset;
    const cp2y = end.y;

    return `M ${start.x} ${start.y} C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${end.x} ${end.y}`;
  }

  // Horizontal-dominant: standard bezier
  const cp1x = start.x + controlOffset;
  const cp1y = start.y;
  const cp2x = end.x - controlOffset;
  const cp2y = end.y;

  return `M ${start.x} ${start.y} C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${end.x} ${end.y}`;
}
</script>

<style scoped>
.node-connection-layer {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  pointer-events: none;
  z-index: 1;
}

.connection {
  transition: stroke-opacity 0.2s ease;
  stroke-linecap: round;
}

.connection.visual-flow {
  stroke-opacity: 0.8;
}

.connection.parameter-link {
  stroke-opacity: 0.6;
}

.connection.modifier-link {
  stroke-opacity: 0.5;
}

/* Hover effect requires parent to set data attribute */
.node-connection-layer[data-highlight] .connection {
  stroke-opacity: 0.2;
}

.node-connection-layer[data-highlight] .connection.highlighted {
  stroke-opacity: 1;
  filter: drop-shadow(0 0 4px currentColor);
}
</style>
