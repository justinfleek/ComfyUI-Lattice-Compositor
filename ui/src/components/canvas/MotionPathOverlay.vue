<!--
  @component MotionPathOverlay
  @description Visualizes the motion path of animated position keyframes in the viewport.
  Shows bezier curves connecting position keyframes with:
  - Path line (white dashed)
  - Keyframe markers (diamonds)
  - Spatial tangent handles (circles when selected)
  - Current frame indicator (filled circle)

  @props
  - layerId: ID of the layer to show motion path for
  - currentFrame: Current playhead frame
  - canvasWidth/canvasHeight: Composition dimensions
  - containerWidth/containerHeight: Viewport dimensions
  - zoom: Current zoom level
  - viewportTransform: Pan offset [x, y]
  - enabled: Whether motion paths are enabled
-->
<template>
  <svg
    v-if="enabled && hasPositionKeyframes"
    class="motion-path-overlay"
    :viewBox="`0 0 ${canvasWidth} ${canvasHeight}`"
    :style="overlayStyle"
    @mousedown.stop="handleMouseDown"
    @mousemove="handleMouseMove"
    @mouseup="handleMouseUp"
  >
    <!-- Motion path curve -->
    <path
      :d="pathData"
      class="motion-path-line"
      fill="none"
      stroke="rgba(255, 255, 255, 0.7)"
      stroke-width="1"
      stroke-dasharray="4 4"
    />

    <!-- Spatial tangent handles (when keyframe is selected) -->
    <template v-for="kf in keyframesWithTangents" :key="`tangent-${kf.id}`">
      <!-- In tangent line -->
      <line
        v-if="kf.showTangents && kf.inTangent"
        :x1="kf.position.x"
        :y1="kf.position.y"
        :x2="kf.position.x + kf.inTangent.x"
        :y2="kf.position.y + kf.inTangent.y"
        class="tangent-line"
        stroke="rgba(139, 92, 246, 0.7)"
        stroke-width="1"
      />
      <!-- Out tangent line -->
      <line
        v-if="kf.showTangents && kf.outTangent"
        :x1="kf.position.x"
        :y1="kf.position.y"
        :x2="kf.position.x + kf.outTangent.x"
        :y2="kf.position.y + kf.outTangent.y"
        class="tangent-line"
        stroke="rgba(139, 92, 246, 0.7)"
        stroke-width="1"
      />
      <!-- In tangent handle -->
      <circle
        v-if="kf.showTangents && kf.inTangent"
        :cx="kf.position.x + kf.inTangent.x"
        :cy="kf.position.y + kf.inTangent.y"
        r="4"
        class="tangent-handle"
        :class="{ dragging: draggingHandleKeyframeId === kf.id && draggingHandleType === 'in' }"
        @mousedown.stop="startDragTangent($event, kf.id, 'in')"
      />
      <!-- Out tangent handle -->
      <circle
        v-if="kf.showTangents && kf.outTangent"
        :cx="kf.position.x + kf.outTangent.x"
        :cy="kf.position.y + kf.outTangent.y"
        r="4"
        class="tangent-handle"
        :class="{ dragging: draggingHandleKeyframeId === kf.id && draggingHandleType === 'out' }"
        @mousedown.stop="startDragTangent($event, kf.id, 'out')"
      />
    </template>

    <!-- Keyframe markers (diamonds) -->
    <template v-for="kf in keyframeMarkers" :key="`marker-${kf.id}`">
      <polygon
        :points="getDiamondPoints(kf.position.x, kf.position.y, 6)"
        class="keyframe-marker"
        :class="{
          selected: selectedKeyframeIds.includes(kf.id),
          current: kf.frame === currentFrame
        }"
        @click.stop="selectKeyframe($event, kf.id)"
        @dblclick.stop="goToKeyframe(kf.frame)"
      />
    </template>

    <!-- Current position indicator -->
    <circle
      v-if="currentPosition"
      :cx="currentPosition.x"
      :cy="currentPosition.y"
      r="5"
      class="current-position"
    />

    <!-- Frame ticks along path (every 5 frames) -->
    <template v-for="tick in frameTicks" :key="`tick-${tick.frame}`">
      <circle
        :cx="tick.x"
        :cy="tick.y"
        r="2"
        class="frame-tick"
        :title="`Frame ${tick.frame}`"
      />
    </template>
  </svg>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { assertDefined, safeCoordinateDefault } from "@/utils/typeGuards";
import { useLayerStore } from "@/stores/layerStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useKeyframeStore } from "@/stores/keyframeStore";
import type { AnimatableProperty, Keyframe } from "@/types/project";

interface Props {
  layerId: string | null;
  currentFrame: number;
  canvasWidth: number;
  canvasHeight: number;
  containerWidth: number;
  containerHeight: number;
  zoom: number;
  viewportTransform: number[];
  enabled: boolean;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: "keyframeSelected", keyframeId: string, addToSelection: boolean): void;
  (e: "goToFrame", frame: number): void;
  (
    e: "tangentUpdated",
    keyframeId: string,
    tangentType: "in" | "out",
    value: { x: number; y: number },
  ): void;
}>();

const layerStore = useLayerStore();
const selectionStore = useSelectionStore();
const keyframeStore = useKeyframeStore();

// Drag state
const draggingHandle = ref<{ keyframeId: string; type: "in" | "out" } | null>(
  null,
);
const dragStart = ref<{ x: number; y: number } | null>(null);

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
const draggingHandleKeyframeId = computed(() => {
  const handle = draggingHandle.value;
  return (handle != null && typeof handle === "object" && "keyframeId" in handle && typeof handle.keyframeId === "string") ? handle.keyframeId : undefined;
});

const draggingHandleType = computed(() => {
  const handle = draggingHandle.value;
  return (handle != null && typeof handle === "object" && "type" in handle && typeof handle.type === "string") ? handle.type : undefined;
});

// Selected keyframes (from store or local state)
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
const selectedKeyframeIds = computed(() => {
  const keyframeIds = selectionStore.selectedKeyframeIds;
  return (keyframeIds !== null && keyframeIds !== undefined && Array.isArray(keyframeIds)) ? keyframeIds : [];
});

// Position value type
type PositionValue = { x: number; y: number; z?: number };

// Get position property from layer
const positionProperty = computed(
  (): AnimatableProperty<PositionValue> | null => {
    if (!props.layerId) return null;
    const layer = layerStore.getLayerById(props.layerId);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    if (layer == null || typeof layer !== "object" || !("transform" in layer)) return null;
    const transform = layer.transform;
    if (transform == null || typeof transform !== "object" || !("position" in transform)) return null;
    return transform.position;
  },
);

// Check if layer has position keyframes
const hasPositionKeyframes = computed(() => {
  const prop = positionProperty.value;
  if (!prop) return false;
  return prop.animated && prop.keyframes && prop.keyframes.length >= 2;
});

// Get keyframes with their positions
const keyframeMarkers = computed(() => {
  const prop = positionProperty.value;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (prop == null || typeof prop !== "object" || !("keyframes" in prop) || prop.keyframes == null || !Array.isArray(prop.keyframes)) return [];

  return prop.keyframes.map((kf: Keyframe<PositionValue>) => {
    // Type proof: Position coordinates are unbounded (can be 0, negative, any ℝ)
    const x = safeCoordinateDefault(kf.value.x, 0, "kf.value.x");
    const y = safeCoordinateDefault(kf.value.y, 0, "kf.value.y");
    const z = safeCoordinateDefault(kf.value.z, 0, "kf.value.z");
    return {
      id: kf.id,
      frame: kf.frame,
      position: { x, y, z },
    };
  });
});

// Get keyframes with tangent info for display
const keyframesWithTangents = computed(() => {
  const prop = positionProperty.value;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (prop == null || typeof prop !== "object" || !("keyframes" in prop) || prop.keyframes == null || !Array.isArray(prop.keyframes)) return [];

  return prop.keyframes.map((kf: Keyframe<PositionValue>, index: number) => {
    // Type proof: Position coordinates are unbounded (can be 0, negative, any ℝ)
    const posX = safeCoordinateDefault(kf.value.x, 0, "kf.value.x");
    const posY = safeCoordinateDefault(kf.value.y, 0, "kf.value.y");
    const pos = { x: posX, y: posY };
    const isSelected = selectedKeyframeIds.value.includes(kf.id);

    // Calculate tangent vectors based on neighboring keyframes
    // For bezier interpolation, create smooth tangents
    let inTangent: { x: number; y: number } | null = null;
    let outTangent: { x: number; y: number } | null = null;

    // Type proof: keyframes is guaranteed non-null by prop?.keyframes check above
    assertDefined(prop.keyframes, "keyframes must exist when prop exists");
    const keyframes = prop.keyframes;

    // In tangent (from previous keyframe)
    if (index > 0) {
      const prevKf = keyframes[index - 1];
      // Type proof: Previous position coordinates are unbounded
      const prevX = safeCoordinateDefault(prevKf.value.x, 0, "prevKf.value.x");
      const prevY = safeCoordinateDefault(prevKf.value.y, 0, "prevKf.value.y");
      const prevPos = { x: prevX, y: prevY };
      const dx = pos.x - prevPos.x;
      const dy = pos.y - prevPos.y;
      // Tangent is 1/3 of the distance back towards previous keyframe
      inTangent = { x: -dx * 0.33, y: -dy * 0.33 };
    }

    // Out tangent (to next keyframe)
    if (index < keyframes.length - 1) {
      const nextKf = keyframes[index + 1];
      // Type proof: Next position coordinates are unbounded
      const nextX = safeCoordinateDefault(nextKf.value.x, 0, "nextKf.value.x");
      const nextY = safeCoordinateDefault(nextKf.value.y, 0, "nextKf.value.y");
      const nextPos = { x: nextX, y: nextY };
      const dx = nextPos.x - pos.x;
      const dy = nextPos.y - pos.y;
      // Tangent is 1/3 of the distance forward towards next keyframe
      outTangent = { x: dx * 0.33, y: dy * 0.33 };
    }

    return {
      id: kf.id,
      frame: kf.frame,
      position: pos,
      inTangent,
      outTangent,
      showTangents: isSelected,
      interpolation: kf.interpolation,
    };
  });
});

// Generate SVG path data for the motion path
const pathData = computed(() => {
  const markers = keyframeMarkers.value;
  if (markers.length < 2) return "";

  let d = `M ${markers[0].position.x} ${markers[0].position.y}`;

  for (let i = 1; i < markers.length; i++) {
    const prev = markers[i - 1];
    const curr = markers[i];

    // Use cubic bezier curves for smooth path
    const dx = curr.position.x - prev.position.x;
    const dy = curr.position.y - prev.position.y;

    // Control points at 1/3 intervals for smooth curve
    const cp1x = prev.position.x + dx * 0.33;
    const cp1y = prev.position.y + dy * 0.33;
    const cp2x = prev.position.x + dx * 0.66;
    const cp2y = prev.position.y + dy * 0.66;

    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${curr.position.x} ${curr.position.y}`;
  }

  return d;
});

// Current interpolated position
const currentPosition = computed(() => {
  const prop = positionProperty.value;
  if (!prop || !props.layerId) return null;

  // Get current value at frame
  const value = keyframeStore.evaluatePropertyAtFrame(
    props.layerId,
    "transform.position",
    props.currentFrame,
  );
  if (!value || !Array.isArray(value)) return null;

  // Type proof: Position coordinates from array are unbounded (can be 0, negative, any ℝ)
  const x = safeCoordinateDefault(value[0], 0, "value[0]");
  const y = safeCoordinateDefault(value[1], 0, "value[1]");
  return { x, y };
});

// Frame ticks along the path (every 5 frames)
const frameTicks = computed(() => {
  const prop = positionProperty.value;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (prop == null || typeof prop !== "object" || !("keyframes" in prop) || prop.keyframes == null || !Array.isArray(prop.keyframes) || prop.keyframes.length < 2) return [];

  const ticks: { frame: number; x: number; y: number }[] = [];
  const firstFrame = prop.keyframes[0].frame;
  const lastFrame = prop.keyframes[prop.keyframes.length - 1].frame;

  // Add tick every 5 frames
  for (let frame = firstFrame; frame <= lastFrame; frame += 5) {
    // Skip if this is a keyframe (will be shown as diamond)
    if (
      prop.keyframes.some((kf: Keyframe<PositionValue>) => kf.frame === frame)
    )
      continue;

    // Interpolate position at this frame
    if (!props.layerId) continue;
    const value = keyframeStore.evaluatePropertyAtFrame(
      props.layerId,
      "transform.position",
      frame,
    );
    if (value && Array.isArray(value)) {
      // Type proof: Position coordinates from array are unbounded (can be 0, negative, any ℝ)
      const x = safeCoordinateDefault(value[0], 0, "value[0]");
      const y = safeCoordinateDefault(value[1], 0, "value[1]");
      ticks.push({ frame, x, y });
    }
  }

  return ticks;
});

// SVG overlay style (matches viewport transform)
const overlayStyle = computed(() => {
  // Type proof: Viewport transform coordinates are unbounded (can be 0, negative for panning)
  const tx = safeCoordinateDefault(props.viewportTransform[4], 0, "viewportTransform[4]"); // translateX
  const ty = safeCoordinateDefault(props.viewportTransform[5], 0, "viewportTransform[5]"); // translateY

  return {
    position: "absolute" as const,
    top: "0",
    left: "0",
    width: `${props.containerWidth}px`,
    height: `${props.containerHeight}px`,
    transform: `translate(${tx}px, ${ty}px) scale(${props.zoom})`,
    transformOrigin: "top left" as const,
    pointerEvents: "none" as const,
    zIndex: 100,
  };
});

// Generate diamond shape points for keyframe markers
function getDiamondPoints(cx: number, cy: number, size: number): string {
  return `${cx},${cy - size} ${cx + size},${cy} ${cx},${cy + size} ${cx - size},${cy}`;
}

// Handle keyframe selection
function selectKeyframe(event: MouseEvent, keyframeId: string) {
  const addToSelection = event.shiftKey || event.ctrlKey || event.metaKey;
  emit("keyframeSelected", keyframeId, addToSelection);
}

// Double-click to go to keyframe frame
function goToKeyframe(frame: number) {
  emit("goToFrame", frame);
}

// Start dragging tangent handle
function startDragTangent(
  event: MouseEvent,
  keyframeId: string,
  type: "in" | "out",
) {
  draggingHandle.value = { keyframeId, type };
  dragStart.value = { x: event.clientX, y: event.clientY };
  event.preventDefault();
}

// Mouse handlers for tangent dragging
function handleMouseDown(_event: MouseEvent) {
  // Handle is started in startDragTangent
}

function handleMouseMove(event: MouseEvent) {
  if (!draggingHandle.value || !dragStart.value) return;

  // Calculate delta in canvas coordinates
  const dx = (event.clientX - dragStart.value.x) / props.zoom;
  const dy = (event.clientY - dragStart.value.y) / props.zoom;

  // Emit tangent update
  emit(
    "tangentUpdated",
    draggingHandle.value.keyframeId,
    draggingHandle.value.type,
    { x: dx, y: dy },
  );

  dragStart.value = { x: event.clientX, y: event.clientY };
}

function handleMouseUp() {
  draggingHandle.value = null;
  dragStart.value = null;
}
</script>

<style scoped>
.motion-path-overlay {
  position: absolute;
  top: 0;
  left: 0;
  overflow: visible;
  pointer-events: none;
}

.motion-path-line {
  pointer-events: stroke;
  cursor: default;
}

.keyframe-marker {
  fill: rgba(255, 255, 255, 0.3);
  stroke: rgba(255, 255, 255, 0.8);
  stroke-width: 1.5;
  cursor: pointer;
  pointer-events: all;
  transition: fill 0.15s, stroke 0.15s;
}

.keyframe-marker:hover {
  fill: rgba(139, 92, 246, 0.5);
  stroke: #8B5CF6;
}

.keyframe-marker.selected {
  fill: #8B5CF6;
  stroke: #fff;
  stroke-width: 2;
}

.keyframe-marker.current {
  fill: rgba(236, 72, 153, 0.8);
  stroke: #EC4899;
}

.current-position {
  fill: #EC4899;
  stroke: #fff;
  stroke-width: 2;
  filter: drop-shadow(0 0 4px rgba(236, 72, 153, 0.5));
}

.tangent-line {
  pointer-events: none;
}

.tangent-handle {
  fill: #8B5CF6;
  stroke: #fff;
  stroke-width: 1.5;
  cursor: move;
  pointer-events: all;
  transition: fill 0.15s;
}

.tangent-handle:hover,
.tangent-handle.dragging {
  fill: #A78BFA;
  stroke-width: 2;
}

.frame-tick {
  fill: rgba(255, 255, 255, 0.4);
  pointer-events: none;
}
</style>
