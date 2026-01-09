<template>
  <svg
    class="track-point-overlay"
    :viewBox="`0 0 ${width} ${height}`"
    :width="width"
    :height="height"
  >
    <!-- Track paths (motion trails) -->
    <g v-if="showTrails">
      <path
        v-for="track in tracksWithPaths"
        :key="`path_${track.id}`"
        :d="track.pathD"
        :stroke="track.color"
        stroke-width="1"
        fill="none"
        opacity="0.5"
      />
    </g>

    <!-- Track points -->
    <g v-for="point in points" :key="point.trackId">
      <!-- Point marker -->
      <g
        :transform="`translate(${point.x * width}, ${point.y * height})`"
        :class="{ selected: point.selected }"
        @click.stop="onPointClick(point, $event)"
        @mousedown.stop="onPointMouseDown(point, $event)"
      >
        <!-- Outer ring (selection indicator) -->
        <circle
          v-if="point.selected"
          r="12"
          fill="none"
          stroke="white"
          stroke-width="2"
          opacity="0.8"
        />

        <!-- Confidence ring -->
        <circle
          :r="6 + point.confidence * 4"
          :fill="point.color"
          :opacity="0.3"
        />

        <!-- Inner dot -->
        <circle
          r="4"
          :fill="point.color"
          stroke="white"
          stroke-width="1"
        />

        <!-- Crosshair -->
        <line
          x1="-8" y1="0" x2="-4" y2="0"
          stroke="white"
          stroke-width="1"
          opacity="0.8"
        />
        <line
          x1="4" y1="0" x2="8" y2="0"
          stroke="white"
          stroke-width="1"
          opacity="0.8"
        />
        <line
          x1="0" y1="-8" x2="0" y2="-4"
          stroke="white"
          stroke-width="1"
          opacity="0.8"
        />
        <line
          x1="0" y1="4" x2="0" y2="8"
          stroke="white"
          stroke-width="1"
          opacity="0.8"
        />
      </g>

      <!-- Label -->
      <text
        v-if="showLabels"
        :x="point.x * width + 12"
        :y="point.y * height - 8"
        fill="white"
        font-size="10"
        font-family="system-ui, sans-serif"
        text-shadow="0 1px 2px rgba(0,0,0,0.5)"
      >
        {{ point.trackName }}
      </text>
    </g>

    <!-- Marquee selection -->
    <rect
      v-if="isSelecting"
      :x="Math.min(selectionStart.x, selectionEnd.x)"
      :y="Math.min(selectionStart.y, selectionEnd.y)"
      :width="Math.abs(selectionEnd.x - selectionStart.x)"
      :height="Math.abs(selectionEnd.y - selectionStart.y)"
      fill="rgba(139, 92, 246, 0.2)"
      stroke="rgba(139, 92, 246, 0.8)"
      stroke-width="1"
      stroke-dasharray="4 2"
    />
  </svg>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import {
  clearSelection,
  deselectTrack,
  getPointsAtFrame,
  getTrackPositions,
  selectTrack,
  setTrackPosition,
  useTrackPoints,
} from "@/services/trackPointService";

const props = defineProps<{
  width: number;
  height: number;
  currentFrame: number;
  showTrails?: boolean;
  showLabels?: boolean;
  editable?: boolean;
}>();

const emit = defineEmits<{
  (e: "point-click", trackId: string, event: MouseEvent): void;
  (e: "point-drag", trackId: string, x: number, y: number): void;
  (e: "selection-change", trackIds: string[]): void;
}>();

const trackPoints = useTrackPoints();

// Get points at current frame
const points = computed(() => getPointsAtFrame(props.currentFrame));

// Get tracks with path data for trails
const tracksWithPaths = computed(() => {
  if (!props.showTrails) return [];

  const tracks: Array<{ id: string; color: string; pathD: string }> = [];

  for (const track of trackPoints.tracks.value) {
    const positions = getTrackPositions(track.id);
    if (positions.length < 2) continue;

    // Build SVG path
    const pathParts: string[] = [];
    for (let i = 0; i < positions.length; i++) {
      const pos = positions[i];
      const x = pos.x * props.width;
      const y = pos.y * props.height;

      if (i === 0) {
        pathParts.push(`M ${x} ${y}`);
      } else {
        pathParts.push(`L ${x} ${y}`);
      }
    }

    tracks.push({
      id: track.id,
      color: track.color,
      pathD: pathParts.join(" "),
    });
  }

  return tracks;
});

// Selection state
const isSelecting = ref(false);
const selectionStart = ref({ x: 0, y: 0 });
const selectionEnd = ref({ x: 0, y: 0 });

// Drag state
const isDragging = ref(false);
const dragTrackId = ref<string | null>(null);

function onPointClick(
  point: { trackId: string; selected: boolean },
  event: MouseEvent,
) {
  if (event.shiftKey) {
    // Toggle selection
    if (point.selected) {
      deselectTrack(point.trackId);
    } else {
      selectTrack(point.trackId, true);
    }
  } else {
    // Select only this point
    selectTrack(point.trackId, false);
  }

  emit("point-click", point.trackId, event);
  emit(
    "selection-change",
    Array.from(trackPoints.selectedTracks.value.map((t) => t.id)),
  );
}

function onPointMouseDown(point: { trackId: string }, event: MouseEvent) {
  if (!props.editable) return;

  isDragging.value = true;
  dragTrackId.value = point.trackId;

  const handleMouseMove = (moveEvent: MouseEvent) => {
    if (!isDragging.value || !dragTrackId.value) return;

    const rect = (
      event.target as SVGElement
    ).ownerSVGElement?.getBoundingClientRect();
    if (!rect) return;

    const x = (moveEvent.clientX - rect.left) / props.width;
    const y = (moveEvent.clientY - rect.top) / props.height;

    // Clamp to 0-1
    const clampedX = Math.max(0, Math.min(1, x));
    const clampedY = Math.max(0, Math.min(1, y));

    setTrackPosition(dragTrackId.value, props.currentFrame, clampedX, clampedY);
    emit("point-drag", dragTrackId.value, clampedX, clampedY);
  };

  const handleMouseUp = () => {
    isDragging.value = false;
    dragTrackId.value = null;
    document.removeEventListener("mousemove", handleMouseMove);
    document.removeEventListener("mouseup", handleMouseUp);
  };

  document.addEventListener("mousemove", handleMouseMove);
  document.addEventListener("mouseup", handleMouseUp);
}

// Handle click on background to clear selection
function _onBackgroundClick() {
  clearSelection();
  emit("selection-change", []);
}
</script>

<style scoped>
.track-point-overlay {
  position: absolute;
  top: 0;
  left: 0;
  pointer-events: none;
  z-index: 100;
}

.track-point-overlay g {
  pointer-events: auto;
  cursor: pointer;
}

.track-point-overlay g.selected circle:first-child {
  animation: pulse 1s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 0.8; }
  50% { opacity: 0.4; }
}

.track-point-overlay text {
  pointer-events: none;
  user-select: none;
}
</style>
