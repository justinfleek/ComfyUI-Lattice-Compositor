<template>
  <div class="spline-editor">
    <!-- Control point visuals are rendered via SVG overlay -->
    <svg
      class="control-overlay"
      :viewBox="`0 0 ${canvasWidth} ${canvasHeight}`"
      @mousedown="handleMouseDown"
      @mousemove="handleMouseMove"
      @mouseup="handleMouseUp"
      @mouseleave="handleMouseUp"
    >
      <!-- Handle lines -->
      <template v-for="point in visibleControlPoints" :key="`handles-${point.id}`">
        <line
          v-if="point.handleIn && selectedPointId === point.id"
          :x1="point.x"
          :y1="point.y"
          :x2="point.handleIn.x"
          :y2="point.handleIn.y"
          class="handle-line"
        />
        <line
          v-if="point.handleOut && selectedPointId === point.id"
          :x1="point.x"
          :y1="point.y"
          :x2="point.handleOut.x"
          :y2="point.handleOut.y"
          class="handle-line"
        />
      </template>

      <!-- Handle points -->
      <template v-for="point in visibleControlPoints" :key="`handle-points-${point.id}`">
        <circle
          v-if="point.handleIn && selectedPointId === point.id"
          :cx="point.handleIn.x"
          :cy="point.handleIn.y"
          r="4"
          class="handle-point"
          :class="{ active: dragTarget?.type === 'handleIn' && dragTarget.pointId === point.id }"
          @mousedown.stop="startDragHandle(point.id, 'in', $event)"
        />
        <circle
          v-if="point.handleOut && selectedPointId === point.id"
          :cx="point.handleOut.x"
          :cy="point.handleOut.y"
          r="4"
          class="handle-point"
          :class="{ active: dragTarget?.type === 'handleOut' && dragTarget.pointId === point.id }"
          @mousedown.stop="startDragHandle(point.id, 'out', $event)"
        />
      </template>

      <!-- Control points -->
      <circle
        v-for="point in visibleControlPoints"
        :key="`point-${point.id}`"
        :cx="point.x"
        :cy="point.y"
        r="6"
        class="control-point"
        :class="{
          selected: selectedPointId === point.id,
          corner: point.type === 'corner',
          smooth: point.type === 'smooth'
        }"
        @mousedown.stop="startDragPoint(point.id, $event)"
      />

      <!-- Preview point when in pen mode -->
      <circle
        v-if="previewPoint && isPenMode"
        :cx="previewPoint.x"
        :cy="previewPoint.y"
        r="4"
        class="preview-point"
      />
    </svg>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { ControlPoint, SplineData } from '@/types/project';

interface Props {
  layerId: string | null;
  canvasWidth: number;
  canvasHeight: number;
  zoom: number;
  viewportTransform: number[];
  isPenMode: boolean;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: 'pointAdded', point: ControlPoint): void;
  (e: 'pointMoved', pointId: string, x: number, y: number): void;
  (e: 'handleMoved', pointId: string, handleType: 'in' | 'out', x: number, y: number): void;
  (e: 'pointDeleted', pointId: string): void;
  (e: 'pathUpdated'): void;
}>();

const store = useCompositorStore();

// State
const selectedPointId = ref<string | null>(null);
const previewPoint = ref<{ x: number; y: number } | null>(null);
const dragTarget = ref<{
  type: 'point' | 'handleIn' | 'handleOut';
  pointId: string;
  startX: number;
  startY: number;
} | null>(null);

// Get control points from active spline layer
const visibleControlPoints = computed<ControlPoint[]>(() => {
  if (!props.layerId) return [];

  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer || layer.type !== 'spline' || !layer.data) return [];

  const splineData = layer.data as SplineData;
  return splineData.controlPoints || [];
});

// Convert screen coords to canvas coords
function screenToCanvas(screenX: number, screenY: number): { x: number; y: number } {
  const vt = props.viewportTransform;
  // Inverse transform
  const x = (screenX - vt[4]) / vt[0];
  const y = (screenY - vt[5]) / vt[3];
  return { x, y };
}

// Get mouse position relative to SVG
function getMousePos(event: MouseEvent): { x: number; y: number } {
  const svg = event.currentTarget as SVGSVGElement;
  const rect = svg.getBoundingClientRect();
  const screenX = event.clientX - rect.left;
  const screenY = event.clientY - rect.top;
  return screenToCanvas(screenX, screenY);
}

// Handle mouse events
function handleMouseDown(event: MouseEvent) {
  if (!props.isPenMode) return;

  const pos = getMousePos(event);

  // In pen mode, add new point on click
  if (props.layerId) {
    const layer = store.layers.find(l => l.id === props.layerId);
    if (layer && layer.type === 'spline') {
      const splineData = layer.data as SplineData;

      const newPoint: ControlPoint = {
        id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
        x: pos.x,
        y: pos.y,
        handleIn: null,
        handleOut: null,
        type: 'corner'
      };

      // Add point to spline data
      if (!splineData.controlPoints) {
        splineData.controlPoints = [];
      }
      splineData.controlPoints.push(newPoint);

      // Select the new point
      selectedPointId.value = newPoint.id;

      // Start dragging to create handle
      dragTarget.value = {
        type: 'handleOut',
        pointId: newPoint.id,
        startX: pos.x,
        startY: pos.y
      };

      emit('pointAdded', newPoint);
      emit('pathUpdated');
    }
  }
}

function handleMouseMove(event: MouseEvent) {
  const pos = getMousePos(event);

  // Update preview point in pen mode
  if (props.isPenMode) {
    previewPoint.value = pos;
  }

  // Handle dragging
  if (dragTarget.value) {
    const layer = store.layers.find(l => l.id === props.layerId);
    if (!layer || layer.type !== 'spline') return;

    const splineData = layer.data as SplineData;
    const point = splineData.controlPoints?.find(p => p.id === dragTarget.value!.pointId);
    if (!point) return;

    if (dragTarget.value.type === 'point') {
      // Move the control point
      const dx = pos.x - point.x;
      const dy = pos.y - point.y;

      point.x = pos.x;
      point.y = pos.y;

      // Move handles with point
      if (point.handleIn) {
        point.handleIn.x += dx;
        point.handleIn.y += dy;
      }
      if (point.handleOut) {
        point.handleOut.x += dx;
        point.handleOut.y += dy;
      }

      emit('pointMoved', point.id, pos.x, pos.y);
    } else if (dragTarget.value.type === 'handleIn') {
      point.handleIn = { x: pos.x, y: pos.y };

      // Mirror to handleOut if smooth
      if (point.type === 'smooth') {
        const dx = pos.x - point.x;
        const dy = pos.y - point.y;
        point.handleOut = { x: point.x - dx, y: point.y - dy };
      }

      emit('handleMoved', point.id, 'in', pos.x, pos.y);
    } else if (dragTarget.value.type === 'handleOut') {
      point.handleOut = { x: pos.x, y: pos.y };

      // Mirror to handleIn if smooth
      if (point.type === 'smooth') {
        const dx = pos.x - point.x;
        const dy = pos.y - point.y;
        point.handleIn = { x: point.x - dx, y: point.y - dy };
      }

      emit('handleMoved', point.id, 'out', pos.x, pos.y);
    }

    emit('pathUpdated');
  }
}

function handleMouseUp() {
  if (dragTarget.value) {
    // If we were creating a new handle by dragging, convert to smooth point
    const layer = store.layers.find(l => l.id === props.layerId);
    if (layer && layer.type === 'spline') {
      const splineData = layer.data as SplineData;
      const point = splineData.controlPoints?.find(p => p.id === dragTarget.value!.pointId);
      if (point && point.handleOut) {
        // Check if handle was dragged far enough
        const dx = point.handleOut.x - point.x;
        const dy = point.handleOut.y - point.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist > 5) {
          point.type = 'smooth';
          // Create mirrored handleIn
          point.handleIn = { x: point.x - dx, y: point.y - dy };
        } else {
          // Too small, remove handle
          point.handleOut = null;
        }
      }
    }

    dragTarget.value = null;
    emit('pathUpdated');
  }
}

function startDragPoint(pointId: string, event: MouseEvent) {
  selectedPointId.value = pointId;

  if (!props.isPenMode) {
    const pos = getMousePos(event);
    dragTarget.value = {
      type: 'point',
      pointId,
      startX: pos.x,
      startY: pos.y
    };
  }
}

function startDragHandle(pointId: string, handleType: 'in' | 'out', event: MouseEvent) {
  const pos = getMousePos(event);
  dragTarget.value = {
    type: handleType === 'in' ? 'handleIn' : 'handleOut',
    pointId,
    startX: pos.x,
    startY: pos.y
  };
}

// Delete selected point on Delete key
function handleKeyDown(event: KeyboardEvent) {
  if (event.key === 'Delete' || event.key === 'Backspace') {
    if (selectedPointId.value && props.layerId) {
      const layer = store.layers.find(l => l.id === props.layerId);
      if (layer && layer.type === 'spline') {
        const splineData = layer.data as SplineData;
        const index = splineData.controlPoints?.findIndex(p => p.id === selectedPointId.value);
        if (index !== undefined && index >= 0) {
          splineData.controlPoints?.splice(index, 1);
          emit('pointDeleted', selectedPointId.value);
          emit('pathUpdated');
          selectedPointId.value = null;
        }
      }
    }
  }
}

onMounted(() => {
  window.addEventListener('keydown', handleKeyDown);
});

onUnmounted(() => {
  window.removeEventListener('keydown', handleKeyDown);
});

// Expose selected point for external access
defineExpose({
  selectedPointId,
  clearSelection: () => { selectedPointId.value = null; }
});
</script>

<style scoped>
.spline-editor {
  position: absolute;
  inset: 0;
  pointer-events: none;
}

.control-overlay {
  width: 100%;
  height: 100%;
  pointer-events: all;
}

.control-point {
  fill: #ffffff;
  stroke: #00ff00;
  stroke-width: 2;
  cursor: pointer;
  transition: fill 0.1s, transform 0.1s;
}

.control-point:hover {
  fill: #00ff00;
}

.control-point.selected {
  fill: #00ff00;
  stroke: #ffffff;
}

.control-point.corner {
  /* Square appearance for corner points */
}

.control-point.smooth {
  /* Circle for smooth points */
}

.handle-line {
  stroke: #00ff00;
  stroke-width: 1;
  stroke-dasharray: 4 2;
  opacity: 0.7;
}

.handle-point {
  fill: #00ff00;
  stroke: #ffffff;
  stroke-width: 1;
  cursor: pointer;
}

.handle-point:hover,
.handle-point.active {
  fill: #ffffff;
  stroke: #00ff00;
}

.preview-point {
  fill: rgba(0, 255, 0, 0.5);
  stroke: #00ff00;
  stroke-width: 1;
  pointer-events: none;
}
</style>
