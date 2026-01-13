<template>
  <div class="mask-editor">
    <!-- Mask path visualization and control points via SVG overlay -->
    <!-- CSS transform applied via overlayStyle keeps masks aligned during pan/zoom -->
    <svg
      class="mask-overlay"
      :viewBox="`0 0 ${canvasWidth} ${canvasHeight}`"
      :style="overlayStyle"
      @mousedown="handleMouseDown"
      @mousemove="handleMouseMove"
      @mouseup="handleMouseUp"
      @mouseleave="handleMouseUp"
    >
      <!-- Render each mask's path -->
      <template v-for="mask in visibleMasks" :key="`mask-path-${mask.id}`">
        <path
          v-if="getMaskPathData(mask)"
          :d="getMaskPathData(mask)"
          class="mask-path"
          :class="{
            selected: selectedMaskId === mask.id,
            inverted: mask.inverted,
            disabled: !mask.enabled
          }"
          :style="{
            stroke: mask.color,
            fill: selectedMaskId === mask.id ? `${mask.color}20` : 'none'
          }"
          @click.stop="selectMask(mask.id)"
        />
      </template>

      <!-- Handle lines for selected mask's selected vertex -->
      <template v-if="selectedMask && selectedVertexIndex !== null">
        <line
          v-if="selectedVertex?.inTangentX || selectedVertex?.inTangentY"
          :x1="selectedVertex.x"
          :y1="selectedVertex.y"
          :x2="selectedVertex.x + (selectedVertex.inTangentX || 0)"
          :y2="selectedVertex.y + (selectedVertex.inTangentY || 0)"
          class="handle-line"
          :style="{ stroke: selectedMask.color }"
        />
        <line
          v-if="selectedVertex?.outTangentX || selectedVertex?.outTangentY"
          :x1="selectedVertex.x"
          :y1="selectedVertex.y"
          :x2="selectedVertex.x + (selectedVertex.outTangentX || 0)"
          :y2="selectedVertex.y + (selectedVertex.outTangentY || 0)"
          class="handle-line"
          :style="{ stroke: selectedMask.color }"
        />
      </template>

      <!-- Handle points for selected vertex -->
      <template v-if="selectedMask && selectedVertexIndex !== null">
        <circle
          v-if="selectedVertex?.inTangentX || selectedVertex?.inTangentY"
          :cx="selectedVertex.x + (selectedVertex.inTangentX || 0)"
          :cy="selectedVertex.y + (selectedVertex.inTangentY || 0)"
          r="4"
          class="handle-point"
          :class="{ active: dragTarget?.type === 'handleIn' }"
          :style="{ fill: selectedMask.color }"
          @mousedown.stop="startDragHandle('in', $event)"
        />
        <circle
          v-if="selectedVertex?.outTangentX || selectedVertex?.outTangentY"
          :cx="selectedVertex.x + (selectedVertex.outTangentX || 0)"
          :cy="selectedVertex.y + (selectedVertex.outTangentY || 0)"
          r="4"
          class="handle-point"
          :class="{ active: dragTarget?.type === 'handleOut' }"
          :style="{ fill: selectedMask.color }"
          @mousedown.stop="startDragHandle('out', $event)"
        />
      </template>

      <!-- Vertices for selected mask -->
      <template v-if="selectedMask">
        <g v-for="(vertex, index) in selectedMaskVertices" :key="`vertex-${index}`">
          <rect
            v-if="isCornerVertex(vertex)"
            :x="vertex.x - 5"
            :y="vertex.y - 5"
            width="10"
            height="10"
            class="vertex-point corner"
            :class="{ selected: selectedVertexIndex === index }"
            :style="{ stroke: selectedMask.color }"
            @mousedown.stop="startDragVertex(index, $event)"
          />
          <circle
            v-else
            :cx="vertex.x"
            :cy="vertex.y"
            r="6"
            class="vertex-point smooth"
            :class="{ selected: selectedVertexIndex === index }"
            :style="{ stroke: selectedMask.color }"
            @mousedown.stop="startDragVertex(index, $event)"
          />
        </g>
      </template>

      <!-- Preview point when in mask pen mode -->
      <circle
        v-if="previewPoint && isMaskPenMode"
        :cx="previewPoint.x"
        :cy="previewPoint.y"
        r="4"
        class="preview-point"
      />

      <!-- Close path indicator -->
      <circle
        v-if="isMaskPenMode && selectedMaskVertices.length >= 2 && closePathPreview"
        :cx="selectedMaskVertices[0].x"
        :cy="selectedMaskVertices[0].y"
        r="10"
        class="close-indicator"
        @mousedown.stop="closePath"
      />
    </svg>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref, watch } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import type { LayerMask, MaskPath, MaskVertex } from "@/types/project";

interface Props {
  layerId: string | null;
  canvasWidth: number;
  canvasHeight: number;
  zoom: number;
  viewportTransform: number[];
  isMaskPenMode: boolean;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: "maskSelected", maskId: string | null): void;
  (e: "vertexSelected", maskId: string, vertexIndex: number | null): void;
  (e: "maskUpdated", maskId: string): void;
  (e: "pathClosed", maskId: string): void;
}>();

const store = useCompositorStore();
const layerStore = useLayerStore();

// State
const selectedMaskId = ref<string | null>(null);
const selectedVertexIndex = ref<number | null>(null);
const previewPoint = ref<{ x: number; y: number } | null>(null);
const closePathPreview = ref(false);
const dragTarget = ref<{
  type: "vertex" | "handleIn" | "handleOut";
  startX: number;
  startY: number;
} | null>(null);

// Get masks from the active layer
const visibleMasks = computed<LayerMask[]>(() => {
  if (!props.layerId) return [];

  const layer = layerStore.getLayerById(store, props.layerId);
  if (!layer) return [];

  return layer.masks ?? [];
});

// Get the selected mask
const selectedMask = computed<LayerMask | null>(() => {
  if (!selectedMaskId.value) return null;
  return visibleMasks.value.find((m) => m.id === selectedMaskId.value) ?? null;
});

// Get vertices of selected mask
const selectedMaskVertices = computed<MaskVertex[]>(() => {
  if (!selectedMask.value) return [];
  const path = getMaskPathValue(selectedMask.value);
  return path?.vertices ?? [];
});

// Get the selected vertex
const selectedVertex = computed<MaskVertex | null>(() => {
  if (selectedVertexIndex.value === null) return null;
  return selectedMaskVertices.value[selectedVertexIndex.value] ?? null;
});

// Compute CSS transform to keep mask overlay aligned with canvas during pan/zoom.
// viewportTransform: [scaleX, skewX, skewY, scaleY, translateX, translateY]
// We apply translate for pan offset and scale for zoom level.
const overlayStyle = computed(() => {
  const vt = props.viewportTransform;
  // Safely extract pan offsets with NaN/Infinity guards
  const tx = vt && vt.length > 4 && Number.isFinite(vt[4]) ? vt[4] : 0;
  const ty = vt && vt.length > 5 && Number.isFinite(vt[5]) ? vt[5] : 0;
  const zoom = props.zoom > 0 && Number.isFinite(props.zoom) ? props.zoom : 1;

  return {
    transform: `translate(${tx}px, ${ty}px) scale(${zoom})`,
    transformOrigin: 'top left',
  };
});

// Helper to get mask path value (handles animated properties)
function getMaskPathValue(mask: LayerMask): MaskPath | null {
  if (!mask.path) return null;
  // For now, use the static value - animation support can be added later
  return mask.path.value;
}

// Generate SVG path data from mask vertices
function getMaskPathData(mask: LayerMask): string {
  const path = getMaskPathValue(mask);
  if (!path || !path.vertices || path.vertices.length < 2) return "";

  const vertices = path.vertices;
  let d = `M ${vertices[0].x} ${vertices[0].y}`;

  for (let i = 0; i < vertices.length; i++) {
    const current = vertices[i];
    const next = vertices[(i + 1) % vertices.length];

    if (!path.closed && i === vertices.length - 1) break;

    // Control points for cubic bezier
    const cp1x = current.x + (current.outTangentX || 0);
    const cp1y = current.y + (current.outTangentY || 0);
    const cp2x = next.x + (next.inTangentX || 0);
    const cp2y = next.y + (next.inTangentY || 0);

    // Use cubic bezier if any tangents exist
    if (
      current.outTangentX ||
      current.outTangentY ||
      next.inTangentX ||
      next.inTangentY
    ) {
      d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${next.x} ${next.y}`;
    } else {
      d += ` L ${next.x} ${next.y}`;
    }
  }

  if (path.closed) {
    d += " Z";
  }

  return d;
}

// Check if vertex is a corner (no tangents)
function isCornerVertex(vertex: MaskVertex): boolean {
  return (
    !vertex.inTangentX &&
    !vertex.inTangentY &&
    !vertex.outTangentX &&
    !vertex.outTangentY
  );
}

// Convert screen coords to canvas coords
function screenToCanvas(
  screenX: number,
  screenY: number,
): { x: number; y: number } {
  const vt = props.viewportTransform;
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

// Select a mask
function selectMask(maskId: string) {
  selectedMaskId.value = maskId;
  selectedVertexIndex.value = null;
  emit("maskSelected", maskId);
}

// Handle mouse events
function handleMouseDown(event: MouseEvent) {
  if (!props.isMaskPenMode || !props.layerId) return;

  const pos = getMousePos(event);

  // Check if clicking near first vertex to close path
  if (selectedMask.value && selectedMaskVertices.value.length >= 2) {
    const firstVertex = selectedMaskVertices.value[0];
    const dist = Math.sqrt(
      (pos.x - firstVertex.x) ** 2 + (pos.y - firstVertex.y) ** 2,
    );
    if (dist < 15) {
      closePath();
      return;
    }
  }

  // Add new vertex to the selected mask or create new mask
  if (selectedMask.value) {
    addVertex(pos.x, pos.y);
  } else {
    // Create new mask with first vertex
    createNewMask(pos.x, pos.y);
  }
}

function handleMouseMove(event: MouseEvent) {
  const pos = getMousePos(event);

  // Update preview point
  if (props.isMaskPenMode) {
    previewPoint.value = pos;

    // Check for close path preview
    if (selectedMaskVertices.value.length >= 2) {
      const firstVertex = selectedMaskVertices.value[0];
      const dist = Math.sqrt(
        (pos.x - firstVertex.x) ** 2 + (pos.y - firstVertex.y) ** 2,
      );
      closePathPreview.value = dist < 15;
    }
  }

  // Handle dragging
  if (
    dragTarget.value &&
    selectedMask.value &&
    selectedVertexIndex.value !== null
  ) {
    const vertices = [...selectedMaskVertices.value];
    const vertex = { ...vertices[selectedVertexIndex.value] };

    if (dragTarget.value.type === "vertex") {
      // Move vertex and its tangents
      const _dx = pos.x - vertex.x;
      const _dy = pos.y - vertex.y;
      vertex.x = pos.x;
      vertex.y = pos.y;
      // Tangents are relative, so they don't need to be moved
    } else if (dragTarget.value.type === "handleIn") {
      vertex.inTangentX = pos.x - vertex.x;
      vertex.inTangentY = pos.y - vertex.y;
      // Mirror for smooth vertex (Alt key to break tangents)
      if (!event.altKey) {
        vertex.outTangentX = -vertex.inTangentX;
        vertex.outTangentY = -vertex.inTangentY;
      }
    } else if (dragTarget.value.type === "handleOut") {
      vertex.outTangentX = pos.x - vertex.x;
      vertex.outTangentY = pos.y - vertex.y;
      // Mirror for smooth vertex (Alt key to break tangents)
      if (!event.altKey) {
        vertex.inTangentX = -vertex.outTangentX;
        vertex.inTangentY = -vertex.outTangentY;
      }
    }

    vertices[selectedVertexIndex.value] = vertex;
    updateMaskVertices(vertices);
  }
}

function handleMouseUp() {
  dragTarget.value = null;
}

function startDragVertex(index: number, event: MouseEvent) {
  selectedVertexIndex.value = index;
  emit("vertexSelected", selectedMaskId.value!, index);

  if (!props.isMaskPenMode) {
    const pos = getMousePos(event);
    dragTarget.value = {
      type: "vertex",
      startX: pos.x,
      startY: pos.y,
    };
  }
}

function startDragHandle(handleType: "in" | "out", event: MouseEvent) {
  const pos = getMousePos(event);
  dragTarget.value = {
    type: handleType === "in" ? "handleIn" : "handleOut",
    startX: pos.x,
    startY: pos.y,
  };
}

// Create new mask
function createNewMask(x: number, y: number) {
  if (!props.layerId) return;

  const maskId = `mask_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
  const newMask: LayerMask = {
    id: maskId,
    name: `Mask ${visibleMasks.value.length + 1}`,
    enabled: true,
    locked: false,
    mode: "add",
    inverted: false,
    path: {
      id: `path_${maskId}`,
      name: "Mask Path",
      type: "position",
      value: {
        closed: false,
        vertices: [
          {
            x,
            y,
            inTangentX: 0,
            inTangentY: 0,
            outTangentX: 0,
            outTangentY: 0,
          },
        ],
      },
      animated: false,
      keyframes: [],
    },
    opacity: {
      id: `opacity_${maskId}`,
      name: "Mask Opacity",
      type: "number",
      value: 100,
      animated: false,
      keyframes: [],
    },
    feather: {
      id: `feather_${maskId}`,
      name: "Mask Feather",
      type: "number",
      value: 0,
      animated: false,
      keyframes: [],
    },
    expansion: {
      id: `expansion_${maskId}`,
      name: "Mask Expansion",
      type: "number",
      value: 0,
      animated: false,
      keyframes: [],
    },
    color: getNextMaskColor(),
  };

  // Add mask to layer via store
  const layer = layerStore.getLayerById(store, props.layerId);
  if (layer) {
    const masks = [...(layer.masks ?? []), newMask];
    layerStore.updateLayer(store, props.layerId, { masks });
    selectedMaskId.value = maskId;
    selectedVertexIndex.value = 0;
    emit("maskSelected", maskId);
  }
}

// Add vertex to current mask
function addVertex(x: number, y: number) {
  if (!selectedMask.value || !props.layerId) return;

  const newVertex: MaskVertex = {
    x,
    y,
    inTangentX: 0,
    inTangentY: 0,
    outTangentX: 0,
    outTangentY: 0,
  };

  const vertices = [...selectedMaskVertices.value, newVertex];
  updateMaskVertices(vertices);
  selectedVertexIndex.value = vertices.length - 1;
}

// Update mask vertices
function updateMaskVertices(vertices: MaskVertex[]) {
  if (!selectedMask.value || !props.layerId) return;

  const path = getMaskPathValue(selectedMask.value);
  if (!path) return;

  const updatedPath = { ...path, vertices };
  const updatedMask = {
    ...selectedMask.value,
    path: { ...selectedMask.value.path, value: updatedPath },
  };

  const masks = visibleMasks.value.map((m) =>
    m.id === selectedMaskId.value ? updatedMask : m,
  );

  layerStore.updateLayer(store, props.layerId, { masks });
  emit("maskUpdated", selectedMaskId.value!);
}

// Close the mask path
function closePath() {
  if (!selectedMask.value || !props.layerId) return;

  const path = getMaskPathValue(selectedMask.value);
  if (!path) return;

  const updatedPath = { ...path, closed: true };
  const updatedMask = {
    ...selectedMask.value,
    path: { ...selectedMask.value.path, value: updatedPath },
  };

  const masks = visibleMasks.value.map((m) =>
    m.id === selectedMaskId.value ? updatedMask : m,
  );

  layerStore.updateLayer(store, props.layerId, { masks });
  emit("pathClosed", selectedMaskId.value.value!);
}

// Get next mask color from palette
const maskColors = [
  "#FFFF00",
  "#FF00FF",
  "#00FFFF",
  "#FF8800",
  "#88FF00",
  "#0088FF",
];
function getNextMaskColor(): string {
  return maskColors[visibleMasks.value.length % maskColors.length];
}

// Delete selected vertex
function deleteSelectedVertex() {
  if (selectedVertexIndex.value === null || !selectedMask.value) return;

  const vertices = selectedMaskVertices.value.filter(
    (_, i) => i !== selectedVertexIndex.value,
  );

  if (vertices.length === 0) {
    // Delete entire mask if no vertices left
    deleteMask(selectedMaskId.value!);
  } else {
    updateMaskVertices(vertices);
    selectedVertexIndex.value = Math.min(
      selectedVertexIndex.value,
      vertices.length - 1,
    );
  }
}

// Delete mask
function deleteMask(maskId: string) {
  if (!props.layerId) return;

  const masks = visibleMasks.value.filter((m) => m.id !== maskId);
  layerStore.updateLayer(store, props.layerId, { masks });

  if (selectedMaskId.value === maskId) {
    selectedMaskId.value = masks.length > 0 ? masks[0].id : null;
    selectedVertexIndex.value = null;
    emit("maskSelected", selectedMaskId.value);
  }
}

// Keyboard handling
function handleKeyDown(event: KeyboardEvent) {
  if (event.key === "Delete" || event.key === "Backspace") {
    if (selectedVertexIndex.value !== null) {
      deleteSelectedVertex();
      event.preventDefault();
    }
  } else if (event.key === "Escape") {
    selectedVertexIndex.value = null;
    selectedMaskId.value = null;
    emit("maskSelected", null);
  }
}

// Clear selection when layer changes
watch(
  () => props.layerId,
  () => {
    selectedMaskId.value = null;
    selectedVertexIndex.value = null;
  },
);

onMounted(() => {
  window.addEventListener("keydown", handleKeyDown);
});

onUnmounted(() => {
  window.removeEventListener("keydown", handleKeyDown);
});

// Expose for external access
defineExpose({
  selectedMaskId,
  selectedVertexIndex,
  selectMask,
  deleteMask,
  clearSelection: () => {
    selectedMaskId.value = null;
    selectedVertexIndex.value = null;
  },
});
</script>

<style scoped>
.mask-editor {
  position: absolute;
  inset: 0;
  pointer-events: none;
}

.mask-overlay {
  width: 100%;
  height: 100%;
  pointer-events: all;
}

/* Mask path */
.mask-path {
  fill: none;
  stroke-width: 2;
  cursor: pointer;
  transition: stroke-width 0.1s;
}

.mask-path:hover {
  stroke-width: 3;
}

.mask-path.selected {
  stroke-width: 2.5;
  stroke-dasharray: none;
}

.mask-path.inverted {
  stroke-dasharray: 8 4;
}

.mask-path.disabled {
  opacity: 0.3;
}

/* Vertex points */
.vertex-point {
  fill: #ffffff;
  stroke-width: 2;
  cursor: pointer;
  transition: fill 0.1s, transform 0.1s;
}

.vertex-point:hover {
  fill: currentColor;
}

.vertex-point.selected {
  fill: currentColor;
  stroke: #ffffff !important;
}

.vertex-point.corner {
  /* Square representation is via rect element */
}

.vertex-point.smooth {
  /* Circle representation */
}

/* Handle lines and points */
.handle-line {
  stroke-width: 1;
  stroke-dasharray: 4 2;
  opacity: 0.8;
}

.handle-point {
  stroke: #ffffff;
  stroke-width: 1.5;
  cursor: pointer;
}

.handle-point:hover,
.handle-point.active {
  stroke-width: 2;
  r: 5;
}

/* Preview elements */
.preview-point {
  fill: rgba(255, 255, 0, 0.5);
  stroke: #ffff00;
  stroke-width: 1;
  pointer-events: none;
}

.close-indicator {
  fill: rgba(0, 255, 0, 0.2);
  stroke: #00ff00;
  stroke-width: 2;
  stroke-dasharray: 4 2;
  cursor: pointer;
}

.close-indicator:hover {
  fill: rgba(0, 255, 0, 0.4);
}
</style>
