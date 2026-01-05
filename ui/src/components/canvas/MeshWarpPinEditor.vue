<template>
  <div class="mesh-warp-pin-editor">
    <!-- Tool tip popup -->
    <div v-if="layerId && isActive" class="tool-tip-popup">
      {{ activeToolTip }}
    </div>

    <!-- Warp toolbar (shown when a spline layer with warp mode is active) -->
    <div v-if="layerId && isActive" class="warp-toolbar">
      <!-- Pin Tools -->
      <div class="toolbar-group pin-tools">
        <!-- Position Pin Tool -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: pinTool === 'position' }"
          @click="setPinTool('position')"
          title="Position Pin - Click to add, drag to move"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <circle cx="12" cy="12" r="6" fill="none" stroke="currentColor" stroke-width="2"/>
            <circle cx="12" cy="12" r="2" fill="currentColor"/>
          </svg>
          <span class="tool-label">Position</span>
        </button>

        <!-- Rotation Pin Tool -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: pinTool === 'rotation' }"
          @click="setPinTool('rotation')"
          title="Rotation Pin - Controls local rotation"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <circle cx="12" cy="12" r="6" fill="none" stroke="currentColor" stroke-width="2"/>
            <path d="M12 6v6l4 4" fill="none" stroke="currentColor" stroke-width="2"/>
          </svg>
          <span class="tool-label">Rotation</span>
        </button>

        <!-- Starch Pin Tool -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: pinTool === 'starch' }"
          @click="setPinTool('starch')"
          title="Starch Pin - Adds stiffness to area"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <rect x="8" y="8" width="8" height="8" fill="none" stroke="currentColor" stroke-width="2"/>
            <circle cx="12" cy="12" r="2" fill="currentColor"/>
          </svg>
          <span class="tool-label">Starch</span>
        </button>

        <!-- Delete Pin Tool -->
        <button
          class="toolbar-btn icon-btn"
          :class="{ active: pinTool === 'delete' }"
          @click="setPinTool('delete')"
          title="Delete Pin - Click pin to remove"
        >
          <svg viewBox="0 0 24 24" width="14" height="14">
            <circle cx="12" cy="12" r="6" fill="none" stroke="currentColor" stroke-width="2"/>
            <path d="M9 9l6 6M15 9l-6 6" stroke="currentColor" stroke-width="2"/>
          </svg>
          <span class="tool-label">Delete</span>
        </button>
      </div>

      <div class="toolbar-separator"></div>

      <!-- Pin Properties (when pin selected) -->
      <div class="toolbar-group" v-if="selectedPin">
        <label class="property-label">
          Radius:
          <input
            type="range"
            v-model.number="selectedPinRadius"
            min="10"
            max="200"
            step="5"
            class="property-slider"
          />
          <span class="property-value">{{ selectedPinRadius }}px</span>
        </label>
        <label class="property-label" v-if="selectedPin.type === 'starch'">
          Stiffness:
          <input
            type="range"
            v-model.number="selectedPinStiffness"
            min="0"
            max="1"
            step="0.1"
            class="property-slider"
          />
          <span class="property-value">{{ Math.round(selectedPinStiffness * 100) }}%</span>
        </label>
      </div>

      <div class="toolbar-info">
        {{ pins.length }} pins{{ selectedPin ? ' (1 selected)' : '' }}
      </div>
    </div>

    <!-- Pin visuals rendered via SVG overlay -->
    <svg
      v-if="layerId && isActive"
      class="pin-overlay"
      :viewBox="`0 0 ${canvasWidth} ${canvasHeight}`"
      :style="overlayStyle"
      @mousedown="handleMouseDown"
      @mousemove="handleMouseMove"
      @mouseup="handleMouseUp"
      @mouseleave="handleMouseUp"
    >
      <!-- Influence radius circles -->
      <template v-for="pin in pins" :key="`radius-${pin.id}`">
        <circle
          :cx="pin.position.value.x"
          :cy="pin.position.value.y"
          :r="pin.radius"
          class="pin-radius"
          :class="{ selected: selectedPinId === pin.id }"
          :style="{
            stroke: getPinColor(pin.type),
            opacity: selectedPinId === pin.id ? 0.4 : 0.2
          }"
        />
      </template>

      <!-- Pin markers -->
      <template v-for="pin in pins" :key="`pin-${pin.id}`">
        <!-- Position pin marker -->
        <g
          v-if="pin.type === 'position'"
          :transform="`translate(${pin.position.value.x}, ${pin.position.value.y})`"
          class="pin-marker position-pin"
          :class="{ selected: selectedPinId === pin.id, dragging: draggingPinId === pin.id }"
        >
          <circle r="8" :fill="getPinColor('position')" />
          <circle r="3" fill="white" />
        </g>

        <!-- Rotation pin marker -->
        <g
          v-else-if="pin.type === 'rotation'"
          :transform="`translate(${pin.position.value.x}, ${pin.position.value.y})`"
          class="pin-marker rotation-pin"
          :class="{ selected: selectedPinId === pin.id, dragging: draggingPinId === pin.id }"
        >
          <circle r="8" :fill="getPinColor('rotation')" />
          <path d="M0 -4v4h4" fill="none" stroke="white" stroke-width="1.5" />
        </g>

        <!-- Starch pin marker -->
        <g
          v-else-if="pin.type === 'starch'"
          :transform="`translate(${pin.position.value.x}, ${pin.position.value.y})`"
          class="pin-marker starch-pin"
          :class="{ selected: selectedPinId === pin.id, dragging: draggingPinId === pin.id }"
        >
          <rect x="-6" y="-6" width="12" height="12" :fill="getPinColor('starch')" />
          <circle r="2" fill="white" />
        </g>
      </template>
    </svg>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref, watch } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import type { WarpPin, WarpPinType } from "@/types/meshWarp";
import { createDefaultWarpPin } from "@/types/meshWarp";

// Props
const props = defineProps<{
  layerId: string | null;
  canvasWidth: number;
  canvasHeight: number;
  isActive: boolean;
}>();

// Emits
const emit = defineEmits<{
  (e: "pin-added", pin: WarpPin): void;
  (e: "pin-removed", pinId: string): void;
  (e: "pin-moved", pinId: string, x: number, y: number): void;
  (e: "pin-selected", pinId: string | null): void;
}>();

// Store
const store = useCompositorStore();

// Local state
const pinTool = ref<WarpPinType | "delete">("position");
const selectedPinId = ref<string | null>(null);
const draggingPinId = ref<string | null>(null);
const dragStartPos = ref<{ x: number; y: number } | null>(null);

// Computed
const pins = computed<WarpPin[]>(() => {
  if (!props.layerId) return [];
  const layer = store.getLayerById(props.layerId);
  if (!layer || layer.type !== "spline") return [];
  // Support both old 'puppetPins' and new 'warpPins' property names
  return (layer.data as any)?.warpPins ?? (layer.data as any)?.puppetPins ?? [];
});

const selectedPin = computed(() => {
  if (!selectedPinId.value) return null;
  return pins.value.find((p) => p.id === selectedPinId.value) ?? null;
});

const _selectedPinRadius = computed({
  get: () => selectedPin.value?.radius ?? 50,
  set: (value: number) => {
    if (selectedPin.value && props.layerId) {
      updatePinProperty(selectedPinId.value!, "radius", value);
    }
  },
});

const _selectedPinStiffness = computed({
  get: () => selectedPin.value?.stiffness ?? 0,
  set: (value: number) => {
    if (selectedPin.value && props.layerId) {
      updatePinProperty(selectedPinId.value!, "stiffness", value);
    }
  },
});

const _activeToolTip = computed(() => {
  switch (pinTool.value) {
    case "position":
      return "Click to add position pin, drag to move";
    case "rotation":
      return "Click to add rotation pin";
    case "starch":
      return "Click to add starch (stiffness) pin";
    case "delete":
      return "Click pin to delete";
    default:
      return "";
  }
});

const _overlayStyle = computed(() => ({
  position: "absolute" as const,
  top: "0",
  left: "0",
  width: "100%",
  height: "100%",
  pointerEvents: props.isActive ? ("auto" as const) : ("none" as const),
}));

// Methods
function _getPinColor(type: WarpPinType): string {
  switch (type) {
    case "position":
      return "#4bcde0";
    case "rotation":
      return "#f5c343";
    case "starch":
      return "#e24b4b";
    default:
      return "#ffffff";
  }
}

function setPinTool(tool: WarpPinType | "delete") {
  pinTool.value = tool;
}

function _handleMouseDown(event: MouseEvent) {
  if (!props.layerId || !props.isActive) return;

  const rect = (event.target as SVGElement).getBoundingClientRect();
  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;

  // Check if clicking on existing pin
  const clickedPin = findPinAt(x, y);

  if (clickedPin) {
    if (pinTool.value === "delete") {
      // Delete the pin
      removePinFromLayer(clickedPin.id);
      emit("pin-removed", clickedPin.id);
    } else {
      // Select and start dragging
      selectedPinId.value = clickedPin.id;
      draggingPinId.value = clickedPin.id;
      dragStartPos.value = { x, y };
      emit("pin-selected", clickedPin.id);
    }
  } else if (pinTool.value !== "delete") {
    // Add new pin
    const newPin = addPinToLayer(x, y, pinTool.value as WarpPinType);
    if (newPin) {
      selectedPinId.value = newPin.id;
      emit("pin-added", newPin);
      emit("pin-selected", newPin.id);
    }
  }
}

function _handleMouseMove(event: MouseEvent) {
  if (!draggingPinId.value || !props.layerId) return;

  const rect = (event.target as SVGElement).getBoundingClientRect();
  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;

  // Update pin position
  updatePinPosition(draggingPinId.value, x, y);
  emit("pin-moved", draggingPinId.value, x, y);
}

function _handleMouseUp() {
  draggingPinId.value = null;
  dragStartPos.value = null;
}

function findPinAt(x: number, y: number): WarpPin | null {
  const hitRadius = 12; // Click tolerance
  for (const pin of pins.value) {
    const dx = pin.position.value.x - x;
    const dy = pin.position.value.y - y;
    if (Math.sqrt(dx * dx + dy * dy) <= hitRadius) {
      return pin;
    }
  }
  return null;
}

function addPinToLayer(
  x: number,
  y: number,
  type: WarpPinType,
): WarpPin | null {
  if (!props.layerId) return null;

  const id = `pin_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
  const newPin = createDefaultWarpPin(id, x, y, type);

  // Get current pins and add new one
  const layer = store.getLayerById(props.layerId);
  if (!layer) return null;

  // Support both old and new property names, prefer new
  const currentPins =
    (layer.data as any)?.warpPins ?? (layer.data as any)?.puppetPins ?? [];
  store.updateLayer(props.layerId, {
    data: {
      ...(layer.data as any),
      warpPins: [...currentPins, newPin],
    },
  });

  return newPin;
}

function removePinFromLayer(pinId: string): void {
  if (!props.layerId) return;

  const layer = store.getLayerById(props.layerId);
  if (!layer) return;

  const currentPins: WarpPin[] =
    (layer.data as any)?.warpPins ?? (layer.data as any)?.puppetPins ?? [];
  store.updateLayer(props.layerId, {
    data: {
      ...(layer.data as any),
      warpPins: currentPins.filter((p) => p.id !== pinId),
    },
  });

  if (selectedPinId.value === pinId) {
    selectedPinId.value = null;
    emit("pin-selected", null);
  }
}

function updatePinPosition(pinId: string, x: number, y: number): void {
  if (!props.layerId) return;

  const layer = store.getLayerById(props.layerId);
  if (!layer) return;

  const currentPins: WarpPin[] =
    (layer.data as any)?.warpPins ?? (layer.data as any)?.puppetPins ?? [];
  const updatedPins = currentPins.map((p) => {
    if (p.id === pinId) {
      return {
        ...p,
        position: {
          ...p.position,
          value: { x, y },
        },
      };
    }
    return p;
  });

  store.updateLayer(props.layerId, {
    data: {
      ...(layer.data as any),
      warpPins: updatedPins,
    },
  });
}

function updatePinProperty(pinId: string, property: string, value: any): void {
  if (!props.layerId) return;

  const layer = store.getLayerById(props.layerId);
  if (!layer) return;

  const currentPins: WarpPin[] =
    (layer.data as any)?.warpPins ?? (layer.data as any)?.puppetPins ?? [];
  const updatedPins = currentPins.map((p) => {
    if (p.id === pinId) {
      return {
        ...p,
        [property]: value,
      };
    }
    return p;
  });

  store.updateLayer(props.layerId, {
    data: {
      ...(layer.data as any),
      warpPins: updatedPins,
    },
  });
}

// Keyboard shortcuts
function handleKeyDown(event: KeyboardEvent) {
  if (!props.isActive) return;

  switch (event.key.toLowerCase()) {
    case "p":
      setPinTool("position");
      break;
    case "r":
      setPinTool("rotation");
      break;
    case "s":
      setPinTool("starch");
      break;
    case "d":
    case "delete":
    case "backspace":
      if (selectedPinId.value) {
        removePinFromLayer(selectedPinId.value);
        emit("pin-removed", selectedPinId.value);
      } else {
        setPinTool("delete");
      }
      break;
    case "escape":
      selectedPinId.value = null;
      emit("pin-selected", null);
      break;
  }
}

// Lifecycle
onMounted(() => {
  window.addEventListener("keydown", handleKeyDown);
});

onUnmounted(() => {
  window.removeEventListener("keydown", handleKeyDown);
});

// Watch for layer changes
watch(
  () => props.layerId,
  () => {
    selectedPinId.value = null;
    emit("pin-selected", null);
  },
);
</script>

<style scoped>
.mesh-warp-pin-editor {
  position: absolute;
  inset: 0;
  pointer-events: none;
}

.tool-tip-popup {
  position: absolute;
  top: 8px;
  left: 50%;
  transform: translateX(-50%);
  background: rgba(0, 0, 0, 0.8);
  color: #ddd;
  padding: 6px 12px;
  border-radius: 4px;
  font-size: 11px;
  z-index: 100;
  pointer-events: none;
}

.warp-toolbar {
  position: absolute;
  top: 8px;
  left: 8px;
  background: var(--panel-bg, #1e1e1e);
  border: 1px solid var(--border-color, #333);
  border-radius: 4px;
  padding: 4px;
  display: flex;
  gap: 8px;
  align-items: center;
  z-index: 100;
  pointer-events: auto;
}

.toolbar-group {
  display: flex;
  gap: 2px;
  align-items: center;
}

.pin-tools {
  display: flex;
  gap: 2px;
}

.toolbar-btn {
  background: transparent;
  border: 1px solid transparent;
  border-radius: 3px;
  color: var(--text-color, #ccc);
  padding: 4px 8px;
  cursor: pointer;
  font-size: 11px;
  display: flex;
  align-items: center;
  gap: 4px;
  transition: all 0.15s;
}

.toolbar-btn:hover {
  background: rgba(255, 255, 255, 0.1);
}

.toolbar-btn.active {
  background: var(--accent-color, #4a9eff);
  color: white;
}

.icon-btn svg {
  width: 14px;
  height: 14px;
}

.tool-label {
  font-size: 10px;
}

.toolbar-separator {
  width: 1px;
  height: 20px;
  background: var(--border-color, #333);
}

.property-label {
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: 10px;
  color: var(--text-muted, #888);
}

.property-slider {
  width: 60px;
  height: 4px;
}

.property-value {
  font-size: 10px;
  color: var(--text-color, #ccc);
  min-width: 40px;
}

.toolbar-info {
  font-size: 10px;
  color: var(--text-muted, #888);
  padding-left: 8px;
}

.pin-overlay {
  position: absolute;
  inset: 0;
  overflow: visible;
}

.pin-radius {
  fill: none;
  stroke-width: 1;
  stroke-dasharray: 4 4;
  pointer-events: none;
}

.pin-radius.selected {
  stroke-dasharray: none;
}

.pin-marker {
  cursor: pointer;
  transition: transform 0.1s;
}

.pin-marker:hover {
  transform: scale(1.2);
}

.pin-marker.selected {
  filter: drop-shadow(0 0 4px white);
}

.pin-marker.dragging {
  cursor: grabbing;
}

.position-pin circle:first-child {
  stroke: white;
  stroke-width: 1;
}

.rotation-pin circle:first-child {
  stroke: white;
  stroke-width: 1;
}

.starch-pin rect {
  stroke: white;
  stroke-width: 1;
}
</style>
