<template>
  <div class="curve-editor">
    <CurveEditorHeader
      :mode="mode"
      :preset-list="presetList"
      :auto-select-nearby="autoSelectNearby"
      :snap-enabled="snapEnabled"
      :is-preset-active="isPresetActive"
      @update:mode="mode = $event"
      @update:auto-select-nearby="autoSelectNearby = $event"
      @update:snap-enabled="snapEnabled = $event"
      @apply-preset="applyPreset"
      @fit-to-view="fitToView"
      @close="emit('close')"
    />

    <div class="curve-content">
      <CurveEditorPropertyList
        :animatable-properties="animatableProperties"
        :selected-property-ids="selectedPropertyIds"
        :visible-property-ids="visiblePropertyIds"
        :visible-dimensions="visibleDimensions"
        :all-properties-visible="allPropertiesVisible"
        :get-property-color="getPropertyColor"
        :has-dimension="hasDimension"
        @toggle-all-properties="toggleAllProperties"
        @toggle-property="toggleProperty"
        @toggle-property-visibility="togglePropertyVisibility"
        @toggle-dimension="toggleDimension"
      />

      <!-- Main graph area -->
      <div class="curve-main">
        <!-- Timeline ruler -->
        <div class="time-ruler" ref="timeRulerRef">
          <canvas ref="timeRulerCanvas" @click="onTimeRulerClick" />
        </div>

        <!-- Graph canvas -->
        <div class="curve-canvas-container" ref="canvasContainerRef">
          <canvas
            ref="canvasRef"
            @mousedown="handleMouseDown"
            @mousemove="handleMouseMove"
            @mouseup="handleMouseUp"
            @mouseleave="handleMouseUp"
            @wheel="handleWheel"
            @contextmenu.prevent="showContextMenu"
          />

          <!-- Keyframe selection box -->
          <div
            v-if="selectionBox"
            class="selection-box"
            :style="{
              left: selectionBox.x + 'px',
              top: selectionBox.y + 'px',
              width: selectionBox.width + 'px',
              height: selectionBox.height + 'px'
            }"
          />

          <!-- Handle controls (SVG overlay) -->
          <svg
            class="handle-overlay"
            :viewBox="`0 0 ${canvasWidth} ${canvasHeight}`"
          >
            <!-- Keyframe handles for each visible property -->
            <g
              v-for="prop in visibleProperties"
              :key="prop.id"
              class="property-handles"
            >
              <template v-for="(kf, kfIndex) in prop.keyframes" :key="kfIndex">
                <!-- Keyframe diamond -->
                <g
                  v-if="isKeyframeInView(kf)"
                  class="keyframe-marker"
                  :class="{
                    selected: isKeyframeSelected(prop.id, kfIndex),
                    hovered: hoveredKeyframe?.propId === prop.id && hoveredKeyframe?.index === kfIndex
                  }"
                  @mousedown.stop="onKeyframeMouseDown(prop.id, kfIndex, $event)"
                >
                  <rect
                    :x="getKeyframeScreenX(kf) - 5"
                    :y="getKeyframeScreenY(prop, kf) - 5"
                    width="10"
                    height="10"
                    :fill="getPropertyColor(prop.id)"
                    transform-origin="center"
                    :transform="`rotate(45, ${getKeyframeScreenX(kf)}, ${getKeyframeScreenY(prop, kf)})`"
                  />
                </g>

                <!-- Bezier handles - show when selected and not hold/linear without handles -->
                <g
                  v-if="isKeyframeSelected(prop.id, kfIndex) && kf.interpolation !== 'hold'"
                  class="bezier-handles"
                >
                  <!-- Out handle (to next keyframe) - show if enabled or if bezier -->
                  <g
                    v-if="prop.keyframes[kfIndex + 1] && (kf.outHandle.enabled || kf.interpolation === 'bezier')"
                    class="handle out-handle"
                  >
                    <line
                      :x1="getKeyframeScreenX(kf)"
                      :y1="getKeyframeScreenY(prop, kf)"
                      :x2="getOutHandleX(prop, kfIndex)"
                      :y2="getOutHandleY(prop, kfIndex)"
                      class="handle-line"
                    />
                    <circle
                      :cx="getOutHandleX(prop, kfIndex)"
                      :cy="getOutHandleY(prop, kfIndex)"
                      r="5"
                      class="handle-point"
                      :class="{ dragging: dragTarget?.type === 'outHandle' && dragTarget?.propId === prop.id && dragTarget?.index === kfIndex }"
                      @mousedown.stop="startDragHandle('outHandle', prop.id, kfIndex, $event)"
                    />
                  </g>

                  <!-- In handle (from previous keyframe) - show if enabled or if bezier -->
                  <g
                    v-if="kfIndex > 0 && (kf.inHandle.enabled || kf.interpolation === 'bezier')"
                    class="handle in-handle"
                  >
                    <line
                      :x1="getKeyframeScreenX(kf)"
                      :y1="getKeyframeScreenY(prop, kf)"
                      :x2="getInHandleX(prop, kfIndex)"
                      :y2="getInHandleY(prop, kfIndex)"
                      class="handle-line"
                    />
                    <circle
                      :cx="getInHandleX(prop, kfIndex)"
                      :cy="getInHandleY(prop, kfIndex)"
                      r="5"
                      class="handle-point"
                      :class="{ dragging: dragTarget?.type === 'inHandle' && dragTarget?.propId === prop.id && dragTarget?.index === kfIndex }"
                      @mousedown.stop="startDragHandle('inHandle', prop.id, kfIndex, $event)"
                    />
                  </g>
                </g>
              </template>
            </g>

            <!-- Current time indicator -->
            <line
              :x1="currentFrameScreenX"
              :y1="0"
              :x2="currentFrameScreenX"
              :y2="canvasHeight"
              class="current-time-line"
            />
          </svg>
        </div>

        <!-- Value axis -->
        <div class="value-axis" ref="valueAxisRef">
          <canvas ref="valueAxisCanvas" />
        </div>
      </div>
    </div>

    <!-- Keyframe info panel -->
    <div v-if="selectedKeyframes.length > 0" class="keyframe-info-panel">
      <div class="info-row">
        <span class="info-label">Frame:</span>
        <input
          type="number"
          :value="selectedKeyframes[0]?.keyframe.frame"
          @change="updateSelectedKeyframeFrame"
          class="info-input"
        />
      </div>
      <div class="info-row">
        <span class="info-label">Value:</span>
        <input
          type="number"
          :value="getKeyframeDisplayValue(selectedKeyframes[0])"
          @change="updateSelectedKeyframeValue"
          class="info-input"
          step="0.1"
        />
      </div>
      <div class="info-row">
        <span class="info-label">Interpolation:</span>
        <select
          :value="selectedKeyframes[0]?.keyframe.interpolation"
          @change="updateSelectedKeyframeInterpolation"
          class="info-select"
        >
          <option value="linear">Linear</option>
          <option value="bezier">Bezier</option>
          <option value="hold">Hold</option>
        </select>
      </div>
    </div>

    <!-- Context menu -->
    <div
      v-if="contextMenu"
      class="context-menu"
      :style="{ left: contextMenu.x + 'px', top: contextMenu.y + 'px' }"
      @click="contextMenu = null"
    >
      <button @click="addKeyframeAtPosition">Add Keyframe</button>
      <button @click="deleteSelectedKeyframes" :disabled="selectedKeyframes.length === 0">Delete Keyframe(s)</button>
      <hr />
      <button @click="copyKeyframes" :disabled="selectedKeyframes.length === 0">Copy</button>
      <button @click="pasteKeyframes" :disabled="!clipboard">Paste</button>
      <hr />
      <button @click="selectAllKeyframes">Select All</button>
      <button @click="invertSelection">Invert Selection</button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, reactive, ref, watch } from "vue";
import { EASING_PRESETS } from "@/services/interpolation";
import { findNearestSnap } from "@/services/timelineSnap";
import { useCompositorStore } from "@/stores/compositorStore";
import { useAudioStore } from "@/stores/audioStore";
import { useKeyframeStore } from "@/stores/keyframeStore";
import { useAnimationStore } from "@/stores/animationStore";
import type { AnimatableProperty, Keyframe, PropertyValue } from "@/types/project";
import type { CurveMode, EasingPreset } from "./CurveEditorHeader.vue";

const emit = defineEmits<(e: "close") => void>();

const store = useCompositorStore();
const audioStore = useAudioStore();
const keyframeStore = useKeyframeStore();
const animationStore = useAnimationStore();

// Refs
const canvasRef = ref<HTMLCanvasElement | null>(null);
const canvasContainerRef = ref<HTMLDivElement | null>(null);
const timeRulerRef = ref<HTMLDivElement | null>(null);
const timeRulerCanvas = ref<HTMLCanvasElement | null>(null);
const valueAxisRef = ref<HTMLDivElement | null>(null);
const valueAxisCanvas = ref<HTMLCanvasElement | null>(null);

const canvasWidth = ref(400);
const canvasHeight = ref(200);

// Mode: value graph or speed graph
const mode = ref<CurveMode>("value");

// View state
const viewState = reactive({
  frameStart: 0,
  frameEnd: 100,
  valueMin: 0,
  valueMax: 100,
  zoom: 1,
});

// Selection state
const selectedPropertyIds = ref<string[]>([]);
const visiblePropertyIds = ref<string[]>([]);
const visibleDimensions = ref<Record<string, string[]>>({});
const selectedKeyframes = ref<
  Array<{ propId: string; index: number; keyframe: Keyframe<PropertyValue> }>
>([]);
const hoveredKeyframe = ref<{ propId: string; index: number } | null>(null);

// Interaction state
const dragTarget = ref<{
  type: "keyframe" | "inHandle" | "outHandle" | "pan" | "select";
  propId?: string;
  index?: number;
  startX?: number;
  startY?: number;
} | null>(null);
const selectionBox = ref<{
  x: number;
  y: number;
  width: number;
  height: number;
} | null>(null);
const contextMenu = ref<{ x: number; y: number } | null>(null);
const clipboard = ref<Keyframe<PropertyValue>[] | null>(null);

// Options
const snapEnabled = ref(false);
const autoSelectNearby = ref(true);

// Graph margins
const margin = { top: 10, right: 10, bottom: 10, left: 10 };

// Property colors
const propertyColors: Record<string, string> = {
  Position: "#ff6b6b",
  "Position.x": "#ff6b6b",
  "Position.y": "#4ecdc4",
  "Position.z": "#45b7d1",
  Scale: "#f7dc6f",
  "Scale.x": "#f7dc6f",
  "Scale.y": "#82e0aa",
  "Scale.z": "#85c1e9",
  Rotation: "#bb8fce",
  Opacity: "#f8b739",
  default: "#7c9cff",
};

// Presets list
const presetList: EasingPreset[] = [
  { key: "linear", label: "Linear", shortLabel: "Lin" },
  { key: "easeIn", label: "Ease In", shortLabel: "In" },
  { key: "easeOut", label: "Ease Out", shortLabel: "Out" },
  { key: "easeInOut", label: "Ease In/Out", shortLabel: "I/O" },
  { key: "easeInCubic", label: "Ease In Cubic", shortLabel: "In3" },
  { key: "easeOutCubic", label: "Ease Out Cubic", shortLabel: "Ou3" },
  { key: "easeInOutCubic", label: "Ease In/Out Cubic", shortLabel: "IO3" },
  { key: "easeInBack", label: "Ease In Back", shortLabel: "InB" },
  { key: "easeOutBack", label: "Ease Out Back", shortLabel: "OuB" },
];

// Get all animatable properties from selected layer
const animatableProperties = computed((): AnimatableProperty<PropertyValue>[] => {
  const layer = store.selectedLayer;
  if (!layer) return [];

  const props: AnimatableProperty<PropertyValue>[] = [];
  const t = layer.transform;

  // Position - check if dimensions are separated
  if (t.separateDimensions?.position && t.positionX && t.positionY) {
    // Separated: show individual X, Y, Z properties
    props.push(t.positionX);
    props.push(t.positionY);
    if (t.positionZ) props.push(t.positionZ);
  } else {
    // Combined: show single position property
    props.push(t.position);
  }

  // Scale - check if dimensions are separated
  if (t.separateDimensions?.scale && t.scaleX && t.scaleY) {
    // Separated: show individual X, Y, Z properties
    props.push(t.scaleX);
    props.push(t.scaleY);
    if (t.scaleZ) props.push(t.scaleZ);
  } else {
    // Combined: show single scale property
    props.push(t.scale);
  }

  // Rotation
  props.push(t.rotation);

  // Opacity
  props.push(layer.opacity);

  // Custom properties
  props.push(...layer.properties);

  return props;
});

// Visible properties
const visibleProperties = computed(() => {
  return animatableProperties.value.filter(
    (p) => visiblePropertyIds.value.includes(p.id) && p.animated,
  );
});

const allPropertiesVisible = computed(() => {
  return animatableProperties.value.every((p) =>
    visiblePropertyIds.value.includes(p.id),
  );
});

// Current frame screen position
const currentFrameScreenX = computed(() => {
  return frameToScreenX(store.currentFrame);
});

// Coordinate conversion functions
function frameToScreenX(frame: number): number {
  const graphWidth = canvasWidth.value - margin.left - margin.right;
  const t =
    (frame - viewState.frameStart) /
    (viewState.frameEnd - viewState.frameStart);
  return margin.left + t * graphWidth;
}

function screenXToFrame(screenX: number): number {
  const graphWidth = canvasWidth.value - margin.left - margin.right;
  const t = (screenX - margin.left) / graphWidth;
  return viewState.frameStart + t * (viewState.frameEnd - viewState.frameStart);
}

function valueToScreenY(value: number): number {
  const graphHeight = canvasHeight.value - margin.top - margin.bottom;
  const t =
    (value - viewState.valueMin) / (viewState.valueMax - viewState.valueMin);
  return canvasHeight.value - margin.bottom - t * graphHeight;
}

function screenYToValue(screenY: number): number {
  const graphHeight = canvasHeight.value - margin.top - margin.bottom;
  const t = (canvasHeight.value - margin.bottom - screenY) / graphHeight;
  return viewState.valueMin + t * (viewState.valueMax - viewState.valueMin);
}

// Keyframe position helpers
function getKeyframeScreenX(kf: Keyframe<PropertyValue>): number {
  return frameToScreenX(kf.frame);
}

function getKeyframeScreenY(
  _prop: AnimatableProperty<PropertyValue>,
  kf: Keyframe<PropertyValue>,
): number {
  const value =
    typeof kf.value === "number"
      ? kf.value
      : typeof kf.value === "object"
        ? (kf.value.x ?? kf.value)
        : 0;
  return valueToScreenY(value);
}

function getKeyframeDisplayValue(
  selection:
    | { propId: string; index: number; keyframe: Keyframe<PropertyValue> }
    | undefined,
): number {
  if (!selection) return 0;
  const value = selection.keyframe.value;
  return typeof value === "number"
    ? value
    : typeof value === "object"
      ? (value.x ?? 0)
      : 0;
}

// Handle position helpers - using new absolute frame/value offsets
function getOutHandleX(
  prop: AnimatableProperty<PropertyValue>,
  kfIndex: number,
): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.outHandle.enabled) return frameToScreenX(kf.frame);

  // outHandle.frame is absolute offset from keyframe (positive = forward)
  const handleFrame = kf.frame + kf.outHandle.frame;
  return frameToScreenX(handleFrame);
}

function getOutHandleY(
  prop: AnimatableProperty<PropertyValue>,
  kfIndex: number,
): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.outHandle.enabled)
    return valueToScreenY(getNumericValue(kf.value));

  // outHandle.value is absolute offset from keyframe value
  const handleValue = getNumericValue(kf.value) + kf.outHandle.value;
  return valueToScreenY(handleValue);
}

function getInHandleX(prop: AnimatableProperty<PropertyValue>, kfIndex: number): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.inHandle.enabled) return frameToScreenX(kf.frame);

  // inHandle.frame is absolute offset from keyframe (typically negative = backward)
  const handleFrame = kf.frame + kf.inHandle.frame;
  return frameToScreenX(handleFrame);
}

function getInHandleY(prop: AnimatableProperty<PropertyValue>, kfIndex: number): number {
  const kf = prop.keyframes[kfIndex];
  if (!kf || !kf.inHandle.enabled)
    return valueToScreenY(getNumericValue(kf.value));

  // inHandle.value is absolute offset from keyframe value
  const handleValue = getNumericValue(kf.value) + kf.inHandle.value;
  return valueToScreenY(handleValue);
}

function getNumericValue(value: PropertyValue): number {
  if (typeof value === "number") return value;
  if (typeof value === "object" && value !== null) {
    if ("x" in value && typeof value.x === "number") return value.x;
    if ("y" in value && typeof value.y === "number") return value.y;
    if ("z" in value && typeof value.z === "number") return value.z;
  }
  return 0;
}

// Utility functions
function getPropertyColor(propId: string): string {
  const prop = animatableProperties.value.find((p) => p.id === propId);
  if (!prop) return propertyColors.default;
  return propertyColors[prop.name] ?? propertyColors.default;
}

function isKeyframeInView(kf: Keyframe<PropertyValue>): boolean {
  return kf.frame >= viewState.frameStart && kf.frame <= viewState.frameEnd;
}

function isKeyframeSelected(propId: string, index: number): boolean {
  return selectedKeyframes.value.some(
    (sk) => sk.propId === propId && sk.index === index,
  );
}

function hasDimension(prop: AnimatableProperty<PropertyValue>, dim: string): boolean {
  if (!prop.animated || prop.keyframes.length === 0) return false;
  const value = prop.keyframes[0].value;
  return typeof value === "object" && dim in value;
}

// Property management
function toggleProperty(propId: string): void {
  const index = selectedPropertyIds.value.indexOf(propId);
  if (index === -1) {
    selectedPropertyIds.value.push(propId);
  } else {
    selectedPropertyIds.value.splice(index, 1);
  }
}

function togglePropertyVisibility(propId: string): void {
  const index = visiblePropertyIds.value.indexOf(propId);
  if (index === -1) {
    visiblePropertyIds.value.push(propId);
  } else {
    visiblePropertyIds.value.splice(index, 1);
  }
  updateViewBounds();
}

function toggleAllProperties(): void {
  if (allPropertiesVisible.value) {
    visiblePropertyIds.value = [];
  } else {
    visiblePropertyIds.value = animatableProperties.value.map((p) => p.id);
  }
  updateViewBounds();
}

function toggleDimension(propId: string, dim: string): void {
  if (!visibleDimensions.value[propId]) {
    visibleDimensions.value[propId] = [];
  }
  const dims = visibleDimensions.value[propId];
  const index = dims.indexOf(dim);
  if (index === -1) {
    dims.push(dim);
  } else {
    dims.splice(index, 1);
  }
}

// View management
function fitToView(): void {
  const visible = visibleProperties.value;
  if (visible.length === 0) return;

  let minFrame = Infinity;
  let maxFrame = -Infinity;
  let minValue = Infinity;
  let maxValue = -Infinity;

  for (const prop of visible) {
    for (const kf of prop.keyframes) {
      minFrame = Math.min(minFrame, kf.frame);
      maxFrame = Math.max(maxFrame, kf.frame);
      const value = getNumericValue(kf.value);
      minValue = Math.min(minValue, value);
      maxValue = Math.max(maxValue, value);
    }
  }

  // Add padding
  const frameMargin = (maxFrame - minFrame) * 0.1 || 10;
  const valueMargin = (maxValue - minValue) * 0.1 || 10;

  viewState.frameStart = minFrame - frameMargin;
  viewState.frameEnd = maxFrame + frameMargin;
  viewState.valueMin = minValue - valueMargin;
  viewState.valueMax = maxValue + valueMargin;
}

function updateViewBounds(): void {
  fitToView();
}

function _toggleAutoSelect(): void {
  autoSelectNearby.value = !autoSelectNearby.value;
}

// Preset handling
function isPresetActive(presetKey: string): boolean {
  if (selectedKeyframes.value.length === 0) return false;

  const preset = EASING_PRESETS[presetKey as keyof typeof EASING_PRESETS];
  if (!preset) return false;

  // Preset comparison is complex because presets are normalized (0-1)
  // but handles are absolute. For now, check by interpolation type.
  if (presetKey === "linear") {
    return selectedKeyframes.value.every(
      (sk) => sk.keyframe.interpolation === "linear",
    );
  }
  // For bezier presets, just check if it's bezier interpolation
  return selectedKeyframes.value.every(
    (sk) => sk.keyframe.interpolation === "bezier",
  );
}

function applyPreset(presetKey: string): void {
  const preset = EASING_PRESETS[presetKey as keyof typeof EASING_PRESETS];
  if (!preset) return;

  const layer = store.selectedLayer;
  if (!layer) return;

  for (const sk of selectedKeyframes.value) {
    const prop = animatableProperties.value.find((p) => p.id === sk.propId);
    if (!prop) continue;

    const propertyPath = getPropertyPath(prop);
    const kfIndex = sk.index;
    const prevKf = kfIndex > 0 ? prop.keyframes[kfIndex - 1] : null;
    const nextKf =
      kfIndex < prop.keyframes.length - 1 ? prop.keyframes[kfIndex + 1] : null;

    // Calculate durations for handle conversion
    const inDuration = prevKf ? sk.keyframe.frame - prevKf.frame : 10;
    const outDuration = nextKf ? nextKf.frame - sk.keyframe.frame : 10;

    // Convert normalized preset to absolute frame/value handles
    if (presetKey === "linear") {
      keyframeStore.setKeyframeInterpolation(
        store,
        layer.id,
        propertyPath,
        sk.keyframe.id,
        "linear",
      );
      // Also update local reference
      sk.keyframe.interpolation = "linear";
      sk.keyframe.outHandle = {
        frame: outDuration * 0.33,
        value: 0,
        enabled: false,
      };
      sk.keyframe.inHandle = {
        frame: -inDuration * 0.33,
        value: 0,
        enabled: false,
      };
    } else {
      // Apply normalized preset values scaled by duration
      const outHandle = {
        frame: preset.outHandle.x * outDuration,
        value: 0, // Would need value delta for proper curve
        enabled: true,
      };
      const inHandle = {
        frame: -preset.inHandle.x * inDuration,
        value: 0, // Would need value delta for proper curve
        enabled: true,
      };

      keyframeStore.setKeyframeInterpolation(
        store,
        layer.id,
        propertyPath,
        sk.keyframe.id,
        "bezier",
      );
      keyframeStore.setKeyframeHandle(
        store,
        layer.id,
        propertyPath,
        sk.keyframe.id,
        "out",
        outHandle,
      );
      keyframeStore.setKeyframeHandle(
        store,
        layer.id,
        propertyPath,
        sk.keyframe.id,
        "in",
        inHandle,
      );

      // Update local reference
      sk.keyframe.interpolation = "bezier";
      sk.keyframe.outHandle = outHandle;
      sk.keyframe.inHandle = inHandle;
    }
  }

  drawGraph();
}

// Mouse event handlers
function handleMouseDown(event: MouseEvent): void {
  const rect = canvasRef.value?.getBoundingClientRect();
  if (!rect) return;

  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;

  if (event.button === 1 || (event.button === 0 && event.altKey)) {
    // Middle click or Alt+left click: pan
    dragTarget.value = { type: "pan", startX: x, startY: y };
  } else if (event.button === 0) {
    // Left click: selection box
    if (!event.shiftKey) {
      selectedKeyframes.value = [];
    }
    selectionBox.value = { x, y, width: 0, height: 0 };
    dragTarget.value = { type: "select", startX: x, startY: y };
  }
}

function handleMouseMove(event: MouseEvent): void {
  const rect = canvasRef.value?.getBoundingClientRect();
  if (!rect) return;

  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;

  // Update hovered keyframe
  updateHoveredKeyframe(x, y);

  if (!dragTarget.value) return;

  if (dragTarget.value.type === "pan") {
    const dx = x - (dragTarget.value.startX ?? 0);
    const dy = y - (dragTarget.value.startY ?? 0);

    const graphWidth = canvasWidth.value - margin.left - margin.right;
    const graphHeight = canvasHeight.value - margin.top - margin.bottom;

    const frameShift =
      (-dx / graphWidth) * (viewState.frameEnd - viewState.frameStart);
    const valueShift =
      (dy / graphHeight) * (viewState.valueMax - viewState.valueMin);

    viewState.frameStart += frameShift;
    viewState.frameEnd += frameShift;
    viewState.valueMin += valueShift;
    viewState.valueMax += valueShift;

    dragTarget.value.startX = x;
    dragTarget.value.startY = y;
    drawGraph();
  } else if (dragTarget.value.type === "select" && selectionBox.value) {
    const startX = dragTarget.value.startX ?? 0;
    const startY = dragTarget.value.startY ?? 0;

    selectionBox.value = {
      x: Math.min(x, startX),
      y: Math.min(y, startY),
      width: Math.abs(x - startX),
      height: Math.abs(y - startY),
    };
  } else if (dragTarget.value.type === "keyframe") {
    moveSelectedKeyframes(x, y);
  } else if (
    dragTarget.value.type === "outHandle" ||
    dragTarget.value.type === "inHandle"
  ) {
    moveHandle(x, y);
  }
}

function handleMouseUp(): void {
  if (dragTarget.value?.type === "select" && selectionBox.value) {
    selectKeyframesInBox();
  }

  dragTarget.value = null;
  selectionBox.value = null;
}

function handleWheel(event: WheelEvent): void {
  event.preventDefault();

  const rect = canvasRef.value?.getBoundingClientRect();
  if (!rect) return;

  const x = event.clientX - rect.left;
  const zoomFactor = event.deltaY > 0 ? 1.1 : 0.9;

  // Zoom around cursor position
  const frameAtCursor = screenXToFrame(x);

  const newFrameStart =
    frameAtCursor - (frameAtCursor - viewState.frameStart) * zoomFactor;
  const newFrameEnd =
    frameAtCursor + (viewState.frameEnd - frameAtCursor) * zoomFactor;

  if (event.shiftKey) {
    // Zoom time only
    viewState.frameStart = newFrameStart;
    viewState.frameEnd = newFrameEnd;
  } else {
    // Zoom both axes
    viewState.frameStart = newFrameStart;
    viewState.frameEnd = newFrameEnd;

    const y = event.clientY - rect.top;
    const valueAtCursor = screenYToValue(y);
    viewState.valueMin =
      valueAtCursor - (valueAtCursor - viewState.valueMin) * zoomFactor;
    viewState.valueMax =
      valueAtCursor + (viewState.valueMax - valueAtCursor) * zoomFactor;
  }

  drawGraph();
}

function updateHoveredKeyframe(x: number, y: number): void {
  hoveredKeyframe.value = null;

  for (const prop of visibleProperties.value) {
    for (let i = 0; i < prop.keyframes.length; i++) {
      const kf = prop.keyframes[i];
      const kfX = getKeyframeScreenX(kf);
      const kfY = getKeyframeScreenY(prop, kf);

      const dist = Math.sqrt((x - kfX) ** 2 + (y - kfY) ** 2);
      if (dist < 10) {
        hoveredKeyframe.value = { propId: prop.id, index: i };
        return;
      }
    }
  }
}

function onKeyframeMouseDown(
  propId: string,
  index: number,
  event: MouseEvent,
): void {
  const prop = animatableProperties.value.find((p) => p.id === propId);
  if (!prop) return;

  const kf = prop.keyframes[index];

  if (!event.shiftKey) {
    selectedKeyframes.value = [];
  }

  if (!isKeyframeSelected(propId, index)) {
    selectedKeyframes.value.push({ propId, index, keyframe: kf });
  }

  dragTarget.value = { type: "keyframe", propId, index };
}

function selectKeyframesInBox(): void {
  if (!selectionBox.value) return;

  const box = selectionBox.value;

  for (const prop of visibleProperties.value) {
    for (let i = 0; i < prop.keyframes.length; i++) {
      const kf = prop.keyframes[i];
      const x = getKeyframeScreenX(kf);
      const y = getKeyframeScreenY(prop, kf);

      if (
        x >= box.x &&
        x <= box.x + box.width &&
        y >= box.y &&
        y <= box.y + box.height
      ) {
        if (!isKeyframeSelected(prop.id, i)) {
          selectedKeyframes.value.push({
            propId: prop.id,
            index: i,
            keyframe: kf,
          });
        }
      }
    }
  }
}

function moveSelectedKeyframes(screenX: number, screenY: number): void {
  let newFrame = Math.round(screenXToFrame(screenX));
  const newValue = screenYToValue(screenY);

  const layer = store.selectedLayer;
  if (!layer) return;

  // For now, just move the first selected keyframe
  if (selectedKeyframes.value.length > 0) {
    const sk = selectedKeyframes.value[0];
    const prop = animatableProperties.value.find((p) => p.id === sk.propId);
    if (!prop) return;

    // Apply smart snapping with audio beat/peak support
    if (snapEnabled.value && store.snapConfig.enabled) {
      // Calculate approximate pixels per frame for snapping threshold
      const pixelsPerFrame =
        canvasWidth.value / (viewState.frameEnd - viewState.frameStart);

      const snap = findNearestSnap(newFrame, store.snapConfig, pixelsPerFrame, {
        layers: store.layers,
        selectedLayerId: layer.id,
        currentFrame: store.currentFrame,
        audioAnalysis: audioStore.audioAnalysis,
        peakData: audioStore.peakData,
      });

      if (snap) {
        newFrame = snap.frame;
      } else {
        // Fallback to basic grid snap
        newFrame =
          Math.round(newFrame / store.snapConfig.gridInterval) *
          store.snapConfig.gridInterval;
      }
    }

    const frame = Math.max(0, Math.min(store.frameCount - 1, newFrame));
    const _value =
      typeof sk.keyframe.value === "number" ? newValue : sk.keyframe.value;

    // Get property path from property name
    const propertyPath = getPropertyPath(prop);

    // Call store method to persist the change
    keyframeStore.updateKeyframe(store, layer.id, propertyPath, sk.keyframe.id, {
      frame,
      value: typeof sk.keyframe.value === "number" ? newValue : undefined,
    });

    // Update local reference
    sk.keyframe.frame = frame;
    if (typeof sk.keyframe.value === "number") {
      sk.keyframe.value = newValue;
    }
  }

  drawGraph();
}

// Helper to get property path from AnimatableProperty
function getPropertyPath(prop: AnimatableProperty<PropertyValue>): string {
  const name = prop.name.toLowerCase();
  if (name === "position") return "transform.position";
  if (name === "scale") return "transform.scale";
  if (name === "rotation") return "transform.rotation";
  if (name === "opacity") return "opacity";
  if (name === "origin" || name === "anchor point")
    return "transform.anchorPoint";
  return prop.id; // Custom properties use ID
}

// Handle dragging
function startDragHandle(
  type: "inHandle" | "outHandle",
  propId: string,
  index: number,
  _event: MouseEvent,
): void {
  dragTarget.value = { type, propId, index };
  document.addEventListener("mousemove", onDragHandle);
  document.addEventListener("mouseup", stopDragHandle);
}

function onDragHandle(event: MouseEvent): void {
  const rect = canvasRef.value?.getBoundingClientRect();
  if (!rect || !dragTarget.value) return;

  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;
  moveHandle(x, y);
}

function moveHandle(screenX: number, screenY: number): void {
  if (!dragTarget.value || !dragTarget.value.propId) return;

  const layer = store.selectedLayer;
  if (!layer) return;

  const prop = animatableProperties.value.find(
    (p) => p.id === dragTarget.value?.propId,
  );
  if (!prop) return;

  const kfIndex = dragTarget.value.index!;
  const kf = prop.keyframes[kfIndex];
  if (!kf) return;

  const handleFrame = screenXToFrame(screenX);
  const handleValue = screenYToValue(screenY);
  const propertyPath = getPropertyPath(prop);

  if (dragTarget.value.type === "outHandle") {
    const nextKf = prop.keyframes[kfIndex + 1];

    // Calculate frame offset (positive = forward from keyframe)
    let frameOffset = handleFrame - kf.frame;
    // Constrain: cannot go past next keyframe or before current
    if (nextKf) {
      frameOffset = Math.max(0, Math.min(nextKf.frame - kf.frame, frameOffset));
    } else {
      frameOffset = Math.max(0, frameOffset);
    }

    // Calculate value offset
    const valueOffset = handleValue - getNumericValue(kf.value);

    const newHandle = {
      frame: frameOffset,
      value: valueOffset,
      enabled: true,
    };

    // Call store method to persist
    keyframeStore.setKeyframeHandle(store, layer.id, propertyPath, kf.id, "out", newHandle);

    // Update local reference
    kf.outHandle = newHandle;
    kf.interpolation = "bezier";

    // Apply control mode constraints (spec B3/B4)
    applyControlModeConstraints(kf, "out", propertyPath);
  } else if (dragTarget.value.type === "inHandle") {
    const prevKf = prop.keyframes[kfIndex - 1];

    // Calculate frame offset (negative = backward from keyframe)
    let frameOffset = handleFrame - kf.frame;
    // Constrain: cannot go past previous keyframe or after current
    if (prevKf) {
      frameOffset = Math.min(0, Math.max(prevKf.frame - kf.frame, frameOffset));
    } else {
      frameOffset = Math.min(0, frameOffset);
    }

    // Calculate value offset
    const valueOffset = handleValue - getNumericValue(kf.value);

    const newHandle = {
      frame: frameOffset,
      value: valueOffset,
      enabled: true,
    };

    // Call store method to persist
    keyframeStore.setKeyframeHandle(store, layer.id, propertyPath, kf.id, "in", newHandle);

    // Update local reference
    kf.inHandle = newHandle;

    // Apply control mode constraints (spec B3/B4)
    applyControlModeConstraints(kf, "in", propertyPath);
  }

  drawGraph();
}

// Control mode constraints (from spec B2, B3, B4)
function applyControlModeConstraints(
  kf: Keyframe<PropertyValue>,
  changedHandle: "in" | "out",
  propertyPath: string,
): void {
  if (!kf.controlMode || kf.controlMode === "corner") {
    // Fully independent - no constraints (spec B4)
    return;
  }

  const layer = store.selectedLayer;
  if (!layer) return;

  if (kf.controlMode === "symmetric") {
    // Mirror opposite handle - same length, opposite direction (spec B2)
    if (changedHandle === "in") {
      kf.outHandle.frame = -kf.inHandle.frame;
      kf.outHandle.value = -kf.inHandle.value;
      kf.outHandle.enabled = kf.inHandle.enabled;
      // Persist to store
      keyframeStore.setKeyframeHandle(store, layer.id, propertyPath, kf.id, "out", {
        ...kf.outHandle,
      });
    } else {
      kf.inHandle.frame = -kf.outHandle.frame;
      kf.inHandle.value = -kf.outHandle.value;
      kf.inHandle.enabled = kf.outHandle.enabled;
      // Persist to store
      keyframeStore.setKeyframeHandle(store, layer.id, propertyPath, kf.id, "in", {
        ...kf.inHandle,
      });
    }
  }

  if (kf.controlMode === "smooth") {
    // Keep collinear but allow different lengths (spec B3)
    const changed = changedHandle === "in" ? kf.inHandle : kf.outHandle;
    const other = changedHandle === "in" ? kf.outHandle : kf.inHandle;
    const otherType = changedHandle === "in" ? "out" : "in";

    if (changed.frame !== 0 || changed.value !== 0) {
      const angle = Math.atan2(changed.value, changed.frame);
      const oppositeAngle = angle + Math.PI;
      const otherLength = Math.hypot(other.frame, other.value);

      other.frame = Math.cos(oppositeAngle) * otherLength;
      other.value = Math.sin(oppositeAngle) * otherLength;

      // Persist to store
      keyframeStore.setKeyframeHandle(store, layer.id, propertyPath, kf.id, otherType, {
        ...other,
      });
    }
  }
}

function stopDragHandle(): void {
  dragTarget.value = null;
  document.removeEventListener("mousemove", onDragHandle);
  document.removeEventListener("mouseup", stopDragHandle);
}

// Context menu
function showContextMenu(event: MouseEvent): void {
  contextMenu.value = { x: event.offsetX, y: event.offsetY };
}

function addKeyframeAtPosition(): void {
  if (!contextMenu.value) return;

  const layer = store.selectedLayer;
  if (!layer) return;

  const frame = Math.round(screenXToFrame(contextMenu.value.x));
  const value = screenYToValue(contextMenu.value.y);

  // Add keyframe to first visible property
  if (visibleProperties.value.length > 0) {
    const prop = visibleProperties.value[0];
    const propertyPath = getPropertyPath(prop);
    const keyframeValue =
      typeof prop.value === "number" ? value : { x: value, y: value };

    // Call store method to persist - it handles sorting and animation flag
    keyframeStore.addKeyframe(store, layer.id, propertyPath, keyframeValue, frame);
    drawGraph();
  }

  contextMenu.value = null;
}

function deleteSelectedKeyframes(): void {
  const layer = store.selectedLayer;
  if (!layer) return;

  for (const sk of selectedKeyframes.value) {
    const prop = animatableProperties.value.find((p) => p.id === sk.propId);
    if (prop) {
      const propertyPath = getPropertyPath(prop);
      // Call store method to persist deletion
      keyframeStore.removeKeyframe(store, layer.id, propertyPath, sk.keyframe.id);
    }
  }
  selectedKeyframes.value = [];
  drawGraph();
}

function copyKeyframes(): void {
  clipboard.value = selectedKeyframes.value.map((sk) => ({ ...sk.keyframe }));
}

function pasteKeyframes(): void {
  if (!clipboard.value || visibleProperties.value.length === 0) return;

  const layer = store.selectedLayer;
  if (!layer) return;

  const prop = visibleProperties.value[0];
  const propertyPath = getPropertyPath(prop);
  const offset = store.currentFrame - clipboard.value[0].frame;

  for (const kf of clipboard.value) {
    const newFrame = kf.frame + offset;
    // Use store method to properly add keyframes
    const newKeyframe = keyframeStore.addKeyframe(
      store,
      layer.id,
      propertyPath,
      kf.value,
      newFrame,
    );

    // Set interpolation and handles on the newly created keyframe
    if (newKeyframe) {
      if (kf.interpolation !== "linear") {
        keyframeStore.setKeyframeInterpolation(
          store,
          layer.id,
          propertyPath,
          newKeyframe.id,
          kf.interpolation,
        );
      }
      if (kf.inHandle?.enabled) {
        keyframeStore.setKeyframeHandle(
          store,
          layer.id,
          propertyPath,
          newKeyframe.id,
          "in",
          kf.inHandle,
        );
      }
      if (kf.outHandle?.enabled) {
        keyframeStore.setKeyframeHandle(
          store,
          layer.id,
          propertyPath,
          newKeyframe.id,
          "out",
          kf.outHandle,
        );
      }
    }
  }

  drawGraph();
}

function selectAllKeyframes(): void {
  selectedKeyframes.value = [];
  for (const prop of visibleProperties.value) {
    for (let i = 0; i < prop.keyframes.length; i++) {
      selectedKeyframes.value.push({
        propId: prop.id,
        index: i,
        keyframe: prop.keyframes[i],
      });
    }
  }
}

function invertSelection(): void {
  const newSelection: typeof selectedKeyframes.value = [];

  for (const prop of visibleProperties.value) {
    for (let i = 0; i < prop.keyframes.length; i++) {
      if (!isKeyframeSelected(prop.id, i)) {
        newSelection.push({
          propId: prop.id,
          index: i,
          keyframe: prop.keyframes[i],
        });
      }
    }
  }

  selectedKeyframes.value = newSelection;
}

// Keyframe info updates
function updateSelectedKeyframeFrame(event: Event): void {
  const value = parseInt((event.target as HTMLInputElement).value, 10);
  if (selectedKeyframes.value.length > 0 && !Number.isNaN(value)) {
    selectedKeyframes.value[0].keyframe.frame = value;
    drawGraph();
  }
}

function updateSelectedKeyframeValue(event: Event): void {
  const value = parseFloat((event.target as HTMLInputElement).value);
  if (selectedKeyframes.value.length > 0 && !Number.isNaN(value)) {
    const kf = selectedKeyframes.value[0].keyframe;
    if (typeof kf.value === "number") {
      kf.value = value;
    } else if (typeof kf.value === "object") {
      kf.value.x = value;
    }
    drawGraph();
  }
}

function updateSelectedKeyframeInterpolation(event: Event): void {
  const value = (event.target as HTMLSelectElement).value as
    | "linear"
    | "bezier"
    | "hold";
  if (selectedKeyframes.value.length > 0) {
    selectedKeyframes.value[0].keyframe.interpolation = value;
    drawGraph();
  }
}

// Time ruler click
function onTimeRulerClick(event: MouseEvent): void {
  const rect = timeRulerCanvas.value?.getBoundingClientRect();
  if (!rect) return;

  const x = event.clientX - rect.left;
  const frame = Math.round(screenXToFrame(x));
  const animationStore = useAnimationStore();
  animationStore.setFrame(store, frame);
}

// Drawing
function drawGraph(): void {
  drawMainCanvas();
  drawTimeRuler();
  drawValueAxis();
}

function drawMainCanvas(): void {
  const canvas = canvasRef.value;
  if (!canvas) return;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  // Set canvas size
  canvas.width = canvasWidth.value;
  canvas.height = canvasHeight.value;

  // Clear
  ctx.fillStyle = "#1a1a1a";
  ctx.fillRect(0, 0, canvasWidth.value, canvasHeight.value);

  // Draw grid
  drawGrid(ctx);

  // Draw curves for each visible property
  for (const prop of visibleProperties.value) {
    drawPropertyCurve(ctx, prop);
  }
}

function drawGrid(ctx: CanvasRenderingContext2D): void {
  const graphWidth = canvasWidth.value - margin.left - margin.right;
  const graphHeight = canvasHeight.value - margin.top - margin.bottom;

  ctx.strokeStyle = "#2a2a2a";
  ctx.lineWidth = 1;

  // Calculate grid spacing based on view
  const frameRange = viewState.frameEnd - viewState.frameStart;
  const frameStep = calculateGridStep(frameRange, graphWidth, 50);
  const valueRange = viewState.valueMax - viewState.valueMin;
  const valueStep = calculateGridStep(valueRange, graphHeight, 30);

  // Vertical lines (frame grid)
  const firstFrame = Math.ceil(viewState.frameStart / frameStep) * frameStep;
  for (
    let frame = firstFrame;
    frame <= viewState.frameEnd;
    frame += frameStep
  ) {
    const x = frameToScreenX(frame);
    ctx.beginPath();
    ctx.moveTo(x, margin.top);
    ctx.lineTo(x, canvasHeight.value - margin.bottom);
    ctx.stroke();
  }

  // Horizontal lines (value grid)
  const firstValue = Math.ceil(viewState.valueMin / valueStep) * valueStep;
  for (
    let value = firstValue;
    value <= viewState.valueMax;
    value += valueStep
  ) {
    const y = valueToScreenY(value);
    ctx.beginPath();
    ctx.moveTo(margin.left, y);
    ctx.lineTo(canvasWidth.value - margin.right, y);
    ctx.stroke();
  }

  // Zero lines
  ctx.strokeStyle = "#3a3a3a";
  ctx.lineWidth = 1;

  if (viewState.frameStart <= 0 && viewState.frameEnd >= 0) {
    const x = frameToScreenX(0);
    ctx.beginPath();
    ctx.moveTo(x, margin.top);
    ctx.lineTo(x, canvasHeight.value - margin.bottom);
    ctx.stroke();
  }

  if (viewState.valueMin <= 0 && viewState.valueMax >= 0) {
    const y = valueToScreenY(0);
    ctx.beginPath();
    ctx.moveTo(margin.left, y);
    ctx.lineTo(canvasWidth.value - margin.right, y);
    ctx.stroke();
  }
}

function calculateGridStep(
  range: number,
  pixelSize: number,
  targetSpacing: number,
): number {
  const rawStep = (range * targetSpacing) / pixelSize;
  const magnitude = 10 ** Math.floor(Math.log10(rawStep));
  const normalized = rawStep / magnitude;

  if (normalized <= 1) return magnitude;
  if (normalized <= 2) return 2 * magnitude;
  if (normalized <= 5) return 5 * magnitude;
  return 10 * magnitude;
}

function drawPropertyCurve(
  ctx: CanvasRenderingContext2D,
  prop: AnimatableProperty<PropertyValue>,
): void {
  if (prop.keyframes.length < 2) return;

  const color = getPropertyColor(prop.id);

  // Two-pass rendering per spec A1: black outline then colored fill
  for (let pass = 0; pass < 2; pass++) {
    if (pass === 0) {
      ctx.strokeStyle = "#000";
      ctx.lineWidth = 4;
    } else {
      ctx.strokeStyle = color;
      ctx.lineWidth = 2;
    }

    ctx.beginPath();
    let started = false;

    for (let i = 0; i < prop.keyframes.length - 1; i++) {
      const kf1 = prop.keyframes[i];
      const kf2 = prop.keyframes[i + 1];

      // Skip segments outside view
      if (kf2.frame < viewState.frameStart || kf1.frame > viewState.frameEnd)
        continue;

      const x1 = getKeyframeScreenX(kf1);
      const y1 = getKeyframeScreenY(prop, kf1);
      const x2 = getKeyframeScreenX(kf2);
      const y2 = getKeyframeScreenY(prop, kf2);

      if (!started) {
        ctx.moveTo(x1, y1);
        started = true;
      }

      if (kf1.interpolation === "hold") {
        // Step function (spec B5)
        ctx.lineTo(x2, y1);
        ctx.lineTo(x2, y2);
      } else if (
        kf1.interpolation === "linear" ||
        (!kf1.outHandle.enabled && !kf2.inHandle.enabled)
      ) {
        // Straight line (spec B1)
        ctx.lineTo(x2, y2);
      } else {
        // Bezier curve using absolute handle offsets (spec B3/B4)
        const cp1x = frameToScreenX(kf1.frame + kf1.outHandle.frame);
        const cp1y = valueToScreenY(
          getNumericValue(kf1.value) + kf1.outHandle.value,
        );
        const cp2x = frameToScreenX(kf2.frame + kf2.inHandle.frame);
        const cp2y = valueToScreenY(
          getNumericValue(kf2.value) + kf2.inHandle.value,
        );

        ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x2, y2);
      }
    }

    ctx.stroke();
  }
}

function drawTimeRuler(): void {
  const canvas = timeRulerCanvas.value;
  if (!canvas) return;

  const rect = timeRulerRef.value?.getBoundingClientRect();
  if (!rect) return;

  canvas.width = rect.width;
  canvas.height = 24;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  ctx.fillStyle = "#252525";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const frameRange = viewState.frameEnd - viewState.frameStart;
  const frameStep = calculateGridStep(frameRange, canvas.width, 60);

  ctx.fillStyle = "#888";
  ctx.font = "10px system-ui";
  ctx.textAlign = "center";

  const firstFrame = Math.ceil(viewState.frameStart / frameStep) * frameStep;
  for (
    let frame = firstFrame;
    frame <= viewState.frameEnd;
    frame += frameStep
  ) {
    const x = frameToScreenX(frame);
    ctx.fillText(frame.toString(), x, 16);

    ctx.strokeStyle = "#444";
    ctx.beginPath();
    ctx.moveTo(x, 20);
    ctx.lineTo(x, 24);
    ctx.stroke();
  }

  // Current frame marker
  const ctfX = frameToScreenX(store.currentFrame);
  ctx.fillStyle = "#ff4444";
  ctx.beginPath();
  ctx.moveTo(ctfX - 5, 0);
  ctx.lineTo(ctfX + 5, 0);
  ctx.lineTo(ctfX, 8);
  ctx.closePath();
  ctx.fill();
}

function drawValueAxis(): void {
  const canvas = valueAxisCanvas.value;
  if (!canvas) return;

  const rect = valueAxisRef.value?.getBoundingClientRect();
  if (!rect) return;

  canvas.width = 40;
  canvas.height = rect.height;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  ctx.fillStyle = "#252525";
  ctx.fillRect(0, 0, canvas.width, canvas.height);

  const valueRange = viewState.valueMax - viewState.valueMin;
  const valueStep = calculateGridStep(valueRange, canvas.height, 30);

  ctx.fillStyle = "#888";
  ctx.font = "10px system-ui";
  ctx.textAlign = "right";

  const firstValue = Math.ceil(viewState.valueMin / valueStep) * valueStep;
  for (
    let value = firstValue;
    value <= viewState.valueMax;
    value += valueStep
  ) {
    const y = valueToScreenY(value);
    ctx.fillText(value.toFixed(0), 36, y + 4);
  }
}

// Easy Ease functions (spec C1, C2, C3)
function applyEasyEase(direction: "both" | "in" | "out" = "both"): void {
  for (const sk of selectedKeyframes.value) {
    const prop = animatableProperties.value.find((p) => p.id === sk.propId);
    if (!prop) continue;

    const kf = sk.keyframe;
    const kfIndex = sk.index;

    // Get adjacent keyframes for duration calculation
    const prevKf = kfIndex > 0 ? prop.keyframes[kfIndex - 1] : null;
    const nextKf =
      kfIndex < prop.keyframes.length - 1 ? prop.keyframes[kfIndex + 1] : null;

    // Calculate segment durations
    const inDuration = prevKf ? kf.frame - prevKf.frame : 10;
    const outDuration = nextKf ? nextKf.frame - kf.frame : 10;

    // 33.33% influence (spec C1)
    const influence = 0.3333;

    if (direction === "both" || direction === "in") {
      // Easy ease in - deceleration (spec C2)
      kf.inHandle = {
        frame: -inDuration * influence,
        value: 0, // 0 velocity at keyframe
        enabled: true,
      };
    }

    if (direction === "both" || direction === "out") {
      // Easy ease out - acceleration (spec C3)
      kf.outHandle = {
        frame: outDuration * influence,
        value: 0, // 0 velocity at keyframe
        enabled: true,
      };
    }

    kf.interpolation = "bezier";
    kf.controlMode = "smooth";
  }

  drawGraph();
}

// J/K Navigation (spec G4)
function goToPreviousKeyframe(): void {
  const currentFrame = store.currentFrame;
  const allKeyframes: number[] = [];

  for (const prop of visibleProperties.value) {
    for (const kf of prop.keyframes) {
      if (!allKeyframes.includes(kf.frame)) {
        allKeyframes.push(kf.frame);
      }
    }
  }

  allKeyframes.sort((a, b) => a - b);
  const prev = [...allKeyframes].reverse().find((f) => f < currentFrame);
  if (prev !== undefined) {
    animationStore.setFrame(store, prev);
  }
}

function goToNextKeyframe(): void {
  const currentFrame = store.currentFrame;
  const allKeyframes: number[] = [];

  for (const prop of visibleProperties.value) {
    for (const kf of prop.keyframes) {
      if (!allKeyframes.includes(kf.frame)) {
        allKeyframes.push(kf.frame);
      }
    }
  }

  allKeyframes.sort((a, b) => a - b);
  const next = allKeyframes.find((f) => f > currentFrame);
  if (next !== undefined) {
    animationStore.setFrame(store, next);
  }
}

// Keyboard shortcuts handler (spec I)
function handleKeyDown(event: KeyboardEvent): void {
  // F9 Easy Ease
  if (event.key === "F9") {
    event.preventDefault();
    if (event.ctrlKey && event.shiftKey) {
      applyEasyEase("out"); // Ctrl+Shift+F9 (spec C3)
    } else if (event.shiftKey) {
      applyEasyEase("in"); // Shift+F9 (spec C2)
    } else {
      applyEasyEase("both"); // F9 (spec C1)
    }
    return;
  }

  // J/K navigation (spec G4)
  if (event.key.toLowerCase() === "j") {
    event.preventDefault();
    goToPreviousKeyframe();
    return;
  }
  if (event.key.toLowerCase() === "k") {
    event.preventDefault();
    goToNextKeyframe();
    return;
  }

  // Delete selected keyframes
  if (event.key === "Delete" || event.key === "Backspace") {
    event.preventDefault();
    deleteSelectedKeyframes();
    return;
  }

  // F = Fit selection to view
  if (event.key.toLowerCase() === "f" && !event.ctrlKey) {
    event.preventDefault();
    if (event.shiftKey) {
      fitToView(); // Shift+F = fit all
    } else if (selectedKeyframes.value.length > 0) {
      fitSelectionToView(); // F = fit selection
    } else {
      fitToView();
    }
    return;
  }

  // Zoom in/out with = / -
  if (event.key === "=" || event.key === "+") {
    event.preventDefault();
    zoomIn();
    return;
  }
  if (event.key === "-" || event.key === "_") {
    event.preventDefault();
    zoomOut();
    return;
  }
}

function fitSelectionToView(): void {
  if (selectedKeyframes.value.length === 0) {
    fitToView();
    return;
  }

  let minFrame = Infinity;
  let maxFrame = -Infinity;
  let minValue = Infinity;
  let maxValue = -Infinity;

  for (const sk of selectedKeyframes.value) {
    minFrame = Math.min(minFrame, sk.keyframe.frame);
    maxFrame = Math.max(maxFrame, sk.keyframe.frame);
    const value = getNumericValue(sk.keyframe.value);
    minValue = Math.min(minValue, value);
    maxValue = Math.max(maxValue, value);
  }

  const frameMargin = (maxFrame - minFrame) * 0.1 || 10;
  const valueMargin = (maxValue - minValue) * 0.1 || 10;

  viewState.frameStart = minFrame - frameMargin;
  viewState.frameEnd = maxFrame + frameMargin;
  viewState.valueMin = minValue - valueMargin;
  viewState.valueMax = maxValue + valueMargin;

  drawGraph();
}

function zoomIn(): void {
  const centerFrame = (viewState.frameStart + viewState.frameEnd) / 2;
  const frameRange = viewState.frameEnd - viewState.frameStart;
  viewState.frameStart = centerFrame - frameRange * 0.4;
  viewState.frameEnd = centerFrame + frameRange * 0.4;
  drawGraph();
}

function zoomOut(): void {
  const centerFrame = (viewState.frameStart + viewState.frameEnd) / 2;
  const frameRange = viewState.frameEnd - viewState.frameStart;
  viewState.frameStart = centerFrame - frameRange * 0.6;
  viewState.frameEnd = centerFrame + frameRange * 0.6;
  drawGraph();
}

// Resize observer
let resizeObserver: ResizeObserver | null = null;

onMounted(() => {
  if (canvasContainerRef.value) {
    resizeObserver = new ResizeObserver((entries) => {
      for (const entry of entries) {
        canvasWidth.value = entry.contentRect.width;
        canvasHeight.value = entry.contentRect.height;
        drawGraph();
      }
    });
    resizeObserver.observe(canvasContainerRef.value);
  }

  // Initialize visibility
  visiblePropertyIds.value = animatableProperties.value
    .filter((p) => p.animated)
    .map((p) => p.id);

  // Add keyboard listener
  window.addEventListener("keydown", handleKeyDown);

  fitToView();
  drawGraph();
});

onUnmounted(() => {
  resizeObserver?.disconnect();
  window.removeEventListener("keydown", handleKeyDown);
});

// Redraw on changes
watch([() => store.currentFrame, visiblePropertyIds, mode], () => {
  drawGraph();
});

watch(
  animatableProperties,
  () => {
    fitToView();
    drawGraph();
  },
  { deep: true },
);
</script>

<style scoped>
.curve-editor {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 12px;
}

.curve-content {
  display: flex;
  flex: 1;
  min-height: 0;
}

.curve-main {
  flex: 1;
  display: flex;
  flex-direction: column;
  min-width: 0;
}

.time-ruler {
  height: 24px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.time-ruler canvas {
  display: block;
  width: 100%;
  height: 100%;
  cursor: pointer;
}

.curve-canvas-container {
  flex: 1;
  position: relative;
  min-height: 0;
}

.curve-canvas-container canvas {
  display: block;
  width: 100%;
  height: 100%;
}

.value-axis {
  width: 40px;
  background: #252525;
  border-left: 1px solid #333;
}

.value-axis canvas {
  display: block;
}

.selection-box {
  position: absolute;
  border: 1px solid #7c9cff;
  background: rgba(124, 156, 255, 0.1);
  pointer-events: none;
}

.handle-overlay {
  position: absolute;
  inset: 0;
  pointer-events: none;
}

.keyframe-marker {
  pointer-events: all;
  cursor: pointer;
}

.keyframe-marker rect {
  stroke: #fff;
  stroke-width: 1;
  stroke-opacity: 0;
  transition: all 0.1s;
}

.keyframe-marker.selected rect,
.keyframe-marker.hovered rect {
  stroke-opacity: 1;
}

.keyframe-marker.selected rect {
  filter: brightness(1.3);
}

.bezier-handles {
  pointer-events: all;
}

/* In handle colors - blue/cyan (spec H4) */
.in-handle .handle-line {
  stroke: #4ecdc4;
  stroke-width: 1;
}

.in-handle .handle-point {
  fill: #fff;
  stroke: #4ecdc4;
  stroke-width: 1;
  cursor: pointer;
  transition: all 0.1s;
}

/* Out handle colors - red/orange (spec H4) */
.out-handle .handle-line {
  stroke: #ff6b6b;
  stroke-width: 1;
}

.out-handle .handle-point {
  fill: #fff;
  stroke: #ff6b6b;
  stroke-width: 1;
  cursor: pointer;
  transition: all 0.1s;
}

.handle-point:hover,
.handle-point.dragging {
  fill: #7c9cff;
  r: 7;
}

.current-time-line {
  stroke: #ff4444;
  stroke-width: 1;
  stroke-dasharray: 4 4;
}

.keyframe-info-panel {
  display: flex;
  gap: 16px;
  padding: 8px 12px;
  background: #252525;
  border-top: 1px solid #333;
}

.info-row {
  display: flex;
  align-items: center;
  gap: 6px;
}

.info-label {
  color: #888;
  font-size: 12px;
}

.info-input {
  width: 60px;
  padding: 3px 6px;
  background: #1e1e1e;
  border: 1px solid #444;
  border-radius: 3px;
  color: #e0e0e0;
  font-size: 13px;
}

.info-select {
  padding: 3px 6px;
  background: #1e1e1e;
  border: 1px solid #444;
  border-radius: 3px;
  color: #e0e0e0;
  font-size: 13px;
}

.context-menu {
  position: absolute;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.5);
  z-index: 100;
  min-width: 150px;
}

.context-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  border: none;
  background: transparent;
  color: #e0e0e0;
  font-size: 13px;
  text-align: left;
  cursor: pointer;
}

.context-menu button:hover {
  background: #3a3a3a;
}

.context-menu button:disabled {
  color: #666;
  cursor: default;
}

.context-menu hr {
  border: none;
  border-top: 1px solid #444;
  margin: 4px 0;
}
</style>
