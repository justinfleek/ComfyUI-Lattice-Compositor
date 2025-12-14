<template>
  <div class="property-track-row">
    <div class="property-info">
      <button
        class="stopwatch-btn"
        :class="{ active: property.animated }"
        @click.stop="toggleAnimation"
        title="Enable/disable animation"
      >
        {{ property.animated ? '⏱' : '○' }}
      </button>
      <button
        class="keyframe-btn"
        :class="{ active: hasKeyframeAtCurrentFrame }"
        @click.stop="toggleKeyframe"
        :title="hasKeyframeAtCurrentFrame ? 'Remove Keyframe' : 'Add Keyframe'"
      >
        {{ hasKeyframeAtCurrentFrame ? '◆' : '◇' }}
      </button>
      <span class="property-name">{{ name }}</span>
      <div class="property-value-inputs">
        <template v-if="isVectorValue">
          <input
            type="number"
            :value="property.value.x"
            @change="updateVectorX"
            class="value-input"
            step="1"
            title="X"
          />
          <input
            type="number"
            :value="property.value.y"
            @change="updateVectorY"
            class="value-input"
            step="1"
            title="Y"
          />
          <input
            type="number"
            :value="property.value.z || 0"
            @change="updateVectorZ"
            class="value-input"
            step="1"
            title="Z"
          />
        </template>
        <template v-else>
          <input
            type="number"
            :value="property.value"
            @change="updateScalarValue"
            class="value-input"
            :step="name === 'Opacity' ? 1 : 0.1"
          />
        </template>
      </div>
    </div>
    <div class="property-keyframes" ref="keyframeTrackRef">
      <!-- KEYFRAME MODE: Show diamonds -->
      <template v-if="viewMode === 'keyframes'">
        <div
          v-for="kf in property.keyframes"
          :key="kf.id"
          class="keyframe-diamond"
          :class="{ selected: selectedKeyframeIds.includes(kf.id) }"
          :style="{ left: `${(kf.frame / frameCount) * 100}%` }"
          @mousedown.stop="startKeyframeDrag(kf, $event)"
          @click.stop="selectKeyframe(kf.id, $event)"
          @contextmenu.prevent="showEasingMenu(kf, $event)"
          :title="`Frame ${kf.frame}: ${JSON.stringify(kf.value)} (${kf.interpolation || 'linear'})`"
        >◆</div>
      </template>

      <!-- GRAPH MODE: Show bezier curves -->
      <template v-else>
        <canvas
          ref="graphCanvasRef"
          class="graph-canvas"
          @mousedown="handleGraphMouseDown"
        ></canvas>
        <!-- Keyframe points in graph mode -->
        <div
          v-for="kf in property.keyframes"
          :key="'graph-' + kf.id"
          class="graph-keyframe-point"
          :class="{ selected: selectedKeyframeIds.includes(kf.id) }"
          :style="getGraphKeyframeStyle(kf)"
          @mousedown.stop="startGraphKeyframeDrag(kf, $event)"
          @click.stop="selectKeyframe(kf.id, $event)"
          :title="`Frame ${kf.frame}: ${getScalarValue(kf.value)}`"
        ></div>
        <!-- Bezier handles for selected keyframes -->
        <template v-for="kf in property.keyframes" :key="'handles-' + kf.id">
          <template v-if="selectedKeyframeIds.includes(kf.id) && kf.interpolation === 'bezier'">
            <!-- In handle -->
            <div
              v-if="kf.inHandle?.enabled"
              class="bezier-handle in-handle"
              :style="getHandleStyle(kf, 'in')"
              @mousedown.stop="startHandleDrag(kf, 'in', $event)"
            ></div>
            <svg v-if="kf.inHandle?.enabled" class="handle-line-svg">
              <line
                :x1="getHandleLineCoords(kf, 'in').x1"
                :y1="getHandleLineCoords(kf, 'in').y1"
                :x2="getHandleLineCoords(kf, 'in').x2"
                :y2="getHandleLineCoords(kf, 'in').y2"
                class="handle-line in-line"
              />
            </svg>
            <!-- Out handle -->
            <div
              v-if="kf.outHandle?.enabled"
              class="bezier-handle out-handle"
              :style="getHandleStyle(kf, 'out')"
              @mousedown.stop="startHandleDrag(kf, 'out', $event)"
            ></div>
            <svg v-if="kf.outHandle?.enabled" class="handle-line-svg">
              <line
                :x1="getHandleLineCoords(kf, 'out').x1"
                :y1="getHandleLineCoords(kf, 'out').y1"
                :x2="getHandleLineCoords(kf, 'out').x2"
                :y2="getHandleLineCoords(kf, 'out').y2"
                class="handle-line out-line"
              />
            </svg>
          </template>
        </template>
      </template>

      <div
        class="playhead-marker"
        :style="{ left: `${(currentFrame / frameCount) * 100}%` }"
      ></div>

      <!-- Easing dropdown popup -->
      <div
        v-if="easingMenuKeyframe"
        class="easing-menu"
        :style="easingMenuPosition"
        @click.stop
      >
        <div class="easing-menu-header">
          <span>Easing</span>
          <button class="close-btn" @click="closeEasingMenu">×</button>
        </div>
        <div class="easing-menu-content">
          <div
            v-for="(groupEasings, groupName) in easingGroups"
            :key="groupName"
            class="easing-group"
          >
            <div class="easing-group-name">{{ groupName }}</div>
            <div class="easing-options">
              <button
                v-for="easingName in groupEasings"
                :key="easingName"
                class="easing-option"
                :class="{ active: easingMenuKeyframe?.interpolation === easingName }"
                @click="setEasing(easingName)"
                :title="easingName"
              >
                {{ formatEasingName(easingName) }}
              </button>
            </div>
          </div>
          <!-- Special options -->
          <div class="easing-group">
            <div class="easing-group-name">Special</div>
            <div class="easing-options">
              <button
                class="easing-option"
                :class="{ active: easingMenuKeyframe?.interpolation === 'hold' }"
                @click="setEasing('hold')"
                title="Hold (step)"
              >
                Hold
              </button>
              <button
                class="easing-option"
                :class="{ active: easingMenuKeyframe?.interpolation === 'bezier' }"
                @click="setEasing('bezier')"
                title="Custom Bezier"
              >
                Bezier
              </button>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, watch, onMounted, onUnmounted, nextTick } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { AnimatableProperty, Keyframe, InterpolationType } from '@/types/project';
import { easingGroups, type EasingName } from '@/services/easing';
import { interpolateValue } from '@/services/interpolation';

const props = defineProps<{
  layerId: string;
  propertyPath: string;
  name: string;
  property: AnimatableProperty<any>;
  frameCount: number;
  selectedKeyframeIds: string[];
  viewMode: 'keyframes' | 'graph';
}>();

const emit = defineEmits<{
  (e: 'selectKeyframe', id: string, addToSelection: boolean): void;
}>();

const store = useCompositorStore();
const currentFrame = computed(() => store.currentFrame);
const keyframeTrackRef = ref<HTMLDivElement | null>(null);
const graphCanvasRef = ref<HTMLCanvasElement | null>(null);

// Easing menu state
const easingMenuKeyframe = ref<Keyframe<any> | null>(null);
const easingMenuPosition = ref({ left: '0px', top: '0px' });

// Graph mode state
const graphValueRange = computed(() => {
  const keyframes = props.property.keyframes || [];
  if (keyframes.length === 0) {
    return { min: 0, max: 100 };
  }

  const values = keyframes.map(kf => getScalarValue(kf.value));
  const min = Math.min(...values);
  const max = Math.max(...values);
  const padding = Math.max((max - min) * 0.2, 10);

  return {
    min: min - padding,
    max: max + padding
  };
});

// Get scalar value from potentially vector value
function getScalarValue(value: any): number {
  if (typeof value === 'number') return value;
  if (typeof value === 'object' && value !== null) {
    // For vectors, use Y component for now (most useful for position)
    return value.y ?? value.x ?? 0;
  }
  return 0;
}

// Convert frame to X position (percentage)
function frameToX(frame: number): number {
  return (frame / props.frameCount) * 100;
}

// Convert value to Y position (percentage, inverted because canvas Y is top-down)
function valueToY(value: number): number {
  const range = graphValueRange.value;
  const normalized = (value - range.min) / (range.max - range.min);
  return (1 - normalized) * 100;
}

// Get style for keyframe point in graph mode
function getGraphKeyframeStyle(kf: Keyframe<any>): Record<string, string> {
  const x = frameToX(kf.frame);
  const y = valueToY(getScalarValue(kf.value));
  return {
    left: `${x}%`,
    top: `${y}%`
  };
}

// Get style for bezier handle
function getHandleStyle(kf: Keyframe<any>, handleType: 'in' | 'out'): Record<string, string> {
  const handle = handleType === 'in' ? kf.inHandle : kf.outHandle;
  if (!handle?.enabled) return { display: 'none' };

  const kfX = frameToX(kf.frame);
  const kfY = valueToY(getScalarValue(kf.value));

  // Handle offset is in frames/value units
  const handleFrame = kf.frame + handle.frame;
  const handleValue = getScalarValue(kf.value) + handle.value;

  const handleX = frameToX(handleFrame);
  const handleY = valueToY(handleValue);

  return {
    left: `${handleX}%`,
    top: `${handleY}%`
  };
}

// Get line coordinates for handle
function getHandleLineCoords(kf: Keyframe<any>, handleType: 'in' | 'out') {
  const handle = handleType === 'in' ? kf.inHandle : kf.outHandle;
  if (!handle?.enabled) return { x1: '0', y1: '0', x2: '0', y2: '0' };

  const kfX = frameToX(kf.frame);
  const kfY = valueToY(getScalarValue(kf.value));

  const handleFrame = kf.frame + handle.frame;
  const handleValue = getScalarValue(kf.value) + handle.value;

  const handleX = frameToX(handleFrame);
  const handleY = valueToY(handleValue);

  return {
    x1: `${kfX}%`,
    y1: `${kfY}%`,
    x2: `${handleX}%`,
    y2: `${handleY}%`
  };
}

// Draw graph on canvas
function drawGraph() {
  const canvas = graphCanvasRef.value;
  if (!canvas) return;

  const ctx = canvas.getContext('2d');
  if (!ctx) return;

  // Set canvas size to match container
  const rect = canvas.parentElement?.getBoundingClientRect();
  if (!rect) return;

  canvas.width = rect.width;
  canvas.height = rect.height;

  const w = canvas.width;
  const h = canvas.height;

  // Clear
  ctx.clearRect(0, 0, w, h);

  // Draw grid
  ctx.strokeStyle = '#333';
  ctx.lineWidth = 1;

  // Vertical grid lines (every 10 frames or so)
  const frameStep = Math.max(1, Math.floor(props.frameCount / 10));
  for (let f = 0; f <= props.frameCount; f += frameStep) {
    const x = (f / props.frameCount) * w;
    ctx.beginPath();
    ctx.moveTo(x, 0);
    ctx.lineTo(x, h);
    ctx.stroke();
  }

  // Horizontal grid lines
  const range = graphValueRange.value;
  const valueStep = (range.max - range.min) / 4;
  for (let v = range.min; v <= range.max; v += valueStep) {
    const y = ((v - range.min) / (range.max - range.min)) * h;
    ctx.beginPath();
    ctx.moveTo(0, h - y);
    ctx.lineTo(w, h - y);
    ctx.stroke();
  }

  // Draw curve
  const keyframes = props.property.keyframes || [];
  if (keyframes.length < 2) return;

  // Sort keyframes by frame
  const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);

  // Two-pass rendering: black outline then colored
  for (let pass = 0; pass < 2; pass++) {
    ctx.strokeStyle = pass === 0 ? '#000' : '#7c9cff';
    ctx.lineWidth = pass === 0 ? 4 : 2;

    ctx.beginPath();

    for (let i = 0; i < sorted.length - 1; i++) {
      const kf1 = sorted[i];
      const kf2 = sorted[i + 1];

      const x1 = (kf1.frame / props.frameCount) * w;
      const y1 = h - ((getScalarValue(kf1.value) - range.min) / (range.max - range.min)) * h;
      const x2 = (kf2.frame / props.frameCount) * w;
      const y2 = h - ((getScalarValue(kf2.value) - range.min) / (range.max - range.min)) * h;

      if (i === 0) {
        ctx.moveTo(x1, y1);
      }

      const interpolation = kf1.interpolation || 'linear';

      if (interpolation === 'hold') {
        // Step function
        ctx.lineTo(x2, y1);
        ctx.lineTo(x2, y2);
      } else if (interpolation === 'bezier' && kf1.outHandle?.enabled && kf2.inHandle?.enabled) {
        // Bezier curve
        const cp1x = ((kf1.frame + kf1.outHandle.frame) / props.frameCount) * w;
        const cp1y = h - ((getScalarValue(kf1.value) + kf1.outHandle.value - range.min) / (range.max - range.min)) * h;
        const cp2x = ((kf2.frame + kf2.inHandle.frame) / props.frameCount) * w;
        const cp2y = h - ((getScalarValue(kf2.value) + kf2.inHandle.value - range.min) / (range.max - range.min)) * h;

        ctx.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x2, y2);
      } else {
        // Linear
        ctx.lineTo(x2, y2);
      }
    }

    ctx.stroke();
  }
}

// Handle graph canvas mouse down
function handleGraphMouseDown(event: MouseEvent) {
  // Could be used for panning/zooming in the future
}

// Graph keyframe dragging
let graphDraggingKeyframe: Keyframe<any> | null = null;

function startGraphKeyframeDrag(kf: Keyframe<any>, event: MouseEvent) {
  graphDraggingKeyframe = kf;
  document.addEventListener('mousemove', handleGraphKeyframeDrag);
  document.addEventListener('mouseup', stopGraphKeyframeDrag);
  event.preventDefault();
}

function handleGraphKeyframeDrag(event: MouseEvent) {
  if (!graphDraggingKeyframe || !keyframeTrackRef.value) return;

  const rect = keyframeTrackRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;

  // Convert to frame and value
  const newFrame = Math.round((x / rect.width) * props.frameCount);
  const clampedFrame = Math.max(0, Math.min(props.frameCount - 1, newFrame));

  const range = graphValueRange.value;
  const normalizedY = 1 - (y / rect.height);
  const newValue = range.min + normalizedY * (range.max - range.min);

  // Update keyframe
  store.moveKeyframe(props.layerId, props.propertyPath, graphDraggingKeyframe.id, clampedFrame);

  // Update value - handle both scalar and vector
  if (isVectorValue.value) {
    const currentValue = props.property.value;
    store.setPropertyValue(props.layerId, props.propertyPath, { ...currentValue, y: newValue });
  } else {
    store.setPropertyValue(props.layerId, props.propertyPath, newValue);
  }
}

function stopGraphKeyframeDrag() {
  graphDraggingKeyframe = null;
  document.removeEventListener('mousemove', handleGraphKeyframeDrag);
  document.removeEventListener('mouseup', stopGraphKeyframeDrag);
}

// Handle dragging
let draggingHandle: { kf: Keyframe<any>; type: 'in' | 'out' } | null = null;

function startHandleDrag(kf: Keyframe<any>, handleType: 'in' | 'out', event: MouseEvent) {
  draggingHandle = { kf, type: handleType };
  document.addEventListener('mousemove', handleHandleDrag);
  document.addEventListener('mouseup', stopHandleDrag);
  event.preventDefault();
}

function handleHandleDrag(event: MouseEvent) {
  if (!draggingHandle || !keyframeTrackRef.value) return;

  const rect = keyframeTrackRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const y = event.clientY - rect.top;

  const kf = draggingHandle.kf;
  const handleType = draggingHandle.type;

  // Convert mouse position to frame/value
  const mouseFrame = (x / rect.width) * props.frameCount;
  const range = graphValueRange.value;
  const mouseValue = range.min + (1 - y / rect.height) * (range.max - range.min);

  // Calculate offset from keyframe
  const frameOffset = mouseFrame - kf.frame;
  const valueOffset = mouseValue - getScalarValue(kf.value);

  // Create new handle
  const newHandle = {
    frame: frameOffset,
    value: valueOffset,
    enabled: true
  };

  // Update via store
  store.setKeyframeHandle(props.layerId, props.propertyPath, kf.id, handleType, newHandle);

  drawGraph();
}

function stopHandleDrag() {
  draggingHandle = null;
  document.removeEventListener('mousemove', handleHandleDrag);
  document.removeEventListener('mouseup', stopHandleDrag);
}

// Watch for changes and redraw graph
watch(
  () => [props.property.keyframes, props.viewMode, props.frameCount],
  () => {
    if (props.viewMode === 'graph') {
      nextTick(() => drawGraph());
    }
  },
  { deep: true }
);

// Draw graph on mount if in graph mode
onMounted(() => {
  if (props.viewMode === 'graph') {
    nextTick(() => drawGraph());
  }
  window.addEventListener('resize', drawGraph);
});

onUnmounted(() => {
  window.removeEventListener('resize', drawGraph);
});

const hasKeyframeAtCurrentFrame = computed(() => {
  return props.property.keyframes?.some(kf => kf.frame === currentFrame.value) ?? false;
});

const isVectorValue = computed(() => {
  const val = props.property.value;
  return typeof val === 'object' && val !== null && 'x' in val && 'y' in val;
});

function selectKeyframe(id: string, event: MouseEvent) {
  emit('selectKeyframe', id, event.shiftKey);
}

function toggleAnimation() {
  store.setPropertyAnimated(props.layerId, props.propertyPath, !props.property.animated);
}

function toggleKeyframe() {
  const frame = currentFrame.value;
  const existingKf = props.property.keyframes?.find(kf => kf.frame === frame);

  if (existingKf) {
    store.removeKeyframe(props.layerId, props.propertyPath, existingKf.id);
  } else {
    store.addKeyframe(props.layerId, props.propertyPath, props.property.value);
  }
}

function updateVectorX(event: Event) {
  const input = event.target as HTMLInputElement;
  const newX = parseFloat(input.value);
  if (!isNaN(newX)) {
    const newValue = { ...props.property.value, x: newX };
    store.setPropertyValue(props.layerId, props.propertyPath, newValue);
  }
}

function updateVectorY(event: Event) {
  const input = event.target as HTMLInputElement;
  const newY = parseFloat(input.value);
  if (!isNaN(newY)) {
    const newValue = { ...props.property.value, y: newY };
    store.setPropertyValue(props.layerId, props.propertyPath, newValue);
  }
}

function updateVectorZ(event: Event) {
  const input = event.target as HTMLInputElement;
  const newZ = parseFloat(input.value);
  if (!isNaN(newZ)) {
    const newValue = { ...props.property.value, z: newZ };
    store.setPropertyValue(props.layerId, props.propertyPath, newValue);
  }
}

function updateScalarValue(event: Event) {
  const input = event.target as HTMLInputElement;
  const newValue = parseFloat(input.value);
  if (!isNaN(newValue)) {
    store.setPropertyValue(props.layerId, props.propertyPath, newValue);
  }
}

// Keyframe dragging
let draggingKeyframe: { id: string; startFrame: number } | null = null;

function startKeyframeDrag(kf: any, event: MouseEvent) {
  draggingKeyframe = { id: kf.id, startFrame: kf.frame };
  document.addEventListener('mousemove', handleKeyframeDrag);
  document.addEventListener('mouseup', stopKeyframeDrag);
  event.preventDefault();
}

function handleKeyframeDrag(event: MouseEvent) {
  if (!draggingKeyframe || !keyframeTrackRef.value) return;

  const rect = keyframeTrackRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const newFrame = Math.round((x / rect.width) * props.frameCount);
  const clampedFrame = Math.max(0, Math.min(props.frameCount - 1, newFrame));

  store.moveKeyframe(props.layerId, props.propertyPath, draggingKeyframe.id, clampedFrame);
}

function stopKeyframeDrag() {
  draggingKeyframe = null;
  document.removeEventListener('mousemove', handleKeyframeDrag);
  document.removeEventListener('mouseup', stopKeyframeDrag);
}

// Easing menu functions
function showEasingMenu(kf: Keyframe<any>, event: MouseEvent) {
  easingMenuKeyframe.value = kf;

  // Position menu near the keyframe
  const trackRect = keyframeTrackRef.value?.getBoundingClientRect();
  if (trackRect) {
    const kfX = (kf.frame / props.frameCount) * trackRect.width;
    easingMenuPosition.value = {
      left: `${Math.min(kfX, trackRect.width - 200)}px`,
      top: '36px'
    };
  }

  // Close menu when clicking outside
  setTimeout(() => {
    document.addEventListener('click', closeEasingMenuOnOutsideClick);
  }, 0);
}

function closeEasingMenu() {
  easingMenuKeyframe.value = null;
  document.removeEventListener('click', closeEasingMenuOnOutsideClick);
}

function closeEasingMenuOnOutsideClick(event: MouseEvent) {
  const target = event.target as HTMLElement;
  if (!target.closest('.easing-menu')) {
    closeEasingMenu();
  }
}

function setEasing(easingName: InterpolationType) {
  if (!easingMenuKeyframe.value) return;

  store.setKeyframeInterpolation(
    props.layerId,
    props.propertyPath,
    easingMenuKeyframe.value.id,
    easingName
  );

  // Update local reference
  easingMenuKeyframe.value.interpolation = easingName;
}

function formatEasingName(name: EasingName): string {
  // Convert easeInQuad -> In, easeOutQuad -> Out, easeInOutQuad -> InOut
  if (name === 'linear') return 'Lin';
  if (name.startsWith('easeInOut')) return 'IO';
  if (name.startsWith('easeIn')) return 'In';
  if (name.startsWith('easeOut')) return 'Out';
  return name;
}
</script>

<style scoped>
.property-track-row {
  display: flex;
  height: 36px;
  background: #252525;
  border-bottom: 1px solid #1a1a1a;
}

.property-info {
  display: flex;
  align-items: center;
  width: 200px;
  min-width: 200px;
  padding-left: 12px;
  gap: 4px;
  background: #222;
  border-right: 1px solid #333;
  box-sizing: border-box;
}

.stopwatch-btn,
.keyframe-btn {
  width: 20px;
  height: 20px;
  padding: 0;
  border: none;
  background: transparent;
  color: #666;
  cursor: pointer;
  font-size: 12px;
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
  border-radius: 3px;
  transition: all 0.15s ease;
}

.stopwatch-btn:hover,
.keyframe-btn:hover {
  background: #3a3a3a;
  color: #ccc;
}

.stopwatch-btn.active {
  color: #4a90d9;
}

.keyframe-btn.active {
  color: #f5c542;
}

.property-name {
  font-size: 12px;
  color: #aaa;
  min-width: 55px;
  font-weight: 400;
}

.property-value-inputs {
  display: flex;
  align-items: center;
  gap: 2px;
  margin-left: auto;
  padding-right: 4px;
}

.value-input {
  width: 48px;
  padding: 4px 5px;
  border: 1px solid #3a3a3a;
  background: #1a1a1a;
  color: #7c9cff;
  font-family: 'SF Mono', Monaco, 'Cascadia Code', monospace;
  font-size: 11px;
  border-radius: 4px;
  text-align: right;
  transition: border-color 0.15s ease, background 0.15s ease;
}

.value-input:focus {
  outline: none;
  border-color: #7c9cff;
  background: #222;
}

.value-input:hover {
  border-color: #555;
}

.property-keyframes {
  position: relative;
  flex: 1;
  background: #1e1e1e;
}

.keyframe-diamond {
  position: absolute;
  top: 50%;
  transform: translate(-50%, -50%);
  font-size: 14px;
  color: #f5c542;
  cursor: grab;
  user-select: none;
  z-index: 2;
  padding: 6px;
  transition: transform 0.15s ease, color 0.15s ease, text-shadow 0.15s ease;
}

.keyframe-diamond:hover {
  color: #ffdd77;
  transform: translate(-50%, -50%) scale(1.4);
  text-shadow: 0 0 8px rgba(245, 197, 66, 0.5);
}

.keyframe-diamond.selected {
  color: #ffffff;
  text-shadow: 0 0 6px rgba(124, 156, 255, 0.6);
}

.keyframe-diamond:active {
  cursor: grabbing;
}

.playhead-marker {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  background: #ff4444;
  pointer-events: none;
  z-index: 1;
}

/* Easing menu styles */
.easing-menu {
  position: absolute;
  z-index: 100;
  background: #2d2d2d;
  border: 1px solid #444;
  border-radius: 8px;
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.5), 0 2px 8px rgba(0, 0, 0, 0.3);
  min-width: 220px;
  max-height: 360px;
  overflow-y: auto;
}

.easing-menu-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 10px 12px;
  border-bottom: 1px solid #3a3a3a;
  font-size: 12px;
  font-weight: 600;
  color: #e0e0e0;
  background: #333;
  border-radius: 8px 8px 0 0;
}

.close-btn {
  background: none;
  border: none;
  color: #888;
  cursor: pointer;
  font-size: 14px;
  padding: 0 4px;
}

.close-btn:hover {
  color: #fff;
}

.easing-menu-content {
  padding: 8px;
}

.easing-group {
  margin-bottom: 8px;
}

.easing-group:last-child {
  margin-bottom: 0;
}

.easing-group-name {
  font-size: 10px;
  color: #888;
  padding: 4px 6px 2px;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  font-weight: 500;
}

.easing-options {
  display: flex;
  gap: 3px;
}

.easing-option {
  flex: 1;
  padding: 6px 8px;
  border: none;
  background: #383838;
  color: #bbb;
  font-size: 11px;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.15s ease;
  font-weight: 500;
}

.easing-option:hover {
  background: #484848;
  color: #fff;
  transform: translateY(-1px);
}

.easing-option.active {
  background: #4a90d9;
  color: #fff;
  box-shadow: 0 2px 6px rgba(74, 144, 217, 0.3);
}

/* Graph mode styles */
.graph-canvas {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  pointer-events: auto;
}

.graph-keyframe-point {
  position: absolute;
  width: 10px;
  height: 10px;
  background: #f5c542;
  border: 2px solid #000;
  border-radius: 50%;
  transform: translate(-50%, -50%);
  cursor: grab;
  z-index: 5;
  transition: transform 0.1s ease, box-shadow 0.1s ease;
}

.graph-keyframe-point:hover {
  transform: translate(-50%, -50%) scale(1.3);
  box-shadow: 0 0 8px rgba(245, 197, 66, 0.6);
}

.graph-keyframe-point.selected {
  background: #fff;
  border-color: #7c9cff;
  box-shadow: 0 0 0 3px rgba(124, 156, 255, 0.4);
}

.graph-keyframe-point:active {
  cursor: grabbing;
}

.bezier-handle {
  position: absolute;
  width: 8px;
  height: 8px;
  border-radius: 50%;
  transform: translate(-50%, -50%);
  cursor: grab;
  z-index: 6;
  border: 1px solid #000;
}

.bezier-handle.in-handle {
  background: #4ecdc4;
}

.bezier-handle.out-handle {
  background: #ff6b6b;
}

.bezier-handle:hover {
  transform: translate(-50%, -50%) scale(1.3);
}

.bezier-handle:active {
  cursor: grabbing;
}

.handle-line-svg {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  pointer-events: none;
  z-index: 4;
  overflow: visible;
}

.handle-line {
  stroke-width: 1.5;
}

.handle-line.in-line {
  stroke: #4ecdc4;
}

.handle-line.out-line {
  stroke: #ff6b6b;
}
</style>
