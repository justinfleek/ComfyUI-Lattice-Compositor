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
    <div
      class="property-keyframes"
      ref="keyframeTrackRef"
      @click="handleTrackClick"
    >
      <!-- Keyframe diamonds - only in keyframes mode -->
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
import { computed, ref } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { AnimatableProperty, Keyframe, InterpolationType } from '@/types/project';
import { easingGroups, type EasingName } from '@/services/easing';

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
  (e: 'selectProperty', propertyId: string, addToSelection: boolean): void;
}>();

// Property ID for graph selection
const propertyId = computed(() => {
  return `${props.layerId}-${props.propertyPath.replace('.', '-')}`;
});

const store = useCompositorStore();
const currentFrame = computed(() => store.currentFrame);
const keyframeTrackRef = ref<HTMLDivElement | null>(null);

// Easing menu state
const easingMenuKeyframe = ref<Keyframe<any> | null>(null);
const easingMenuPosition = ref({ left: '0px', top: '0px' });

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

// Handle click on track area - in graph mode, select this property
function handleTrackClick(event: MouseEvent) {
  if (props.viewMode === 'graph') {
    emit('selectProperty', propertyId.value, event.shiftKey);
  }
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

</style>
