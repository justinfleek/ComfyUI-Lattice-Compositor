<template>
  <div class="property-track-row">
    <div class="property-info">
      <!-- STOPWATCH BUTTON - Fixed position on left -->
      <button
        class="stopwatch-btn"
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
          />
          <span class="value-separator">,</span>
          <input
            type="number"
            :value="property.value.y"
            @change="updateVectorY"
            class="value-input"
            step="1"
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
    <div class="property-keyframes">
      <!-- Existing keyframe diamonds - these show WHERE keyframes are on timeline -->
      <div
        v-for="kf in property.keyframes"
        :key="kf.id"
        class="keyframe-diamond"
        :class="{ selected: selectedKeyframeIds.includes(kf.id) }"
        :style="{ left: `${(kf.frame / frameCount) * 100}%` }"
        @click.stop="selectKeyframe(kf.id, $event)"
        @dblclick.stop="editKeyframe(kf)"
        :title="`Frame ${kf.frame}: ${JSON.stringify(kf.value)}`"
      >◆</div>

      <!-- Playhead position indicator (vertical line showing current frame) -->
      <div
        class="playhead-marker"
        :style="{ left: `${(currentFrame / frameCount) * 100}%` }"
      ></div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { AnimatableProperty } from '@/types/project';

const props = defineProps<{
  layerId: string;
  propertyPath: string;
  name: string;
  property: AnimatableProperty<any>;
  frameCount: number;
  selectedKeyframeIds: string[];
}>();

const emit = defineEmits<{
  (e: 'selectKeyframe', id: string, addToSelection: boolean): void;
}>();

const store = useCompositorStore();
const currentFrame = computed(() => store.currentFrame);

const hasKeyframeAtCurrentFrame = computed(() => {
  return props.property.keyframes?.some(kf => kf.frame === currentFrame.value) ?? false;
});

const isVectorValue = computed(() => {
  const val = props.property.value;
  return typeof val === 'object' && val !== null && 'x' in val && 'y' in val;
});

function updateVectorX(event: Event) {
  const input = event.target as HTMLInputElement;
  const newX = parseFloat(input.value);
  if (!isNaN(newX)) {
    const newValue = { ...props.property.value, x: newX };
    updatePropertyValue(newValue);
  }
}

function updateVectorY(event: Event) {
  const input = event.target as HTMLInputElement;
  const newY = parseFloat(input.value);
  if (!isNaN(newY)) {
    const newValue = { ...props.property.value, y: newY };
    updatePropertyValue(newValue);
  }
}

function updateScalarValue(event: Event) {
  const input = event.target as HTMLInputElement;
  const newValue = parseFloat(input.value);
  if (!isNaN(newValue)) {
    updatePropertyValue(newValue);
  }
}

function updatePropertyValue(newValue: any) {
  // Update the property value in the store
  const layer = store.layers.find(l => l.id === props.layerId);
  if (!layer) return;

  if (props.propertyPath === 'opacity') {
    layer.opacity.value = newValue;
  } else if (props.propertyPath.startsWith('transform.')) {
    const propName = props.propertyPath.split('.')[1];
    (layer.transform as any)[propName].value = newValue;
  }
}

function selectKeyframe(id: string, event: MouseEvent) {
  emit('selectKeyframe', id, event.shiftKey);
}

function editKeyframe(kf: any) {
  // TODO: Open graph editor or value editor
  console.log('Edit keyframe:', kf);
}

function toggleKeyframe() {
  const frame = currentFrame.value;
  const existingKf = props.property.keyframes?.find(kf => kf.frame === frame);

  console.log('[PropertyTrack] toggleKeyframe called for layer:', props.layerId, 'property:', props.propertyPath, 'frame:', frame, 'existing:', existingKf?.id);

  if (existingKf) {
    console.log('[PropertyTrack] Removing keyframe:', existingKf.id);
    store.removeKeyframe(props.layerId, props.propertyPath, existingKf.id);
  } else {
    // Note: store.addKeyframe uses store.currentFrame internally, so we don't pass frame
    console.log('[PropertyTrack] Adding keyframe at frame', frame, 'with value:', props.property.value);
    store.addKeyframe(props.layerId, props.propertyPath, props.property.value);
  }
}
</script>

<style scoped>
.property-track-row {
  display: flex;
  height: 22px;
  background: #222;
  border-bottom: 1px solid #1a1a1a;
}

.property-info {
  display: flex;
  align-items: center;
  width: 236px;
  min-width: 236px;
  padding-left: 32px; /* 16px (twirl-down width) + 16px indent */
  gap: 6px;
  background: #1e1e1e;
  border-right: 1px solid #333;
  box-sizing: border-box;
}

.stopwatch-btn {
  width: 16px;
  height: 16px;
  padding: 0;
  border: none;
  background: transparent;
  color: #555;
  cursor: pointer;
  font-size: 10px;
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
}

.stopwatch-btn:hover {
  color: #999;
}

.stopwatch-btn.active {
  color: #f5c542;
}

.property-name {
  font-size: 11px;
  color: #888;
  min-width: 55px;
}

.property-value-inputs {
  display: flex;
  align-items: center;
  gap: 2px;
  margin-left: auto;
  padding-right: 4px;
}

.value-input {
  width: 45px;
  padding: 1px 4px;
  border: 1px solid #333;
  background: #1a1a1a;
  color: #7c9cff;
  font-family: monospace;
  font-size: 10px;
  border-radius: 2px;
  text-align: right;
}

.value-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.value-separator {
  color: #555;
  font-size: 10px;
}

.property-keyframes {
  position: relative;
  flex: 1;
  background: #1a1a1a;
}

.keyframe-diamond {
  position: absolute;
  top: 50%;
  transform: translate(-50%, -50%);
  font-size: 9px;
  color: #f5c542;
  cursor: pointer;
  user-select: none;
  z-index: 2;
}

.keyframe-diamond:hover {
  color: #ffdd77;
  transform: translate(-50%, -50%) scale(1.3);
}

.keyframe-diamond.selected {
  color: #ff9500;
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
</style>
