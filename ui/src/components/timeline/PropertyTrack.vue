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
      <span class="property-value">{{ formattedValue }}</span>
    </div>
    <div class="property-keyframes" :style="{ width: trackWidth + 'px' }">
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
  trackWidth: number;
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

const formattedValue = computed(() => {
  const val = props.property.value;
  if (typeof val === 'number') {
    return val.toFixed(1);
  } else if (typeof val === 'object' && val !== null) {
    if ('x' in val && 'y' in val) {
      return `${(val as any).x.toFixed(1)}, ${(val as any).y.toFixed(1)}`;
    }
  }
  return String(val);
});

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

  if (existingKf) {
    store.removeKeyframe(props.layerId, props.propertyPath, existingKf.id);
  } else {
    store.addKeyframe(props.layerId, props.propertyPath, frame, props.property.value);
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
  width: 220px;
  min-width: 220px;
  padding-left: 20px;
  gap: 6px;
  background: #1e1e1e;
  border-right: 1px solid #333;
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

.property-value {
  color: #7c9cff;
  font-family: monospace;
  font-size: 10px;
  margin-left: auto;
  padding-right: 8px;
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
