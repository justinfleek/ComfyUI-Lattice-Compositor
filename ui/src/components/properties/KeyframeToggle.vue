<template>
  <button
    class="keyframe-toggle"
    :class="{
      animated: property.animated,
      'has-keyframe': hasKeyframeAtCurrentFrame
    }"
    @click="toggleKeyframe"
    :title="buttonTitle"
  >
    <i class="pi" :class="iconClass" />
  </button>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { AnimatableProperty, Keyframe, BezierHandle } from '@/types/project';

interface Props {
  property: AnimatableProperty<any>;
  layerId: string;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: 'keyframeAdded', keyframe: Keyframe<any>): void;
  (e: 'keyframeRemoved', keyframeId: string): void;
  (e: 'animationToggled', animated: boolean): void;
}>();

const store = useCompositorStore();

// Check if there's a keyframe at current frame
const hasKeyframeAtCurrentFrame = computed(() => {
  if (!props.property.animated) return false;
  return props.property.keyframes.some(k => k.frame === store.currentFrame);
});

// Get the keyframe at current frame (if exists)
const keyframeAtCurrentFrame = computed(() => {
  if (!props.property.animated) return null;
  return props.property.keyframes.find(k => k.frame === store.currentFrame) || null;
});

// Icon class based on state
const iconClass = computed(() => {
  if (hasKeyframeAtCurrentFrame.value) {
    return 'pi-circle-fill'; // Filled diamond/circle for keyframe present
  }
  if (props.property.animated) {
    return 'pi-circle'; // Empty circle for animated but no keyframe here
  }
  return 'pi-stopwatch'; // Stopwatch for not animated
});

// Button title
const buttonTitle = computed(() => {
  if (hasKeyframeAtCurrentFrame.value) {
    return 'Remove keyframe at current frame';
  }
  if (props.property.animated) {
    return 'Add keyframe at current frame';
  }
  return 'Enable animation (add keyframe)';
});

// Toggle keyframe
function toggleKeyframe(): void {
  if (hasKeyframeAtCurrentFrame.value) {
    // Remove keyframe at current frame
    removeKeyframe();
  } else {
    // Add keyframe at current frame
    addKeyframe();
  }
}

function addKeyframe(): void {
  const defaultHandles: BezierHandle = { x: 0.33, y: 0.33 };

  const newKeyframe: Keyframe<any> = {
    id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    frame: store.currentFrame,
    value: props.property.value,
    interpolation: 'bezier',
    inHandle: { ...defaultHandles },
    outHandle: { ...defaultHandles },
    handlesBroken: false
  };

  // Enable animation if not already
  if (!props.property.animated) {
    props.property.animated = true;
    emit('animationToggled', true);
  }

  // Add keyframe and sort by frame
  props.property.keyframes.push(newKeyframe);
  props.property.keyframes.sort((a, b) => a.frame - b.frame);

  emit('keyframeAdded', newKeyframe);
}

function removeKeyframe(): void {
  const keyframe = keyframeAtCurrentFrame.value;
  if (!keyframe) return;

  const index = props.property.keyframes.findIndex(k => k.id === keyframe.id);
  if (index >= 0) {
    props.property.keyframes.splice(index, 1);
    emit('keyframeRemoved', keyframe.id);
  }

  // If no keyframes left, disable animation
  if (props.property.keyframes.length === 0) {
    props.property.animated = false;
    emit('animationToggled', false);
  }
}
</script>

<style scoped>
.keyframe-toggle {
  width: 20px;
  height: 20px;
  padding: 0;
  border: none;
  background: transparent;
  color: #666;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  border-radius: 3px;
  transition: all 0.1s;
}

.keyframe-toggle:hover {
  background: #3a3a3a;
  color: #aaa;
}

.keyframe-toggle.animated {
  color: #4a90d9;
}

.keyframe-toggle.has-keyframe {
  color: #ffc107;
}

.keyframe-toggle.has-keyframe:hover {
  color: #ffca28;
}

.keyframe-toggle i {
  font-size: 12px;
}
</style>
