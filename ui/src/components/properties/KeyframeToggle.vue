<template>
  <button
    class="keyframe-toggle"
    :class="{
      animated: property.animated,
      'has-keyframe': hasKeyframeAtCurrentFrame,
      'has-expression': hasExpression
    }"
    @click="handleClick"
    :title="buttonTitle"
  >
    <i class="pi" :class="iconClass" />
  </button>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useExpressionEditor } from "@/composables/useExpressionEditor";
import { useCompositorStore } from "@/stores/compositorStore";
import { useAnimationStore } from "@/stores/animationStore";
import type {
  AnimatableProperty,
  BezierHandle,
  Keyframe,
} from "@/types/project";

interface Props {
  property: AnimatableProperty;
  layerId: string;
  propertyPath?: string; // Optional path for identifying the property
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: "keyframeAdded", keyframe: Keyframe): void;
  (e: "keyframeRemoved", keyframeId: string): void;
  (e: "animationToggled", animated: boolean): void;
}>();

const store = useCompositorStore();
const animationStore = useAnimationStore();
const expressionEditor = useExpressionEditor();

// Check if there's a keyframe at current frame
const hasKeyframeAtCurrentFrame = computed(() => {
  if (!props.property.animated) return false;
  return props.property.keyframes.some((k) => k.frame === animationStore.getCurrentFrame(store));
});

// Check if property has an expression
const hasExpression = computed(() => {
  return props.property.expression?.enabled ?? false;
});

// Get the keyframe at current frame (if exists)
const keyframeAtCurrentFrame = computed(() => {
  if (!props.property.animated) return null;
  return (
    props.property.keyframes.find((k) => k.frame === animationStore.getCurrentFrame(store)) || null
  );
});

// Icon class based on state
const iconClass = computed(() => {
  if (hasKeyframeAtCurrentFrame.value) {
    return "pi-circle-fill"; // Filled diamond/circle for keyframe present
  }
  if (props.property.animated) {
    return "pi-circle"; // Empty circle for animated but no keyframe here
  }
  return "pi-times"; // X for not animated (no PrimeVue diamond icon available)
});

// Button title
const buttonTitle = computed(() => {
  const exprHint = "\nAlt+click: Add expression";
  if (hasExpression.value) {
    return "Expression active (Alt+click to edit)";
  }
  if (hasKeyframeAtCurrentFrame.value) {
    return `Remove keyframe at current frame${exprHint}`;
  }
  if (props.property.animated) {
    return `Add keyframe at current frame${exprHint}`;
  }
  return `Enable animation (add keyframe)${exprHint}`;
});

// Handle click - Alt+click opens expression mode
function handleClick(event: MouseEvent): void {
  if (event.altKey) {
    // Alt+click: Open expression editor
    expressionEditor.openExpressionEditor(
      props.property,
      props.layerId,
      props.propertyPath || "",
    );
  } else {
    // Normal click: Toggle keyframe
    toggleKeyframe();
  }
}

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
  const defaultHandle: BezierHandle = { frame: 0, value: 0, enabled: false };

  const newKeyframe: Keyframe = {
    id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    frame: animationStore.getCurrentFrame(store),
    value: props.property.value,
    interpolation: "linear",
    inHandle: { ...defaultHandle },
    outHandle: { ...defaultHandle },
    controlMode: "smooth",
  };

  // Enable animation if not already
  if (!props.property.animated) {
    props.property.animated = true;
    emit("animationToggled", true);
  }

  // Add keyframe and sort by frame
  props.property.keyframes.push(newKeyframe);
  props.property.keyframes.sort((a, b) => a.frame - b.frame);

  emit("keyframeAdded", newKeyframe);
}

function removeKeyframe(): void {
  const keyframe = keyframeAtCurrentFrame.value;
  if (!keyframe) return;

  const index = props.property.keyframes.findIndex((k) => k.id === keyframe.id);
  if (index >= 0) {
    props.property.keyframes.splice(index, 1);
    emit("keyframeRemoved", keyframe.id);
  }

  // If no keyframes left, disable animation
  if (props.property.keyframes.length === 0) {
    props.property.animated = false;
    emit("animationToggled", false);
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

.keyframe-toggle.has-expression {
  color: #EC4899; /* Pink for expression */
  text-shadow: 0 0 4px rgba(236, 72, 153, 0.5);
}

.keyframe-toggle.has-expression:hover {
  color: #F472B6;
}

.keyframe-toggle i {
  font-size: 12px;
}
</style>
