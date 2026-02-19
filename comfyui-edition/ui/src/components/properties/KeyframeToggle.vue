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
import { useAnimationStore } from "@/stores/animationStore";
import { addKeyframe as addKeyframeToStore, removeKeyframe as removeKeyframeFromStore } from "@/stores/keyframeStore/crud";
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

const animationStore = useAnimationStore();
const expressionEditor = useExpressionEditor();

// Check if there's a keyframe at current frame
const hasKeyframeAtCurrentFrame = computed(() => {
  if (!props.property.animated) return false;
  const currentFrame = animationStore.currentFrame;
  return props.property.keyframes.some((k) => k.frame === currentFrame);
});

// Check if property has an expression
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
const hasExpression = computed(() => {
  const property = props.property;
  const expression = (property !== null && property !== undefined && typeof property === "object" && "expression" in property && property.expression !== null && property.expression !== undefined) ? property.expression : undefined;
  return (expression !== null && expression !== undefined && typeof expression === "object" && "enabled" in expression && typeof expression.enabled === "boolean") ? expression.enabled : false;
});

// Get the keyframe at current frame (if exists)
const keyframeAtCurrentFrame = computed(() => {
  if (!props.property.animated) return null;
  const currentFrame = animationStore.currentFrame;
  return (
    props.property.keyframes.find((k) => k.frame === currentFrame) || null
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
  // Use keyframeStore.addKeyframe for deterministic ID generation
  // This ensures consistency with the rest of the system
  const frame = animationStore.currentFrame;
  const propertyPath = props.propertyPath || props.property.name;
  
  // Use store function for deterministic ID generation
  const newKeyframe = addKeyframeToStore(
    props.layerId,
    propertyPath,
    props.property.value,
    frame,
  );

  emit("keyframeAdded", newKeyframe);
}

function removeKeyframe(): void {
  const keyframe = keyframeAtCurrentFrame.value;
  if (!keyframe) return;

  // Use keyframeStore.removeKeyframe for consistency
  const propertyPath = props.propertyPath || props.property.name;
  
  removeKeyframeFromStore(props.layerId, propertyPath, keyframe.id);
  
  emit("keyframeRemoved", keyframe.id);

  // Note: removeKeyframeFromStore handles animation flag and history
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
