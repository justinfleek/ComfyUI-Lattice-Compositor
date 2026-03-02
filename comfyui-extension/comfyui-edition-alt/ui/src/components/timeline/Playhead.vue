<template>
  <div
    class="playhead"
    :style="{ left: `${position}px` }"
    @mousedown.stop="startDrag"
  >
    <div class="playhead-head" />
    <div class="playhead-line" />
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { useAnimationStore } from "@/stores/animationStore";
import { useProjectStore } from "@/stores/projectStore";

interface Props {
  trackOffset: number; // Offset from left where tracks start
  trackWidth: number; // Width of track area
}

const props = defineProps<Props>();

const emit = defineEmits<(e: "scrub", frame: number) => void>();

const animationStore = useAnimationStore();
const projectStore = useProjectStore();

// Calculate position based on current frame
const position = computed(() => {
  const frameCount = projectStore.getFrameCount();
  const progress = animationStore.currentFrame / (frameCount - 1);
  return props.trackOffset + progress * props.trackWidth;
});

// Drag state
const isDragging = ref(false);

function startDrag(event: MouseEvent) {
  isDragging.value = true;
  document.addEventListener("mousemove", handleDrag);
  document.addEventListener("mouseup", stopDrag);
  handleDrag(event);
}

function handleDrag(event: MouseEvent) {
  if (!isDragging.value) return;

  const parent = (event.target as HTMLElement).closest(".timeline-content");
  if (!parent) return;

  const rect = parent.getBoundingClientRect();
  const x = event.clientX - rect.left - props.trackOffset;
  const progress = Math.max(0, Math.min(1, x / props.trackWidth));
  const frame = Math.round(progress * (projectStore.getFrameCount() - 1));

  emit("scrub", frame);
}

function stopDrag() {
  isDragging.value = false;
  document.removeEventListener("mousemove", handleDrag);
  document.removeEventListener("mouseup", stopDrag);
}
</script>

<style scoped>
.playhead {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 2px;
  z-index: 10;
  cursor: ew-resize;
  transform: translateX(-1px);
}

.playhead-head {
  position: absolute;
  top: 0;
  left: 50%;
  transform: translateX(-50%);
  width: 12px;
  height: 12px;
  background: #ff4444;
  border-radius: 2px 2px 0 0;
  clip-path: polygon(0 0, 100% 0, 100% 50%, 50% 100%, 0 50%);
}

.playhead-line {
  position: absolute;
  top: 12px;
  bottom: 0;
  left: 0;
  width: 2px;
  background: #ff4444;
}

.playhead:hover .playhead-head,
.playhead:hover .playhead-line {
  background: #ff6666;
}
</style>
