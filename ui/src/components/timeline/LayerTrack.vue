<template>
  <div
    class="layer-track"
    :class="{
      selected: isSelected,
      locked: layer.locked,
      hidden: !layer.visible
    }"
    @click="selectLayer"
  >
    <!-- Layer info sidebar -->
    <div class="layer-info">
      <button
        class="icon-btn visibility-btn"
        :class="{ active: layer.visible }"
        @click.stop="toggleVisibility"
        :title="layer.visible ? 'Hide layer' : 'Show layer'"
      >
        <i :class="layer.visible ? 'pi pi-eye' : 'pi pi-eye-slash'" />
      </button>

      <button
        class="icon-btn lock-btn"
        :class="{ active: layer.locked }"
        @click.stop="toggleLock"
        :title="layer.locked ? 'Unlock layer' : 'Lock layer'"
      >
        <i :class="layer.locked ? 'pi pi-lock' : 'pi pi-lock-open'" />
      </button>

      <span class="layer-name" :title="layer.name">
        {{ layer.name }}
      </span>

      <span class="layer-type">{{ layer.type }}</span>
    </div>

    <!-- Timeline track area -->
    <div class="track-area" ref="trackAreaRef">
      <!-- Layer duration bar -->
      <div
        class="duration-bar"
        :style="durationBarStyle"
        :class="{ 'has-keyframes': hasKeyframes }"
      >
        <!-- In/Out handles for trimming -->
        <div
          class="trim-handle trim-in"
          @mousedown.stop="startTrimIn"
        />
        <div
          class="trim-handle trim-out"
          @mousedown.stop="startTrimOut"
        />
      </div>

      <!-- Keyframe diamonds -->
      <div
        v-for="keyframe in allKeyframes"
        :key="keyframe.id"
        class="keyframe-diamond"
        :style="{ left: `${getKeyframePosition(keyframe.frame)}%` }"
        :class="{ selected: selectedKeyframeIds.includes(keyframe.id) }"
        :title="`Frame ${keyframe.frame}`"
        @click.stop="selectKeyframe(keyframe.id)"
      />
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, Keyframe } from '@/types/project';

interface Props {
  layer: Layer;
  frameCount: number;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: 'select', layerId: string): void;
  (e: 'updateLayer', layerId: string, updates: Partial<Layer>): void;
  (e: 'selectKeyframe', keyframeId: string): void;
}>();

const store = useCompositorStore();

const trackAreaRef = ref<HTMLDivElement | null>(null);

// Selection state
const isSelected = computed(() => store.selectedLayerIds.includes(props.layer.id));
const selectedKeyframeIds = computed(() => store.selectedKeyframeIds);

// Calculate duration bar style
const durationBarStyle = computed(() => {
  const inPercent = (props.layer.inPoint / props.frameCount) * 100;
  const outPercent = ((props.layer.outPoint + 1) / props.frameCount) * 100;
  const width = outPercent - inPercent;

  return {
    left: `${inPercent}%`,
    width: `${width}%`
  };
});

// Collect all keyframes from all animated properties
const allKeyframes = computed(() => {
  const keyframes: Array<Keyframe<any> & { propertyName: string }> = [];

  // From opacity
  if (props.layer.opacity.animated) {
    props.layer.opacity.keyframes.forEach(kf => {
      keyframes.push({ ...kf, propertyName: 'opacity' });
    });
  }

  // From transform properties
  ['position', 'scale', 'rotation'].forEach(propName => {
    const prop = (props.layer.transform as any)[propName];
    if (prop?.animated) {
      prop.keyframes.forEach((kf: Keyframe<any>) => {
        keyframes.push({ ...kf, propertyName: propName });
      });
    }
  });

  // From custom properties
  props.layer.properties.forEach(prop => {
    if (prop.animated) {
      prop.keyframes.forEach(kf => {
        keyframes.push({ ...kf, propertyName: prop.name });
      });
    }
  });

  // Deduplicate by frame (show one diamond per frame)
  const frameMap = new Map<number, typeof keyframes[0]>();
  keyframes.forEach(kf => {
    if (!frameMap.has(kf.frame)) {
      frameMap.set(kf.frame, kf);
    }
  });

  return Array.from(frameMap.values());
});

const hasKeyframes = computed(() => allKeyframes.value.length > 0);

// Get keyframe position as percentage
function getKeyframePosition(frame: number): number {
  return (frame / props.frameCount) * 100;
}

// Actions
function selectLayer() {
  emit('select', props.layer.id);
}

function toggleVisibility() {
  emit('updateLayer', props.layer.id, { visible: !props.layer.visible });
}

function toggleLock() {
  emit('updateLayer', props.layer.id, { locked: !props.layer.locked });
}

function selectKeyframe(keyframeId: string) {
  emit('selectKeyframe', keyframeId);
}

// Trimming
let trimType: 'in' | 'out' | null = null;

function startTrimIn(_event: MouseEvent) {
  if (props.layer.locked) return;
  trimType = 'in';
  document.addEventListener('mousemove', handleTrim);
  document.addEventListener('mouseup', stopTrim);
}

function startTrimOut(_event: MouseEvent) {
  if (props.layer.locked) return;
  trimType = 'out';
  document.addEventListener('mousemove', handleTrim);
  document.addEventListener('mouseup', stopTrim);
}

function handleTrim(event: MouseEvent) {
  if (!trimType || !trackAreaRef.value) return;

  const rect = trackAreaRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const progress = Math.max(0, Math.min(1, x / rect.width));
  const frame = Math.round(progress * props.frameCount);

  if (trimType === 'in') {
    const newInPoint = Math.min(frame, props.layer.outPoint - 1);
    emit('updateLayer', props.layer.id, { inPoint: Math.max(0, newInPoint) });
  } else {
    const newOutPoint = Math.max(frame, props.layer.inPoint + 1);
    emit('updateLayer', props.layer.id, { outPoint: Math.min(props.frameCount - 1, newOutPoint) });
  }
}

function stopTrim() {
  trimType = null;
  document.removeEventListener('mousemove', handleTrim);
  document.removeEventListener('mouseup', stopTrim);
}
</script>

<style scoped>
.layer-track {
  display: flex;
  height: 28px;
  border-bottom: 1px solid #333;
  background: #252525;
  transition: background 0.1s;
}

.layer-track:hover {
  background: #2a2a2a;
}

.layer-track.selected {
  background: rgba(74, 144, 217, 0.15);
}

.layer-track.hidden {
  opacity: 0.5;
}

.layer-info {
  width: 180px;
  min-width: 180px;
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 0 8px;
  border-right: 1px solid #333;
  background: #2a2a2a;
}

.icon-btn {
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
  font-size: 12px;
}

.icon-btn:hover {
  background: #3a3a3a;
  color: #aaa;
}

.icon-btn.active {
  color: #4a90d9;
}

.layer-name {
  flex: 1;
  font-size: 11px;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
  color: #e0e0e0;
}

.layer-type {
  font-size: 9px;
  color: #666;
  text-transform: uppercase;
  padding: 2px 4px;
  background: #333;
  border-radius: 2px;
}

.track-area {
  flex: 1;
  position: relative;
  min-width: 0;
}

.duration-bar {
  position: absolute;
  top: 4px;
  bottom: 4px;
  background: #4a90d9;
  border-radius: 3px;
  opacity: 0.7;
  transition: opacity 0.1s;
}

.duration-bar:hover {
  opacity: 0.9;
}

.duration-bar.has-keyframes {
  background: linear-gradient(to right, #4a90d9, #6ab0e9);
}

.trim-handle {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 6px;
  cursor: ew-resize;
  background: transparent;
}

.trim-handle:hover {
  background: rgba(255, 255, 255, 0.2);
}

.trim-in {
  left: 0;
  border-radius: 3px 0 0 3px;
}

.trim-out {
  right: 0;
  border-radius: 0 3px 3px 0;
}

.keyframe-diamond {
  position: absolute;
  top: 50%;
  width: 8px;
  height: 8px;
  background: #ffc107;
  transform: translate(-50%, -50%) rotate(45deg);
  cursor: pointer;
  z-index: 2;
  transition: transform 0.1s, background 0.1s;
}

.keyframe-diamond:hover {
  transform: translate(-50%, -50%) rotate(45deg) scale(1.2);
  background: #ffca28;
}

.keyframe-diamond.selected {
  background: #ffffff;
  box-shadow: 0 0 0 2px #4a90d9;
}
</style>
