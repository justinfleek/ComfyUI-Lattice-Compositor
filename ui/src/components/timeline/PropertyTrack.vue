<template>
  <div class="property-track-row">
    <div class="property-info">
      <span class="property-indent"></span>
      <span class="property-name">{{ name }}</span>
      <span class="property-value">{{ formattedValue }}</span>
    </div>
    <div class="property-keyframes" :style="{ width: trackWidth + 'px' }">
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

      <div
        class="keyframe-toggle"
        :style="{ left: `${(currentFrame / frameCount) * 100}%` }"
        @click.stop="toggleKeyframe"
        :title="hasKeyframeAtCurrentFrame ? 'Remove Keyframe' : 'Add Keyframe'"
      >
        <span v-if="hasKeyframeAtCurrentFrame" class="kf-filled">◆</span>
        <span v-else class="kf-empty">◇</span>
      </div>
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
  height: 20px;
  background: #252525;
  border-bottom: 1px solid #1a1a1a;
}

.property-info {
  display: flex;
  align-items: center;
  width: 220px;
  padding-left: 24px;
  font-size: 11px;
  color: #999;
  gap: 8px;
}

.property-indent {
  width: 16px;
}

.property-name {
  flex: 1;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.property-value {
  color: #7c9cff;
  font-family: monospace;
  font-size: 10px;
  min-width: 60px;
  text-align: right;
  padding-right: 8px;
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
  font-size: 10px;
  color: #f5c542;
  cursor: pointer;
  user-select: none;
}

.keyframe-diamond:hover {
  color: #ffdd77;
  transform: translate(-50%, -50%) scale(1.3);
}

.keyframe-diamond.selected {
  color: #ff9500;
}

.keyframe-toggle {
  position: absolute;
  top: 50%;
  transform: translate(-50%, -50%);
  font-size: 12px;
  cursor: pointer;
  opacity: 0;
  transition: opacity 0.15s;
}

.property-track-row:hover .keyframe-toggle {
  opacity: 1;
}

.kf-filled {
  color: #f5c542;
}

.kf-empty {
  color: #666;
}

.kf-empty:hover {
  color: #999;
}
</style>
