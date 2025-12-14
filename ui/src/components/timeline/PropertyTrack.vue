<template>
  <div class="property-track-wrapper">

    <!-- MODE: SIDEBAR (Left Panel - Name, Value, Stopwatch) -->
    <div
      v-if="layoutMode === 'sidebar'"
      class="property-sidebar-row"
      :class="{ selected: isSelected }"
      @click="selectProperty"
    >
      <span class="prop-indent"></span>

      <!-- Stopwatch (Animation Toggle) -->
      <button
        class="stopwatch-btn"
        :class="{ active: property.animated }"
        @click.stop="toggleAnimation"
        title="Toggle Animation"
      >
        <span class="icon">⏱</span>
      </button>

      <!-- Property Name -->
      <span class="prop-name">{{ name }}</span>

      <!-- Current Value (Display only) -->
      <div class="prop-value">
        <span class="val-text">{{ formatValue(currentValue) }}</span>
      </div>
    </div>

    <!-- MODE: TRACK (Right Panel - Keyframes Only) -->
    <div
      v-else-if="layoutMode === 'track'"
      class="property-track-row"
      @click="handleTrackClick"
    >
      <div class="property-track-area" ref="keyframeTrackRef">
        <!-- Keyframe Diamonds -->
        <template v-if="viewMode === 'keyframes'">
          <div
            v-for="kf in property.keyframes"
            :key="kf.id"
            class="keyframe-diamond"
            :class="{
              selected: selectedKeyframeIds.includes(kf.id),
              [kf.interpolation || 'linear']: true
            }"
            :style="{ left: `${getKeyframePercent(kf.frame)}%` }"
            @mousedown.stop="startKeyframeDrag(kf, $event)"
            @click.stop="selectKeyframe(kf.id, $event)"
            @contextmenu.prevent="showEasingMenu(kf, $event)"
            :title="`Frame ${kf.frame}: ${formatValue(kf.value)}`"
          ></div>
        </template>
      </div>
    </div>

  </div>
</template>

<script setup lang="ts">
import { computed, ref } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Keyframe, AnimatableProperty } from '@/types/project';

interface Props {
  layerId: string;
  propertyPath: string;
  name: string;
  property: AnimatableProperty<any>;
  frameCount: number;
  selectedKeyframeIds: string[];
  viewMode: 'keyframes' | 'graph';
  layoutMode: 'sidebar' | 'track';
  selectedPropertyIds?: string[];
}

const props = withDefaults(defineProps<Props>(), {
  selectedPropertyIds: () => []
});

const emit = defineEmits<{
  (e: 'selectKeyframe', id: string, addToSelection: boolean): void;
  (e: 'selectProperty', propertyId: string, addToSelection: boolean): void;
}>();

const store = useCompositorStore();
const keyframeTrackRef = ref<HTMLDivElement | null>(null);

const propertyId = computed(() => `${props.layerId}-${props.propertyPath.replace('.', '-')}`);
const isSelected = computed(() => props.selectedPropertyIds?.includes(propertyId.value));
const currentValue = computed(() => props.property.value);

function formatValue(val: any): string {
  if (typeof val === 'number') return val.toFixed(1);
  if (typeof val === 'object' && val !== null && 'x' in val) return `${val.x.toFixed(1)},${val.y.toFixed(1)}`;
  return String(val);
}

function getKeyframePercent(frame: number) {
  return (frame / props.frameCount) * 100;
}

function toggleAnimation() {
  store.setPropertyAnimated(props.layerId, props.propertyPath, !props.property.animated);
}

function selectProperty(event: MouseEvent) {
  emit('selectProperty', propertyId.value, event.shiftKey);
}

function handleTrackClick(event: MouseEvent) {
  if (props.viewMode === 'graph') {
    emit('selectProperty', propertyId.value, event.shiftKey);
  }
}

function selectKeyframe(id: string, event: MouseEvent) {
  emit('selectKeyframe', id, event.shiftKey);
}

function startKeyframeDrag(kf: Keyframe<any>, event: MouseEvent) {
  if (!props.selectedKeyframeIds.includes(kf.id)) {
    emit('selectKeyframe', kf.id, event.shiftKey);
  }
}

function showEasingMenu(kf: Keyframe<any>, event: MouseEvent) {
  // Placeholder for context menu
}
</script>

<style scoped>
.property-track-wrapper { width: 100%; display: flex; flex-direction: column; }

/* SIDEBAR STYLES */
.property-sidebar-row {
  display: flex;
  align-items: center;
  height: 32px;
  padding-left: 20px;
  border-bottom: 1px solid #2a2a2a;
  color: #aaa;
  font-size: 18px;
  cursor: pointer;
  background: #1e1e1e;
}
.property-sidebar-row:hover { background: #2a2a2a; color: #eee; }
.property-sidebar-row.selected { background: rgba(124, 156, 255, 0.15); border-left: 2px solid #7c9cff; padding-left: 18px; }
.prop-indent { width: 16px; }
.stopwatch-btn { background: none; border: none; color: #666; cursor: pointer; padding: 0 4px; display: flex; align-items: center; }
.stopwatch-btn .icon { font-size: 18px; }
.stopwatch-btn.active { color: #7c9cff; }
.prop-name { flex: 1; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 18px; }
.prop-value { margin-right: 8px; color: #7c9cff; font-family: monospace; }

/* TRACK STYLES */
.property-track-row {
  height: 32px;
  border-bottom: 1px solid #2a2a2a;
  position: relative;
  background: #1a1a1a;
}
.property-track-area { width: 100%; height: 100%; position: relative; }

.keyframe-diamond {
  position: absolute;
  top: 50%;
  width: 8px;
  height: 8px;
  background: #f5c542;
  transform: translate(-50%, -50%) rotate(45deg);
  border: 1px solid #000;
  cursor: pointer;
  z-index: 2;
}
.keyframe-diamond.selected { background: #fff; border-color: #7c9cff; }
.keyframe-diamond.bezier { border-radius: 50%; }
.keyframe-diamond.hold { border-radius: 0; transform: translate(-50%, -50%); }
</style>
