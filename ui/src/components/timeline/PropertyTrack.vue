<template>
  <div class="prop-wrapper">
    <div v-if="layoutMode === 'sidebar'" class="prop-sidebar" :class="{ selected: isSelected }" :style="gridStyle" @click="selectProp">
      <div class="indent-spacer"></div>

      <div class="icon-box" @click.stop="addKeyframeAtCurrent">
        <span class="kf-btn" :class="{ active: hasKeyframeAtCurrent }">◇</span>
      </div>

      <div class="icon-box" @click.stop="toggleAnim">
        <span class="stopwatch" :class="{ active: property.animated }">⏱</span>
      </div>

      <div class="prop-content">
        <span class="prop-name">{{ name }}</span>

        <div class="prop-inputs">
          <!-- Z Position only (special case for 3D layers) -->
          <template v-if="name === 'Z Position'">
            <div class="vec-item">
              <span class="label z-label">Z</span>
              <ScrubableNumber
                :modelValue="property.value?.z ?? 0"
                @update:modelValue="v => updateValByIndex('z', v)"
              />
            </div>
          </template>

          <!-- Color input -->
          <template v-else-if="property.type === 'color'">
            <div class="color-input-wrapper">
              <input type="color" :value="property.value" @input="e => updateValDirect((e.target as HTMLInputElement).value)" />
              <span class="color-hex">{{ property.value }}</span>
            </div>
          </template>

          <!-- Vector (X/Y or X/Y/Z) -->
          <template v-else-if="typeof property.value === 'object'">
            <div class="vec-item">
              <span class="label x-label">X</span>
              <ScrubableNumber :modelValue="property.value.x" @update:modelValue="v => updateValByIndex('x', v)" />
            </div>
            <div class="vec-item">
              <span class="label y-label">Y</span>
              <ScrubableNumber :modelValue="property.value.y" @update:modelValue="v => updateValByIndex('y', v)" />
            </div>
          </template>

          <!-- Single number -->
          <template v-else-if="typeof property.value === 'number'">
            <ScrubableNumber :modelValue="property.value" @update:modelValue="updateValDirect" :precision="1" />
          </template>
        </div>
      </div>
    </div>

    <div v-else class="prop-track" @mousedown="handleTrackClick">
       <div v-for="kf in property.keyframes" :key="kf.id"
            class="keyframe"
            :class="{ selected: selectedKeyframeIds.has(kf.id) }"
            :style="{ left: `${kf.frame * pixelsPerFrame}px` }"
            @mousedown.stop="startKeyframeDrag($event, kf)"
            @dblclick.stop="deleteKeyframe(kf.id)"
       >
       </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import ScrubableNumber from '@/components/controls/ScrubableNumber.vue';
import type { Keyframe } from '@/types/project';

const props = defineProps(['name', 'property', 'layerId', 'propertyPath', 'layoutMode', 'pixelsPerFrame', 'gridStyle']);
const emit = defineEmits(['selectKeyframe', 'deleteKeyframe', 'moveKeyframe']);
const store = useCompositorStore();

const selectedKeyframeIds = ref<Set<string>>(new Set());

const hasKeyframeAtCurrent = computed(() => props.property.keyframes?.some((k:any) => k.frame === store.currentFrame));
const isSelected = computed(() => store.selectedPropertyPath === props.propertyPath);

function toggleAnim() { store.setPropertyAnimated(props.layerId, props.propertyPath, !props.property.animated); }
function addKeyframeAtCurrent() { store.addKeyframe(props.layerId, props.propertyPath, props.property.value); }
function updateValDirect(v: any) { store.setPropertyValue(props.layerId, props.propertyPath, v); }
function updateValByIndex(axis: string, v: number) {
  const newVal = { ...props.property.value, [axis]: v };
  store.setPropertyValue(props.layerId, props.propertyPath, newVal);
}
function selectProp() { store.selectProperty(props.propertyPath); }

// Click on empty track area to add keyframe at that position
function handleTrackClick(e: MouseEvent) {
  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect();
  const x = e.clientX - rect.left;
  const frame = Math.round(x / props.pixelsPerFrame);
  // Navigate to that frame
  store.setFrame(Math.max(0, Math.min(store.frameCount - 1, frame)));
}

// Keyframe selection and dragging
function startKeyframeDrag(e: MouseEvent, kf: Keyframe) {
  // Toggle selection with Shift, otherwise single select
  if (e.shiftKey) {
    if (selectedKeyframeIds.value.has(kf.id)) {
      selectedKeyframeIds.value.delete(kf.id);
    } else {
      selectedKeyframeIds.value.add(kf.id);
    }
  } else {
    selectedKeyframeIds.value.clear();
    selectedKeyframeIds.value.add(kf.id);
  }

  // Set up drag
  const startX = e.clientX;
  const startFrame = kf.frame;

  const onMove = (ev: MouseEvent) => {
    const dx = ev.clientX - startX;
    const frameDelta = Math.round(dx / props.pixelsPerFrame);
    const newFrame = Math.max(0, Math.min(store.frameCount - 1, startFrame + frameDelta));

    if (newFrame !== kf.frame) {
      store.moveKeyframe(props.layerId, props.propertyPath, kf.id, newFrame);
    }
  };

  const onUp = () => {
    window.removeEventListener('mousemove', onMove);
    window.removeEventListener('mouseup', onUp);
  };

  window.addEventListener('mousemove', onMove);
  window.addEventListener('mouseup', onUp);
}

// Delete keyframe
function deleteKeyframe(kfId: string) {
  store.removeKeyframe(props.layerId, props.propertyPath, kfId);
  selectedKeyframeIds.value.delete(kfId);
}
</script>

<style scoped>
.prop-wrapper { width: 100%; display: flex; flex-direction: column; }
.prop-sidebar {
  display: grid;
  /* Must match parent grid. Columns: 24 24 30 24 24 24 1fr 70 70 */
  grid-template-columns: 24px 24px 30px 24px 24px 24px 1fr 70px 70px;
  align-items: center;
  height: 32px;
  border-bottom: 1px solid #2a2a2a;
  background: #1a1a1a;
  font-size: 13px;
  color: #ccc;
}
.indent-spacer { grid-column: span 3; }
.icon-box { display: flex; justify-content: center; cursor: pointer; }
.kf-btn.active { color: #f1c40f; }
.stopwatch.active { color: #3498db; }

/* Content spans from column 7 (Name) to the end */
.prop-content {
  grid-column: 7 / -1;
  display: flex;
  align-items: center;
  padding-right: 10px;
  overflow: hidden;
}
.prop-name { min-width: 100px; color: #999; font-size: 13px; }
.prop-inputs { display: flex; gap: 8px; flex: 1; align-items: center; }

.vec-item { display: flex; align-items: center; gap: 4px; }
.label { font-size: 10px; font-weight: bold; }
.x-label { color: #e74c3c; } .y-label { color: #2ecc71; } .z-label { color: #3498db; }

.color-input-wrapper { display: flex; align-items: center; gap: 8px; }
.color-hex { font-family: monospace; font-size: 11px; color: #aaa; }

.prop-track { height: 32px; background: #151515; border-bottom: 1px solid #2a2a2a; position: relative; cursor: pointer; }
.keyframe {
  position: absolute;
  width: 10px;
  height: 10px;
  background: #f1c40f;
  transform: rotate(45deg);
  top: 11px;
  border: 1px solid #000;
  cursor: ew-resize;
  transition: transform 0.1s;
}
.keyframe:hover {
  transform: rotate(45deg) scale(1.2);
}
.keyframe.selected {
  background: #fff;
  border-color: #4a90d9;
  box-shadow: 0 0 4px #4a90d9;
}
</style>
