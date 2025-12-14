<template>
  <div class="prop-wrapper">

    <!-- SIDEBAR MODE -->
    <div v-if="layoutMode === 'sidebar'" class="prop-sidebar" :class="{ selected: isSelected }" :style="gridStyle" @click="selectProp">

      <!-- Indent spacer (spans arrow + color + id columns) -->
      <div class="indent-spacer"></div>

      <!-- 1. Diamond FIRST (Add Keyframe) - in icon columns -->
      <div class="icon-box" @click.stop="addKeyframeAtCurrent" title="Add Keyframe">
        <span class="kf-btn" :class="{ active: hasKeyframeAtCurrent }">◇</span>
      </div>

      <!-- 2. Stopwatch -->
      <div class="icon-box" @click.stop="toggleAnim">
        <span class="stopwatch" :class="{ active: property.animated }">⏱</span>
      </div>

      <!-- Property Name + Values (spans name column) -->
      <div class="prop-content">
        <span class="prop-name">{{ name }}</span>

        <!-- Editable Value Display using ScrubableNumber for hot-text feel -->
        <div class="prop-value-container">
          <!-- Number type -->
          <template v-if="typeof property.value === 'number'">
            <ScrubableNumber
              :modelValue="property.value"
              @update:modelValue="(v) => updateValDirect(v)"
              :precision="1"
              :sensitivity="0.5"
            />
          </template>

          <!-- X/Y type -->
          <template v-else-if="property.value?.x !== undefined && property.value?.z === undefined">
            <ScrubableNumber
              :modelValue="property.value.x"
              @update:modelValue="(v) => updateValByIndex(0, v)"
              :precision="0"
              :sensitivity="1"
            />
            <ScrubableNumber
              :modelValue="property.value.y"
              @update:modelValue="(v) => updateValByIndex(1, v)"
              :precision="0"
              :sensitivity="1"
            />
          </template>

          <!-- X/Y/Z type -->
          <template v-else-if="property.value?.z !== undefined">
            <ScrubableNumber
              :modelValue="property.value.x"
              @update:modelValue="(v) => updateValByIndex(0, v)"
              :precision="0"
              :sensitivity="1"
            />
            <ScrubableNumber
              :modelValue="property.value.y"
              @update:modelValue="(v) => updateValByIndex(1, v)"
              :precision="0"
              :sensitivity="1"
            />
            <ScrubableNumber
              :modelValue="property.value.z"
              @update:modelValue="(v) => updateValByIndex(2, v)"
              :precision="0"
              :sensitivity="1"
            />
          </template>

          <!-- Fallback -->
          <template v-else>
            <span class="val-display">{{ formatValue(property.value) }}</span>
          </template>
        </div>
      </div>

      <!-- Empty columns for mode/parent alignment -->
      <div class="col-spacer"></div>
      <div class="col-spacer"></div>
    </div>

    <!-- TRACK MODE -->
    <div v-else-if="layoutMode === 'track'" class="prop-track">
      <div class="track-bg"></div>
      <template v-if="viewMode === 'keyframes'">
        <div v-for="kf in property.keyframes" :key="kf.id"
             class="keyframe"
             :style="{ left: `${kf.frame * pixelsPerFrame}px` }"
             @mousedown.stop="startKeyframeDrag(kf, $event)"
             @click.stop="$emit('selectKeyframe', kf.id, true)"
        ></div>
      </template>
    </div>

  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import ScrubableNumber from '@/components/controls/ScrubableNumber.vue';

const props = defineProps(['name', 'property', 'layerId', 'propertyPath', 'layoutMode', 'viewMode', 'frameCount', 'selectedPropertyIds', 'pixelsPerFrame', 'gridStyle']);
const emit = defineEmits(['selectProperty', 'selectKeyframe']);
const store = useCompositorStore();

const propId = computed(() => `${props.layerId}-${props.propertyPath}`);
const isSelected = computed(() => props.selectedPropertyIds?.includes(propId.value));

function formatValue(v: any) {
  if (typeof v === 'number') return v.toFixed(1);
  if (typeof v === 'object') {
    if (v?.z !== undefined) return `${v.x.toFixed(0)},${v.y.toFixed(0)},${v.z.toFixed(0)}`;
    if (v?.x !== undefined) return `${v.x.toFixed(0)},${v.y.toFixed(0)}`;
  }
  return String(v);
}

const hasKeyframeAtCurrent = computed(() => {
  return props.property.keyframes?.some((k: any) => k.frame === store.currentFrame);
});

function toggleAnim() {
  store.setPropertyAnimated(props.layerId, props.propertyPath, !props.property.animated);
}

function addKeyframeAtCurrent() {
  store.addKeyframe(props.layerId, props.propertyPath, props.property.value);
}

function selectProp(e: MouseEvent) {
  emit('selectProperty', propId.value, e.shiftKey);
}

function updateVal(idx: number, e: Event) {
  const num = parseFloat((e.target as HTMLInputElement).value);
  if (isNaN(num)) return;
  updateValByIndex(idx, num);
}

// Direct value update for scalar properties
function updateValDirect(num: number) {
  store.setPropertyValue(props.layerId, props.propertyPath, num);
}

// Update value by component index (0=x, 1=y, 2=z)
function updateValByIndex(idx: number, num: number) {
  let newVal = props.property.value;

  if (typeof newVal === 'number') {
    newVal = num;
  } else if (typeof newVal === 'object' && newVal !== null) {
    newVal = { ...newVal };
    if (idx === 0) newVal.x = num;
    if (idx === 1) newVal.y = num;
    if (idx === 2 && newVal.z !== undefined) newVal.z = num;
  }

  store.setPropertyValue(props.layerId, props.propertyPath, newVal);
}

function startKeyframeDrag(kf: any, e: MouseEvent) {
  e.stopPropagation();
  const ppf = props.pixelsPerFrame || 5;
  const startX = e.clientX;
  const startFrame = kf.frame;

  const onMove = (ev: MouseEvent) => {
    const dx = ev.clientX - startX;
    const dFrames = Math.round(dx / ppf);
    const newFrame = Math.max(0, Math.min(props.frameCount - 1, startFrame + dFrames));
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

  // Also select the keyframe
  emit('selectKeyframe', kf.id, true);
}
</script>

<style scoped>
.prop-wrapper { width: 100%; display: flex; flex-direction: column; }

/* SIDEBAR - Grid layout matching parent */
.prop-sidebar {
  display: grid;
  height: 24px;
  align-items: center;
  border-bottom: 1px solid #2a2a2a;
  background: #1a1a1a;
  color: #bbb;
  font-size: 12px;
  cursor: pointer;
}
.prop-sidebar:hover { background: #222; color: #fff; }
.prop-sidebar.selected { background: #252525; border-left: 2px solid #3ea6ff; }

/* Indent spans arrow + color + id columns */
.indent-spacer { grid-column: span 3; }

.icon-box {
  display: flex;
  justify-content: center;
  align-items: center;
  cursor: pointer;
}

/* Diamond FIRST - highlighted when keyframe exists */
.kf-btn { font-size: 12px; color: #555; }
.kf-btn:hover { color: #fff; }
.kf-btn.active { color: #ebcb8b; }

.stopwatch { font-size: 12px; color: #555; }
.stopwatch.active { color: #3ea6ff; }

/* Property content (name + values) */
.prop-content {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 0 4px;
  overflow: hidden;
}

.prop-name {
  color: #888;
  font-size: 11px;
  white-space: nowrap;
  min-width: 60px;
}

/* Value Container with ScrubableNumber components */
.prop-value-container {
  display: flex;
  gap: 2px;
  align-items: center;
}

/* Scrubable number overrides for compact timeline display */
.prop-value-container :deep(.scrubable-number) {
  gap: 0;
}
.prop-value-container :deep(.scrub-input) {
  width: 45px;
  padding: 2px 3px;
  font-size: 11px;
  background: #111;
  border: 1px solid #333;
  color: #3ea6ff;
}
.prop-value-container :deep(.scrub-label) {
  display: none;
}

.val-display { color: #3ea6ff; font-family: monospace; font-size: 11px; }

/* Spacers for mode/parent columns */
.col-spacer { }

/* TRACK */
.prop-track { height: 24px; border-bottom: 1px solid #2a2a2a; position: relative; background: #161616; }

.keyframe {
  position: absolute; width: 9px; height: 9px;
  background: #ebcb8b;
  transform: rotate(45deg) translateX(-50%);
  top: 7px;
  border: 1px solid #000;
  z-index: 5; cursor: pointer;
}
.keyframe:hover { background: #fff; transform: rotate(45deg) translateX(-50%) scale(1.2); }
</style>
