<template>
  <div class="prop-wrapper">

    <!-- SIDEBAR MODE -->
    <div v-if="layoutMode === 'sidebar'" class="prop-sidebar" :class="{ selected: isSelected }" @click="selectProp">
      <div class="indent-spacer"></div>

      <!-- 1. Diamond FIRST (Add Keyframe) -->
      <div class="icon-box" @click.stop="addKeyframeAtCurrent" title="Add Keyframe">
        <span class="kf-btn" :class="{ active: hasKeyframeAtCurrent }">◇</span>
      </div>

      <!-- 2. Stopwatch -->
      <div class="icon-box" @click.stop="toggleAnim">
        <span class="stopwatch" :class="{ active: property.animated }">⏱</span>
      </div>

      <div class="prop-name">{{ name }}</div>

      <!-- 3. Editable Value Display -->
      <div class="prop-value-container">
        <!-- Number type -->
        <template v-if="typeof property.value === 'number'">
          <input type="number" class="val-input" :value="property.value.toFixed(1)" @change="updateVal(0, $event)" />
        </template>

        <!-- X/Y type -->
        <template v-else-if="property.value?.x !== undefined && property.value?.z === undefined">
          <input type="number" class="val-input small" :value="property.value.x.toFixed(0)" @change="updateVal(0, $event)" />
          <input type="number" class="val-input small" :value="property.value.y.toFixed(0)" @change="updateVal(1, $event)" />
        </template>

        <!-- X/Y/Z type -->
        <template v-else-if="property.value?.z !== undefined">
          <input type="number" class="val-input small" :value="property.value.x.toFixed(0)" @change="updateVal(0, $event)" />
          <input type="number" class="val-input small" :value="property.value.y.toFixed(0)" @change="updateVal(1, $event)" />
          <input type="number" class="val-input small" :value="property.value.z.toFixed(0)" @change="updateVal(2, $event)" />
        </template>

        <!-- Fallback -->
        <template v-else>
          <span class="val-display">{{ formatValue(property.value) }}</span>
        </template>
      </div>
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

const props = defineProps(['name', 'property', 'layerId', 'propertyPath', 'layoutMode', 'viewMode', 'frameCount', 'selectedPropertyIds', 'pixelsPerFrame']);
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

/* SIDEBAR */
.prop-sidebar {
  display: flex; height: 24px; align-items: center;
  border-bottom: 1px solid #2a2a2a;
  background: #1e1e1e;
  color: #bbb;
  font-size: 12px;
  padding-right: 5px; cursor: pointer;
}
.prop-sidebar:hover { background: #252525; color: #fff; }
.prop-sidebar.selected { background: #2c2c2c; border-left: 2px solid #3ea6ff; }

.indent-spacer { width: 35px; flex-shrink: 0; }

.icon-box { width: 24px; text-align: center; cursor: pointer; display: flex; justify-content: center; align-items: center; flex-shrink: 0; }

/* Diamond FIRST - now highlighted */
.kf-btn { font-size: 14px; color: #666; }
.kf-btn:hover { color: #fff; }
.kf-btn.active { color: #ebcb8b; }

.stopwatch { font-size: 14px; color: #666; }
.stopwatch.active { color: #3ea6ff; }

.prop-name { flex: 1; padding-left: 4px; min-width: 60px; }

/* Value Container with editable inputs */
.prop-value-container {
  display: flex; gap: 4px; align-items: center; margin-right: 4px;
}

.val-input {
  background: #111; border: 1px solid #333; color: #3ea6ff;
  font-family: monospace; font-size: 11px; padding: 2px 4px;
  width: 50px; text-align: right; border-radius: 2px;
}
.val-input:focus { border-color: #3ea6ff; outline: none; }
.val-input.small { width: 40px; }

.val-display { color: #3ea6ff; font-family: monospace; font-size: 12px; }

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
