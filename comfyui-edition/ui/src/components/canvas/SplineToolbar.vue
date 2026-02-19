<!--
  @component SplineToolbar
  @description Toolbar for spline editing tools and operations.
  Extracted from SplineEditor.vue to reduce file size.
-->
<template>
  <div class="spline-toolbar">
    <!-- Pen Tool Options -->
    <div class="toolbar-group pen-tools">
      <!-- Pen Tool (add points at end) -->
      <button
        class="toolbar-btn icon-btn"
        :class="{ active: isPenMode && penSubMode === 'add' }"
        @click="$emit('setPenSubMode', 'add')"
        title="Pen Tool (P) - Add points at end of path"
      >
        <svg viewBox="0 0 24 24" width="14" height="14">
          <path fill="currentColor" d="M20.71,7.04C21.1,6.65 21.1,6 20.71,5.63L18.37,3.29C18,2.9 17.35,2.9 16.96,3.29L15.12,5.12L18.87,8.87L20.71,7.04Z M3,17.25V21H6.75L17.81,9.93L14.06,6.18L3,17.25Z"/>
        </svg>
        <span class="tool-label">Pen</span>
      </button>
      <!-- Add Point Tool (insert on segment) -->
      <button
        class="toolbar-btn icon-btn"
        :class="{ active: isPenMode && penSubMode === 'insert' }"
        @click="$emit('setPenSubMode', 'insert')"
        title="Add Point (+) - Click on path to insert point"
      >
        <svg viewBox="0 0 24 24" width="14" height="14">
          <path fill="currentColor" d="M20.71,7.04C21.1,6.65 21.1,6 20.71,5.63L18.37,3.29C18,2.9 17.35,2.9 16.96,3.29L15.12,5.12L18.87,8.87L20.71,7.04Z M3,17.25V21H6.75L17.81,9.93L14.06,6.18L3,17.25Z"/>
          <circle cx="18" cy="18" r="5" fill="#1e1e1e"/>
          <path fill="currentColor" d="M18,15v6M15,18h6" stroke="currentColor" stroke-width="1.5"/>
        </svg>
        <span class="tool-label">Pen+</span>
      </button>
      <!-- Delete Point Tool -->
      <button
        class="toolbar-btn icon-btn"
        :class="{ active: isPenMode && penSubMode === 'delete' }"
        @click="$emit('setPenSubMode', 'delete')"
        title="Delete Point (-) - Click point to remove"
      >
        <svg viewBox="0 0 24 24" width="14" height="14">
          <path fill="currentColor" d="M20.71,7.04C21.1,6.65 21.1,6 20.71,5.63L18.37,3.29C18,2.9 17.35,2.9 16.96,3.29L15.12,5.12L18.87,8.87L20.71,7.04Z M3,17.25V21H6.75L17.81,9.93L14.06,6.18L3,17.25Z"/>
          <circle cx="18" cy="18" r="5" fill="#1e1e1e"/>
          <path fill="currentColor" d="M15,18h6" stroke="currentColor" stroke-width="1.5"/>
        </svg>
        <span class="tool-label">Pen-</span>
      </button>
      <!-- Convert Point Tool -->
      <button
        class="toolbar-btn icon-btn"
        :class="{ active: isPenMode && penSubMode === 'convert' }"
        @click="$emit('setPenSubMode', 'convert')"
        title="Convert Point (^) - Click to toggle smooth/corner"
      >
        <svg viewBox="0 0 24 24" width="14" height="14">
          <path fill="currentColor" d="M12,2L6,8H9V14H6L12,20L18,14H15V8H18L12,2Z" transform="rotate(180 12 11)"/>
        </svg>
        <span class="tool-label">Convert</span>
      </button>
    </div>
    <div class="toolbar-separator"></div>
    <!-- Path Operations -->
    <div class="toolbar-group" v-if="hasControlPoints">
      <button
        class="toolbar-btn"
        @click="$emit('smoothSelectedPoints')"
        :title="selectedPointCount > 0 ? 'Smooth selected points' : 'Smooth all path handles'"
      >
        Smooth{{ selectedPointCount > 0 ? ` (${selectedPointCount})` : '' }}
      </button>
      <button
        class="toolbar-btn"
        @click="$emit('simplifySpline')"
        title="Simplify path (reduce control points)"
      >
        Simplify
      </button>
      <button
        class="toolbar-btn"
        :class="{ active: isClosed }"
        @click="$emit('toggleClosePath')"
        title="Toggle closed path"
      >
        {{ isClosed ? 'Open' : 'Close' }}
      </button>
    </div>
    <div class="toolbar-group" v-if="hasControlPoints">
      <label class="tolerance-label">
        Tolerance:
        <input
          type="range"
          :value="smoothTolerance"
          @input="$emit('update:smoothTolerance', Number(($event.target as HTMLInputElement).value))"
          min="1"
          max="50"
          step="1"
          class="tolerance-slider"
        />
        <span class="tolerance-value">{{ smoothTolerance }}px</span>
      </label>
    </div>
    <div class="toolbar-info" v-if="hasControlPoints">
      {{ controlPointCount }} points{{ selectedPointCount > 0 ? ` (${selectedPointCount} selected)` : '' }}
    </div>
    <!-- Z-Depth controls (shown when point is selected) -->
    <div class="toolbar-group z-depth-controls" v-if="hasSelectedPoint">
      <label class="z-depth-label">
        Z:
        <input
          type="number"
          :value="selectedPointDepth"
          @input="$emit('updateSelectedPointDepth', $event)"
          class="z-depth-input"
          step="10"
        />
      </label>
      <span class="z-depth-hint">(↑/↓ keys)</span>
    </div>
    <div class="toolbar-separator"></div>
    <!-- Animation controls -->
    <div class="toolbar-group animation-controls" v-if="hasControlPoints">
      <button
        class="toolbar-btn"
        :class="{ active: isSplineAnimated }"
        @click="$emit('toggleSplineAnimation')"
        :title="isSplineAnimated ? 'Spline animation enabled' : 'Enable spline point animation'"
      >
        {{ isSplineAnimated ? '◆ Animated' : '◇ Animate' }}
      </button>
      <button
        v-if="selectedPointCount > 0"
        class="toolbar-btn keyframe-btn"
        @click="$emit('keyframeSelectedPoints')"
        title="Add keyframe to selected points at current frame"
      >
        ◆ Keyframe ({{ selectedPointCount }})
      </button>
    </div>
  </div>
</template>

<script setup lang="ts">
export type PenSubMode = "add" | "insert" | "delete" | "convert";

defineProps<{
  isPenMode: boolean;
  penSubMode: PenSubMode;
  hasControlPoints: boolean;
  controlPointCount: number;
  selectedPointCount: number;
  hasSelectedPoint: boolean;
  selectedPointDepth: number;
  isClosed: boolean;
  isSplineAnimated: boolean;
  smoothTolerance: number;
}>();

defineEmits<{
  setPenSubMode: [mode: PenSubMode];
  smoothSelectedPoints: [];
  simplifySpline: [];
  toggleClosePath: [];
  "update:smoothTolerance": [value: number];
  updateSelectedPointDepth: [event: Event];
  toggleSplineAnimation: [];
  keyframeSelectedPoints: [];
}>();
</script>

<style scoped>
.spline-toolbar {
  position: absolute;
  top: 8px;
  left: 50%;
  transform: translateX(-50%);
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 8px;
  background: rgba(30, 30, 30, 0.95);
  border: 1px solid rgba(139, 92, 246, 0.3);
  border-radius: 6px;
  z-index: 100;
  backdrop-filter: blur(8px);
}

.toolbar-group {
  display: flex;
  align-items: center;
  gap: 4px;
}

.pen-tools {
  gap: 2px;
}

.toolbar-btn {
  padding: 4px 8px;
  background: rgba(50, 50, 50, 0.8);
  border: 1px solid rgba(100, 100, 100, 0.3);
  border-radius: 4px;
  color: #ccc;
  font-size: 11px;
  cursor: pointer;
  transition: all 0.15s ease;
  white-space: nowrap;
}

.toolbar-btn:hover {
  background: rgba(70, 70, 70, 0.9);
  color: #fff;
}

.toolbar-btn.active {
  background: rgba(139, 92, 246, 0.3);
  border-color: rgba(139, 92, 246, 0.6);
  color: #a78bfa;
}

.icon-btn {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 6px;
}

.icon-btn svg {
  flex-shrink: 0;
}

.tool-label {
  font-size: 10px;
}

.toolbar-separator {
  width: 1px;
  height: 20px;
  background: rgba(100, 100, 100, 0.3);
  margin: 0 4px;
}

.toolbar-info {
  font-size: 10px;
  color: #888;
  padding: 0 4px;
}

.tolerance-label {
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: 10px;
  color: #888;
}

.tolerance-slider {
  width: 60px;
  height: 4px;
  -webkit-appearance: none;
  background: rgba(100, 100, 100, 0.5);
  border-radius: 2px;
  cursor: pointer;
}

.tolerance-slider::-webkit-slider-thumb {
  -webkit-appearance: none;
  width: 10px;
  height: 10px;
  background: #8b5cf6;
  border-radius: 50%;
  cursor: pointer;
}

.tolerance-value {
  min-width: 30px;
  text-align: right;
}

.z-depth-controls {
  gap: 4px;
}

.z-depth-label {
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: 10px;
  color: #888;
}

.z-depth-input {
  width: 50px;
  padding: 2px 4px;
  background: rgba(50, 50, 50, 0.8);
  border: 1px solid rgba(100, 100, 100, 0.3);
  border-radius: 3px;
  color: #ccc;
  font-size: 10px;
  text-align: right;
}

.z-depth-hint {
  font-size: 9px;
  color: #666;
}

.animation-controls {
  gap: 4px;
}

.keyframe-btn {
  background: rgba(139, 92, 246, 0.2);
  border-color: rgba(139, 92, 246, 0.4);
}

.keyframe-btn:hover {
  background: rgba(139, 92, 246, 0.3);
}
</style>
