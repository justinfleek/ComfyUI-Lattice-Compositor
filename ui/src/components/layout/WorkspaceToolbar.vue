<template>
  <div class="toolbar" role="toolbar" aria-label="Drawing tools">
    <div class="tool-group labeled-tools" role="group" aria-label="Selection and drawing tools">
      <button
        :class="{ active: currentTool === 'select' }"
        :aria-pressed="currentTool === 'select'"
        @click="emit('update:currentTool', 'select')"
        title="Select Tool (V) - Select and move layers"
        aria-label="Select tool"
      >
        <PhCursor class="icon" aria-hidden="true" />
        <span class="tool-label">Select</span>
      </button>
      <button
        :class="{ active: currentTool === 'pen' }"
        :aria-pressed="currentTool === 'pen'"
        @click="emit('update:currentTool', 'pen')"
        title="Pen Tool (P) - Draw paths and shapes"
        aria-label="Pen tool"
      >
        <PhPen class="icon" aria-hidden="true" />
        <span class="tool-label">Pen</span>
      </button>
      <button
        :class="{ active: currentTool === 'text' }"
        :aria-pressed="currentTool === 'text'"
        @click="emit('update:currentTool', 'text')"
        title="Text Tool (T) - Add text layers"
        aria-label="Text tool"
      >
        <PhTextT class="icon" aria-hidden="true" />
        <span class="tool-label">Text</span>
      </button>
      <button
        :class="{ active: currentTool === 'hand' }"
        :aria-pressed="currentTool === 'hand'"
        @click="emit('update:currentTool', 'hand')"
        title="Hand Tool (H) - Pan the viewport"
        aria-label="Pan tool"
      >
        <PhHand class="icon" aria-hidden="true" />
        <span class="tool-label">Pan</span>
      </button>
      <button
        :class="{ active: currentTool === 'zoom' }"
        :aria-pressed="currentTool === 'zoom'"
        @click="emit('update:currentTool', 'zoom')"
        title="Zoom Tool (Z) - Zoom in/out the viewport"
        aria-label="Zoom tool"
      >
        <PhMagnifyingGlass class="icon" aria-hidden="true" />
        <span class="tool-label">Zoom</span>
      </button>
      <button
        :class="{ active: currentTool === 'segment' }"
        :aria-pressed="currentTool === 'segment'"
        @click="emit('update:currentTool', 'segment')"
        title="AI Segment (S) - Auto-select objects using AI"
        aria-label="AI Segment tool"
      >
        <PhSparkle class="icon" aria-hidden="true" />
        <span class="tool-label">AI Seg</span>
      </button>
    </div>

    <div class="divider"></div>

    <!-- Shape Drawing Tools -->
    <div class="tool-group labeled-tools shape-tools" role="group" aria-label="Shape drawing tools">
      <button
        :class="{ active: currentTool === 'rectangle' }"
        :aria-pressed="currentTool === 'rectangle'"
        @click="emit('update:currentTool', 'rectangle')"
        title="Rectangle Tool (R) - Draw rectangles and squares"
        aria-label="Rectangle tool"
      >
        <PhSquare class="icon" aria-hidden="true" />
        <span class="tool-label">Rect</span>
      </button>
      <button
        :class="{ active: currentTool === 'ellipse' }"
        :aria-pressed="currentTool === 'ellipse'"
        @click="emit('update:currentTool', 'ellipse')"
        title="Ellipse Tool (E) - Draw ellipses and circles"
        aria-label="Ellipse tool"
      >
        <PhCircle class="icon" aria-hidden="true" />
        <span class="tool-label">Ellipse</span>
      </button>
      <button
        :class="{ active: currentTool === 'polygon' }"
        :aria-pressed="currentTool === 'polygon'"
        @click="emit('update:currentTool', 'polygon')"
        title="Polygon Tool - Draw regular polygons"
        aria-label="Polygon tool"
      >
        <PhPolygon class="icon" aria-hidden="true" />
        <span class="tool-label">Polygon</span>
      </button>
      <button
        :class="{ active: currentTool === 'star' }"
        :aria-pressed="currentTool === 'star'"
        @click="emit('update:currentTool', 'star')"
        title="Star Tool - Draw stars"
        aria-label="Star tool"
      >
        <PhStar class="icon" aria-hidden="true" weight="fill" />
        <span class="tool-label">Star</span>
      </button>
    </div>

    <!-- Shape Tool Options (shown when a shape tool is active) -->
    <template v-if="isShapeTool">
      <div class="tool-group shape-options">
        <label class="shape-option-label">
          <input type="checkbox" v-model="shapeFromCenter" />
          <span>From Center</span>
        </label>
        <label class="shape-option-label">
          <input type="checkbox" v-model="shapeConstrain" />
          <span>Constrain</span>
        </label>
        <template v-if="currentTool === 'polygon'">
          <label class="shape-option-label">
            <span>Sides:</span>
            <input type="number" v-model.number="polygonSides" min="3" max="20" class="sides-input" />
          </label>
        </template>
        <template v-if="currentTool === 'star'">
          <label class="shape-option-label">
            <span>Points:</span>
            <input type="number" v-model.number="starPoints" min="3" max="20" class="sides-input" />
          </label>
          <label class="shape-option-label">
            <span>Inner:</span>
            <input type="number" v-model.number="starInnerRadius" min="10" max="90" class="radius-input" />
            <span>%</span>
          </label>
        </template>
      </div>
    </template>

    <div class="divider"></div>

    <!-- Import Button -->
    <div class="tool-group">
      <button
        @click="emit('import')"
        title="Import Asset (Ctrl+I)"
        class="import-btn"
      >
        <PhDownload class="icon" />
        <span class="btn-label">Import</span>
      </button>
    </div>

    <!-- Segment Tool Options (shown when segment tool is active) -->
    <template v-if="currentTool === 'segment'">
      <div class="divider"></div>
      <div class="tool-group segment-options">
        <button
          :class="{ active: segmentMode === 'point' }"
          @click="setSegmentMode('point')"
          title="Point Mode - Click to segment"
        >
          <span class="icon">●</span> Point
        </button>
        <button
          :class="{ active: segmentMode === 'box' }"
          @click="setSegmentMode('box')"
          title="Box Mode - Draw rectangle to segment"
        >
          <span class="icon">▢</span> Box
        </button>
        <template v-if="segmentPendingMask">
          <div class="divider"></div>
          <button @click="confirmSegmentMask" class="confirm-btn" title="Create Layer from Selection">
            <PhCheck class="icon" /> Create Layer
          </button>
          <button @click="clearSegmentMask" class="cancel-btn" title="Cancel Selection">
            <PhX class="icon" />
          </button>
        </template>
        <span v-if="segmentIsLoading" class="loading-indicator">Segmenting...</span>
      </div>
    </template>

    <div class="divider"></div>

    <div class="tool-group">
      <button @click="goToStart" title="Go to Start (Home)">
        <PhSkipBack class="icon" weight="fill" />
      </button>
      <button @click="stepBackward" title="Step Backward (←)">
        <PhRewind class="icon" weight="fill" />
      </button>
      <button @click="togglePlay" :title="isPlaying ? 'Pause (Space)' : 'Play (Space)'">
        <PhPause v-if="isPlaying" class="icon" weight="fill" />
        <PhPlay v-else class="icon" weight="fill" />
      </button>
      <button @click="stepForward" title="Step Forward (→)">
        <PhFastForward class="icon" weight="fill" />
      </button>
      <button @click="goToEnd" title="Go to End (End)">
        <PhSkipForward class="icon" weight="fill" />
      </button>
    </div>

    <div class="timecode-display">
      {{ formattedTimecode }}
    </div>

    <!-- Undo/Redo (left side, before spacer) -->
    <div class="tool-group undo-redo-group">
      <button @click="undo" :disabled="!canUndo" title="Undo (Ctrl+Z)" class="undo-btn">
        <PhArrowCounterClockwise class="icon" />
        <span class="btn-label">Undo</span>
      </button>
      <button @click="redo" :disabled="!canRedo" title="Redo (Ctrl+Shift+Z)" class="redo-btn">
        <PhArrowClockwise class="icon" />
        <span class="btn-label">Redo</span>
      </button>
    </div>

    <div class="spacer"></div>

    <div class="tool-group action-buttons">
      <button @click="emit('showPreview')" title="Full Resolution Preview (`)">
        <PhMonitor class="icon" /> Preview
      </button>
      <button @click="emit('showTemplateBuilder')" title="Create reusable motion graphics templates">
        <PhPackage class="icon" /> Template
      </button>
      <button class="primary-btn" @click="emit('showExport')" title="Export frame sequence for AI processing">
        <PhExport class="icon" /> Export
      </button>
      <button @click="emit('showComfyUI')" title="Send to ComfyUI workflow">
        <PhLink class="icon" /> ComfyUI
      </button>
    </div>

    <div class="divider"></div>

    <!-- GPU & Memory (right side) -->
    <div class="tool-group right-status-group">
      <span class="gpu-badge" :class="gpuTier">{{ gpuTier.toUpperCase() }}</span>
      <MemoryIndicator />
      <div class="divider"></div>
      <!-- Theme Selector (circular) -->
      <div class="theme-selector-wrapper">
        <button
          class="theme-btn-circle"
          :class="{ active: showThemeSelector }"
          @click.stop="showThemeSelector = !showThemeSelector"
          title="Change Theme"
        >
          <span class="theme-indicator-circle" :style="{ background: themeGradient }"></span>
        </button>
        <div v-if="showThemeSelector" class="theme-dropdown" @click.stop>
          <div class="theme-dropdown-header">Theme</div>
          <div class="theme-options">
            <button
              v-for="theme in themes"
              :key="theme.name"
              class="theme-option-circle"
              :class="{ active: currentTheme === theme.name }"
              :style="{ background: theme.gradient }"
              :title="theme.label"
              @click="selectTheme(theme.name)"
            ></button>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { usePlaybackStore } from '@/stores/playbackStore';
import { useThemeStore, type ThemeName } from '@/stores/themeStore';
import MemoryIndicator from '@/components/common/MemoryIndicator.vue';
import {
  PhCursor, PhPen, PhTextT, PhHand, PhMagnifyingGlass, PhSparkle,
  PhSquare, PhCircle, PhPolygon, PhStar, PhDownload,
  PhSkipBack, PhRewind, PhPlay, PhPause, PhFastForward, PhSkipForward,
  PhArrowCounterClockwise, PhArrowClockwise, PhMonitor, PhExport, PhLink,
  PhCheck, PhX, PhPackage
} from '@phosphor-icons/vue';

const props = defineProps<{
  currentTool: string;
  isPlaying: boolean;
  gpuTier: string;
}>();

const emit = defineEmits<{
  (e: 'update:currentTool', tool: string): void;
  (e: 'import'): void;
  (e: 'showPreview'): void;
  (e: 'showExport'): void;
  (e: 'showComfyUI'): void;
  (e: 'showTemplateBuilder'): void;
}>();

const store = useCompositorStore();
const playbackStore = usePlaybackStore();
const themeStore = useThemeStore();

// Shape tool state
const isShapeTool = computed(() =>
  ['rectangle', 'ellipse', 'polygon', 'star'].includes(props.currentTool)
);
const shapeFromCenter = ref(false);
const shapeConstrain = ref(false);
const polygonSides = ref(6);
const starPoints = ref(5);
const starInnerRadius = ref(50);

// Expose shape options to parent for canvas drawing
const shapeOptions = computed(() => ({
  fromCenter: shapeFromCenter.value,
  constrain: shapeConstrain.value,
  polygonSides: polygonSides.value,
  starPoints: starPoints.value,
  starInnerRadius: starInnerRadius.value / 100,
}));

// Watch for shape option changes and update store
watch(shapeOptions, (options) => {
  store.setShapeToolOptions(options);
}, { immediate: true, deep: true });

// Segment state from store
const segmentMode = computed(() => store.segmentMode);
const segmentPendingMask = computed(() => store.segmentPendingMask);
const segmentIsLoading = computed(() => store.segmentIsLoading);

function setSegmentMode(mode: 'point' | 'box') {
  store.setSegmentMode(mode);
}

function confirmSegmentMask() {
  store.confirmSegmentMask();
}

function clearSegmentMask() {
  store.clearSegmentMask();
}

// Theme selector
const showThemeSelector = ref(false);
const currentTheme = computed(() => themeStore.currentTheme);
const themeGradient = computed(() => themeStore.themeGradient);

const themes: Array<{ name: ThemeName; label: string; gradient: string }> = [
  { name: 'violet', label: 'Violet', gradient: 'linear-gradient(135deg, #8B5CF6, #EC4899)' },
  { name: 'ocean', label: 'Ocean', gradient: 'linear-gradient(135deg, #06B6D4, #3B82F6)' },
  { name: 'sunset', label: 'Rose', gradient: 'linear-gradient(135deg, #FB7185, #F43F5E)' },
  { name: 'forest', label: 'Forest', gradient: 'linear-gradient(135deg, #10B981, #06B6D4)' },
  { name: 'ember', label: 'Ember', gradient: 'linear-gradient(135deg, #EF4444, #F97316)' },
  { name: 'mono', label: 'Mono', gradient: 'linear-gradient(135deg, #4B5563, #6B7280)' },
];

function selectTheme(theme: ThemeName) {
  themeStore.setTheme(theme);
  showThemeSelector.value = false;
}

// Click outside handler for theme dropdown
function handleClickOutside(event: MouseEvent) {
  const target = event.target as HTMLElement;
  if (!target.closest('.theme-selector-wrapper')) {
    showThemeSelector.value = false;
  }
}

onMounted(() => {
  document.addEventListener('click', handleClickOutside);
});

onUnmounted(() => {
  document.removeEventListener('click', handleClickOutside);
});

// Timecode
const formattedTimecode = computed(() => {
  const frame = store.currentFrame;
  const fps = store.activeComposition?.frameRate || 16;
  const seconds = Math.floor(frame / fps);
  const frames = frame % fps;
  const minutes = Math.floor(seconds / 60);
  const secs = seconds % 60;
  return `${minutes.toString().padStart(2, '0')}:${secs.toString().padStart(2, '0')}:${frames.toString().padStart(2, '0')}`;
});

// Playback controls
function goToStart() {
  playbackStore.setFrame(0);
}

function goToEnd() {
  const frameCount = store.activeComposition?.frameCount || 81;
  playbackStore.setFrame(frameCount - 1);
}

function stepBackward() {
  const newFrame = Math.max(0, store.currentFrame - 1);
  playbackStore.setFrame(newFrame);
}

function stepForward() {
  const frameCount = store.activeComposition?.frameCount || 81;
  const newFrame = Math.min(frameCount - 1, store.currentFrame + 1);
  playbackStore.setFrame(newFrame);
}

function togglePlay() {
  playbackStore.togglePlayback();
}

// Undo/Redo
const canUndo = computed(() => store.canUndo);
const canRedo = computed(() => store.canRedo);

function undo() {
  store.undo();
}

function redo() {
  store.redo();
}
</script>

<style scoped>
.toolbar {
  display: flex;
  align-items: center;
  gap: 12px;
  padding: 10px 12px;
  background: var(--lattice-surface-1, #0f0f0f);
  border-radius: 8px;
  min-height: 54px;
}

.tool-group {
  display: flex;
  align-items: center;
  gap: 0;
}

.tool-group button {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 5px;
  min-width: 34px;
  height: 34px;
  padding: 0 10px;
  border: none;
  background: transparent;
  color: var(--lattice-text-secondary, #9CA3AF);
  border-radius: 6px;
  cursor: pointer;
  font-size: var(--lattice-text-md, 14px);
  font-weight: 500;
  transition: var(--lattice-transition-fast, 100ms ease);
}

/* Labeled tools container - connected buttons */
.labeled-tools {
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 8px;
  padding: 4px;
  gap: 0;
}

.labeled-tools button {
  flex-direction: column;
  gap: 2px;
  min-width: 52px;
  height: 44px;
  padding: 4px 8px;
  border-radius: 6px;
}

.tool-label {
  font-size: 10px;
  font-weight: 600;
  color: #999;
  line-height: 1;
}

.labeled-tools button.active .tool-label {
  color: #fff;
}

.labeled-tools button:hover .tool-label {
  color: #ccc;
}

.tool-group button:hover {
  background: var(--lattice-surface-3, #2d2d2d);
  color: var(--lattice-text-primary, #e5e5e5);
}

.tool-group button.active {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
}

.tool-group button:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.tool-group button:focus-visible {
  outline: 2px solid var(--lattice-accent, #8B5CF6);
  outline-offset: 2px;
}

.icon {
  font-size: 18px;
}

.divider {
  width: 1px;
  height: 24px;
  background: var(--lattice-surface-3, #222222);
  margin: 0 6px;
}

.spacer {
  flex: 1;
}

.timecode-display {
  font-family: var(--lattice-font-mono, 'SF Mono', Monaco, monospace);
  font-size: var(--lattice-text-lg, 15px);
  padding: 8px 18px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 8px;
  min-width: 110px;
  text-align: center;
  color: var(--lattice-text-primary, #e5e5e5);
}

.gpu-badge {
  font-size: var(--lattice-text-xs, 11px);
  padding: 2px 8px;
  border-radius: 999px;
  font-weight: 600;
  text-transform: uppercase;
}

.gpu-badge.cpu { background: var(--lattice-surface-3, #555); }
.gpu-badge.webgl { background: var(--lattice-success, #10B981); color: white; }
.gpu-badge.webgpu { background: var(--lattice-info, #3B82F6); color: white; }
.gpu-badge.blackwell { background: #76b900; color: #000; }

/* Undo/Redo Buttons - more prominent */
.undo-redo-group {
  gap: 6px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 8px;
  padding: 4px;
}

.undo-btn,
.redo-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 14px !important;
  height: 36px !important;
  background: transparent !important;
  border-radius: 6px !important;
}

.undo-btn:hover:not(:disabled),
.redo-btn:hover:not(:disabled) {
  background: var(--lattice-surface-3, #2a2a2a) !important;
}

.undo-btn:disabled,
.redo-btn:disabled {
  opacity: 0.3;
}

.undo-btn .icon,
.redo-btn .icon {
  font-size: 18px;
}

.undo-btn .btn-label,
.redo-btn .btn-label {
  font-size: 13px;
  font-weight: 500;
}

/* Right Status Group */
.right-status-group {
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 0 12px;
  margin-left: auto;
}

/* Theme Selector */
.theme-selector-wrapper {
  position: relative;
}

.theme-btn-circle {
  width: 28px;
  height: 28px;
  min-width: 28px;
  min-height: 28px;
  padding: 3px;
  border: none;
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 50%;
  cursor: pointer;
  transition: var(--lattice-transition-fast, 100ms ease);
  flex-shrink: 0;
}

.theme-btn-circle:hover,
.theme-btn-circle.active {
  background: var(--lattice-surface-3, #222222);
  transform: scale(1.1);
}

.theme-indicator-circle {
  display: block;
  width: 22px;
  height: 22px;
  min-width: 22px;
  min-height: 22px;
  border-radius: 50%;
  aspect-ratio: 1 / 1;
  flex-shrink: 0;
}

.theme-dropdown {
  position: absolute;
  top: calc(100% + 8px);
  right: 0;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-surface-3, #222222);
  border-radius: var(--lattice-radius-lg, 8px);
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.5);
  padding: 12px;
  z-index: 1000;
  min-width: 140px;
}

.theme-dropdown-header {
  font-size: var(--lattice-text-xs, 11px);
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--lattice-text-muted, #6B7280);
  margin-bottom: 8px;
}

.theme-options {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 6px;
}

.theme-option-circle {
  width: 28px;
  height: 28px;
  border: none;
  border-radius: 50%;
  cursor: pointer;
  transition: var(--lattice-transition-fast, 100ms ease);
}

.theme-option-circle:hover {
  transform: scale(1.15);
}

.theme-option-circle.active {
  box-shadow: 0 0 0 2px var(--lattice-surface-1, #121212), 0 0 0 3px white;
}

.loading-indicator {
  font-size: var(--lattice-text-sm, 12px);
  color: var(--lattice-text-muted, #6B7280);
  margin-left: 8px;
}

.confirm-btn {
  background: var(--lattice-success, #10B981) !important;
  color: white !important;
}

.cancel-btn {
  background: var(--lattice-surface-3, #333) !important;
}

/* Shape tool options */
.shape-tools {
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 8px;
  padding: 4px;
}

.shape-options {
  display: flex;
  align-items: center;
  gap: 12px;
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 8px;
}

.shape-option-label {
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: var(--lattice-text-xs, 11px);
  color: var(--lattice-text-secondary, #9CA3AF);
  cursor: pointer;
}

.shape-option-label input[type="checkbox"] {
  width: 14px;
  height: 14px;
  accent-color: var(--lattice-accent, #8B5CF6);
}

.shape-option-label .sides-input,
.shape-option-label .radius-input {
  width: 40px;
  padding: 2px 4px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: var(--lattice-radius-sm, 2px);
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: var(--lattice-text-xs, 11px);
  text-align: center;
}

.shape-option-label .sides-input:focus,
.shape-option-label .radius-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

/* Action buttons group (Preview/Export/ComfyUI) */
.action-buttons {
  gap: 12px !important;
}

.action-buttons button {
  padding: 0 14px !important;
}

/* Primary action button (Export) */
.tool-group button.primary-btn {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
  padding: 0 14px;
  font-weight: 500;
}

.tool-group button.primary-btn:hover {
  background: var(--lattice-accent-hover, #9D7AFA);
  color: white;
}
</style>
