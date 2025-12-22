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
        <span class="icon" aria-hidden="true">↖</span>
        <span class="tool-label">Select</span>
      </button>
      <button
        :class="{ active: currentTool === 'pen' }"
        :aria-pressed="currentTool === 'pen'"
        @click="emit('update:currentTool', 'pen')"
        title="Pen Tool (P) - Draw paths and shapes"
        aria-label="Pen tool"
      >
        <span class="icon" aria-hidden="true">✒</span>
        <span class="tool-label">Pen</span>
      </button>
      <button
        :class="{ active: currentTool === 'text' }"
        :aria-pressed="currentTool === 'text'"
        @click="emit('update:currentTool', 'text')"
        title="Text Tool (T) - Add text layers"
        aria-label="Text tool"
      >
        <span class="icon" aria-hidden="true">T</span>
        <span class="tool-label">Text</span>
      </button>
      <button
        :class="{ active: currentTool === 'hand' }"
        :aria-pressed="currentTool === 'hand'"
        @click="emit('update:currentTool', 'hand')"
        title="Hand Tool (H) - Pan the viewport"
        aria-label="Pan tool"
      >
        <span class="icon" aria-hidden="true">✋</span>
        <span class="tool-label">Pan</span>
      </button>
      <button
        :class="{ active: currentTool === 'zoom' }"
        :aria-pressed="currentTool === 'zoom'"
        @click="emit('update:currentTool', 'zoom')"
        title="Zoom Tool (Z) - Zoom in/out the viewport"
        aria-label="Zoom tool"
      >
        <span class="icon" aria-hidden="true">🔍</span>
        <span class="tool-label">Zoom</span>
      </button>
      <button
        :class="{ active: currentTool === 'segment' }"
        :aria-pressed="currentTool === 'segment'"
        @click="emit('update:currentTool', 'segment')"
        title="AI Segment (S) - Auto-select objects using AI"
        aria-label="AI Segment tool"
      >
        <span class="icon" aria-hidden="true">✨</span>
        <span class="tool-label">AI Seg</span>
      </button>
    </div>

    <div class="divider"></div>

    <!-- Import Button -->
    <div class="tool-group">
      <button
        @click="emit('import')"
        title="Import Asset (Ctrl+I)"
        class="import-btn"
      >
        <span class="icon">📥</span>
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
            <span class="icon">✓</span> Create Layer
          </button>
          <button @click="clearSegmentMask" class="cancel-btn" title="Cancel Selection">
            <span class="icon">✕</span>
          </button>
        </template>
        <span v-if="segmentIsLoading" class="loading-indicator">Segmenting...</span>
      </div>
    </template>

    <div class="divider"></div>

    <div class="tool-group">
      <button @click="goToStart" title="Go to Start (Home)">
        <span class="icon">⏮</span>
      </button>
      <button @click="stepBackward" title="Step Backward">
        <span class="icon">⏪</span>
      </button>
      <button @click="togglePlay" :title="isPlaying ? 'Pause (Space)' : 'Play (Space)'">
        <span class="icon">{{ isPlaying ? '⏸' : '▶' }}</span>
      </button>
      <button @click="stepForward" title="Step Forward">
        <span class="icon">⏩</span>
      </button>
      <button @click="goToEnd" title="Go to End (End)">
        <span class="icon">⏭</span>
      </button>
    </div>

    <div class="timecode-display">
      {{ formattedTimecode }}
    </div>

    <div class="divider"></div>

    <div class="tool-group">
      <select v-model="activeWorkspaceLocal" class="workspace-selector">
        <option value="standard">Standard</option>
        <option value="animation">Animation</option>
        <option value="effects">Effects</option>
        <option value="minimal">Minimal</option>
      </select>
    </div>

    <!-- Theme Selector -->
    <div class="tool-group theme-selector-group">
      <button
        class="theme-btn"
        :class="{ active: showThemeSelector }"
        @click="showThemeSelector = !showThemeSelector"
        title="Change Theme"
      >
        <span class="theme-indicator" :style="{ background: themeGradient }"></span>
      </button>
      <div v-if="showThemeSelector" class="theme-dropdown">
        <div class="theme-dropdown-header">Theme</div>
        <div class="theme-options">
          <button
            v-for="theme in themes"
            :key="theme.name"
            class="theme-option"
            :class="{ active: currentTheme === theme.name }"
            :style="{ background: theme.gradient }"
            :title="theme.label"
            @click="selectTheme(theme.name)"
          ></button>
        </div>
      </div>
    </div>

    <div class="spacer"></div>

    <div class="tool-group">
      <span class="gpu-badge" :class="gpuTier">{{ gpuTier.toUpperCase() }}</span>
      <MemoryIndicator />
      <button @click="undo" :disabled="!canUndo" title="Undo (Ctrl+Z)">
        <span class="icon">↩</span>
      </button>
      <button @click="redo" :disabled="!canRedo" title="Redo (Ctrl+Shift+Z)">
        <span class="icon">↪</span>
      </button>
      <div class="divider"></div>
      <button @click="emit('showPreview')" title="Full Resolution Preview (`)">
        <span class="icon">🖥</span> Preview
      </button>
      <button class="primary-btn" @click="emit('showExport')" title="Export frame sequence for AI processing">
        <span class="icon">📤</span> Export
      </button>
      <button @click="emit('showComfyUI')" title="Send to ComfyUI workflow">
        <span class="icon">🔗</span> ComfyUI
      </button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { usePlaybackStore } from '@/stores/playbackStore';
import { useThemeStore, type ThemeName } from '@/stores/themeStore';
import MemoryIndicator from '@/components/common/MemoryIndicator.vue';

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
}>();

const store = useCompositorStore();
const playbackStore = usePlaybackStore();
const themeStore = useThemeStore();

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

// Workspace selector
const activeWorkspaceLocal = ref('standard');

// Theme selector
const showThemeSelector = ref(false);
const currentTheme = computed(() => themeStore.currentTheme);
const themeGradient = computed(() => themeStore.themeGradient);

const themes: Array<{ name: ThemeName; label: string; gradient: string }> = [
  { name: 'violet', label: 'Violet', gradient: 'linear-gradient(135deg, #8B5CF6, #EC4899)' },
  { name: 'ocean', label: 'Ocean', gradient: 'linear-gradient(135deg, #06B6D4, #3B82F6)' },
  { name: 'sunset', label: 'Sunset', gradient: 'linear-gradient(135deg, #F59E0B, #EF4444)' },
  { name: 'forest', label: 'Forest', gradient: 'linear-gradient(135deg, #10B981, #06B6D4)' },
  { name: 'ember', label: 'Ember', gradient: 'linear-gradient(135deg, #EF4444, #F97316)' },
  { name: 'mono', label: 'Mono', gradient: 'linear-gradient(135deg, #4B5563, #6B7280)' },
];

function selectTheme(theme: ThemeName) {
  themeStore.setTheme(theme);
  showThemeSelector.value = false;
}

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
  gap: 6px;
  padding: 6px 12px;
  background: var(--weyl-surface-1, #0f0f0f);
  border-radius: var(--weyl-radius-lg, 6px);
  border: 1px solid var(--weyl-border-subtle, #1a1a1a);
  min-height: 40px;
}

.tool-group {
  display: flex;
  align-items: center;
  gap: 2px;
}

.tool-group button {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
  min-width: 28px;
  height: 28px;
  padding: 0 6px;
  border: none;
  background: transparent;
  color: var(--weyl-text-secondary, #9CA3AF);
  border-radius: var(--weyl-radius-md, 4px);
  cursor: pointer;
  font-size: var(--weyl-text-base, 13px);
  transition: var(--weyl-transition-fast, 100ms ease);
}

.labeled-tools button {
  flex-direction: column;
  gap: 1px;
  min-width: 44px;
  height: 36px;
  padding: 2px 6px;
}

.tool-label {
  font-size: 9px;
  color: #888;
  line-height: 1;
}

.labeled-tools button.active .tool-label {
  color: #fff;
}

.labeled-tools button:hover .tool-label {
  color: #ccc;
}

.tool-group button:hover {
  background: var(--weyl-surface-3, #222222);
  color: var(--weyl-text-primary, #e5e5e5);
}

.tool-group button.active {
  background: var(--weyl-accent, #8B5CF6);
  color: white;
}

.tool-group button:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.tool-group button:focus-visible {
  outline: 2px solid var(--weyl-accent, #8B5CF6);
  outline-offset: 2px;
}

.icon {
  font-size: 14px;
}

.divider {
  width: 1px;
  height: 20px;
  background: var(--weyl-surface-3, #222222);
  margin: 0 4px;
}

.spacer {
  flex: 1;
}

.timecode-display {
  font-family: var(--weyl-font-mono, 'SF Mono', Monaco, monospace);
  font-size: var(--weyl-text-lg, 15px);
  padding: 6px 16px;
  background: var(--weyl-surface-2, #1a1a1a);
  border-radius: 999px;
  min-width: 100px;
  text-align: center;
  color: var(--weyl-text-primary, #e5e5e5);
}

.workspace-selector {
  padding: 6px 12px;
  background: var(--weyl-surface-2, #1a1a1a);
  border: none;
  color: var(--weyl-text-primary, #e5e5e5);
  border-radius: var(--weyl-radius-md, 4px);
  font-size: var(--weyl-text-base, 13px);
}

.gpu-badge {
  font-size: var(--weyl-text-xs, 11px);
  padding: 2px 8px;
  border-radius: 999px;
  font-weight: 600;
  text-transform: uppercase;
}

.gpu-badge.cpu { background: var(--weyl-surface-3, #555); }
.gpu-badge.webgl { background: var(--weyl-success, #10B981); color: white; }
.gpu-badge.webgpu { background: var(--weyl-info, #3B82F6); color: white; }
.gpu-badge.blackwell { background: #76b900; color: #000; }

/* Theme Selector */
.theme-selector-group {
  position: relative;
}

.theme-btn {
  width: 28px;
  height: 28px;
  padding: 4px;
  border: none;
  background: var(--weyl-surface-2, #1a1a1a);
  border-radius: var(--weyl-radius-md, 4px);
  cursor: pointer;
  transition: var(--weyl-transition-fast, 100ms ease);
}

.theme-btn:hover,
.theme-btn.active {
  background: var(--weyl-surface-3, #222222);
}

.theme-indicator {
  display: block;
  width: 100%;
  height: 100%;
  border-radius: 2px;
}

.theme-dropdown {
  position: absolute;
  top: 100%;
  left: 50%;
  transform: translateX(-50%);
  margin-top: 8px;
  background: var(--weyl-surface-1, #121212);
  border-radius: var(--weyl-radius-lg, 6px);
  box-shadow: var(--weyl-shadow-dropdown, 0 4px 16px rgba(0, 0, 0, 0.3));
  padding: 12px;
  z-index: var(--weyl-z-dropdown, 100);
  min-width: 120px;
}

.theme-dropdown-header {
  font-size: var(--weyl-text-xs, 11px);
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--weyl-text-muted, #6B7280);
  margin-bottom: 8px;
}

.theme-options {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 6px;
}

.theme-option {
  width: 28px;
  height: 28px;
  border: none;
  border-radius: var(--weyl-radius-sm, 2px);
  cursor: pointer;
  transition: var(--weyl-transition-fast, 100ms ease);
}

.theme-option:hover {
  transform: scale(1.1);
}

.theme-option.active {
  box-shadow: 0 0 0 2px var(--weyl-surface-1, #121212), 0 0 0 3px white;
}

.loading-indicator {
  font-size: var(--weyl-text-sm, 12px);
  color: var(--weyl-text-muted, #6B7280);
  margin-left: 8px;
}

.confirm-btn {
  background: var(--weyl-success, #10B981) !important;
  color: white !important;
}

.cancel-btn {
  background: var(--weyl-surface-3, #333) !important;
}

/* Primary action button (Export) */
.tool-group button.primary-btn {
  background: var(--weyl-accent, #8B5CF6);
  color: white;
  padding: 0 12px;
  font-weight: 500;
}

.tool-group button.primary-btn:hover {
  background: var(--weyl-accent-hover, #9D7AFA);
  color: white;
}
</style>
