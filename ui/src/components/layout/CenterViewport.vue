<!--
  @component CenterViewport
  @description Center viewport area with canvas, guides, rulers, and timeline.
  Extracted from WorkspaceLayout.vue to reduce file size.
-->
<template>
  <Splitpanes horizontal class="default-theme">
    <!-- Viewport -->
    <Pane :size="65" :min-size="20">
      <div class="panel viewport-panel">
        <div class="viewport-header">
          <div class="viewport-tabs" role="tablist" aria-label="Viewport tabs">
            <button
              role="tab"
              :aria-selected="viewportTab === 'composition'"
              :class="{ active: viewportTab === 'composition' }"
              @click="$emit('update:viewportTab', 'composition')"
            >
              Composition
            </button>
            <button
              role="tab"
              :aria-selected="viewportTab === 'layer'"
              :class="{ active: viewportTab === 'layer' }"
              @click="$emit('update:viewportTab', 'layer')"
            >
              Layer
            </button>
            <button
              role="tab"
              :aria-selected="viewportTab === 'footage'"
              :class="{ active: viewportTab === 'footage' }"
              @click="$emit('update:viewportTab', 'footage')"
            >
              Footage
            </button>
          </div>
          <div class="viewport-controls">
            <button
              :class="{ active: viewOptions.showRulers }"
              @click="toggleRulers"
              title="Toggle Rulers/Guides"
              aria-label="Toggle rulers and guides"
              :aria-pressed="viewOptions.showRulers"
            >
              <span class="icon" aria-hidden="true">📏</span>
            </button>
            <button
              :class="{ active: viewOptions.showGrid }"
              @click="toggleGrid"
              title="Toggle Grid"
              aria-label="Toggle grid"
              :aria-pressed="viewOptions.showGrid"
            >
              <span class="icon">▦</span>
            </button>
          </div>
        </div>
        <div class="viewport-content" :class="{ 'rulers-active': viewOptions.showRulers }">
          <!-- Grid overlay -->
          <div v-if="viewOptions.showGrid" class="grid-overlay" :style="gridOverlayStyle"></div>

          <!-- Guides overlay -->
          <div v-if="guides.length > 0" class="guides-overlay">
            <div
              v-for="guide in guides"
              :key="guide.id"
              :class="['guide', guide.orientation]"
              :style="getGuideStyle(guide)"
              @mousedown="startGuideDrag(guide, $event)"
              @contextmenu.prevent="showGuideContextMenu(guide, $event)"
            >
              <button
                class="guide-delete-btn"
                @click.stop="removeGuide(guide.id)"
                @mousedown.stop
                title="Delete guide"
              >×</button>
            </div>
          </div>

          <!-- Guide context menu -->
          <Teleport to="body">
            <div
              v-if="guideContextMenu.visible"
              class="guide-context-menu"
              :style="{ left: guideContextMenu.x + 'px', top: guideContextMenu.y + 'px' }"
              @click.stop
            >
              <button @click="deleteGuideFromMenu">Delete Guide</button>
              <button @click="clearAllGuides">Clear All Guides</button>
            </div>
          </Teleport>

          <!-- Rulers overlay -->
          <div v-if="viewOptions.showRulers" class="rulers-overlay">
            <div class="ruler ruler-horizontal" @mousedown="createGuideFromRuler('horizontal', $event)">
              <span v-for="i in 20" :key="'h'+i" class="tick" :style="{ left: (i * 5) + '%' }">
                {{ Math.round((i * 5 / 100) * compWidth) }}
              </span>
            </div>
            <div class="ruler ruler-vertical" @mousedown="createGuideFromRuler('vertical', $event)">
              <span v-for="i in 20" :key="'v'+i" class="tick" :style="{ top: (i * 5) + '%' }">
                {{ Math.round((i * 5 / 100) * compHeight) }}
              </span>
            </div>
          </div>

          <!-- Snap indicator -->
          <div v-if="snapEnabled && (snapIndicatorX || snapIndicatorY)" class="snap-indicator">
            <div v-if="snapIndicatorX" class="snap-line vertical" :style="{ left: snapIndicatorX + 'px' }"></div>
            <div v-if="snapIndicatorY" class="snap-line horizontal" :style="{ top: snapIndicatorY + 'px' }"></div>
          </div>

          <ThreeCanvas v-if="viewportTab === 'composition'" ref="threeCanvasRef" />
          <ViewportRenderer
            v-else
            :camera="activeCamera"
            :viewportState="viewportState"
            :viewOptions="viewOptions"
            :compWidth="compWidth"
            :compHeight="compHeight"
          />
        </div>
      </div>
    </Pane>

    <!-- Timeline + Graph Editor -->
    <Pane :size="35" :min-size="15">
      <Splitpanes v-if="showCurveEditor" horizontal class="default-theme">
        <Pane :size="50" :min-size="20">
          <div class="panel timeline-panel">
            <TimelinePanel
              @openCompositionSettings="$emit('openCompositionSettings')"
              @openPathSuggestion="$emit('openPathSuggestion')"
            />
          </div>
        </Pane>
        <Pane :size="50" :min-size="20">
          <div class="panel curve-editor-panel">
            <CurveEditor @close="$emit('update:showCurveEditor', false)" />
          </div>
        </Pane>
      </Splitpanes>
      <div v-else class="panel timeline-panel">
        <TimelinePanel
          @openCompositionSettings="$emit('openCompositionSettings')"
          @openPathSuggestion="$emit('openPathSuggestion')"
        />
      </div>
    </Pane>
  </Splitpanes>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
// Components
import type ThreeCanvas from "@/components/canvas/ThreeCanvas.vue";
import type { Camera3D, ViewportState } from "@/types/camera";

export type ViewportTab = "composition" | "layer" | "footage";

export interface ViewOptions {
  showGrid: boolean;
  showRulers: boolean;
  showAxes: boolean;
  showCameraFrustum: boolean;
  showCompositionBounds: boolean;
  showFocalPlane: boolean;
  showLayerOutlines: boolean;
  showSafeZones: boolean;
  showGuides: boolean;
  gridSize: number;
  gridDivisions: number;
}

export interface Guide {
  id: string;
  orientation: "horizontal" | "vertical";
  position: number;
}

export interface GuideContextMenu {
  visible: boolean;
  x: number;
  y: number;
  guideId: string | null;
}

const props = defineProps<{
  viewportTab: ViewportTab;
  viewOptions: ViewOptions;
  showCurveEditor: boolean;
  guides: Guide[];
  guideContextMenu: GuideContextMenu;
  snapEnabled: boolean;
  snapIndicatorX: number | null;
  snapIndicatorY: number | null;
  compWidth: number;
  compHeight: number;
  gridOverlayStyle: Record<string, any>;
  activeCamera: Camera3D;
  viewportState: ViewportState;
}>();

const emit = defineEmits<{
  "update:viewportTab": [tab: ViewportTab];
  "update:viewOptions": [options: ViewOptions];
  "update:showCurveEditor": [show: boolean];
  openCompositionSettings: [];
  openPathSuggestion: [];
  // Guide events
  startGuideDrag: [guide: Guide, event: MouseEvent];
  showGuideContextMenu: [guide: Guide, event: MouseEvent];
  removeGuide: [id: string];
  deleteGuideFromMenu: [];
  clearAllGuides: [];
  createGuideFromRuler: [
    orientation: "horizontal" | "vertical",
    event: MouseEvent,
  ];
}>();

// Template ref for ThreeCanvas - expose to parent
const threeCanvasRef = ref<InstanceType<typeof ThreeCanvas> | null>(null);

// Expose threeCanvasRef to parent
defineExpose({
  threeCanvasRef,
  getEngine: () => threeCanvasRef.value?.engine ?? null,
  engine: computed(() => threeCanvasRef.value?.engine ?? null),
});

// View option toggles
function toggleRulers() {
  emit("update:viewOptions", {
    ...props.viewOptions,
    showRulers: !props.viewOptions.showRulers,
  });
}

function toggleGrid() {
  emit("update:viewOptions", {
    ...props.viewOptions,
    showGrid: !props.viewOptions.showGrid,
  });
}

// Guide style helper
function getGuideStyle(guide: Guide) {
  if (guide.orientation === "horizontal") {
    return { top: `${guide.position}px`, left: 0, right: 0 };
  }
  return { left: `${guide.position}px`, top: 0, bottom: 0 };
}

// Delegate guide events to parent
function startGuideDrag(guide: Guide, event: MouseEvent) {
  emit("startGuideDrag", guide, event);
}

function showGuideContextMenu(guide: Guide, event: MouseEvent) {
  emit("showGuideContextMenu", guide, event);
}

function removeGuide(id: string) {
  emit("removeGuide", id);
}

function deleteGuideFromMenu() {
  emit("deleteGuideFromMenu");
}

function clearAllGuides() {
  emit("clearAllGuides");
}

function createGuideFromRuler(
  orientation: "horizontal" | "vertical",
  event: MouseEvent,
) {
  emit("createGuideFromRuler", orientation, event);
}
</script>

<style scoped>
.viewport-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-void, #050505);
}

.viewport-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border, #333);
}

.viewport-tabs {
  display: flex;
  gap: 0;
}

.viewport-tabs button {
  padding: 4px 12px;
  background: transparent;
  border: none;
  color: var(--lattice-text-secondary, #888);
  cursor: pointer;
  font-size: 11px;
  font-weight: 500;
  transition: all 0.15s ease;
}

.viewport-tabs button:hover {
  color: var(--lattice-text-primary, #e5e5e5);
}

.viewport-tabs button.active {
  color: var(--lattice-accent, #8b5cf6);
  border-bottom: 2px solid var(--lattice-accent, #8b5cf6);
}

.viewport-controls {
  display: flex;
  gap: 4px;
}

.viewport-controls button {
  padding: 4px 8px;
  background: transparent;
  border: 1px solid transparent;
  color: var(--lattice-text-secondary, #888);
  cursor: pointer;
  border-radius: 4px;
  font-size: 12px;
  transition: all 0.15s ease;
}

.viewport-controls button:hover {
  background: var(--lattice-surface-3, #252525);
  color: var(--lattice-text-primary, #e5e5e5);
}

.viewport-controls button.active {
  background: var(--lattice-accent-dim, rgba(139, 92, 246, 0.2));
  color: var(--lattice-accent, #8b5cf6);
  border-color: var(--lattice-accent, #8b5cf6);
}

.viewport-content {
  flex: 1;
  position: relative;
  overflow: hidden;
  display: flex;
  justify-content: center;
  align-items: center;
}

.viewport-content.rulers-active {
  margin-left: 20px;
  margin-top: 20px;
}

/* Grid overlay */
.grid-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 1;
}

/* Guides */
.guides-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 10;
}

.guide {
  position: absolute;
  pointer-events: auto;
  cursor: move;
}

.guide.horizontal {
  height: 1px;
  background: var(--lattice-accent, #8b5cf6);
  left: 0;
  right: 0;
}

.guide.vertical {
  width: 1px;
  background: var(--lattice-accent, #8b5cf6);
  top: 0;
  bottom: 0;
}

.guide-delete-btn {
  position: absolute;
  width: 14px;
  height: 14px;
  padding: 0;
  background: var(--lattice-surface-3, #252525);
  border: 1px solid var(--lattice-accent, #8b5cf6);
  color: var(--lattice-text-primary, #e5e5e5);
  cursor: pointer;
  font-size: 10px;
  line-height: 1;
  border-radius: 2px;
  opacity: 0;
  transition: opacity 0.15s ease;
}

.guide:hover .guide-delete-btn {
  opacity: 1;
}

.guide.horizontal .guide-delete-btn {
  right: 4px;
  top: -7px;
}

.guide.vertical .guide-delete-btn {
  top: 4px;
  left: -7px;
}

/* Guide context menu */
.guide-context-menu {
  position: fixed;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border, #333);
  border-radius: 4px;
  padding: 4px 0;
  z-index: 1000;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
}

.guide-context-menu button {
  display: block;
  width: 100%;
  padding: 6px 16px;
  background: transparent;
  border: none;
  color: var(--lattice-text-primary, #e5e5e5);
  text-align: left;
  cursor: pointer;
  font-size: 12px;
}

.guide-context-menu button:hover {
  background: var(--lattice-surface-3, #252525);
}

/* Rulers */
.rulers-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 5;
}

.ruler {
  position: absolute;
  background: var(--lattice-surface-2, #1a1a1a);
  pointer-events: auto;
  cursor: crosshair;
}

.ruler-horizontal {
  top: -20px;
  left: 0;
  right: 0;
  height: 20px;
  border-bottom: 1px solid var(--lattice-border, #333);
}

.ruler-vertical {
  left: -20px;
  top: 0;
  bottom: 0;
  width: 20px;
  border-right: 1px solid var(--lattice-border, #333);
}

.ruler .tick {
  position: absolute;
  font-size: 8px;
  color: var(--lattice-text-secondary, #888);
}

.ruler-horizontal .tick {
  bottom: 2px;
  transform: translateX(-50%);
}

.ruler-vertical .tick {
  right: 2px;
  transform: translateY(-50%);
  writing-mode: vertical-rl;
  text-orientation: mixed;
}

/* Snap indicator */
.snap-indicator {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 15;
}

.snap-line {
  position: absolute;
  background: var(--lattice-warning, #f59e0b);
}

.snap-line.vertical {
  width: 1px;
  top: 0;
  bottom: 0;
}

.snap-line.horizontal {
  height: 1px;
  left: 0;
  right: 0;
}

/* Timeline */
.timeline-panel {
  height: 100%;
  background: var(--lattice-surface-1, #121212);
}

.curve-editor-panel {
  height: 100%;
  background: var(--lattice-surface-1, #121212);
}
</style>
