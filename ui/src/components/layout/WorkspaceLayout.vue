<!--
  @component WorkspaceLayout
  @description Main application layout component for Weyl Compositor.
  Orchestrates the complete motion graphics workspace including:
  - Top toolbar with drawing/selection tools
  - Left sidebar (Project/Effects panels)
  - Center canvas (ThreeCanvas renderer)
  - Right sidebar (Properties/AI Agent panels)
  - Bottom timeline panel
  - HD Preview window
  - Modal dialogs (composition settings, AI chat, exports)

  @features
  - Responsive panel sizing with splitters
  - Tool selection (select, pen, text, hand, segment)
  - Keyboard shortcut handling
  - AI agent integration for natural language animation
  - HD preview window toggle

  @emits None - root layout component
  @slots None
-->
<template>
  <div class="workspace-layout">
    <!-- Top Toolbar -->
    <div class="toolbar" role="toolbar" aria-label="Drawing tools">
      <div class="tool-group labeled-tools" role="group" aria-label="Selection and drawing tools">
        <button
          :class="{ active: currentTool === 'select' }"
          :aria-pressed="currentTool === 'select'"
          @click="currentTool = 'select'"
          title="Select Tool (V) - Select and move layers"
          aria-label="Select tool"
        >
          <span class="icon" aria-hidden="true">↖</span>
          <span class="tool-label">Select</span>
        </button>
        <button
          :class="{ active: currentTool === 'pen' }"
          :aria-pressed="currentTool === 'pen'"
          @click="currentTool = 'pen'"
          title="Pen Tool (P) - Draw paths and shapes"
          aria-label="Pen tool"
        >
          <span class="icon" aria-hidden="true">✒</span>
          <span class="tool-label">Pen</span>
        </button>
        <button
          :class="{ active: currentTool === 'text' }"
          :aria-pressed="currentTool === 'text'"
          @click="currentTool = 'text'"
          title="Text Tool (T) - Add text layers"
          aria-label="Text tool"
        >
          <span class="icon" aria-hidden="true">T</span>
          <span class="tool-label">Text</span>
        </button>
        <button
          :class="{ active: currentTool === 'hand' }"
          :aria-pressed="currentTool === 'hand'"
          @click="currentTool = 'hand'"
          title="Hand Tool (H) - Pan the viewport"
          aria-label="Pan tool"
        >
          <span class="icon" aria-hidden="true">✋</span>
          <span class="tool-label">Pan</span>
        </button>
        <button
          :class="{ active: currentTool === 'zoom' }"
          :aria-pressed="currentTool === 'zoom'"
          @click="currentTool = 'zoom'"
          title="Zoom Tool (Z) - Zoom in/out the viewport"
          aria-label="Zoom tool"
        >
          <span class="icon" aria-hidden="true">🔍</span>
          <span class="tool-label">Zoom</span>
        </button>
        <button
          :class="{ active: currentTool === 'segment' }"
          :aria-pressed="currentTool === 'segment'"
          @click="currentTool = 'segment'"
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
          @click="triggerAssetImport"
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
        <select v-model="activeWorkspace" class="workspace-selector">
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
        <button @click="showHDPreview = true" title="Full Resolution Preview (`)">
          <span class="icon">🖥</span> Preview
        </button>
        <button @click="showExportDialog = true" title="Export frame sequence for AI processing">
          <span class="icon">📤</span> Export
        </button>
        <button @click="showComfyUIExportDialog = true" title="Send to ComfyUI workflow">
          <span class="icon">🔗</span> ComfyUI
        </button>
      </div>
    </div>

    <!-- Main Workspace with Splitpanes -->
    <div class="workspace-content">
      <Splitpanes class="default-theme horizontal-split">
        <!-- Left Panel: Project/Effects -->
        <Pane :size="14" :min-size="10" :max-size="25">
          <div class="panel left-panel">
            <div class="panel-tabs" role="tablist" aria-label="Left panel tabs">
              <button
                role="tab"
                :aria-selected="leftTab === 'project'"
                aria-controls="left-panel-project"
                :class="{ active: leftTab === 'project' }"
                @click="leftTab = 'project'"
              >
                Project
              </button>
              <button
                role="tab"
                :aria-selected="leftTab === 'effects'"
                aria-controls="left-panel-effects"
                :class="{ active: leftTab === 'effects' }"
                @click="leftTab = 'effects'"
              >
                Effects
              </button>
              <button
                role="tab"
                :aria-selected="leftTab === 'assets'"
                aria-controls="left-panel-assets"
                :class="{ active: leftTab === 'assets' }"
                @click="leftTab = 'assets'"
              >
                Assets
              </button>
            </div>
            <div class="panel-content" role="tabpanel" :id="`left-panel-${leftTab}`">
              <ProjectPanel v-if="leftTab === 'project'" @openCompositionSettings="showCompositionSettingsDialog = true" />
              <EffectsPanel v-else-if="leftTab === 'effects'" />
              <AssetsPanel
                v-else-if="leftTab === 'assets'"
                @create-layers-from-svg="onCreateLayersFromSvg"
                @use-mesh-as-emitter="onUseMeshAsEmitter"
                @environment-update="onEnvironmentUpdate"
                @environment-load="onEnvironmentLoad"
                @environment-clear="onEnvironmentClear"
              />
            </div>
          </div>
        </Pane>

        <!-- Center: Viewport + Timeline -->
        <Pane :size="62" :min-size="35">
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
                      @click="viewportTab = 'composition'"
                    >
                      Composition
                    </button>
                    <button
                      role="tab"
                      :aria-selected="viewportTab === 'layer'"
                      :class="{ active: viewportTab === 'layer' }"
                      @click="viewportTab = 'layer'"
                    >
                      Layer
                    </button>
                    <button
                      role="tab"
                      :aria-selected="viewportTab === 'footage'"
                      :class="{ active: viewportTab === 'footage' }"
                      @click="viewportTab = 'footage'"
                    >
                      Footage
                    </button>
                  </div>
                  <div class="viewport-controls">
                    <select v-model="viewZoom" @change="handleZoomChange" class="zoom-select" aria-label="Zoom level">
                      <option value="fit">Fit</option>
                      <option value="25">25%</option>
                      <option value="50">50%</option>
                      <option value="75">75%</option>
                      <option value="100">100%</option>
                      <option value="150">150%</option>
                      <option value="200">200%</option>
                    </select>
                    <button
                      :class="{ active: viewOptions.showRulers }"
                      @click="viewOptions.showRulers = !viewOptions.showRulers"
                      title="Toggle Rulers/Guides"
                      aria-label="Toggle rulers and guides"
                      :aria-pressed="viewOptions.showRulers"
                    >
                      <span class="icon" aria-hidden="true">📏</span>
                    </button>
                    <button
                      :class="{ active: viewOptions.showGrid }"
                      @click="viewOptions.showGrid = !viewOptions.showGrid"
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
                    <TimelinePanel @openCompositionSettings="showCompositionSettingsDialog = true" @openPathSuggestion="showPathSuggestionDialog = true" />
                  </div>
                </Pane>
                <Pane :size="50" :min-size="20">
                  <div class="panel curve-editor-panel">
                    <CurveEditor @close="showCurveEditor = false" />
                  </div>
                </Pane>
              </Splitpanes>
              <div v-else class="panel timeline-panel">
                <TimelinePanel @openCompositionSettings="showCompositionSettingsDialog = true" @openPathSuggestion="showPathSuggestionDialog = true" />
              </div>
            </Pane>
          </Splitpanes>
        </Pane>

        <!-- Right Panel: Effects/Properties/Camera -->
        <Pane :size="24" :min-size="15" :max-size="35">
          <div class="panel right-panel">
            <div class="panel-tabs" role="tablist" aria-label="Right panel tabs">
              <button
                role="tab"
                :aria-selected="rightTab === 'properties'"
                aria-controls="right-panel-properties"
                :class="{ active: rightTab === 'properties' }"
                @click="rightTab = 'properties'"
              >
                Properties
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'effects'"
                aria-controls="right-panel-effects"
                :class="{ active: rightTab === 'effects' }"
                @click="rightTab = 'effects'"
              >
                Effects
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'camera'"
                aria-controls="right-panel-camera"
                :class="{ active: rightTab === 'camera' }"
                @click="rightTab = 'camera'"
              >
                Cam
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'audio'"
                aria-controls="right-panel-audio"
                :class="{ active: rightTab === 'audio' }"
                @click="rightTab = 'audio'"
              >
                Audio
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'export'"
                aria-controls="right-panel-export"
                :class="{ active: rightTab === 'export' }"
                @click="rightTab = 'export'"
              >
                Export
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'preview'"
                aria-controls="right-panel-preview"
                :class="{ active: rightTab === 'preview' }"
                @click="rightTab = 'preview'"
              >
                Preview
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'ai'"
                aria-controls="right-panel-ai"
                :class="{ active: rightTab === 'ai' }"
                @click="rightTab = 'ai'"
                title="AI Compositor Agent"
              >
                AI
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'generate'"
                aria-controls="right-panel-generate"
                :class="{ active: rightTab === 'generate' }"
                @click="rightTab = 'generate'"
                title="AI Generation (Depth, Normal, Segment)"
              >
                Gen
              </button>
              <button
                role="tab"
                :aria-selected="rightTab === 'align'"
                aria-controls="right-panel-align"
                :class="{ active: rightTab === 'align' }"
                @click="rightTab = 'align'"
                title="Align and Distribute Layers"
              >
                Align
              </button>
            </div>
            <div class="panel-content" role="tabpanel" :id="`right-panel-${rightTab}`">
              <EffectControlsPanel v-if="rightTab === 'effects'" />
              <PropertiesPanel v-else-if="rightTab === 'properties'" />
              <CameraProperties
                v-else-if="rightTab === 'camera'"
                :camera="activeCamera"
                @update:camera="updateCamera"
              />
              <AudioPanel v-else-if="rightTab === 'audio'" />
              <ExportPanel v-else-if="rightTab === 'export'" />
              <PreviewPanel v-else-if="rightTab === 'preview'" :engine="canvasEngine" />
              <AIChatPanel v-else-if="rightTab === 'ai'" />
              <AIGeneratePanel v-else-if="rightTab === 'generate'" />
              <AlignPanel v-else-if="rightTab === 'align'" />
            </div>
          </div>
        </Pane>
      </Splitpanes>
    </div>

    <!-- Status Bar removed - info relocated to toolbar and timeline -->

    <!-- Export Dialog -->
    <ExportDialog
      v-if="showExportDialog"
      @close="showExportDialog = false"
      @exported="onExportComplete"
    />

    <!-- ComfyUI Export Dialog -->
    <ComfyUIExportDialog
      v-if="showComfyUIExportDialog"
      :layers="store.layers"
      :camera-keyframes="activeCameraKeyframes"
      :current-frame="store.currentFrame"
      :total-frames="store.frameCount"
      @close="showComfyUIExportDialog = false"
      @exported="onComfyUIExportComplete"
    />

    <!-- Composition Settings Dialog -->
    <CompositionSettingsDialog
      :visible="showCompositionSettingsDialog"
      @close="showCompositionSettingsDialog = false"
      @confirm="onCompositionSettingsConfirm"
    />

    <!-- Pre-compose Dialog -->
    <PrecomposeDialog
      :visible="showPrecomposeDialog"
      :layer-count="store.selectedLayerIds.length"
      @close="showPrecomposeDialog = false"
      @confirm="onPrecomposeConfirm"
    />

    <!-- Keyframe Interpolation Dialog -->
    <KeyframeInterpolationDialog
      :visible="showKeyframeInterpolationDialog"
      :keyframe-count="store.selectedKeyframeIds.length"
      @close="showKeyframeInterpolationDialog = false"
      @confirm="onKeyframeInterpolationConfirm"
    />

    <!-- Time Stretch Dialog -->
    <TimeStretchDialog
      :visible="showTimeStretchDialog"
      :layer-id="store.selectedLayerIds[0] ?? ''"
      @close="showTimeStretchDialog = false"
      @applied="showTimeStretchDialog = false"
    />

    <!-- AI Path Suggestion Dialog -->
    <PathSuggestionDialog
      :visible="showPathSuggestionDialog"
      @close="onPathSuggestionClose"
      @accept="onPathSuggestionAccept"
      @preview="onPathSuggestionPreview"
    />

    <!-- HD Preview Window -->
    <HDPreviewWindow
      :visible="showHDPreview"
      :engine="canvasEngine"
      @close="showHDPreview = false"
    />

    <!-- Global Expression Editor -->
    <ExpressionInput
      :visible="expressionEditor.isVisible.value"
      :current-expression="expressionEditor.currentProperty.value?.expression"
      @close="expressionEditor.closeExpressionEditor()"
      @apply="expressionEditor.applyExpression($event)"
      @remove="expressionEditor.removeExpression()"
    />

    <!-- Path Preview Overlay (shown in viewport when suggestions exist) -->
    <Teleport to=".viewport-content" v-if="pathSuggestions.length > 0">
      <PathPreviewOverlay
        :width="compWidth"
        :height="compHeight"
        :suggestions="pathSuggestions"
        :selectedIndex="selectedPathIndex"
        @select="selectedPathIndex = $event"
      />
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, provide } from 'vue';
import { Splitpanes, Pane } from 'splitpanes';
import 'splitpanes/dist/splitpanes.css';

import { useCompositorStore } from '@/stores/compositorStore';
import { detectGPUTier, type GPUTier } from '@/services/gpuDetection';
import { createDefaultCamera, createDefaultViewportState } from '@/types/camera';
import type { Camera3D, ViewportState } from '@/types/camera';

// Panels
import ProjectPanel from '@/components/panels/ProjectPanel.vue';
import EffectsPanel from '@/components/panels/EffectsPanel.vue';
import EffectControlsPanel from '@/components/panels/EffectControlsPanel.vue';
import PropertiesPanel from '@/components/panels/PropertiesPanel.vue';
import CameraProperties from '@/components/panels/CameraProperties.vue';
import AudioPanel from '@/components/panels/AudioPanel.vue';
import AssetsPanel from '@/components/panels/AssetsPanel.vue';
import ExportPanel from '@/components/panels/ExportPanel.vue';
import PreviewPanel from '@/components/panels/PreviewPanel.vue';
import AIChatPanel from '@/components/panels/AIChatPanel.vue';
import AIGeneratePanel from '@/components/panels/AIGeneratePanel.vue';
import AlignPanel from '@/components/panels/AlignPanel.vue';

// Viewport
import ViewportRenderer from '@/components/viewport/ViewportRenderer.vue';
import ThreeCanvas from '@/components/canvas/ThreeCanvas.vue';

// Timeline
import TimelinePanel from '@/components/timeline/TimelinePanel.vue';
import CurveEditor from '@/components/curve-editor/CurveEditor.vue';

// Dialogs
import ExportDialog from '@/components/dialogs/ExportDialog.vue';
import ComfyUIExportDialog from '@/components/export/ComfyUIExportDialog.vue';
import CompositionSettingsDialog from '@/components/dialogs/CompositionSettingsDialog.vue';
import PrecomposeDialog from '@/components/dialogs/PrecomposeDialog.vue';
import PathSuggestionDialog from '@/components/dialogs/PathSuggestionDialog.vue';
import KeyframeInterpolationDialog from '@/components/dialogs/KeyframeInterpolationDialog.vue';
import TimeStretchDialog from '@/components/dialogs/TimeStretchDialog.vue';
import ExpressionInput from '@/components/properties/ExpressionInput.vue';
import { useExpressionEditor } from '@/composables/useExpressionEditor';

// Canvas overlays
import PathPreviewOverlay from '@/components/canvas/PathPreviewOverlay.vue';

// Preview
import HDPreviewWindow from '@/components/preview/HDPreviewWindow.vue';

// Common
import MemoryIndicator from '@/components/common/MemoryIndicator.vue';

// Stores
const store = useCompositorStore();
import { useAssetStore } from '@/stores/assetStore';
const assetStore = useAssetStore();
import { useAudioStore } from '@/stores/audioStore';
import { usePlaybackStore } from '@/stores/playbackStore';
const audioStore = useAudioStore();
const playbackStore = usePlaybackStore();

// Expression editor composable
const expressionEditor = useExpressionEditor();
import { useThemeStore, type ThemeName } from '@/stores/themeStore';
const themeStore = useThemeStore();

// Theme selector state
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

// Tool state - synced with store
const currentTool = computed({
  get: () => store.currentTool,
  set: (tool: 'select' | 'pen' | 'text' | 'hand' | 'zoom' | 'segment') => store.setTool(tool)
});

// Segmentation state - synced with store
const segmentMode = computed(() => store.segmentMode);
const segmentPendingMask = computed(() => store.segmentPendingMask);
const segmentIsLoading = computed(() => store.segmentIsLoading);

function setSegmentMode(mode: 'point' | 'box') {
  store.setSegmentMode(mode);
}

async function confirmSegmentMask() {
  await store.confirmSegmentMask();
}

function clearSegmentMask() {
  store.clearSegmentPendingMask();
}

const activeWorkspace = ref('standard');
const leftTab = ref<'project' | 'effects' | 'assets'>('project');
const rightTab = ref<'effects' | 'properties' | 'camera' | 'audio' | 'export' | 'preview' | 'ai' | 'generate'>('properties');
const viewportTab = ref<'composition' | 'layer' | 'footage'>('composition');

const viewZoom = ref('fit');
const showCurveEditor = ref(false);
const showExportDialog = ref(false);
const showComfyUIExportDialog = ref(false);
const showCompositionSettingsDialog = ref(false);
const showPrecomposeDialog = ref(false);
const showPathSuggestionDialog = ref(false);
const showKeyframeInterpolationDialog = ref(false);
const showHDPreview = ref(false);

// Vision authoring state
const pathSuggestions = ref<any[]>([]);
const selectedPathIndex = ref<number | null>(null);

const isPlaying = ref(false);
const gpuTier = ref<GPUTier['tier']>('cpu');

const threeCanvasRef = ref<InstanceType<typeof ThreeCanvas> | null>(null);

// Engine accessor for panels
const canvasEngine = computed(() => threeCanvasRef.value?.engine ?? null);

// Camera state - use computed to get from store, fallback to default
const activeCamera = computed<Camera3D>(() => {
  const cam = store.getActiveCameraAtFrame();
  if (cam) return cam;
  // Fallback to a default camera
  return createDefaultCamera('default', compWidth.value, compHeight.value);
});
const viewportState = ref<ViewportState>(createDefaultViewportState());
const viewOptions = ref({
  showGrid: false,
  showRulers: false,
  showAxes: true,
  showCameraFrustum: true,
  showCompositionBounds: true,
  showFocalPlane: false,
  showLayerOutlines: true,
  showSafeZones: false,
  gridSize: 100,
  gridDivisions: 10
});

// Grid overlay computed style
const gridOverlayStyle = computed(() => {
  const size = viewOptions.value.gridSize || 100;
  const divisions = viewOptions.value.gridDivisions || 10;
  const minorSize = size / divisions;

  // Create a repeating grid pattern using CSS
  return {
    position: 'absolute',
    top: 0,
    left: 0,
    right: 0,
    bottom: 0,
    pointerEvents: 'none',
    zIndex: 5,
    backgroundImage: `
      linear-gradient(to right, ${gridColor.value} 1px, transparent 1px),
      linear-gradient(to bottom, ${gridColor.value} 1px, transparent 1px),
      linear-gradient(to right, ${gridMajorColor.value} 1px, transparent 1px),
      linear-gradient(to bottom, ${gridMajorColor.value} 1px, transparent 1px)
    `,
    backgroundSize: `
      ${minorSize}px ${minorSize}px,
      ${minorSize}px ${minorSize}px,
      ${size}px ${size}px,
      ${size}px ${size}px
    `,
    opacity: 0.5
  };
});

// Guide styling - 11px hit area with 1px visible line centered
function getGuideStyle(guide: { id: string; orientation: 'horizontal' | 'vertical'; position: number }) {
  if (guide.orientation === 'horizontal') {
    return {
      position: 'absolute',
      left: 0,
      right: 0,
      top: `${guide.position - 5}px`,  // Center the 11px hit area on the guide position
      height: '11px',
      background: 'linear-gradient(to bottom, transparent 5px, #00BFFF 5px, #00BFFF 6px, transparent 6px)',
      cursor: 'ns-resize',
      zIndex: 10
    };
  } else {
    return {
      position: 'absolute',
      top: 0,
      bottom: 0,
      left: `${guide.position - 5}px`,  // Center the 11px hit area on the guide position
      width: '11px',
      background: 'linear-gradient(to right, transparent 5px, #00BFFF 5px, #00BFFF 6px, transparent 6px)',
      cursor: 'ew-resize',
      zIndex: 10
    };
  }
}

// Guide creation from rulers
function createGuideFromRuler(orientation: 'horizontal' | 'vertical', event: MouseEvent) {
  const rect = (event.currentTarget as HTMLElement).getBoundingClientRect();
  let position: number;

  if (orientation === 'horizontal') {
    position = event.clientY - rect.top;
  } else {
    position = event.clientX - rect.left;
  }

  addGuide(orientation, position);
}

// Guide dragging state
const draggingGuide = ref<{ id: string; orientation: 'horizontal' | 'vertical' } | null>(null);

function startGuideDrag(guide: { id: string; orientation: 'horizontal' | 'vertical'; position: number }, event: MouseEvent) {
  event.preventDefault();
  draggingGuide.value = { id: guide.id, orientation: guide.orientation };

  const handleMove = (e: MouseEvent) => {
    if (!draggingGuide.value) return;

    const viewportContent = document.querySelector('.viewport-content');
    if (!viewportContent) return;

    const rect = viewportContent.getBoundingClientRect();
    let newPosition: number;

    if (draggingGuide.value.orientation === 'horizontal') {
      newPosition = e.clientY - rect.top;
    } else {
      newPosition = e.clientX - rect.left;
    }

    // Remove guide if dragged off the viewport
    if (newPosition < 0 || newPosition > (draggingGuide.value.orientation === 'horizontal' ? rect.height : rect.width)) {
      removeGuide(draggingGuide.value.id);
      draggingGuide.value = null;
      window.removeEventListener('mousemove', handleMove);
      window.removeEventListener('mouseup', handleUp);
      return;
    }

    updateGuidePosition(draggingGuide.value.id, newPosition);
  };

  const handleUp = () => {
    draggingGuide.value = null;
    window.removeEventListener('mousemove', handleMove);
    window.removeEventListener('mouseup', handleUp);
  };

  window.addEventListener('mousemove', handleMove);
  window.addEventListener('mouseup', handleUp);
}

// Snap indicator state (for visual feedback)
const snapIndicatorX = ref<number | null>(null);
const snapIndicatorY = ref<number | null>(null);

// Composition dimensions
const compWidth = computed(() => store.project?.composition?.width || 1920);
const compHeight = computed(() => store.project?.composition?.height || 1080);

// Performance tracking
const fps = ref(60);
const memoryUsage = ref('0 MB');
const renderProgress = ref(0);

// Computed
const formattedTimecode = computed(() => {
  const frame = store.currentFrame;
  const fpsVal = store.project?.composition?.fps || 30;
  const totalSeconds = frame / fpsVal;
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = Math.floor(totalSeconds % 60);
  const frames = frame % fpsVal;
  return `${String(minutes).padStart(2, '0')}:${String(seconds).padStart(2, '0')}:${String(frames).padStart(2, '0')}`;
});

const projectName = computed(() => {
  return store.project?.meta?.name || 'Untitled Project';
});

const compositionInfo = computed(() => {
  const comp = store.project?.composition;
  if (!comp) return 'No Composition';
  return `${comp.width}×${comp.height} @ ${comp.fps}fps`;
});

const canUndo = computed(() => store.canUndo);
const canRedo = computed(() => store.canRedo);

// Actions
function togglePlay() {
  isPlaying.value = !isPlaying.value;
  if (isPlaying.value) {
    store.play();
  } else {
    store.pause();
  }
}

function goToStart() {
  store.goToStart();
}

function goToEnd() {
  store.goToEnd();
}

function stepForward(frames: number = 1) {
  store.setFrame(Math.min(store.currentFrame + frames, store.frameCount - 1));
}

function stepBackward(frames: number = 1) {
  store.setFrame(Math.max(0, store.currentFrame - frames));
}

// Apply smooth easing (F9) to all keyframes on selected layers
function applySmoothEasing() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  let keyframesUpdated = 0;

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer?.transform) continue;

    // Apply to all transform properties
    const transform = layer.transform as any;
    for (const propKey of ['position', 'scale', 'rotation', 'anchor', 'opacity']) {
      const prop = transform[propKey];
      if (prop?.animated && prop?.keyframes) {
        for (const kf of prop.keyframes) {
          // Set to bezier interpolation with default easing handles
          store.setKeyframeInterpolation(layerId, `transform.${propKey}`, kf.id, 'bezier');
          keyframesUpdated++;
        }
      }
    }

    // Also apply to opacity if it's at layer level
    if (layer.opacity?.animated && layer.opacity?.keyframes) {
      for (const kf of layer.opacity.keyframes) {
        store.setKeyframeInterpolation(layerId, 'opacity', kf.id, 'bezier');
        keyframesUpdated++;
      }
    }
  }

  if (keyframesUpdated > 0) {
    console.log(`[Weyl] Applied smooth easing to ${keyframesUpdated} keyframes`);
  }
}

// Keyframe navigation - find nearest keyframe across all animated properties of selected layer(s)
function goToPrevKeyframe() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  let prevFrame = -1;
  const currentFrame = store.currentFrame;

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer?.transform) continue;

    // Check all transform properties
    const transform = layer.transform as any;
    for (const propKey of ['position', 'scale', 'rotation', 'anchor', 'opacity']) {
      const prop = transform[propKey];
      if (prop?.animated && prop?.keyframes) {
        for (const kf of prop.keyframes) {
          if (kf.frame < currentFrame && kf.frame > prevFrame) {
            prevFrame = kf.frame;
          }
        }
      }
    }
  }

  if (prevFrame >= 0) {
    store.setFrame(prevFrame);
  }
}

function goToNextKeyframe() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  let nextFrame = Infinity;
  const currentFrame = store.currentFrame;

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer?.transform) continue;

    // Check all transform properties
    const transform = layer.transform as any;
    for (const propKey of ['position', 'scale', 'rotation', 'anchor', 'opacity']) {
      const prop = transform[propKey];
      if (prop?.animated && prop?.keyframes) {
        for (const kf of prop.keyframes) {
          if (kf.frame > currentFrame && kf.frame < nextFrame) {
            nextFrame = kf.frame;
          }
        }
      }
    }
  }

  if (nextFrame < Infinity) {
    store.setFrame(nextFrame);
  }
}

// Property solo state - tracks which properties are currently soloed (P, S, R, T, A, U shortcuts)
// Use a Set to support additive reveals with Shift+letter
type SoloPropertyType = 'position' | 'scale' | 'rotation' | 'opacity' | 'anchor' | 'animated' | 'modified' | 'expressions' | 'effects' | 'masks';
const soloedProperties = ref<Set<SoloPropertyType>>(new Set());

function soloProperty(prop: SoloPropertyType, additive: boolean = false) {
  if (additive) {
    // Shift+letter: Add to current reveals
    if (soloedProperties.value.has(prop)) {
      soloedProperties.value.delete(prop);
    } else {
      soloedProperties.value.add(prop);
    }
    // Force reactivity update
    soloedProperties.value = new Set(soloedProperties.value);
  } else {
    // Solo mode: Toggle single property (replace current)
    if (soloedProperties.value.size === 1 && soloedProperties.value.has(prop)) {
      soloedProperties.value = new Set();
    } else {
      soloedProperties.value = new Set([prop]);
    }
  }
}

// Backward compatibility: single soloed property (first in set)
const soloedProperty = computed(() => {
  const arr = Array.from(soloedProperties.value);
  return arr.length > 0 ? arr[0] : null;
});

// Provide soloedProperty to child components
provide('soloedProperty', soloedProperty);
provide('soloedProperties', soloedProperties);

// ========================================================================
// DOUBLE-TAP DETECTION SYSTEM
// For UU, EE, MM shortcuts that require pressing the key twice quickly
// ========================================================================
const lastKeyPress = ref<{ key: string; time: number } | null>(null);
const DOUBLE_TAP_THRESHOLD = 300; // milliseconds

function isDoubleTap(key: string): boolean {
  const now = Date.now();
  const last = lastKeyPress.value;

  // Update last key press
  lastKeyPress.value = { key, time: now };

  // Check if this is a double-tap of the same key
  if (last && last.key === key && (now - last.time) < DOUBLE_TAP_THRESHOLD) {
    // Reset to prevent triple-tap triggering
    lastKeyPress.value = null;
    return true;
  }

  return false;
}

// ========================================================================
// WORK AREA STATE (B/N shortcuts)
// ========================================================================
const workAreaStart = ref<number | null>(null);
const workAreaEnd = ref<number | null>(null);

function setWorkAreaStart() {
  workAreaStart.value = store.currentFrame;
  // Sync to playbackStore
  playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
  console.log(`[Weyl] Work area start set to frame ${store.currentFrame}`);
}

function setWorkAreaEnd() {
  workAreaEnd.value = store.currentFrame;
  // Sync to playbackStore
  playbackStore.setWorkArea(workAreaStart.value, workAreaEnd.value);
  console.log(`[Weyl] Work area end set to frame ${store.currentFrame}`);
}

function clearWorkArea() {
  workAreaStart.value = null;
  workAreaEnd.value = null;
  // Sync to playbackStore
  playbackStore.clearWorkArea();
  console.log('[Weyl] Work area cleared');
}

// Provide work area state to timeline
provide('workAreaStart', workAreaStart);
provide('workAreaEnd', workAreaEnd);

// ========================================================================
// HIDDEN LAYERS SYSTEM (renamed from "Shy" for trade dress safety)
// ========================================================================
const showHiddenLayers = ref(true); // Master toggle - when false, hidden layers are not shown in timeline

function toggleHiddenLayersVisibility() {
  showHiddenLayers.value = !showHiddenLayers.value;
  console.log(`[Weyl] Hidden layers visibility: ${showHiddenLayers.value ? 'shown' : 'hidden'}`);
}

function toggleLayerHidden(layerId: string) {
  const layer = store.getLayerById(layerId);
  if (layer) {
    store.updateLayer(layerId, { hidden: !layer.hidden });
  }
}

// Provide hidden layers state
provide('showHiddenLayers', showHiddenLayers);
provide('toggleLayerHidden', toggleLayerHidden);

// ========================================================================
// PREVIEW PAUSE STATE (Caps Lock feature)
// ========================================================================
const previewUpdatesPaused = ref(false);

function togglePreviewPause() {
  previewUpdatesPaused.value = !previewUpdatesPaused.value;
  console.log(`[Weyl] Preview updates: ${previewUpdatesPaused.value ? 'PAUSED' : 'active'}`);
}

provide('previewUpdatesPaused', previewUpdatesPaused);

// ========================================================================
// TRANSPARENCY GRID
// ========================================================================
const showTransparencyGrid = ref(false);

function toggleTransparencyGrid() {
  showTransparencyGrid.value = !showTransparencyGrid.value;
  console.log(`[Weyl] Transparency grid: ${showTransparencyGrid.value ? 'ON' : 'OFF'}`);
}

provide('showTransparencyGrid', showTransparencyGrid);

// ========================================================================
// GRID OVERLAY SYSTEM (Ctrl+')
// Uses viewOptions.showGrid which is defined later in the script
// ========================================================================
const gridColor = ref('#444444');
const gridMajorColor = ref('#666666');

function toggleGrid() {
  viewOptions.value.showGrid = !viewOptions.value.showGrid;
  console.log(`[Weyl] Grid: ${viewOptions.value.showGrid ? 'ON' : 'OFF'}`);
}

function setGridSize(size: number) {
  viewOptions.value.gridSize = Math.max(10, Math.min(200, size));
}

// Provide grid state to canvas components (will use viewOptions)
provide('gridColor', gridColor);
provide('gridMajorColor', gridMajorColor);

// ========================================================================
// RULERS OVERLAY SYSTEM (Ctrl+R)
// Uses viewOptions.showRulers which is defined later in the script
// ========================================================================
const rulerUnits = ref<'pixels' | 'percent'>('pixels');

function toggleRulers() {
  viewOptions.value.showRulers = !viewOptions.value.showRulers;
  console.log(`[Weyl] Rulers: ${viewOptions.value.showRulers ? 'ON' : 'OFF'}`);
}

// Provide rulers state
provide('rulerUnits', rulerUnits);

// ========================================================================
// GUIDES SYSTEM
// Guides are draggable lines from rulers
// ========================================================================
const guides = ref<Array<{ id: string; orientation: 'horizontal' | 'vertical'; position: number }>>([]);

function addGuide(orientation: 'horizontal' | 'vertical', position: number) {
  const id = `guide-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  guides.value.push({ id, orientation, position });
  console.log(`[Weyl] Added ${orientation} guide at ${position}px`);
}

function removeGuide(id: string) {
  guides.value = guides.value.filter(g => g.id !== id);
}

function clearGuides() {
  guides.value = [];
  console.log('[Weyl] Cleared all guides');
}

// Guide context menu state
const guideContextMenu = ref<{ visible: boolean; x: number; y: number; guideId: string | null }>({
  visible: false,
  x: 0,
  y: 0,
  guideId: null
});

function showGuideContextMenu(guide: { id: string; orientation: 'horizontal' | 'vertical'; position: number }, event: MouseEvent) {
  guideContextMenu.value = {
    visible: true,
    x: event.clientX,
    y: event.clientY,
    guideId: guide.id
  };
  // Close menu on next click anywhere
  setTimeout(() => {
    document.addEventListener('click', hideGuideContextMenu, { once: true });
  }, 0);
}

function hideGuideContextMenu() {
  guideContextMenu.value.visible = false;
  guideContextMenu.value.guideId = null;
}

function deleteGuideFromMenu() {
  if (guideContextMenu.value.guideId) {
    removeGuide(guideContextMenu.value.guideId);
  }
  hideGuideContextMenu();
}

function clearAllGuides() {
  clearGuides();
  hideGuideContextMenu();
}

function updateGuidePosition(id: string, position: number) {
  const guide = guides.value.find(g => g.id === id);
  if (guide) {
    guide.position = position;
  }
}

// Provide guides state
provide('guides', guides);
provide('addGuide', addGuide);
provide('removeGuide', removeGuide);
provide('clearGuides', clearGuides);
provide('updateGuidePosition', updateGuidePosition);

// ========================================================================
// SNAP SYSTEM
// ========================================================================
const snapEnabled = ref(false);
const snapToGrid = ref(true);
const snapToGuides = ref(true);
const snapToLayers = ref(true);
const snapTolerance = ref(10); // pixels

function toggleSnap() {
  snapEnabled.value = !snapEnabled.value;
  console.log(`[Weyl] Snap: ${snapEnabled.value ? 'ON' : 'OFF'}`);
}

function getSnapPoint(x: number, y: number): { x: number; y: number; snappedX: boolean; snappedY: boolean } {
  if (!snapEnabled.value) {
    return { x, y, snappedX: false, snappedY: false };
  }

  let snappedX = false;
  let snappedY = false;
  let resultX = x;
  let resultY = y;

  // Snap to grid (uses viewOptions.showGrid and viewOptions.gridSize)
  if (snapToGrid.value && viewOptions.value.showGrid) {
    const currentGridSize = viewOptions.value.gridSize || 50;
    const gridX = Math.round(x / currentGridSize) * currentGridSize;
    const gridY = Math.round(y / currentGridSize) * currentGridSize;

    if (Math.abs(x - gridX) < snapTolerance.value) {
      resultX = gridX;
      snappedX = true;
    }
    if (Math.abs(y - gridY) < snapTolerance.value) {
      resultY = gridY;
      snappedY = true;
    }
  }

  // Snap to guides
  if (snapToGuides.value) {
    for (const guide of guides.value) {
      if (guide.orientation === 'vertical' && Math.abs(x - guide.position) < snapTolerance.value) {
        resultX = guide.position;
        snappedX = true;
      }
      if (guide.orientation === 'horizontal' && Math.abs(y - guide.position) < snapTolerance.value) {
        resultY = guide.position;
        snappedY = true;
      }
    }
  }

  // Snap to composition edges and center
  const compCenterX = compWidth.value / 2;
  const compCenterY = compHeight.value / 2;

  if (Math.abs(x - compCenterX) < snapTolerance.value) {
    resultX = compCenterX;
    snappedX = true;
  }
  if (Math.abs(y - compCenterY) < snapTolerance.value) {
    resultY = compCenterY;
    snappedY = true;
  }
  if (Math.abs(x) < snapTolerance.value) {
    resultX = 0;
    snappedX = true;
  }
  if (Math.abs(y) < snapTolerance.value) {
    resultY = 0;
    snappedY = true;
  }
  if (Math.abs(x - compWidth.value) < snapTolerance.value) {
    resultX = compWidth.value;
    snappedX = true;
  }
  if (Math.abs(y - compHeight.value) < snapTolerance.value) {
    resultY = compHeight.value;
    snappedY = true;
  }

  return { x: resultX, y: resultY, snappedX, snappedY };
}

// Provide snap state and function
provide('snapEnabled', snapEnabled);
provide('snapToGrid', snapToGrid);
provide('snapToGuides', snapToGuides);
provide('snapToLayers', snapToLayers);
provide('snapTolerance', snapTolerance);
provide('getSnapPoint', getSnapPoint);
provide('toggleSnap', toggleSnap);

function undo() {
  store.undo();
}

function redo() {
  store.redo();
}

function updateCamera(camera: Camera3D) {
  // Update the camera in the store
  if (store.activeCameraId) {
    store.updateCamera(camera.id, camera);
  }
}

// Play a notification chime when export completes
function playExportChime() {
  try {
    const audioCtx = new (window.AudioContext || (window as any).webkitAudioContext)();
    const gainNode = audioCtx.createGain();
    gainNode.connect(audioCtx.destination);
    gainNode.gain.setValueAtTime(0.3, audioCtx.currentTime);
    gainNode.gain.exponentialRampToValueAtTime(0.01, audioCtx.currentTime + 0.5);

    // Two-tone chime (pleasant major third)
    const freqs = [523.25, 659.25]; // C5, E5
    freqs.forEach((freq, i) => {
      const osc = audioCtx.createOscillator();
      osc.type = 'sine';
      osc.frequency.setValueAtTime(freq, audioCtx.currentTime + i * 0.1);
      osc.connect(gainNode);
      osc.start(audioCtx.currentTime + i * 0.1);
      osc.stop(audioCtx.currentTime + 0.5 + i * 0.1);
    });
  } catch (e) {
    // Silently fail if audio not available
    console.warn('[Weyl] Audio notification not available:', e);
  }
}

function onExportComplete() {
  console.log('[Weyl] Matte export completed');
  playExportChime();
}

function onComfyUIExportComplete(result: any) {
  console.log('[Weyl] ComfyUI export completed', result);
  showComfyUIExportDialog.value = false;
  playExportChime();
}

function onCompositionSettingsConfirm(settings: {
  name: string;
  width: number;
  height: number;
  fps: number;
  frameCount: number;
  backgroundColor: string;
  autoResizeToContent: boolean;
}) {
  console.log('[Weyl] Composition settings updated:', settings);

  // Update active composition's settings
  store.updateCompositionSettings(store.activeCompositionId, {
    width: settings.width,
    height: settings.height,
    fps: settings.fps,
    frameCount: settings.frameCount,
    backgroundColor: settings.backgroundColor,
    autoResizeToContent: settings.autoResizeToContent
  });

  // Rename the composition
  store.renameComposition(store.activeCompositionId, settings.name);

  showCompositionSettingsDialog.value = false;
}

function onPrecomposeConfirm(name: string) {
  if (store.selectedLayerIds.length > 0) {
    store.nestSelectedLayers(name);
    showPrecomposeDialog.value = false;
  }
}

// Keyframe interpolation dialog handler
function onKeyframeInterpolationConfirm(settings: {
  interpolation: 'linear' | 'bezier' | 'hold';
  easingPreset: string;
  controlMode: 'symmetric' | 'smooth' | 'corner';
}) {
  const selectedKeyframeIds = store.selectedKeyframeIds;
  if (selectedKeyframeIds.length === 0) return;

  // Get the layers that contain these keyframes
  const layers = store.layers;
  for (const layer of layers) {
    const transform = layer.transform as any;
    if (!transform) continue;

    // Check all animatable properties for keyframes
    const props = ['position', 'rotation', 'scale', 'anchor', 'opacity'];
    for (const propName of props) {
      const prop = transform[propName];
      if (!prop?.keyframes) continue;

      for (const kf of prop.keyframes) {
        if (selectedKeyframeIds.includes(kf.id)) {
          // Update interpolation
          kf.interpolation = settings.interpolation;
          kf.controlMode = settings.controlMode;

          // For bezier, set easing preset handles
          if (settings.interpolation === 'bezier' && settings.easingPreset) {
            // Apply preset handle positions based on easing type
            const presetHandles = getEasingPresetHandles(settings.easingPreset);
            if (presetHandles) {
              kf.outHandle = { x: presetHandles.outX, y: presetHandles.outY };
              kf.inHandle = { x: presetHandles.inX, y: presetHandles.inY };
            }
          }
        }
      }
    }
  }

  // Mark dirty and log
  console.log(`[Weyl] Applied ${settings.interpolation} interpolation to ${selectedKeyframeIds.length} keyframes`);
  showKeyframeInterpolationDialog.value = false;
}

// Get bezier handle positions for easing presets
function getEasingPresetHandles(preset: string): { outX: number; outY: number; inX: number; inY: number } | null {
  // Standard easing preset handle positions
  const presets: Record<string, { outX: number; outY: number; inX: number; inY: number }> = {
    // Ease In
    'easeInSine': { outX: 0.47, outY: 0, inX: 0.745, inY: 0.715 },
    'easeInQuad': { outX: 0.55, outY: 0.085, inX: 0.68, inY: 0.53 },
    'easeInCubic': { outX: 0.55, outY: 0.055, inX: 0.675, inY: 0.19 },
    'easeInQuart': { outX: 0.895, outY: 0.03, inX: 0.685, inY: 0.22 },
    'easeInQuint': { outX: 0.755, outY: 0.05, inX: 0.855, inY: 0.06 },
    'easeInExpo': { outX: 0.95, outY: 0.05, inX: 0.795, inY: 0.035 },
    'easeInCirc': { outX: 0.6, outY: 0.04, inX: 0.98, inY: 0.335 },
    'easeInBack': { outX: 0.6, outY: -0.28, inX: 0.735, inY: 0.045 },
    'easeInElastic': { outX: 0.5, outY: -0.5, inX: 0.7, inY: 0 },

    // Ease Out
    'easeOutSine': { outX: 0.39, outY: 0.575, inX: 0.565, inY: 1 },
    'easeOutQuad': { outX: 0.25, outY: 0.46, inX: 0.45, inY: 0.94 },
    'easeOutCubic': { outX: 0.215, outY: 0.61, inX: 0.355, inY: 1 },
    'easeOutQuart': { outX: 0.165, outY: 0.84, inX: 0.44, inY: 1 },
    'easeOutQuint': { outX: 0.23, outY: 1, inX: 0.32, inY: 1 },
    'easeOutExpo': { outX: 0.19, outY: 1, inX: 0.22, inY: 1 },
    'easeOutCirc': { outX: 0.075, outY: 0.82, inX: 0.165, inY: 1 },
    'easeOutBack': { outX: 0.175, outY: 0.885, inX: 0.32, inY: 1.275 },
    'easeOutElastic': { outX: 0.3, outY: 1, inX: 0.5, inY: 1.5 },
    'easeOutBounce': { outX: 0.2, outY: 0.9, inX: 0.3, inY: 1 },

    // Ease In/Out
    'easeInOutSine': { outX: 0.445, outY: 0.05, inX: 0.55, inY: 0.95 },
    'easeInOutQuad': { outX: 0.455, outY: 0.03, inX: 0.515, inY: 0.955 },
    'easeInOutCubic': { outX: 0.645, outY: 0.045, inX: 0.355, inY: 1 },
    'easeInOutQuart': { outX: 0.77, outY: 0, inX: 0.175, inY: 1 },
    'easeInOutQuint': { outX: 0.86, outY: 0, inX: 0.07, inY: 1 },
    'easeInOutExpo': { outX: 1, outY: 0, inX: 0, inY: 1 },
    'easeInOutCirc': { outX: 0.785, outY: 0.135, inX: 0.15, inY: 0.86 },
    'easeInOutBack': { outX: 0.68, outY: -0.55, inX: 0.265, inY: 1.55 },
    'easeInOutElastic': { outX: 0.5, outY: -0.3, inX: 0.5, inY: 1.3 },
  };

  return presets[preset] || null;
}

// Helper: Generate SVG path data from control points (for audio reactivity integration)
function generatePathDataFromPoints(
  points: Array<{ x: number; y: number; handleIn?: { x: number; y: number } | null; handleOut?: { x: number; y: number } | null }>,
  closed: boolean
): string {
  if (points.length === 0) return '';
  if (points.length === 1) return `M ${points[0].x} ${points[0].y}`;

  let d = `M ${points[0].x} ${points[0].y}`;

  for (let i = 0; i < points.length - 1; i++) {
    const p0 = points[i];
    const p1 = points[i + 1];

    // If both points have handles, use cubic bezier
    if (p0.handleOut && p1.handleIn) {
      const cp1x = p0.x + p0.handleOut.x;
      const cp1y = p0.y + p0.handleOut.y;
      const cp2x = p1.x + p1.handleIn.x;
      const cp2y = p1.y + p1.handleIn.y;
      d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p1.x} ${p1.y}`;
    } else if (p0.handleOut) {
      // Quadratic with control point from handleOut
      const cpx = p0.x + p0.handleOut.x;
      const cpy = p0.y + p0.handleOut.y;
      d += ` Q ${cpx} ${cpy}, ${p1.x} ${p1.y}`;
    } else if (p1.handleIn) {
      // Quadratic with control point from handleIn
      const cpx = p1.x + p1.handleIn.x;
      const cpy = p1.y + p1.handleIn.y;
      d += ` Q ${cpx} ${cpy}, ${p1.x} ${p1.y}`;
    } else {
      // Simple line
      d += ` L ${p1.x} ${p1.y}`;
    }
  }

  if (closed && points.length > 2) {
    d += ' Z';
  }

  return d;
}

// Path Suggestion handlers
function onPathSuggestionClose() {
  showPathSuggestionDialog.value = false;
  // Clear preview when dialog closes
  pathSuggestions.value = [];
  selectedPathIndex.value = null;
}

function onPathSuggestionPreview(suggestions: any[]) {
  pathSuggestions.value = suggestions;
  selectedPathIndex.value = suggestions.length > 0 ? 0 : null;
}

function onPathSuggestionAccept(result: { keyframes: any[]; splines: any[] }) {
  console.log('[Weyl] Path suggestion accepted:', result);

  // Apply keyframes to the store
  if (result.keyframes && result.keyframes.length > 0) {
    for (const batch of result.keyframes) {
      // batch contains layerId, propertyPath, and keyframes
      // Add keyframes to the appropriate layer/property
      for (const keyframe of batch.keyframes) {
        store.addKeyframe(batch.layerId, batch.propertyPath, keyframe.frame, keyframe.value, keyframe.easing);
      }
    }
  }

  // Create new spline layers if suggested
  if (result.splines && result.splines.length > 0) {
    for (const spline of result.splines) {
      // Create a new spline layer
      const layer = store.createSplineLayer();

      // Rename if name provided
      if (spline.name) {
        store.renameLayer(layer.id, spline.name);
      }

      // Convert points to control points format (preserve depth and handles from translator)
      const controlPoints = (spline.points || []).map((p: any, i: number) => ({
        id: p.id || `cp_${Date.now()}_${i}`,
        x: p.x,
        y: p.y,
        depth: p.depth ?? 0,  // Preserve z-space depth
        handleIn: p.handleIn || null,  // Preserve bezier handles from translator
        handleOut: p.handleOut || null,
        type: p.type || 'smooth' as const
      }));

      // Generate SVG path data from control points for audio reactivity
      const pathData = generatePathDataFromPoints(controlPoints, spline.closed || false);

      // Update the layer data with the points and pathData
      store.updateLayerData(layer.id, {
        controlPoints,
        pathData,
        closed: spline.closed || false
      });
    }
  }

  // Clear preview
  pathSuggestions.value = [];
  selectedPathIndex.value = null;
  showPathSuggestionDialog.value = false;
}

// Get camera keyframes for the active camera
const activeCameraKeyframes = computed(() => {
  const activeCam = store.getActiveCameraAtFrame();
  if (!activeCam) return [];
  return store.getCameraKeyframes(activeCam.id);
});

// Handle zoom dropdown change
function handleZoomChange() {
  if (!threeCanvasRef.value) return;

  if (viewZoom.value === 'fit') {
    threeCanvasRef.value.fitToView();
  } else {
    // Convert percentage string to decimal (e.g., '100' → 1.0, '200' → 2.0)
    const zoomLevel = parseInt(viewZoom.value) / 100;
    threeCanvasRef.value.setZoom(zoomLevel);
  }
}

// ========================================================================
// ASSETS PANEL HANDLERS
// ========================================================================

/**
 * Create layers from imported SVG paths
 */
function onCreateLayersFromSvg(svgId: string) {
  const storedSvg = assetStore.svgDocuments.get(svgId);
  if (!storedSvg) return;

  // Create a model layer for each path in the SVG
  storedSvg.document.paths.forEach((path, index) => {
    const config = storedSvg.layerConfigs[index];

    // Create a 3D model layer
    // Note: This would ideally create a proper ModelLayer with the extruded geometry
    // For now, we'll create a shape layer with the path data
    const layer = store.createShapeLayer();
    store.renameLayer(layer.id, `${storedSvg.name}_${path.id}`);

    // Store the SVG path reference in the layer data
    store.updateLayerData(layer.id, {
      svgDocumentId: svgId,
      svgPathId: path.id,
      svgPathIndex: index,
      extrusionConfig: config,
      // Set Z position based on layer depth
      transform: {
        ...layer.transform,
        position: {
          ...layer.transform.position,
          value: {
            ...layer.transform.position.value,
            z: config?.depth || 0
          }
        }
      }
    });
  });

  console.log(`[Weyl] Created ${storedSvg.document.paths.length} layers from SVG: ${storedSvg.name}`);
}

/**
 * Configure a particle emitter to use a mesh shape
 */
function onUseMeshAsEmitter(meshId: string) {
  const emitterConfig = assetStore.getMeshEmitterConfig(meshId);
  if (!emitterConfig) return;

  // Get the selected layer if it's a particle layer
  const selectedLayerIds = store.selectedLayerIds;
  if (selectedLayerIds.length === 0) {
    console.warn('[Weyl] No layer selected for mesh emitter');
    return;
  }

  const layer = store.layers.find(l => l.id === selectedLayerIds[0]);
  if (!layer || layer.type !== 'particle') {
    console.warn('[Weyl] Selected layer is not a particle layer');
    return;
  }

  // Update the particle layer's emitter config with mesh vertices
  store.updateLayerData(layer.id, {
    emitter: {
      ...(layer.data as any).emitter,
      shape: 'mesh',
      meshVertices: emitterConfig.meshVertices,
      meshNormals: emitterConfig.meshNormals,
    }
  });

  console.log(`[Weyl] Set mesh emitter for layer: ${layer.name}`);
}

/**
 * Update environment settings in the engine
 */
function onEnvironmentUpdate(settings: any) {
  if (!threeCanvasRef.value) return;
  const engine = threeCanvasRef.value.getEngine?.();
  if (!engine) return;

  engine.setEnvironmentConfig(settings);
}

/**
 * Load environment map into the engine
 */
async function onEnvironmentLoad(settings: any) {
  if (!threeCanvasRef.value) return;
  const engine = threeCanvasRef.value.getEngine?.();
  if (!engine) return;

  if (settings.url) {
    try {
      await engine.loadEnvironmentMap(settings.url, {
        intensity: settings.intensity,
        rotation: settings.rotation,
        backgroundBlur: settings.backgroundBlur,
        useAsBackground: settings.useAsBackground,
      });
      console.log('[Weyl] Environment map loaded');
    } catch (error) {
      console.error('[Weyl] Failed to load environment map:', error);
    }
  }
}

/**
 * Clear environment map from the engine
 */
function onEnvironmentClear() {
  if (!threeCanvasRef.value) return;
  const engine = threeCanvasRef.value.getEngine?.();
  if (!engine) return;

  engine.setEnvironmentEnabled(false);
}

// Navigate to selected layer's in/out point
function goToLayerInPoint() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;
  const layer = store.getLayerById(selectedIds[0]);
  if (layer) {
    store.setFrame(layer.inPoint ?? 0);
  }
}

function goToLayerOutPoint() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;
  const layer = store.getLayerById(selectedIds[0]);
  if (layer) {
    store.setFrame((layer.outPoint ?? store.frameCount) - 1);
  }
}

// Move layer in/out point to current frame
function moveLayerInPointToPlayhead() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;
  for (const id of selectedIds) {
    store.updateLayer(id, { inPoint: store.currentFrame });
  }
}

function moveLayerOutPointToPlayhead() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;
  for (const id of selectedIds) {
    store.updateLayer(id, { outPoint: store.currentFrame + 1 });
  }
}

// Trim layer in/out point to current frame (Alt+[ Alt+])
function trimLayerInPoint() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;
  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (layer) {
      // Only trim if current frame is after current in point
      const currentIn = layer.inPoint ?? 0;
      if (store.currentFrame > currentIn) {
        store.updateLayer(id, { inPoint: store.currentFrame });
      }
    }
  }
}

function trimLayerOutPoint() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;
  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (layer) {
      // Only trim if current frame is before current out point
      const currentOut = layer.outPoint ?? store.frameCount;
      if (store.currentFrame < currentOut) {
        store.updateLayer(id, { outPoint: store.currentFrame + 1 });
      }
    }
  }
}

// Select previous/next layer (Ctrl+Arrow)
function selectPreviousLayer(extend: boolean = false) {
  const layers = store.layers;
  if (layers.length === 0) return;

  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) {
    // Select first layer
    store.selectLayer(layers[0].id);
    return;
  }

  // Find current layer index (use first selected for navigation anchor)
  const currentIndex = layers.findIndex(l => l.id === selectedIds[0]);
  if (currentIndex > 0) {
    const targetLayer = layers[currentIndex - 1];
    if (extend) {
      // Add to selection (Shift+Ctrl+Up)
      store.selectLayer(targetLayer.id, true);
    } else {
      store.selectLayer(targetLayer.id);
    }
  }
}

function selectNextLayer(extend: boolean = false) {
  const layers = store.layers;
  if (layers.length === 0) return;

  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) {
    // Select first layer
    store.selectLayer(layers[0].id);
    return;
  }

  // Find current layer index (use last selected for navigation anchor)
  const lastSelectedIndex = layers.findIndex(l => l.id === selectedIds[selectedIds.length - 1]);
  if (lastSelectedIndex < layers.length - 1) {
    const targetLayer = layers[lastSelectedIndex + 1];
    if (extend) {
      // Add to selection (Shift+Ctrl+Down)
      store.selectLayer(targetLayer.id, true);
    } else {
      store.selectLayer(targetLayer.id);
    }
  }
}

// Split layer at current frame (Ctrl+Shift+D)
function splitLayerAtPlayhead() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (!layer) continue;

    const currentFrame = store.currentFrame;
    const inPoint = layer.inPoint ?? 0;
    const outPoint = layer.outPoint ?? store.frameCount;

    // Only split if playhead is within layer bounds
    if (currentFrame > inPoint && currentFrame < outPoint) {
      // Trim current layer to end at playhead
      store.updateLayer(id, { outPoint: currentFrame });

      // Duplicate layer and set it to start at playhead
      const newLayer = store.duplicateLayer(id);
      if (newLayer) {
        store.updateLayer(newLayer.id, {
          inPoint: currentFrame,
          outPoint: outPoint
        });
        store.renameLayer(newLayer.id, `${layer.name} (split)`);
      }
    }
  }
}

// Reverse selected layers (Ctrl+Alt+R)
function reverseSelectedLayers() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const id of selectedIds) {
    store.reverseLayer(id);
  }
}

// Freeze frame at playhead (Ctrl+Shift+F)
function freezeFrameSelectedLayers() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const id of selectedIds) {
    store.freezeFrameAtPlayhead(id);
  }
}

// Time stretch dialog state
const showTimeStretchDialog = ref(false);

// Open time stretch dialog (Ctrl+Alt+T)
function openTimeStretchDialog() {
  if (store.selectedLayerIds.length === 0) return;
  showTimeStretchDialog.value = true;
}

// Timeline zoom level
const timelineZoom = ref(1);

function zoomTimelineIn() {
  timelineZoom.value = Math.min(timelineZoom.value * 1.5, 10);
  store.setTimelineZoom?.(timelineZoom.value);
}

function zoomTimelineOut() {
  timelineZoom.value = Math.max(timelineZoom.value / 1.5, 0.1);
  store.setTimelineZoom?.(timelineZoom.value);
}

function zoomTimelineToFit() {
  timelineZoom.value = 1;
  store.setTimelineZoom?.(1);
}

// ========================================================================
// VIEWER ZOOM CONTROLS
// Using different keys from AE for trade dress safety:
// Instead of . , / we use Ctrl+= Ctrl+- Ctrl+0
// ========================================================================
const viewerZoom = ref(1);

function zoomViewerIn() {
  viewerZoom.value = Math.min(viewerZoom.value * 1.25, 8);
  if (threeCanvasRef.value) {
    threeCanvasRef.value.setZoom?.(viewerZoom.value);
  }
  // Update the viewZoom dropdown
  const percent = Math.round(viewerZoom.value * 100);
  viewZoom.value = String(percent);
}

function zoomViewerOut() {
  viewerZoom.value = Math.max(viewerZoom.value / 1.25, 0.1);
  if (threeCanvasRef.value) {
    threeCanvasRef.value.setZoom?.(viewerZoom.value);
  }
  // Update the viewZoom dropdown
  const percent = Math.round(viewerZoom.value * 100);
  viewZoom.value = String(percent);
}

function zoomViewerToFit() {
  viewerZoom.value = 1;
  viewZoom.value = 'fit';
  if (threeCanvasRef.value) {
    threeCanvasRef.value.fitToView?.();
  }
}

function zoomViewerTo100() {
  viewerZoom.value = 1;
  viewZoom.value = '100';
  if (threeCanvasRef.value) {
    threeCanvasRef.value.setZoom?.(1);
  }
}

// ========================================================================
// EASE VARIANTS (Smooth In/Out)
// Using "Smooth" instead of "Easy Ease" for trade dress safety
// ========================================================================
function applySmoothEaseIn() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  let keyframesUpdated = 0;

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer?.transform) continue;

    const transform = layer.transform as any;
    for (const propKey of ['position', 'scale', 'rotation', 'anchor', 'opacity']) {
      const prop = transform[propKey];
      if (prop?.animated && prop?.keyframes) {
        for (const kf of prop.keyframes) {
          // Set to bezier with ease-in curve (slow start, fast end)
          store.setKeyframeInterpolation(layerId, `transform.${propKey}`, kf.id, 'bezier');
          // Set ease-in handles: strong in-handle, weak out-handle
          store.updateKeyframeHandles?.(layerId, `transform.${propKey}`, kf.id, {
            inHandle: { x: -0.42, y: 0 },    // Pull back (slow arrival)
            outHandle: { x: 0.1, y: 0 }       // Quick departure
          });
          keyframesUpdated++;
        }
      }
    }
  }

  if (keyframesUpdated > 0) {
    console.log(`[Weyl] Applied Smooth In to ${keyframesUpdated} keyframes`);
  }
}

function applySmoothEaseOut() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  let keyframesUpdated = 0;

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer?.transform) continue;

    const transform = layer.transform as any;
    for (const propKey of ['position', 'scale', 'rotation', 'anchor', 'opacity']) {
      const prop = transform[propKey];
      if (prop?.animated && prop?.keyframes) {
        for (const kf of prop.keyframes) {
          // Set to bezier with ease-out curve (fast start, slow end)
          store.setKeyframeInterpolation(layerId, `transform.${propKey}`, kf.id, 'bezier');
          // Set ease-out handles: weak in-handle, strong out-handle
          store.updateKeyframeHandles?.(layerId, `transform.${propKey}`, kf.id, {
            inHandle: { x: -0.1, y: 0 },      // Quick arrival
            outHandle: { x: 0.42, y: 0 }      // Pull forward (slow departure)
          });
          keyframesUpdated++;
        }
      }
    }
  }

  if (keyframesUpdated > 0) {
    console.log(`[Weyl] Applied Smooth Out to ${keyframesUpdated} keyframes`);
  }
}

// ========================================================================
// HOLD KEYFRAMES CONVERSION
// Ctrl+Alt+H - Convert keyframes to hold interpolation
// ========================================================================
function convertToHoldKeyframes() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  let keyframesUpdated = 0;

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer?.transform) continue;

    const transform = layer.transform as any;
    for (const propKey of ['position', 'scale', 'rotation', 'anchor', 'opacity']) {
      const prop = transform[propKey];
      if (prop?.animated && prop?.keyframes) {
        for (const kf of prop.keyframes) {
          store.setKeyframeInterpolation(layerId, `transform.${propKey}`, kf.id, 'hold');
          keyframesUpdated++;
        }
      }
    }
  }

  if (keyframesUpdated > 0) {
    console.log(`[Weyl] Converted ${keyframesUpdated} keyframes to hold`);
  }
}

// ========================================================================
// TIME-REVERSE KEYFRAMES
// Reverses the order of keyframes on selected properties
// ========================================================================
function timeReverseKeyframes() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer?.transform) continue;

    const transform = layer.transform as any;
    for (const propKey of ['position', 'scale', 'rotation', 'anchor', 'opacity']) {
      const prop = transform[propKey];
      if (prop?.animated && prop?.keyframes && prop.keyframes.length >= 2) {
        // Get keyframe frames and values
        const keyframes = [...prop.keyframes];
        const frames = keyframes.map((kf: any) => kf.frame);
        const values = keyframes.map((kf: any) => kf.value);

        // Reverse values while keeping frames in place
        values.reverse();

        // Update each keyframe with reversed value
        for (let i = 0; i < keyframes.length; i++) {
          store.updateKeyframeValue?.(layerId, `transform.${propKey}`, keyframes[i].id, values[i]);
        }
      }
    }
  }

  console.log('[Weyl] Keyframes time-reversed');
}

// ========================================================================
// FIT LAYER TO COMPOSITION
// Scales and positions layer to fill composition
// ========================================================================
function fitLayerToComp() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const compW = compWidth.value;
  const compH = compHeight.value;

  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (!layer) continue;

    // Get layer dimensions (from data if available)
    const data = layer.data as any;
    const layerW = data?.width || compW;
    const layerH = data?.height || compH;

    // Calculate scale to fit
    const scaleX = compW / layerW;
    const scaleY = compH / layerH;
    const scale = Math.max(scaleX, scaleY); // Use max to fill (cover)

    // Center position
    const centerX = compW / 2;
    const centerY = compH / 2;

    // Update transform
    store.updateLayerTransform?.(id, {
      position: { x: centerX, y: centerY, z: 0 },
      scale: { x: scale * 100, y: scale * 100, z: 100 },
      anchor: { x: layerW / 2, y: layerH / 2, z: 0 }
    });
  }

  console.log('[Weyl] Fit layer(s) to composition');
}

function fitLayerToCompWidth() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const compW = compWidth.value;

  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (!layer) continue;

    const data = layer.data as any;
    const layerW = data?.width || compW;

    const scale = compW / layerW;

    store.updateLayerTransform?.(id, {
      scale: { x: scale * 100, y: scale * 100, z: 100 }
    });
  }

  console.log('[Weyl] Fit layer(s) to composition width');
}

function fitLayerToCompHeight() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const compH = compHeight.value;

  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (!layer) continue;

    const data = layer.data as any;
    const layerH = data?.height || compH;

    const scale = compH / layerH;

    store.updateLayerTransform?.(id, {
      scale: { x: scale * 100, y: scale * 100, z: 100 }
    });
  }

  console.log('[Weyl] Fit layer(s) to composition height');
}

// ========================================================================
// LOCK LAYER (Ctrl+L)
// ========================================================================
function toggleLayerLock() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (layer) {
      store.updateLayer(id, { locked: !layer.locked });
    }
  }
}

// ========================================================================
// CENTER ANCHOR POINT (Ctrl+Alt+Home)
// Moves anchor to layer center without moving the layer visually
// ========================================================================
function centerAnchorPoint() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (!layer) continue;

    // Get layer dimensions from data
    const data = layer.data as any;
    const layerW = data?.width || compWidth.value;
    const layerH = data?.height || compHeight.value;

    // Calculate center of layer
    const centerX = layerW / 2;
    const centerY = layerH / 2;

    // Get current anchor and position
    const transform = layer.transform as any;
    const currentAnchor = transform?.anchor?.value || transform?.anchor?.defaultValue || { x: 0, y: 0, z: 0 };
    const currentPos = transform?.position?.value || transform?.position?.defaultValue || { x: 0, y: 0, z: 0 };

    // Calculate offset to maintain visual position
    const offsetX = centerX - (currentAnchor.x || 0);
    const offsetY = centerY - (currentAnchor.y || 0);

    // Update both anchor and position to maintain visual position
    store.updateLayerTransform?.(id, {
      anchor: { x: centerX, y: centerY, z: currentAnchor.z || 0 },
      position: {
        x: (currentPos.x || 0) + offsetX,
        y: (currentPos.y || 0) + offsetY,
        z: currentPos.z || 0
      }
    });
  }

  console.log('[Weyl] Centered anchor point(s)');
}

// ========================================================================
// CENTER LAYER IN COMPOSITION (Ctrl+Home)
// Moves layer to center of composition
// ========================================================================
function centerLayerInComp() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const centerX = compWidth.value / 2;
  const centerY = compHeight.value / 2;

  for (const id of selectedIds) {
    const layer = store.getLayerById(id);
    if (!layer) continue;

    const transform = layer.transform as any;
    const currentPos = transform?.position?.value || transform?.position?.defaultValue || { x: 0, y: 0, z: 0 };

    store.updateLayerTransform?.(id, {
      position: { x: centerX, y: centerY, z: currentPos.z || 0 }
    });
  }

  console.log('[Weyl] Centered layer(s) in composition');
}

// ========================================================================
// CREATE ADJUSTMENT LAYER (Ctrl+Alt+Y)
// ========================================================================
function createAdjustmentLayer() {
  store.addLayer('adjustment', {
    name: 'Adjustment Layer',
    width: compWidth.value,
    height: compHeight.value
  });
  console.log('[Weyl] Created adjustment layer');
}

// ========================================================================
// CREATE NULL LAYER (Ctrl+Alt+Shift+Y)
// ========================================================================
function createNullLayer() {
  store.addLayer('null', {
    name: 'Null Object'
  });
  console.log('[Weyl] Created null layer');
}

// ========================================================================
// REVEAL SOURCE IN PROJECT (Ctrl+Alt+E)
// Shows the source asset of the selected layer in the Assets panel
// ========================================================================
function revealSourceInProject() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) {
    console.log('[Weyl] No layer selected to reveal source');
    return;
  }

  const layer = store.getLayerById(selectedIds[0]);
  if (!layer) return;

  // Get asset ID based on layer type
  const data = layer.data as any;
  let assetId: string | null = null;

  if (data?.assetId) {
    assetId = data.assetId;
  } else if (layer.type === 'precomp') {
    // For precomp, show the composition (switch to Comps tab)
    if (data?.compositionId) {
      leftTab.value = 'comps';
      console.log(`[Weyl] Revealed precomp source: ${data.compositionId}`);
      return;
    }
  }

  if (assetId) {
    // Switch to assets tab and highlight the asset
    leftTab.value = 'assets';
    // Set selected asset if the store supports it
    if (typeof store.selectAsset === 'function') {
      store.selectAsset(assetId);
    }
    console.log(`[Weyl] Revealed source asset: ${assetId}`);
  } else {
    console.log(`[Weyl] Layer type '${layer.type}' has no source asset`);
  }
}

// ========================================================================
// SELECT LAYERS BY LABEL COLOR
// Selects all layers with the same label color as the first selected layer
// ========================================================================
// Select all keyframes on selected layers (Ctrl+A when layers selected)
function selectAllKeyframesOnSelectedLayers(): boolean {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return false;

  const keyframeIds: string[] = [];

  for (const layerId of selectedIds) {
    const layer = store.getLayerById(layerId);
    if (!layer) continue;

    // Get keyframes from transform properties
    const transform = layer.transform as any;
    if (transform) {
      const props = ['position', 'rotation', 'scale', 'anchor', 'opacity'];
      for (const propName of props) {
        const prop = transform[propName];
        if (prop?.keyframes && Array.isArray(prop.keyframes)) {
          for (const kf of prop.keyframes) {
            if (kf.id) keyframeIds.push(kf.id);
          }
        }
      }
    }

    // Get keyframes from layer-specific data
    const data = layer.data as any;
    if (data) {
      // Check for animatable properties in data
      const checkForKeyframes = (obj: any) => {
        if (!obj || typeof obj !== 'object') return;
        if (Array.isArray(obj.keyframes)) {
          for (const kf of obj.keyframes) {
            if (kf.id) keyframeIds.push(kf.id);
          }
        }
        for (const key of Object.keys(obj)) {
          if (typeof obj[key] === 'object') checkForKeyframes(obj[key]);
        }
      };
      checkForKeyframes(data);
    }
  }

  if (keyframeIds.length > 0) {
    useSelectionStore().selectKeyframes(keyframeIds);
    console.log(`[Weyl] Selected ${keyframeIds.length} keyframes on ${selectedIds.length} layer(s)`);
    return true;
  }
  return false;
}

function selectLayersByLabel() {
  const selectedIds = store.selectedLayerIds;
  if (selectedIds.length === 0) return;

  const firstLayer = store.getLayerById(selectedIds[0]);
  if (!firstLayer) return;

  const targetColor = firstLayer.labelColor || firstLayer.color || '#808080';

  // Find all layers with same label color
  const layers = store.layers;
  const matchingIds: string[] = [];

  for (const layer of layers) {
    const layerColor = layer.labelColor || layer.color || '#808080';
    if (layerColor === targetColor) {
      matchingIds.push(layer.id);
    }
  }

  // Select all matching layers
  if (matchingIds.length > 0) {
    store.selectLayers?.(matchingIds) || matchingIds.forEach(id => store.selectLayer(id, true));
    console.log(`[Weyl] Selected ${matchingIds.length} layers with label color ${targetColor}`);
  }
}

// Keyboard shortcuts
function handleKeydown(e: KeyboardEvent) {
  // Don't handle if input is focused
  if (document.activeElement?.tagName === 'INPUT' ||
      document.activeElement?.tagName === 'TEXTAREA') {
    return;
  }

  const hasSelectedLayer = store.selectedLayerIds.length > 0;

  switch (e.key.toLowerCase()) {
    case ' ':
      e.preventDefault();
      togglePlay();
      break;

    // Property solo shortcuts (AE-style) - only when layer is selected
    // Shift+letter adds to current reveals (additive mode)
    case 'p':
      if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        soloProperty('position', e.shiftKey);
      } else if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
        currentTool.value = 'pen';
      }
      break;
    case 's':
      if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        soloProperty('scale', e.shiftKey);
      }
      break;
    case 't':
      if ((e.ctrlKey || e.metaKey) && e.altKey && hasSelectedLayer) {
        // Ctrl+Alt+T: Time Stretch dialog
        e.preventDefault();
        openTimeStretchDialog();
      } else if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        soloProperty('opacity', e.shiftKey); // T for opacity (AE convention)
      } else if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
        currentTool.value = 'text';
      }
      break;
    case 'a':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        // If layers are selected, try to select all keyframes on those layers
        // Otherwise, select all layers
        if (hasSelectedLayer) {
          const selectedKeyframes = selectAllKeyframesOnSelectedLayers();
          if (!selectedKeyframes) {
            // No keyframes found, select all layers instead
            store.selectAllLayers();
          }
        } else {
          store.selectAllLayers();
        }
      } else if (hasSelectedLayer) {
        e.preventDefault();
        soloProperty('anchor', e.shiftKey);
      } else if (!e.shiftKey) {
        // Switch to Assets tab
        leftTab.value = 'assets';
      }
      break;
    case 'u':
      if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        // Check for double-tap (UU = modified properties)
        if (isDoubleTap('u')) {
          soloProperty('modified', e.shiftKey); // UU shows all modified properties
        } else {
          soloProperty('animated', e.shiftKey); // U shows all animated properties
        }
      }
      break;

    // E key: Effects reveal (single), Expressions reveal (double-tap EE), Ctrl+Alt+E: Reveal source
    case 'e':
      if ((e.ctrlKey || e.metaKey) && e.altKey && hasSelectedLayer) {
        // Ctrl+Alt+E: Reveal source in Project panel
        e.preventDefault();
        revealSourceInProject();
      } else if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        if (isDoubleTap('e')) {
          soloProperty('expressions', e.shiftKey); // EE shows expressions
        } else {
          soloProperty('effects', e.shiftKey); // E shows effects
        }
      }
      break;

    // M key: Masks reveal (single M), All mask properties (double-tap MM)
    case 'm':
      if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        if (isDoubleTap('m')) {
          // MM: Show all mask properties expanded
          soloProperty('masks', e.shiftKey);
          console.log('[Weyl] Showing all mask properties (MM)');
        } else {
          // M: Show mask group
          soloProperty('masks', e.shiftKey);
        }
      } else if (e.ctrlKey || e.metaKey) {
        // Ctrl+M: Export (existing behavior)
        e.preventDefault();
        showExportDialog.value = true;
      }
      break;

    case 'h':
      if (e.ctrlKey && e.altKey) {
        // Ctrl+Alt+H: Convert keyframes to hold
        e.preventDefault();
        convertToHoldKeyframes();
      } else if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        // Ctrl+Shift+H: Toggle transparency grid
        e.preventDefault();
        toggleTransparencyGrid();
      } else if (!e.ctrlKey && !e.metaKey && !e.shiftKey && !e.altKey) {
        // H alone: Hand tool
        currentTool.value = 'hand';
      }
      break;
    case 'z':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        if (e.shiftKey) {
          redo();
        } else {
          undo();
        }
      } else {
        currentTool.value = 'zoom';
      }
      break;

    // Navigation shortcuts
    // Note: 'home' handled below with Ctrl+Alt/Ctrl modifiers
    case 'end':
      e.preventDefault();
      goToEnd();
      break;
    case 'pageup':
      e.preventDefault();
      stepBackward(e.shiftKey ? 10 : 1);
      break;
    case 'pagedown':
      e.preventDefault();
      stepForward(e.shiftKey ? 10 : 1);
      break;
    case 'arrowleft':
      e.preventDefault();
      stepBackward(e.shiftKey ? 10 : 1);
      break;
    case 'arrowright':
      e.preventDefault();
      stepForward(e.shiftKey ? 10 : 1);
      break;

    // Keyframe navigation (J = prev, K = next) - AE standard
    case 'j':
      if (!e.ctrlKey && !e.metaKey) {
        e.preventDefault();
        goToPrevKeyframe();
      }
      break;
    case 'k':
      if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        // Ctrl+Shift+K: Keyframe Interpolation dialog
        e.preventDefault();
        if (store.selectedKeyframeIds.length > 0) {
          showKeyframeInterpolationDialog.value = true;
        } else {
          console.log('[Weyl] No keyframes selected for interpolation dialog');
        }
      } else if (e.ctrlKey || e.metaKey) {
        // Ctrl/Cmd+K: Open composition settings
        e.preventDefault();
        showCompositionSettingsDialog.value = true;
      } else {
        // K alone: Go to next keyframe
        e.preventDefault();
        goToNextKeyframe();
      }
      break;

    case 'g':
      if ((e.ctrlKey || e.metaKey) && e.shiftKey && hasSelectedLayer) {
        // Ctrl+Shift+G: Select layers by label group
        e.preventDefault();
        selectLayersByLabel();
      } else if (e.shiftKey) {
        // Shift+G: Toggle curve editor
        e.preventDefault();
        showCurveEditor.value = !showCurveEditor.value;
      }
      break;
    case 'i':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        triggerAssetImport();
      } else if (hasSelectedLayer) {
        // I: Go to layer in point (AE standard)
        e.preventDefault();
        goToLayerInPoint();
      }
      break;
    case 'o':
      if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        // O: Go to layer out point (AE standard)
        e.preventDefault();
        goToLayerOutPoint();
      }
      break;

    // Pre-compose shortcut (Ctrl+Shift+C)
    case 'c':
      if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        e.preventDefault();
        if (store.selectedLayerIds.length > 0) {
          showPrecomposeDialog.value = true;
        }
      } else if (e.ctrlKey || e.metaKey) {
        // Copy selected layers
        e.preventDefault();
        store.copySelectedLayers();
      }
      break;
    case 'delete':
    case 'backspace':
      // Delete selected layers
      if (store.selectedLayerIds.length > 0) {
        e.preventDefault();
        store.deleteSelectedLayers();
      }
      break;
    case 'f9':
      e.preventDefault();
      if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        // Ctrl+Shift+F9: Apply Smooth Out (ease-out curve)
        applySmoothEaseOut();
      } else if (e.shiftKey) {
        // Shift+F9: Apply Smooth In (ease-in curve)
        applySmoothEaseIn();
      } else {
        // F9: Apply Smooth easing (both)
        applySmoothEasing();
      }
      break;
    case 'v':
      if (e.ctrlKey || e.metaKey) {
        // Paste layers from clipboard
        e.preventDefault();
        store.pasteLayers();
      } else if (!e.shiftKey) {
        // Select tool (existing behavior)
        currentTool.value = 'select';
      }
      break;
    case 'x':
      if (e.ctrlKey || e.metaKey) {
        // Cut selected layers
        e.preventDefault();
        store.cutSelectedLayers();
      }
      break;

    // Layer timing shortcuts (AE standard)
    case '[':
      if (e.altKey) {
        // Alt+[: Trim layer in point to playhead
        e.preventDefault();
        trimLayerInPoint();
      } else if (hasSelectedLayer) {
        // [: Move layer in point to playhead
        e.preventDefault();
        moveLayerInPointToPlayhead();
      }
      break;
    case ']':
      if (e.altKey) {
        // Alt+]: Trim layer out point to playhead
        e.preventDefault();
        trimLayerOutPoint();
      } else if (hasSelectedLayer) {
        // ]: Move layer out point to playhead
        e.preventDefault();
        moveLayerOutPointToPlayhead();
      }
      break;

    // Layer navigation (Ctrl+Arrow)
    case 'arrowup':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        selectPreviousLayer(e.shiftKey); // Shift extends selection
      }
      break;
    case 'arrowdown':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        selectNextLayer(e.shiftKey); // Shift extends selection
      }
      break;

    // Split layer (Ctrl+Shift+D)
    case 'd':
      if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        e.preventDefault();
        splitLayerAtPlayhead();
      } else if (e.ctrlKey || e.metaKey) {
        // Duplicate selected layers
        e.preventDefault();
        store.duplicateSelectedLayers();
      }
      break;

    // R key shortcuts: Rotation solo, Time-reverse layer, Rulers, Reverse keyframes
    case 'r':
      if ((e.ctrlKey || e.metaKey) && e.shiftKey && !e.altKey) {
        // Ctrl+Shift+R: Toggle rulers
        e.preventDefault();
        toggleRulers();
      } else if ((e.ctrlKey || e.metaKey) && e.altKey && hasSelectedLayer) {
        // Ctrl+Alt+R: Reverse layer timing
        e.preventDefault();
        reverseSelectedLayers();
      } else if ((e.ctrlKey || e.metaKey) && e.altKey) {
        // Ctrl+Alt+R (no layer selected): Time-reverse keyframes
        e.preventDefault();
        timeReverseKeyframes();
      } else if (hasSelectedLayer && !e.ctrlKey && !e.metaKey) {
        // R alone: Solo rotation property
        e.preventDefault();
        soloProperty('rotation', e.shiftKey);
      }
      break;

    // Note: Freeze frame (freezeFrameSelectedLayers) is available via Layer menu
    // Ctrl+Shift+F is used for Fit to Width, so no keyboard shortcut for freeze frame

    // Timeline zoom shortcuts (= zoom in, - zoom out, ; zoom to fit)
    case '=':
    case '+':
      if (e.ctrlKey || e.metaKey) {
        // Ctrl+= : Viewer zoom in (instead of AE's . key for trade dress safety)
        e.preventDefault();
        zoomViewerIn();
      } else {
        // = alone: Timeline zoom in
        e.preventDefault();
        zoomTimelineIn();
      }
      break;
    case '-':
      if (e.ctrlKey || e.metaKey) {
        // Ctrl+- : Viewer zoom out (instead of AE's , key for trade dress safety)
        e.preventDefault();
        zoomViewerOut();
      } else {
        // - alone: Timeline zoom out
        e.preventDefault();
        zoomTimelineOut();
      }
      break;
    case ';':
      if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        // Ctrl+Shift+;: Toggle snap
        e.preventDefault();
        toggleSnap();
      } else if (!e.ctrlKey && !e.metaKey) {
        // ; alone: Fit timeline to view
        e.preventDefault();
        zoomTimelineToFit();
      }
      break;
    case '0':
      if (e.ctrlKey || e.metaKey) {
        // Ctrl+0: Fit viewer to screen (instead of AE's / key)
        e.preventDefault();
        zoomViewerToFit();
      } else if (e.shiftKey && (e.ctrlKey || e.metaKey)) {
        // Ctrl+Shift+0: Viewer to 100% (instead of AE's Shift+/ key)
        e.preventDefault();
        zoomViewerTo100();
      }
      break;

    // Audio-only preview (Ctrl+.) - AE standard
    case '.':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        audioStore.toggleAudioPlayback(store.currentFrame, store.fps);
      }
      break;

    // Work area shortcuts
    // B: Set work area beginning, N: Set work area end
    case 'b':
      if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
        e.preventDefault();
        setWorkAreaStart();
      }
      break;
    case 'n':
      if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
        e.preventDefault();
        setWorkAreaEnd();
      }
      break;

    // Lock layer shortcut (Ctrl+L)
    case 'l':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        toggleLayerLock();
      }
      break;

    // Caps Lock: Toggle preview updates pause
    case 'capslock':
      e.preventDefault();
      togglePreviewPause();
      break;

    // Fit Layer to Comp (Ctrl+Alt+F)
    case 'f':
      if ((e.ctrlKey || e.metaKey) && e.altKey) {
        e.preventDefault();
        if (e.shiftKey) {
          fitLayerToCompHeight();
        } else {
          fitLayerToComp();
        }
      } else if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        // Ctrl+Shift+F: Fit to width
        e.preventDefault();
        fitLayerToCompWidth();
      }
      break;

    // Y key shortcuts
    case 'y':
      if ((e.ctrlKey || e.metaKey) && e.altKey && e.shiftKey) {
        // Ctrl+Alt+Shift+Y: Create null layer
        e.preventDefault();
        createNullLayer();
      } else if ((e.ctrlKey || e.metaKey) && e.altKey) {
        // Ctrl+Alt+Y: Create adjustment layer
        e.preventDefault();
        createAdjustmentLayer();
      } else if ((e.ctrlKey || e.metaKey) && e.shiftKey) {
        // Ctrl+Shift+Y: Toggle hidden layers visibility
        e.preventDefault();
        toggleHiddenLayersVisibility();
      }
      break;

    // Home key shortcuts
    case 'home':
      if ((e.ctrlKey || e.metaKey) && e.altKey) {
        // Ctrl+Alt+Home: Center anchor point
        e.preventDefault();
        centerAnchorPoint();
      } else if (e.ctrlKey || e.metaKey) {
        // Ctrl+Home: Center layer in composition
        e.preventDefault();
        centerLayerInComp();
      } else {
        // Home alone: Go to start of composition
        e.preventDefault();
        store.setFrame(0);
      }
      break;

    // Grid toggle (Ctrl+')
    case "'":
    case '`':
      if (e.ctrlKey || e.metaKey) {
        e.preventDefault();
        toggleGrid();
      }
      break;
  }
}

// Import dialog trigger
const importFileInput = ref<HTMLInputElement | null>(null);

function triggerAssetImport() {
  // Create a temporary file input for import
  const input = document.createElement('input');
  input.type = 'file';
  input.accept = '.svg,.gltf,.glb,.obj,.fbx,.hdr,.exr,.png,.jpg';
  input.multiple = true;
  input.onchange = async (e) => {
    const files = (e.target as HTMLInputElement).files;
    if (!files) return;

    for (const file of files) {
      const ext = file.name.split('.').pop()?.toLowerCase();
      if (ext === 'svg') {
        await assetStore.importSvgFromFile(file);
      } else if (['hdr', 'exr'].includes(ext || '')) {
        await assetStore.loadEnvironment(file);
      }
      // Models and other assets handled by AssetsPanel
    }

    // Switch to assets tab to show imported items
    leftTab.value = 'assets';
  };
  input.click();
}

// Performance monitoring
let perfInterval: number;

function updatePerformanceStats() {
  // Memory usage (if available)
  if ('memory' in performance) {
    const mem = (performance as any).memory;
    const usedMB = Math.round(mem.usedJSHeapSize / 1024 / 1024);
    memoryUsage.value = `${usedMB} MB`;
  }
}

// Lifecycle
onMounted(async () => {
  const tierInfo = await detectGPUTier();
  gpuTier.value = tierInfo.tier;

  window.addEventListener('keydown', handleKeydown);

  perfInterval = window.setInterval(updatePerformanceStats, 1000);

  // Start autosave timer
  if (store.autosaveEnabled) {
    store.startAutosaveTimer();
  }
});

onUnmounted(() => {
  window.removeEventListener('keydown', handleKeydown);
  clearInterval(perfInterval);

  // Stop autosave timer
  store.stopAutosaveTimer();
});
</script>

<style scoped>
.workspace-layout {
  display: flex;
  flex-direction: column;
  /* Use 100% height for ComfyUI sidebar compatibility, fallback to 100vh for standalone */
  height: 100%;
  min-height: 100vh;
  background: var(--weyl-void, #050505);
  color: var(--weyl-text-primary, #e5e5e5);
  font-family: var(--weyl-font-sans, -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif);
  font-size: var(--weyl-text-base, 12px);
  /* Minimal padding for maximum workspace */
  padding: 4px;
  gap: 4px;
}

/* Toolbar - floating panel */
.toolbar {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 12px;
  background: var(--weyl-surface-1, #121212);
  border-radius: var(--weyl-radius-md, 4px);
  box-shadow: var(--weyl-shadow-panel, 0 4px 16px rgba(0,0,0,0.3));
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
  font-size: var(--weyl-text-base, 12px);
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
  font-size: var(--weyl-text-lg, 14px);
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
  font-size: var(--weyl-text-base, 12px);
}

.gpu-badge {
  font-size: var(--weyl-text-xs, 10px);
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
  font-size: var(--weyl-text-xs, 10px);
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

.ai-btn {
  background: var(--weyl-accent-gradient, linear-gradient(135deg, #8B5CF6, #EC4899)) !important;
  color: white !important;
}

.ai-btn:hover {
  filter: brightness(1.1);
}

/* Main Workspace */
.workspace-content {
  flex: 1;
  min-height: 0;
  overflow: hidden;
}

.horizontal-split {
  height: 100%;
}

/* Panels - clean flat design */
.panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--weyl-surface-1, #121212);
  border-radius: var(--weyl-radius-sm, 2px);
  overflow: hidden;
}

.left-panel,
.right-panel {
  /* No borders - use shadows for separation */
  /* Minimum pixel widths ensure readability on all screens */
  min-width: 180px;
}

.right-panel {
  /* No borders - use shadows for separation */
  /* Properties panel needs more space for controls */
  min-width: 220px;
}

.panel-tabs {
  display: flex;
  background: var(--weyl-surface-2, #1a1a1a);
  padding: 4px;
  gap: 2px;
}

.panel-tabs button {
  flex: 1;
  padding: 6px 8px;
  border: none;
  background: transparent;
  color: var(--weyl-text-secondary, #9CA3AF);
  font-size: var(--weyl-text-sm, 11px);
  font-weight: 500;
  cursor: pointer;
  border-radius: var(--weyl-radius-md, 4px);
  transition: var(--weyl-transition-fast, 100ms ease);
}

.panel-tabs button:hover {
  color: var(--weyl-text-primary, #e5e5e5);
  background: var(--weyl-surface-3, #222222);
}

.panel-tabs button.active {
  color: white;
  background: var(--weyl-accent, #8B5CF6);
}

.panel-tabs button:focus-visible {
  outline: 2px solid var(--weyl-accent, #8B5CF6);
  outline-offset: 2px;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  overflow-x: hidden;
}

/* Custom scrollbar styling for dark theme */
.panel-content::-webkit-scrollbar {
  width: 8px;
}

.panel-content::-webkit-scrollbar-track {
  background: var(--weyl-surface-1, #121212);
}

.panel-content::-webkit-scrollbar-thumb {
  background: var(--weyl-surface-3, #333);
  border-radius: 4px;
}

.panel-content::-webkit-scrollbar-thumb:hover {
  background: var(--weyl-surface-4, #444);
}

/* Viewport */
.viewport-panel {
  background: var(--weyl-surface-0, #0a0a0a);
}

.viewport-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 6px 10px;
  background: var(--weyl-surface-2, #1a1a1a);
  gap: 8px;
}

.viewport-tabs {
  display: flex;
  gap: 2px;
}

.viewport-tabs button {
  padding: 5px 10px;
  border: none;
  background: transparent;
  color: var(--weyl-text-secondary, #9CA3AF);
  font-size: var(--weyl-text-sm, 11px);
  border-radius: var(--weyl-radius-md, 4px);
  cursor: pointer;
  transition: var(--weyl-transition-fast, 100ms ease);
}

.viewport-tabs button:hover {
  color: var(--weyl-text-primary, #e5e5e5);
}

.viewport-tabs button.active {
  background: var(--weyl-surface-3, #222222);
  color: var(--weyl-text-primary, #e5e5e5);
}

.viewport-controls {
  display: flex;
  align-items: center;
  gap: 4px;
}

.zoom-select {
  padding: 4px 8px;
  background: var(--weyl-surface-2, #1a1a1a);
  border: none;
  color: var(--weyl-text-primary, #e5e5e5);
  border-radius: var(--weyl-radius-md, 4px);
  font-size: var(--weyl-text-sm, 11px);
}

.viewport-controls button {
  width: 24px;
  height: 24px;
  padding: 0;
  border: none;
  background: transparent;
  color: var(--weyl-text-muted, #6B7280);
  border-radius: var(--weyl-radius-md, 4px);
  cursor: pointer;
  font-size: var(--weyl-text-base, 12px);
  transition: var(--weyl-transition-fast, 100ms ease);
}

.viewport-controls button:hover {
  background: var(--weyl-surface-3, #222222);
  color: var(--weyl-text-primary, #e5e5e5);
}

.viewport-controls button.active {
  color: var(--weyl-accent, #8B5CF6);
}

.viewport-content {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--weyl-surface-0, #0a0a0a);
  overflow: hidden;
  position: relative;
}

.viewport-content.rulers-active {
  padding-top: 20px;
  padding-left: 20px;
}

/* Rulers */
.rulers-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 100;
}

.ruler {
  position: absolute;
  background: rgba(30, 30, 30, 0.9);
  font-size: 11px;
  color: #888;
}

.ruler-horizontal {
  top: 0;
  left: 20px;
  right: 0;
  height: 20px;
  border-bottom: 1px solid #444;
}

.ruler-vertical {
  top: 20px;
  left: 0;
  bottom: 0;
  width: 20px;
  border-right: 1px solid #444;
}

.ruler .tick {
  position: absolute;
  font-size: 11px;
  color: #666;
}

.ruler-horizontal .tick {
  transform: translateX(-50%);
  top: 4px;
}

.ruler-vertical .tick {
  transform: translateY(-50%) rotate(-90deg);
  left: 2px;
  white-space: nowrap;
}

/* Make rulers interactive for guide creation */
.ruler-horizontal,
.ruler-vertical {
  pointer-events: auto;
  cursor: pointer;
}

.ruler-horizontal:hover {
  background: rgba(0, 191, 255, 0.1);
}

.ruler-vertical:hover {
  background: rgba(0, 191, 255, 0.1);
}

/* Grid Overlay */
.grid-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 5;
}

/* Guides Overlay */
.guides-overlay {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  pointer-events: none;
  z-index: 10;
}

.guides-overlay .guide {
  pointer-events: auto;
  transition: background 0.1s;
  position: relative;
}

.guides-overlay .guide:hover {
  /* Change gradient color to red on hover */
}

.guides-overlay .guide.horizontal:hover {
  background: linear-gradient(to bottom, transparent 5px, #FF6B6B 5px, #FF6B6B 6px, transparent 6px) !important;
}

.guides-overlay .guide.vertical:hover {
  background: linear-gradient(to right, transparent 5px, #FF6B6B 5px, #FF6B6B 6px, transparent 6px) !important;
}

.guides-overlay .guide.horizontal {
  width: 100%;
}

.guides-overlay .guide.vertical {
  height: 100%;
}

/* Guide delete button - shown on hover */
.guide-delete-btn {
  position: absolute;
  width: 16px;
  height: 16px;
  border-radius: 50%;
  background: #FF4444;
  color: white;
  border: none;
  font-size: 12px;
  line-height: 14px;
  cursor: pointer;
  opacity: 0;
  transition: opacity 0.15s;
  display: flex;
  align-items: center;
  justify-content: center;
  padding: 0;
}

.guide:hover .guide-delete-btn {
  opacity: 1;
}

.guide.horizontal .guide-delete-btn {
  right: 4px;
  top: -2px;
}

.guide.vertical .guide-delete-btn {
  top: 4px;
  left: -2px;
}

.guide-delete-btn:hover {
  background: #FF0000;
  transform: scale(1.1);
}

/* Guide context menu */
.guide-context-menu {
  position: fixed;
  background: var(--weyl-surface-3, #222);
  border: 1px solid var(--weyl-border-default, #333);
  border-radius: 4px;
  padding: 4px 0;
  min-width: 140px;
  box-shadow: 0 4px 12px rgba(0,0,0,0.3);
  z-index: 10000;
}

.guide-context-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  background: none;
  border: none;
  color: var(--weyl-text-primary, #e5e5e5);
  text-align: left;
  cursor: pointer;
  font-size: 12px;
}

.guide-context-menu button:hover {
  background: var(--weyl-accent-muted, rgba(139, 92, 246, 0.2));
}

/* Snap Indicator */
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
  background-color: #FF00FF;
  opacity: 0.8;
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

/* Timeline Panel */
.timeline-panel {
  /* No borders - floating panel */
}

.curve-editor-panel {
  /* No borders - floating panel */
}

/* Status bar removed - info now in toolbar */

/* Splitpanes Theme Overrides */
:deep(.splitpanes.default-theme .splitpanes__pane) {
  background: transparent;
  /* Allow dropdowns to overflow outside pane boundaries */
  overflow: visible !important;
}

:deep(.splitpanes.default-theme .splitpanes__splitter) {
  background: transparent;
  border: none;
}

:deep(.splitpanes.default-theme .splitpanes__splitter:hover) {
  background: var(--weyl-accent, #8B5CF6);
}

:deep(.splitpanes--vertical > .splitpanes__splitter) {
  width: 2px;
  min-width: 2px;
}

:deep(.splitpanes--horizontal > .splitpanes__splitter) {
  height: 2px;
  min-height: 2px;
}

/* Ensure timeline pane allows dropdown overflow */
:deep(.splitpanes--horizontal .splitpanes__pane:last-child) {
  overflow: visible !important;
}

/* Segmentation tool options */
.segment-options {
  display: flex;
  align-items: center;
  gap: 4px;
}

.segment-options .confirm-btn {
  background: var(--weyl-success, #10B981) !important;
  color: white !important;
}

.segment-options .confirm-btn:hover {
  filter: brightness(1.1);
}

.segment-options .cancel-btn {
  background: var(--weyl-error, #F43F5E) !important;
  color: white !important;
}

.segment-options .cancel-btn:hover {
  filter: brightness(1.1);
}

.loading-indicator {
  color: var(--weyl-success, #10B981);
  font-size: var(--weyl-text-base, 12px);
  padding: 0 8px;
  animation: pulse 1s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 0.6; }
  50% { opacity: 1; }
}
</style>