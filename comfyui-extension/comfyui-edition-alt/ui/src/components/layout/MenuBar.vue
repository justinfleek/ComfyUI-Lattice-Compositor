<template>
  <div class="menu-bar" role="menubar">
    <!-- File Menu -->
    <div class="menu-item" @mouseenter="openMenu('file')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'file' }"
        @click="toggleMenu('file')"
      >
        File
      </button>
      <div v-if="activeMenu === 'file'" class="menu-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <button @click="handleAction('newProject')">
          <span class="label">New Project</span>
          <span class="shortcut">Ctrl+N</span>
        </button>
        <button @click="handleAction('openProject')">
          <span class="label">Open Project...</span>
          <span class="shortcut">Ctrl+O</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('saveProject')">
          <span class="label">Save Project</span>
          <span class="shortcut">Ctrl+S</span>
        </button>
        <button @click="handleAction('saveProjectAs')">
          <span class="label">Save Project As...</span>
          <span class="shortcut">Ctrl+Shift+S</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('import')">
          <span class="label">Import...</span>
          <span class="shortcut">Ctrl+I</span>
        </button>
        <button @click="handleAction('export')">
          <span class="label">Export...</span>
          <span class="shortcut">Ctrl+M</span>
        </button>
        <div class="separator"></div>
        <div class="menu-section-label">Server</div>
        <button @click="handleAction('saveProjectToServer')">
          <span class="label">Save to Server...</span>
        </button>
        <button @click="handleAction('loadProjectFromServer')">
          <span class="label">Load from Server...</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('projectSettings')">
          <span class="label">Project Settings...</span>
          <span class="shortcut">Ctrl+Alt+P</span>
        </button>
        <button @click="handleAction('preferences')">
          <span class="label">Preferences...</span>
          <span class="shortcut">Ctrl+,</span>
        </button>
      </div>
    </div>

    <!-- Edit Menu -->
    <div class="menu-item" @mouseenter="openMenu('edit')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'edit' }"
        @click="toggleMenu('edit')"
      >
        Edit
      </button>
      <div v-if="activeMenu === 'edit'" class="menu-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <button @click="handleAction('undo')" :disabled="!canUndo">
          <span class="label">Undo</span>
          <span class="shortcut">Ctrl+Z</span>
        </button>
        <button @click="handleAction('redo')" :disabled="!canRedo">
          <span class="label">Redo</span>
          <span class="shortcut">Ctrl+Shift+Z</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('cut')">
          <span class="label">Cut</span>
          <span class="shortcut">Ctrl+X</span>
        </button>
        <button @click="handleAction('copy')">
          <span class="label">Copy</span>
          <span class="shortcut">Ctrl+C</span>
        </button>
        <button @click="handleAction('paste')">
          <span class="label">Paste</span>
          <span class="shortcut">Ctrl+V</span>
        </button>
        <button @click="handleAction('duplicate')">
          <span class="label">Duplicate</span>
          <span class="shortcut">Ctrl+D</span>
        </button>
        <button @click="handleAction('delete')">
          <span class="label">Delete</span>
          <span class="shortcut">Delete</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('selectAll')">
          <span class="label">Select All</span>
          <span class="shortcut">Ctrl+A</span>
        </button>
        <button @click="handleAction('deselectAll')">
          <span class="label">Deselect All</span>
          <span class="shortcut">F2</span>
        </button>
        <div class="separator"></div>
        <div class="menu-section-label">Markers</div>
        <button @click="handleAction('addMarkerAtPlayhead')">
          <span class="label">Add Marker at Playhead</span>
          <span class="shortcut">*</span>
        </button>
        <button @click="handleAction('jumpToNextMarker')">
          <span class="label">Jump to Next Marker</span>
          <span class="shortcut">Shift+J</span>
        </button>
        <button @click="handleAction('jumpToPreviousMarker')">
          <span class="label">Jump to Previous Marker</span>
          <span class="shortcut">Shift+K</span>
        </button>
        <button @click="handleAction('clearMarkers')">
          <span class="label">Clear All Markers</span>
        </button>
        <div class="separator"></div>
        <div class="menu-section-label">Cache</div>
        <button @click="handleAction('clearFrameCache')">
          <span class="label">Clear Frame Cache</span>
        </button>
      </div>
    </div>

    <!-- Create Menu -->
    <div class="menu-item" @mouseenter="openMenu('create')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'create' }"
        @click="toggleMenu('create')"
      >
        Create
      </button>
      <div v-if="activeMenu === 'create'" class="menu-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <button @click="handleAction('createSolid')">
          <span class="label">Solid</span>
        </button>
        <button @click="handleAction('createText')">
          <span class="label">Text</span>
          <span class="shortcut">T</span>
        </button>
        <button @click="handleAction('createShape')">
          <span class="label">Shape</span>
          <span class="shortcut">P</span>
        </button>
        <button @click="handleAction('createPath')">
          <span class="label">Path</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('createCamera')">
          <span class="label">Camera</span>
        </button>
        <button @click="handleAction('createLight')">
          <span class="label">Light</span>
        </button>
        <button @click="handleAction('createControl')">
          <span class="label">Control (Null)</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('createParticle')">
          <span class="label">Particle System</span>
        </button>
        <button @click="handleAction('createDepth')">
          <span class="label">Depth Map</span>
        </button>
        <button @click="handleAction('createNormal')">
          <span class="label">Normal Map</span>
        </button>
        <button @click="handleAction('createGenerated')">
          <span class="label">AI Generated</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('createGroup')">
          <span class="label">Group</span>
        </button>
        <button @click="handleAction('createEffectLayer')">
          <span class="label">Effect Layer</span>
        </button>
        <button @click="handleAction('createMatte')">
          <span class="label">Procedural Matte</span>
        </button>
      </div>
    </div>

    <!-- Effects Menu -->
    <div class="menu-item" @mouseenter="openMenu('effects')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'effects' }"
        @click="toggleMenu('effects')"
      >
        Effects
      </button>
      <div v-if="activeMenu === 'effects'" class="menu-dropdown effects-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <!-- Blur & Sharpen -->
        <div class="menu-section-label">Blur & Sharpen</div>
        <button @click="handleAction('effect:gaussian-blur')"><span class="label">Gaussian Blur</span></button>
        <button @click="handleAction('effect:directional-blur')"><span class="label">Directional Blur</span></button>
        <button @click="handleAction('effect:radial-blur')"><span class="label">Radial Blur</span></button>
        <button @click="handleAction('effect:box-blur')"><span class="label">Box Blur</span></button>
        <button @click="handleAction('effect:sharpen')"><span class="label">Sharpen</span></button>

        <div class="separator"></div>

        <!-- Color Correction -->
        <div class="menu-section-label">Color Correction</div>
        <button @click="handleAction('effect:brightness-contrast')"><span class="label">Brightness/Contrast</span></button>
        <button @click="handleAction('effect:hue-saturation')"><span class="label">Hue/Saturation</span></button>
        <button @click="handleAction('effect:levels')"><span class="label">Levels</span></button>
        <button @click="handleAction('effect:curves')"><span class="label">Curves</span></button>
        <button @click="handleAction('effect:color-balance')"><span class="label">Color Balance</span></button>
        <button @click="handleAction('effect:exposure')"><span class="label">Exposure</span></button>
        <button @click="handleAction('effect:vibrance')"><span class="label">Vibrance</span></button>
        <button @click="handleAction('effect:tint')"><span class="label">Tint</span></button>
        <button @click="handleAction('effect:invert')"><span class="label">Invert</span></button>
        <button @click="handleAction('effect:posterize')"><span class="label">Posterize</span></button>
        <button @click="handleAction('effect:threshold')"><span class="label">Threshold</span></button>
        <button @click="handleAction('effect:lut')"><span class="label">LUT (Color Lookup)</span></button>

        <div class="separator"></div>

        <!-- Color Grading -->
        <div class="menu-section-label">Color Grading</div>
        <button @click="handleAction('effect:lift-gamma-gain')"><span class="label">Lift/Gamma/Gain</span></button>
        <button @click="handleAction('effect:hsl-secondary')"><span class="label">HSL Secondary</span></button>
        <button @click="handleAction('effect:hue-vs-curves')"><span class="label">Hue vs Curves</span></button>
        <button @click="handleAction('effect:color-match')"><span class="label">Color Match</span></button>

        <div class="separator"></div>

        <!-- Light & Glow -->
        <div class="menu-section-label">Light & Glow</div>
        <button @click="handleAction('effect:glow')"><span class="label">Glow</span></button>
        <button @click="handleAction('effect:cinematic-bloom')"><span class="label">Cinematic Bloom</span></button>
        <button @click="handleAction('effect:drop-shadow')"><span class="label">Drop Shadow</span></button>
        <button @click="handleAction('effect:vignette')"><span class="label">Vignette</span></button>

        <div class="separator"></div>

        <!-- Distort -->
        <div class="menu-section-label">Distort</div>
        <button @click="handleAction('effect:transform')"><span class="label">Transform</span></button>
        <button @click="handleAction('effect:warp')"><span class="label">Warp</span></button>
        <button @click="handleAction('effect:displacement-map')"><span class="label">Displacement Map</span></button>
        <button @click="handleAction('effect:turbulent-displace')"><span class="label">Turbulent Displace</span></button>
        <button @click="handleAction('effect:ripple-distort')"><span class="label">Ripple</span></button>

        <div class="separator"></div>

        <!-- Stylize -->
        <div class="menu-section-label">Stylize</div>
        <button @click="handleAction('effect:pixel-sort')"><span class="label">Pixel Sort</span></button>
        <button @click="handleAction('effect:glitch')"><span class="label">Glitch</span></button>
        <button @click="handleAction('effect:vhs')"><span class="label">VHS</span></button>
        <button @click="handleAction('effect:rgb-split')"><span class="label">RGB Split</span></button>
        <button @click="handleAction('effect:scanlines')"><span class="label">Scanlines</span></button>
        <button @click="handleAction('effect:halftone')"><span class="label">Halftone</span></button>
        <button @click="handleAction('effect:dither')"><span class="label">Dither</span></button>
        <button @click="handleAction('effect:emboss')"><span class="label">Emboss</span></button>
        <button @click="handleAction('effect:find-edges')"><span class="label">Find Edges</span></button>
        <button @click="handleAction('effect:mosaic')"><span class="label">Mosaic</span></button>

        <div class="separator"></div>

        <!-- Generate -->
        <div class="menu-section-label">Generate</div>
        <button @click="handleAction('effect:fill')"><span class="label">Fill</span></button>
        <button @click="handleAction('effect:gradient-ramp')"><span class="label">Gradient Ramp</span></button>
        <button @click="handleAction('effect:fractal-noise')"><span class="label">Fractal Noise</span></button>
        <button @click="handleAction('effect:add-grain')"><span class="label">Add Grain</span></button>
        <button @click="handleAction('effect:radio-waves')"><span class="label">Radio Waves</span></button>
        <button @click="handleAction('effect:ellipse')"><span class="label">Ellipse</span></button>

        <div class="separator"></div>

        <!-- Audio Visualization -->
        <div class="menu-section-label">Audio Visualization</div>
        <button @click="handleAction('effect:audio-spectrum')"><span class="label">Audio Spectrum</span></button>
        <button @click="handleAction('effect:audio-waveform')"><span class="label">Audio Waveform</span></button>

        <div class="separator"></div>

        <!-- Time Effects -->
        <div class="menu-section-label">Time</div>
        <button @click="handleAction('effect:echo')"><span class="label">Echo</span></button>
        <button @click="handleAction('effect:posterize-time')"><span class="label">Posterize Time</span></button>
        <button @click="handleAction('effect:time-displacement')"><span class="label">Time Displacement</span></button>

        <div class="separator"></div>

        <!-- Expression Controls -->
        <div class="menu-section-label">Expression Controls</div>
        <button @click="handleAction('effect:slider-control')"><span class="label">Slider Control</span></button>
        <button @click="handleAction('effect:checkbox-control')"><span class="label">Checkbox Control</span></button>
        <button @click="handleAction('effect:color-control')"><span class="label">Color Control</span></button>
        <button @click="handleAction('effect:point-control')"><span class="label">Point Control</span></button>
        <button @click="handleAction('effect:angle-control')"><span class="label">Angle Control</span></button>
        <button @click="handleAction('effect:dropdown-menu-control')"><span class="label">Dropdown Menu Control</span></button>
        <button @click="handleAction('effect:layer-control')"><span class="label">Layer Control</span></button>

        <div class="separator"></div>
        <button @click="handleAction('removeAllEffects')" :disabled="!hasSelection">
          <span class="label">Remove All Effects</span>
        </button>
      </div>
    </div>

    <!-- Layer Menu -->
    <div class="menu-item" @mouseenter="openMenu('layer')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'layer' }"
        @click="toggleMenu('layer')"
      >
        Layer
      </button>
      <div v-if="activeMenu === 'layer'" class="menu-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <button @click="handleAction('precompose')" :disabled="!hasSelection">
          <span class="label">Pre-compose...</span>
          <span class="shortcut">Ctrl+Shift+C</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('splitLayer')" :disabled="!hasSelection">
          <span class="label">Split Layer</span>
          <span class="shortcut">Ctrl+Shift+D</span>
        </button>
        <button @click="handleAction('timeStretch')" :disabled="!hasSelection">
          <span class="label">Time Stretch...</span>
          <span class="shortcut">Ctrl+Alt+T</span>
        </button>
        <button @click="handleAction('timeReverse')" :disabled="!hasSelection">
          <span class="label">Time Reverse</span>
          <span class="shortcut">Ctrl+Alt+R</span>
        </button>
        <button @click="handleAction('freezeFrame')" :disabled="!hasSelection">
          <span class="label">Freeze Frame</span>
          <span class="shortcut">Ctrl+Shift+F</span>
        </button>
        <button @click="handleAction('frameInterpolation')" :disabled="!hasSelection">
          <span class="label">Frame Interpolation (RIFE)...</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('lockLayer')" :disabled="!hasSelection">
          <span class="label">Lock Layer</span>
          <span class="shortcut">Ctrl+L</span>
        </button>
        <button @click="handleAction('toggleVisibility')" :disabled="!hasSelection">
          <span class="label">Show/Hide Layer</span>
        </button>
        <button @click="handleAction('isolateLayer')" :disabled="!hasSelection">
          <span class="label">Isolate (Solo)</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('bringToFront')" :disabled="!hasSelection">
          <span class="label">Bring to Front</span>
          <span class="shortcut">Ctrl+Shift+]</span>
        </button>
        <button @click="handleAction('sendToBack')" :disabled="!hasSelection">
          <span class="label">Send to Back</span>
          <span class="shortcut">Ctrl+Shift+[</span>
        </button>
        <button @click="handleAction('bringForward')" :disabled="!hasSelection">
          <span class="label">Bring Forward</span>
          <span class="shortcut">Ctrl+]</span>
        </button>
        <button @click="handleAction('sendBackward')" :disabled="!hasSelection">
          <span class="label">Send Backward</span>
          <span class="shortcut">Ctrl+[</span>
        </button>
      </div>
    </div>

    <!-- View Menu -->
    <div class="menu-item" @mouseenter="openMenu('view')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'view' }"
        @click="toggleMenu('view')"
      >
        View
      </button>
      <div v-if="activeMenu === 'view'" class="menu-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <button @click="handleAction('zoomIn')">
          <span class="label">Zoom In</span>
          <span class="shortcut">Ctrl+=</span>
        </button>
        <button @click="handleAction('zoomOut')">
          <span class="label">Zoom Out</span>
          <span class="shortcut">Ctrl+-</span>
        </button>
        <button @click="handleAction('zoomFit')">
          <span class="label">Fit in Window</span>
          <span class="shortcut">Ctrl+0</span>
        </button>
        <button @click="handleAction('zoom100')">
          <span class="label">100%</span>
          <span class="shortcut">Ctrl+Shift+0</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('toggleGrid')">
          <span class="label">{{ showGrid ? '✓ ' : '' }}Show Grid</span>
          <span class="shortcut">Ctrl+'</span>
        </button>
        <button @click="handleAction('toggleRulers')">
          <span class="label">{{ showRulers ? '✓ ' : '' }}Show Rulers</span>
          <span class="shortcut">Ctrl+R</span>
        </button>
        <button @click="handleAction('toggleGuides')">
          <span class="label">{{ showGuides ? '✓ ' : '' }}Show Guides</span>
          <span class="shortcut">Ctrl+;</span>
        </button>
        <button @click="handleAction('toggleSafeZones')">
          <span class="label">{{ showSafeZones ? '✓ ' : '' }}Safe Zones</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('toggleTransparency')">
          <span class="label">{{ showTransparency ? '✓ ' : '' }}Transparency Grid</span>
          <span class="shortcut">Ctrl+Shift+H</span>
        </button>
        <button @click="handleAction('toggleMotionBlur')">
          <span class="label">{{ showMotionBlur ? '✓ ' : '' }}Motion Blur</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('toggleCurveEditor')">
          <span class="label">Curve Editor</span>
          <span class="shortcut">Shift+G</span>
        </button>
      </div>
    </div>

    <!-- Window Menu -->
    <div class="menu-item" @mouseenter="openMenu('window')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'window' }"
        @click="toggleMenu('window')"
      >
        Window
      </button>
      <div v-if="activeMenu === 'window'" class="menu-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <button @click="handleAction('showProperties')">
          <span class="label">Properties</span>
        </button>
        <button @click="handleAction('showEffects')">
          <span class="label">Effects</span>
        </button>
        <button @click="handleAction('showCamera')">
          <span class="label">Camera</span>
        </button>
        <button @click="handleAction('showAudio')">
          <span class="label">Audio</span>
        </button>
        <button @click="handleAction('showAlign')">
          <span class="label">Align</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('showAIChat')">
          <span class="label">AI Chat</span>
        </button>
        <button @click="handleAction('showAIGenerate')">
          <span class="label">AI Generate</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('showExport')">
          <span class="label">Export</span>
        </button>
        <button @click="handleAction('showPreview')">
          <span class="label">Preview</span>
        </button>
      </div>
    </div>

    <!-- Help Menu -->
    <div class="menu-item" @mouseenter="openMenu('help')" @mouseleave="scheduleClose">
      <button
        class="menu-trigger"
        :class="{ active: activeMenu === 'help' }"
        @click="toggleMenu('help')"
      >
        Help
      </button>
      <div v-if="activeMenu === 'help'" class="menu-dropdown" @mouseenter="cancelClose" @mouseleave="scheduleClose">
        <button @click="handleAction('showKeyboardShortcuts')">
          <span class="label">Keyboard Shortcuts</span>
          <span class="shortcut">Ctrl+/</span>
        </button>
        <button @click="handleAction('showDocumentation')">
          <span class="label">Documentation</span>
        </button>
        <div class="separator"></div>
        <button @click="handleAction('showAbout')">
          <span class="label">About Lattice Compositor</span>
        </button>
      </div>
    </div>

    <!-- Spacer -->
    <div class="spacer"></div>

    <!-- Project name display -->
    <div class="project-name" :title="hasUnsavedChanges ? 'Project has unsaved changes' : 'Project saved'">
      <span v-if="hasUnsavedChanges" class="unsaved-indicator">*</span>{{ projectName || 'Untitled Project' }}
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";

const emit = defineEmits<{
  (e: "action", action: string): void;
  (e: "showPreferences"): void;
  (e: "showProjectSettings"): void;
}>();

const projectStore = useProjectStore();
const selectionStore = useSelectionStore();

const activeMenu = ref<string | null>(null);
let closeTimeout: ReturnType<typeof setTimeout> | null = null;

// Computed properties
const canUndo = computed(() => projectStore.canUndo());
const canRedo = computed(() => projectStore.canRedo());
const hasSelection = computed(
  () => selectionStore.selectedLayerIds.length > 0,
);
const projectName = computed(() => projectStore.project.meta.name || "");
const hasUnsavedChanges = computed(() => projectStore.hasUnsavedChanges);

// View state (these should come from a view store in a real implementation)
const showGrid = ref(false);
const showRulers = ref(false);
const showGuides = ref(true);
const showSafeZones = ref(false);
const showTransparency = ref(false);
const showMotionBlur = ref(false);

function toggleMenu(menu: string) {
  if (activeMenu.value === menu) {
    activeMenu.value = null;
  } else {
    activeMenu.value = menu;
  }
}

function openMenu(menu: string) {
  if (activeMenu.value !== null) {
    activeMenu.value = menu;
  }
  cancelClose();
}

function scheduleClose() {
  closeTimeout = setTimeout(() => {
    activeMenu.value = null;
  }, 150);
}

function cancelClose() {
  if (closeTimeout) {
    clearTimeout(closeTimeout);
    closeTimeout = null;
  }
}

function handleAction(action: string) {
  activeMenu.value = null;

  // Handle view toggles locally
  switch (action) {
    case "toggleGrid":
      showGrid.value = !showGrid.value;
      break;
    case "toggleRulers":
      showRulers.value = !showRulers.value;
      break;
    case "toggleGuides":
      showGuides.value = !showGuides.value;
      break;
    case "toggleSafeZones":
      showSafeZones.value = !showSafeZones.value;
      break;
    case "toggleTransparency":
      showTransparency.value = !showTransparency.value;
      break;
    case "toggleMotionBlur":
      showMotionBlur.value = !showMotionBlur.value;
      break;
    case "preferences":
      emit("showPreferences");
      return;
    case "projectSettings":
      emit("showProjectSettings");
      return;
  }

  emit("action", action);
}

// Close menu when clicking outside
function handleClickOutside(e: MouseEvent) {
  const target = e.target as HTMLElement;
  if (!target.closest(".menu-bar")) {
    activeMenu.value = null;
  }
}

// Add click listener
if (typeof window !== "undefined") {
  window.addEventListener("click", handleClickOutside);
}
</script>

<style scoped>
.menu-bar {
  display: flex;
  align-items: center;
  height: 28px;
  background: var(--lattice-surface-0);
  border-bottom: 1px solid var(--lattice-surface-3);
  padding: 0 8px;
  font-size: 12px;
  font-weight: 500;
  user-select: none;
}

.menu-item {
  position: relative;
}

.menu-trigger {
  background: transparent;
  border: none;
  color: var(--lattice-text-secondary);
  padding: 4px 10px;
  cursor: pointer;
  border-radius: 4px;
  transition: all 0.15s ease;
}

.menu-trigger:hover,
.menu-trigger.active {
  background: var(--lattice-surface-2);
  color: var(--lattice-text-primary);
}

.menu-dropdown {
  position: absolute;
  top: 100%;
  left: 0;
  min-width: 220px;
  background: var(--lattice-surface-1);
  border: 1px solid var(--lattice-surface-3);
  border-radius: 6px;
  padding: 4px 0;
  box-shadow: 0 8px 24px rgba(0, 0, 0, 0.4);
  z-index: 1000;
}

.menu-dropdown button {
  display: flex;
  align-items: center;
  justify-content: space-between;
  width: 100%;
  padding: 6px 12px;
  background: transparent;
  border: none;
  color: var(--lattice-text-primary);
  cursor: pointer;
  text-align: left;
  font-size: 12px;
}

.menu-dropdown button:hover:not(:disabled) {
  background: var(--lattice-accent-muted);
  color: var(--lattice-text-primary);
}

.menu-dropdown button:disabled {
  color: var(--lattice-text-muted);
  cursor: not-allowed;
}

.menu-dropdown .label {
  flex: 1;
}

.menu-dropdown .shortcut {
  color: var(--lattice-text-muted);
  font-size: 11px;
  margin-left: 24px;
}

.separator {
  height: 1px;
  background: var(--lattice-surface-3);
  margin: 4px 8px;
}

.spacer {
  flex: 1;
}

.project-name {
  color: var(--lattice-text-muted);
  font-size: 11px;
  padding: 0 12px;
  max-width: 200px;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.unsaved-indicator {
  color: var(--lattice-accent);
  font-weight: bold;
  margin-right: 2px;
}

/* Effects Dropdown - Scrollable with sections */
.effects-dropdown {
  max-height: 70vh;
  overflow-y: auto;
  min-width: 240px;
}

.effects-dropdown::-webkit-scrollbar {
  width: 6px;
}

.effects-dropdown::-webkit-scrollbar-track {
  background: var(--lattice-surface-2);
  border-radius: 3px;
}

.effects-dropdown::-webkit-scrollbar-thumb {
  background: var(--lattice-surface-4);
  border-radius: 3px;
}

.effects-dropdown::-webkit-scrollbar-thumb:hover {
  background: var(--lattice-accent-muted);
}

.menu-section-label {
  font-size: 10px;
  font-weight: 600;
  text-transform: uppercase;
  color: var(--lattice-text-muted);
  padding: 10px 12px 4px;
  letter-spacing: 0.5px;
  pointer-events: none;
  border-top: 1px solid var(--lattice-surface-3);
  margin-top: 4px;
}

.menu-section-label:first-child {
  border-top: none;
  margin-top: 0;
  padding-top: 6px;
}
</style>
