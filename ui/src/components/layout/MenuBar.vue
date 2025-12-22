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
          <span class="label">About Weyl Compositor</span>
        </button>
      </div>
    </div>

    <!-- Spacer -->
    <div class="spacer"></div>

    <!-- Project name display -->
    <div class="project-name">
      {{ projectName || 'Untitled Project' }}
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { useHistoryStore } from '@/stores/historyStore';

const emit = defineEmits<{
  (e: 'action', action: string): void;
  (e: 'showPreferences'): void;
  (e: 'showProjectSettings'): void;
}>();

const compositorStore = useCompositorStore();
const historyStore = useHistoryStore();

const activeMenu = ref<string | null>(null);
let closeTimeout: ReturnType<typeof setTimeout> | null = null;

// Computed properties
const canUndo = computed(() => historyStore.canUndo);
const canRedo = computed(() => historyStore.canRedo);
const hasSelection = computed(() => compositorStore.selectedLayerIds.length > 0);
const projectName = computed(() => compositorStore.project?.name || '');

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
    case 'toggleGrid':
      showGrid.value = !showGrid.value;
      break;
    case 'toggleRulers':
      showRulers.value = !showRulers.value;
      break;
    case 'toggleGuides':
      showGuides.value = !showGuides.value;
      break;
    case 'toggleSafeZones':
      showSafeZones.value = !showSafeZones.value;
      break;
    case 'toggleTransparency':
      showTransparency.value = !showTransparency.value;
      break;
    case 'toggleMotionBlur':
      showMotionBlur.value = !showMotionBlur.value;
      break;
    case 'preferences':
      emit('showPreferences');
      return;
    case 'projectSettings':
      emit('showProjectSettings');
      return;
  }

  emit('action', action);
}

// Close menu when clicking outside
function handleClickOutside(e: MouseEvent) {
  const target = e.target as HTMLElement;
  if (!target.closest('.menu-bar')) {
    activeMenu.value = null;
  }
}

// Add click listener
if (typeof window !== 'undefined') {
  window.addEventListener('click', handleClickOutside);
}
</script>

<style scoped>
.menu-bar {
  display: flex;
  align-items: center;
  height: 28px;
  background: var(--weyl-surface-0);
  border-bottom: 1px solid var(--weyl-surface-3);
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
  color: var(--weyl-text-secondary);
  padding: 4px 10px;
  cursor: pointer;
  border-radius: 4px;
  transition: all 0.15s ease;
}

.menu-trigger:hover,
.menu-trigger.active {
  background: var(--weyl-surface-2);
  color: var(--weyl-text-primary);
}

.menu-dropdown {
  position: absolute;
  top: 100%;
  left: 0;
  min-width: 220px;
  background: var(--weyl-surface-1);
  border: 1px solid var(--weyl-surface-3);
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
  color: var(--weyl-text-primary);
  cursor: pointer;
  text-align: left;
  font-size: 12px;
}

.menu-dropdown button:hover:not(:disabled) {
  background: var(--weyl-accent-muted);
  color: var(--weyl-text-primary);
}

.menu-dropdown button:disabled {
  color: var(--weyl-text-muted);
  cursor: not-allowed;
}

.menu-dropdown .label {
  flex: 1;
}

.menu-dropdown .shortcut {
  color: var(--weyl-text-muted);
  font-size: 11px;
  margin-left: 24px;
}

.separator {
  height: 1px;
  background: var(--weyl-surface-3);
  margin: 4px 8px;
}

.spacer {
  flex: 1;
}

.project-name {
  color: var(--weyl-text-muted);
  font-size: 11px;
  padding: 0 12px;
  max-width: 200px;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}
</style>
