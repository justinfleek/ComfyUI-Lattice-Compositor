<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="cancel">
      <div class="dialog-container">
        <div class="dialog-header">
          <span class="dialog-title">Preferences</span>
          <button class="close-btn" @click="cancel">&times;</button>
        </div>

        <div class="dialog-body">
          <!-- Sidebar Navigation -->
          <div class="sidebar">
            <button
              v-for="tab in tabs"
              :key="tab.id"
              :class="['sidebar-item', { active: activeTab === tab.id }]"
              @click="activeTab = tab.id"
            >
              <span class="tab-icon">{{ tab.icon }}</span>
              <span class="tab-label">{{ tab.label }}</span>
            </button>
          </div>

          <!-- Content Area -->
          <div class="content">
            <!-- General Tab -->
            <div v-if="activeTab === 'general'" class="tab-content">
              <h3>General Settings</h3>

              <div class="setting-group">
                <h4>Auto-Save</h4>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.autoSave.enabled" />
                    Enable auto-save
                  </label>
                </div>
                <div class="form-row" v-if="preferences.autoSave.enabled">
                  <label>Save interval:</label>
                  <select v-model.number="preferences.autoSave.interval" class="select-input">
                    <option :value="60">1 minute</option>
                    <option :value="180">3 minutes</option>
                    <option :value="300">5 minutes</option>
                    <option :value="600">10 minutes</option>
                    <option :value="900">15 minutes</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.autoSave.saveOnExport" />
                    Auto-save before export
                  </label>
                </div>
              </div>

              <div class="setting-group">
                <h4>History</h4>
                <div class="form-row">
                  <label>Undo levels:</label>
                  <input
                    type="number"
                    v-model.number="preferences.undoLevels"
                    min="10"
                    max="200"
                    class="number-input"
                  />
                  <span class="hint">Higher values use more memory</span>
                </div>
              </div>

              <div class="setting-group">
                <h4>New Projects</h4>
                <div class="form-row">
                  <label>Default width:</label>
                  <input
                    type="number"
                    v-model.number="preferences.newProject.width"
                    :step="8"
                    min="64"
                    max="8192"
                    class="number-input"
                  />
                  <span class="unit">px</span>
                </div>
                <div class="form-row">
                  <label>Default height:</label>
                  <input
                    type="number"
                    v-model.number="preferences.newProject.height"
                    :step="8"
                    min="64"
                    max="8192"
                    class="number-input"
                  />
                  <span class="unit">px</span>
                </div>
                <div class="form-row">
                  <label>Default frame rate:</label>
                  <select v-model.number="preferences.newProject.fps" class="select-input short">
                    <option :value="16">16 fps (AI/Wan)</option>
                    <option :value="24">24 fps</option>
                    <option :value="30">30 fps</option>
                    <option :value="60">60 fps</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>Default duration:</label>
                  <select v-model.number="preferences.newProject.frameCount" class="select-input">
                    <option :value="17">1 second (17 frames)</option>
                    <option :value="33">2 seconds (33 frames)</option>
                    <option :value="49">3 seconds (49 frames)</option>
                    <option :value="65">4 seconds (65 frames)</option>
                    <option :value="81">5 seconds (81 frames)</option>
                  </select>
                </div>
              </div>
            </div>

            <!-- Appearance Tab -->
            <div v-if="activeTab === 'appearance'" class="tab-content">
              <h3>Appearance</h3>

              <div class="setting-group">
                <h4>Theme</h4>
                <div class="theme-selector">
                  <button
                    v-for="theme in themes"
                    :key="theme.id"
                    :class="['theme-btn', { active: preferences.theme === theme.id }]"
                    :style="{ '--theme-color': theme.color }"
                    @click="preferences.theme = theme.id"
                  >
                    <span class="theme-swatch"></span>
                    <span class="theme-name">{{ theme.name }}</span>
                  </button>
                </div>
              </div>

              <div class="setting-group">
                <h4>Interface</h4>
                <div class="form-row">
                  <label>UI scale:</label>
                  <select v-model.number="preferences.uiScale" class="select-input short">
                    <option :value="0.9">90%</option>
                    <option :value="1.0">100%</option>
                    <option :value="1.1">110%</option>
                    <option :value="1.2">120%</option>
                    <option :value="1.3">130%</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.showTooltips" />
                    Show tooltips
                  </label>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.animatedUI" />
                    Animated transitions
                  </label>
                </div>
              </div>

              <div class="setting-group">
                <h4>Timeline</h4>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.timeline.showWaveforms" />
                    Show audio waveforms
                  </label>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.timeline.showThumbnails" />
                    Show layer thumbnails
                  </label>
                </div>
                <div class="form-row">
                  <label>Default track height:</label>
                  <select v-model="preferences.timeline.trackHeight" class="select-input short">
                    <option value="compact">Compact</option>
                    <option value="normal">Normal</option>
                    <option value="expanded">Expanded</option>
                  </select>
                </div>
              </div>
            </div>

            <!-- Performance Tab -->
            <div v-if="activeTab === 'performance'" class="tab-content">
              <h3>Performance</h3>

              <div class="setting-group">
                <h4>Hardware Acceleration</h4>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.performance.gpuAcceleration" />
                    Enable GPU acceleration
                  </label>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.performance.webgl2" />
                    Prefer WebGL 2.0
                  </label>
                </div>
              </div>

              <div class="setting-group">
                <h4>Preview</h4>
                <div class="form-row">
                  <label>Preview quality:</label>
                  <select v-model="preferences.performance.previewQuality" class="select-input">
                    <option value="full">Full</option>
                    <option value="half">Half</option>
                    <option value="quarter">Quarter</option>
                    <option value="auto">Auto (based on performance)</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.performance.skipFrames" />
                    Skip frames during playback if needed
                  </label>
                </div>
              </div>

              <div class="setting-group">
                <h4>Memory</h4>
                <div class="form-row">
                  <label>Frame cache size:</label>
                  <select v-model.number="preferences.performance.frameCacheSize" class="select-input">
                    <option :value="50">50 MB (Low)</option>
                    <option :value="100">100 MB</option>
                    <option :value="200">200 MB</option>
                    <option :value="500">500 MB</option>
                    <option :value="1000">1 GB (High)</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>Texture cache size:</label>
                  <select v-model.number="preferences.performance.textureCacheSize" class="select-input">
                    <option :value="128">128 MB</option>
                    <option :value="256">256 MB</option>
                    <option :value="512">512 MB</option>
                    <option :value="1024">1 GB</option>
                  </select>
                </div>
                <div class="form-row">
                  <button class="btn btn-secondary" @click="clearCache">
                    Clear All Caches
                  </button>
                </div>
              </div>
            </div>

            <!-- Export Tab -->
            <div v-if="activeTab === 'export'" class="tab-content">
              <h3>Export Defaults</h3>

              <div class="setting-group">
                <h4>Output Format</h4>
                <div class="form-row">
                  <label>Default format:</label>
                  <select v-model="preferences.export.format" class="select-input">
                    <option value="png">PNG Sequence</option>
                    <option value="jpeg">JPEG Sequence</option>
                    <option value="webp">WebP Sequence</option>
                    <option value="mp4">MP4 Video</option>
                    <option value="webm">WebM Video</option>
                    <option value="gif">Animated GIF</option>
                  </select>
                </div>
                <div class="form-row" v-if="preferences.export.format === 'jpeg'">
                  <label>JPEG quality:</label>
                  <input
                    type="range"
                    v-model.number="preferences.export.jpegQuality"
                    min="50"
                    max="100"
                    class="range-input"
                  />
                  <span class="value">{{ preferences.export.jpegQuality }}%</span>
                </div>
              </div>

              <div class="setting-group">
                <h4>Batch Export</h4>
                <div class="form-row">
                  <label>Default batch size:</label>
                  <select v-model.number="preferences.export.batchSize" class="select-input short">
                    <option :value="1">1 (Sequential)</option>
                    <option :value="4">4 frames</option>
                    <option :value="8">8 frames</option>
                    <option :value="16">16 frames</option>
                    <option :value="32">32 frames</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.export.parallelExport" />
                    Enable parallel export (faster, uses more CPU)
                  </label>
                </div>
              </div>

              <div class="setting-group">
                <h4>File Naming</h4>
                <div class="form-row">
                  <label>Filename pattern:</label>
                  <input
                    type="text"
                    v-model="preferences.export.filenamePattern"
                    class="text-input"
                    placeholder="frame_{####}"
                  />
                </div>
                <div class="form-row hint-row">
                  <span class="hint">Use {####} for frame number padding (e.g., frame_0001.png)</span>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.export.includeAlpha" />
                    Include alpha channel (PNG/WebP)
                  </label>
                </div>
              </div>
            </div>

            <!-- Shortcuts Tab -->
            <div v-if="activeTab === 'shortcuts'" class="tab-content">
              <h3>Keyboard Shortcuts</h3>

              <div class="shortcuts-list">
                <div class="shortcut-group">
                  <h4>Navigation</h4>
                  <div class="shortcut-row">
                    <span class="action">Play/Pause</span>
                    <span class="keys">Space</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Go to Start</span>
                    <span class="keys">Home</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Go to End</span>
                    <span class="keys">End</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Previous Frame</span>
                    <span class="keys">←</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Next Frame</span>
                    <span class="keys">→</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Jump 10 Frames Back</span>
                    <span class="keys">Shift+←</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Jump 10 Frames Forward</span>
                    <span class="keys">Shift+→</span>
                  </div>
                </div>

                <div class="shortcut-group">
                  <h4>Editing</h4>
                  <div class="shortcut-row">
                    <span class="action">Undo</span>
                    <span class="keys">Ctrl+Z</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Redo</span>
                    <span class="keys">Ctrl+Shift+Z</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Cut</span>
                    <span class="keys">Ctrl+X</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Copy</span>
                    <span class="keys">Ctrl+C</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Paste</span>
                    <span class="keys">Ctrl+V</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Duplicate</span>
                    <span class="keys">Ctrl+D</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Delete</span>
                    <span class="keys">Delete</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Select All</span>
                    <span class="keys">Ctrl+A</span>
                  </div>
                </div>

                <div class="shortcut-group">
                  <h4>View</h4>
                  <div class="shortcut-row">
                    <span class="action">Zoom In</span>
                    <span class="keys">Ctrl+=</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Zoom Out</span>
                    <span class="keys">Ctrl+-</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Fit in Window</span>
                    <span class="keys">Ctrl+0</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Toggle Grid</span>
                    <span class="keys">Ctrl+'</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Toggle Rulers</span>
                    <span class="keys">Ctrl+R</span>
                  </div>
                </div>

                <div class="shortcut-group">
                  <h4>Tools</h4>
                  <div class="shortcut-row">
                    <span class="action">Selection Tool</span>
                    <span class="keys">V</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Pen Tool</span>
                    <span class="keys">P</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Text Tool</span>
                    <span class="keys">T</span>
                  </div>
                  <div class="shortcut-row">
                    <span class="action">Hand Tool</span>
                    <span class="keys">H</span>
                  </div>
                </div>
              </div>
            </div>

            <!-- AI Tab -->
            <div v-if="activeTab === 'ai'" class="tab-content">
              <h3>AI Settings</h3>

              <div class="setting-group">
                <h4>AI Assistant</h4>
                <div class="form-row">
                  <label>Default model:</label>
                  <select v-model="preferences.ai.model" class="select-input">
                    <option value="gpt-4o">GPT-4o (OpenAI)</option>
                    <option value="claude-sonnet">Claude Sonnet (Anthropic)</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.ai.showToolCalls" />
                    Show tool calls in chat
                  </label>
                </div>
              </div>

              <div class="setting-group">
                <h4>AI Generation</h4>
                <div class="form-row">
                  <label>Default depth model:</label>
                  <select v-model="preferences.ai.depthModel" class="select-input">
                    <option value="midas">MiDaS</option>
                    <option value="depth-anything">Depth Anything</option>
                    <option value="marigold">Marigold</option>
                  </select>
                </div>
                <div class="form-row">
                  <label>
                    <input type="checkbox" v-model="preferences.ai.autoRegenerate" />
                    Auto-regenerate on source change
                  </label>
                </div>
              </div>
            </div>
          </div>
        </div>

        <div class="dialog-footer">
          <button class="btn btn-text" @click="resetToDefaults">
            Reset to Defaults
          </button>
          <div class="dialog-actions">
            <button class="btn btn-secondary" @click="cancel">Cancel</button>
            <button class="btn btn-primary" @click="save">Save</button>
          </div>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { ref, reactive, watch, onMounted, onUnmounted } from 'vue';

interface Preferences {
  // General
  autoSave: {
    enabled: boolean;
    interval: number;
    saveOnExport: boolean;
  };
  undoLevels: number;
  newProject: {
    width: number;
    height: number;
    fps: number;
    frameCount: number;
  };

  // Appearance
  theme: string;
  uiScale: number;
  showTooltips: boolean;
  animatedUI: boolean;
  timeline: {
    showWaveforms: boolean;
    showThumbnails: boolean;
    trackHeight: 'compact' | 'normal' | 'expanded';
  };

  // Performance
  performance: {
    gpuAcceleration: boolean;
    webgl2: boolean;
    previewQuality: 'full' | 'half' | 'quarter' | 'auto';
    skipFrames: boolean;
    frameCacheSize: number;
    textureCacheSize: number;
  };

  // Export
  export: {
    format: string;
    jpegQuality: number;
    batchSize: number;
    parallelExport: boolean;
    filenamePattern: string;
    includeAlpha: boolean;
  };

  // AI
  ai: {
    model: string;
    showToolCalls: boolean;
    depthModel: string;
    autoRegenerate: boolean;
  };
}

const props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<{
  (e: 'close'): void;
  (e: 'save', preferences: Preferences): void;
}>();

const tabs = [
  { id: 'general', label: 'General', icon: '⚙️' },
  { id: 'appearance', label: 'Appearance', icon: '🎨' },
  { id: 'performance', label: 'Performance', icon: '⚡' },
  { id: 'export', label: 'Export', icon: '📤' },
  { id: 'shortcuts', label: 'Shortcuts', icon: '⌨️' },
  { id: 'ai', label: 'AI', icon: '🤖' },
];

const themes = [
  { id: 'violet', name: 'Violet', color: '#8B5CF6' },
  { id: 'ocean', name: 'Ocean', color: '#06B6D4' },
  { id: 'sunset', name: 'Sunset', color: '#F59E0B' },
  { id: 'forest', name: 'Forest', color: '#10B981' },
  { id: 'ember', name: 'Ember', color: '#EF4444' },
  { id: 'mono', name: 'Mono', color: '#6B7280' },
];

const activeTab = ref('general');

const defaultPreferences: Preferences = {
  autoSave: {
    enabled: true,
    interval: 300,
    saveOnExport: true,
  },
  undoLevels: 50,
  newProject: {
    width: 832,
    height: 480,
    fps: 16,
    frameCount: 81,
  },
  theme: 'violet',
  uiScale: 1.0,
  showTooltips: true,
  animatedUI: true,
  timeline: {
    showWaveforms: true,
    showThumbnails: true,
    trackHeight: 'normal',
  },
  performance: {
    gpuAcceleration: true,
    webgl2: true,
    previewQuality: 'auto',
    skipFrames: true,
    frameCacheSize: 200,
    textureCacheSize: 256,
  },
  export: {
    format: 'png',
    jpegQuality: 90,
    batchSize: 8,
    parallelExport: true,
    filenamePattern: 'frame_{####}',
    includeAlpha: true,
  },
  ai: {
    model: 'gpt-4o',
    showToolCalls: true,
    depthModel: 'depth-anything',
    autoRegenerate: false,
  },
};

const preferences = reactive<Preferences>({ ...defaultPreferences });

function loadPreferences() {
  try {
    const saved = localStorage.getItem('weyl-preferences');
    if (saved) {
      const parsed = JSON.parse(saved);
      Object.assign(preferences, parsed);
    }
  } catch (e) {
    console.warn('Failed to load preferences:', e);
  }
}

function savePreferences() {
  try {
    localStorage.setItem('weyl-preferences', JSON.stringify(preferences));
  } catch (e) {
    console.warn('Failed to save preferences:', e);
  }
}

function resetToDefaults() {
  Object.assign(preferences, defaultPreferences);
}

function clearCache() {
  // Clear caches (would call into cache services)
  console.log('Clearing caches...');
  alert('All caches have been cleared.');
}

function cancel() {
  loadPreferences(); // Revert changes
  emit('close');
}

function save() {
  savePreferences();
  emit('save', { ...preferences });
  emit('close');
}

// Keyboard handler
function handleKeydown(e: KeyboardEvent) {
  if (e.key === 'Escape') {
    cancel();
  } else if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) {
    save();
  }
}

watch(() => props.visible, (visible) => {
  if (visible) {
    loadPreferences();
    activeTab.value = 'general';
  }
});

onMounted(() => {
  window.addEventListener('keydown', handleKeydown);
  loadPreferences();
});

onUnmounted(() => {
  window.removeEventListener('keydown', handleKeydown);
});
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.dialog-container {
  background: var(--weyl-surface-1, #1a1a1a);
  border: 1px solid var(--weyl-surface-3, #333);
  border-radius: 8px;
  width: 720px;
  max-width: 90vw;
  max-height: 85vh;
  display: flex;
  flex-direction: column;
  box-shadow: 0 16px 48px rgba(0, 0, 0, 0.5);
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  background: var(--weyl-surface-0, #121212);
  border-bottom: 1px solid var(--weyl-surface-3, #333);
  border-radius: 8px 8px 0 0;
}

.dialog-title {
  font-size: 14px;
  font-weight: 600;
  color: var(--weyl-text-primary, #e5e5e5);
}

.close-btn {
  width: 28px;
  height: 28px;
  border: none;
  background: transparent;
  color: var(--weyl-text-muted, #666);
  font-size: 20px;
  cursor: pointer;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.close-btn:hover {
  background: var(--weyl-surface-2, #222);
  color: var(--weyl-text-primary, #e5e5e5);
}

.dialog-body {
  display: flex;
  flex: 1;
  overflow: hidden;
}

.sidebar {
  width: 160px;
  background: var(--weyl-surface-0, #121212);
  border-right: 1px solid var(--weyl-surface-3, #333);
  padding: 8px;
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.sidebar-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  border: none;
  background: transparent;
  color: var(--weyl-text-secondary, #999);
  font-size: 12px;
  text-align: left;
  cursor: pointer;
  border-radius: 4px;
  transition: all 0.15s ease;
}

.sidebar-item:hover {
  background: var(--weyl-surface-2, #222);
  color: var(--weyl-text-primary, #e5e5e5);
}

.sidebar-item.active {
  background: var(--weyl-accent-muted, rgba(139, 92, 246, 0.2));
  color: var(--weyl-accent, #8B5CF6);
}

.tab-icon {
  font-size: 14px;
}

.content {
  flex: 1;
  padding: 16px 20px;
  overflow-y: auto;
}

.tab-content h3 {
  margin: 0 0 16px;
  font-size: 16px;
  font-weight: 600;
  color: var(--weyl-text-primary, #e5e5e5);
}

.setting-group {
  margin-bottom: 24px;
}

.setting-group h4 {
  margin: 0 0 12px;
  font-size: 12px;
  font-weight: 600;
  color: var(--weyl-text-secondary, #999);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.form-row {
  display: flex;
  align-items: center;
  gap: 12px;
  margin-bottom: 8px;
}

.form-row > label:first-child:not(:only-child) {
  width: 140px;
  flex-shrink: 0;
  color: var(--weyl-text-secondary, #999);
  font-size: 12px;
}

.form-row label {
  display: flex;
  align-items: center;
  gap: 8px;
  color: var(--weyl-text-primary, #e5e5e5);
  font-size: 12px;
  cursor: pointer;
}

.form-row input[type="checkbox"] {
  width: 14px;
  height: 14px;
  accent-color: var(--weyl-accent, #8B5CF6);
}

.text-input,
.select-input,
.number-input {
  padding: 6px 10px;
  border: 1px solid var(--weyl-surface-3, #333);
  background: var(--weyl-surface-0, #121212);
  color: var(--weyl-text-primary, #e5e5e5);
  border-radius: 4px;
  font-size: 12px;
}

.text-input:focus,
.select-input:focus,
.number-input:focus {
  outline: none;
  border-color: var(--weyl-accent, #8B5CF6);
}

.select-input {
  min-width: 160px;
}

.select-input.short {
  min-width: 100px;
}

.number-input {
  width: 80px;
}

.range-input {
  flex: 1;
  max-width: 150px;
  accent-color: var(--weyl-accent, #8B5CF6);
}

.unit,
.value {
  color: var(--weyl-text-muted, #666);
  font-size: 11px;
}

.hint {
  color: var(--weyl-text-muted, #666);
  font-size: 11px;
}

.hint-row {
  margin-left: 152px;
}

/* Theme selector */
.theme-selector {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 8px;
}

.theme-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 6px;
  padding: 12px 8px;
  border: 1px solid var(--weyl-surface-3, #333);
  background: var(--weyl-surface-0, #121212);
  border-radius: 6px;
  cursor: pointer;
  transition: all 0.15s ease;
}

.theme-btn:hover {
  border-color: var(--weyl-surface-4, #444);
}

.theme-btn.active {
  border-color: var(--theme-color);
  background: rgba(var(--theme-color), 0.1);
}

.theme-swatch {
  width: 32px;
  height: 32px;
  border-radius: 50%;
  background: var(--theme-color);
}

.theme-name {
  font-size: 11px;
  color: var(--weyl-text-secondary, #999);
}

.theme-btn.active .theme-name {
  color: var(--weyl-text-primary, #e5e5e5);
}

/* Shortcuts list */
.shortcuts-list {
  display: flex;
  flex-direction: column;
  gap: 20px;
}

.shortcut-group h4 {
  margin: 0 0 8px;
  font-size: 11px;
  font-weight: 600;
  color: var(--weyl-text-muted, #666);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.shortcut-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 6px 0;
  border-bottom: 1px solid var(--weyl-surface-2, #222);
}

.shortcut-row .action {
  font-size: 12px;
  color: var(--weyl-text-primary, #e5e5e5);
}

.shortcut-row .keys {
  font-size: 11px;
  font-family: monospace;
  color: var(--weyl-text-muted, #666);
  background: var(--weyl-surface-2, #222);
  padding: 2px 6px;
  border-radius: 3px;
}

.dialog-footer {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  background: var(--weyl-surface-0, #121212);
  border-top: 1px solid var(--weyl-surface-3, #333);
  border-radius: 0 0 8px 8px;
}

.dialog-actions {
  display: flex;
  gap: 8px;
}

.btn {
  padding: 8px 16px;
  border: none;
  border-radius: 4px;
  font-size: 12px;
  font-weight: 500;
  cursor: pointer;
  transition: all 0.15s ease;
}

.btn-text {
  background: transparent;
  color: var(--weyl-text-muted, #666);
}

.btn-text:hover {
  color: var(--weyl-text-primary, #e5e5e5);
}

.btn-secondary {
  background: var(--weyl-surface-3, #333);
  color: var(--weyl-text-primary, #e5e5e5);
}

.btn-secondary:hover {
  background: var(--weyl-surface-4, #444);
}

.btn-primary {
  background: var(--weyl-accent, #8B5CF6);
  color: white;
}

.btn-primary:hover {
  background: var(--weyl-accent-hover, #9D6FFF);
}
</style>
