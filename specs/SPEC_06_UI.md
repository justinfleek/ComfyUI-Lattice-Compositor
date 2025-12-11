# 8. VUE COMPONENTS

## 8.1 Main App Entry (ui/src/main.ts)

```typescript
/**
 * Vue Application Entry Point
 */
import { createApp } from 'vue';
import { createPinia } from 'pinia';
import PrimeVue from 'primevue/config';
import App from './App.vue';

// PrimeVue components we'll use
import Button from 'primevue/button';
import Slider from 'primevue/slider';
import Dropdown from 'primevue/dropdown';
import InputText from 'primevue/inputtext';
import InputNumber from 'primevue/inputnumber';
import ColorPicker from 'primevue/colorpicker';
import Dialog from 'primevue/dialog';
import Tooltip from 'primevue/tooltip';

// Styles
import 'primevue/resources/themes/lara-dark-blue/theme.css';
import 'primeicons/primeicons.css';

const app = createApp(App);

// Pinia for state management
const pinia = createPinia();
app.use(pinia);

// PrimeVue
app.use(PrimeVue);

// Register components
app.component('Button', Button);
app.component('Slider', Slider);
app.component('Dropdown', Dropdown);
app.component('InputText', InputText);
app.component('InputNumber', InputNumber);
app.component('ColorPicker', ColorPicker);
app.component('Dialog', Dialog);
app.directive('tooltip', Tooltip);

// Mount
app.mount('#weyl-compositor-root');

// Listen for messages from ComfyUI
window.addEventListener('weyl:inputs-ready', (event: any) => {
  const { useCompositorStore } = await import('./stores/compositorStore');
  const store = useCompositorStore();
  store.loadInputs(event.detail);
});

window.addEventListener('weyl:keydown', (event: any) => {
  const { useKeyboardService } = await import('./services/keyboardService');
  useKeyboardService().handleKeydown(event.detail);
});

console.log('[Weyl] Vue app mounted');
```

## 8.2 Main Layout Component (ui/src/App.vue)

```vue
<template>
  <div class="weyl-compositor">
    <!-- Toolbar -->
    <div class="toolbar">
      <div class="tool-group">
        <Button
          icon="pi pi-arrow-up-right"
          :class="{ active: uiStore.currentTool === 'select' }"
          @click="uiStore.setTool('select')"
          v-tooltip="'Select (V)'"
        />
        <Button
          icon="pi pi-pencil"
          :class="{ active: uiStore.currentTool === 'pen' }"
          @click="uiStore.setTool('pen')"
          v-tooltip="'Pen Tool (P)'"
        />
        <Button
          icon="pi pi-align-left"
          :class="{ active: uiStore.currentTool === 'text' }"
          @click="uiStore.setTool('text')"
          v-tooltip="'Text Tool (T)'"
        />
      </div>

      <div class="tool-group">
        <Button
          icon="pi pi-play"
          v-if="!compositorStore.isPlaying"
          @click="compositorStore.play()"
          v-tooltip="'Play (Space)'"
        />
        <Button
          icon="pi pi-pause"
          v-else
          @click="compositorStore.pause()"
          v-tooltip="'Pause (Space)'"
        />
        <Button
          icon="pi pi-step-backward"
          @click="compositorStore.goToStart()"
          v-tooltip="'Go to Start (Home)'"
        />
        <Button
          icon="pi pi-step-forward"
          @click="compositorStore.goToEnd()"
          v-tooltip="'Go to End (End)'"
        />
      </div>

      <div class="tool-group">
        <span class="frame-display">
          Frame: {{ compositorStore.currentFrame }} / 80
        </span>
      </div>

      <div class="tool-group right">
        <Button
          icon="pi pi-download"
          label="Export Matte"
          @click="showExportDialog = true"
        />
      </div>
    </div>

    <!-- Main Content Area -->
    <div class="main-content">
      <!-- Composition Canvas -->
      <CompositionCanvas class="canvas-area" />

      <!-- Properties Panel -->
      <PropertiesPanel class="properties-panel" />
    </div>

    <!-- Timeline -->
    <TimelinePanel class="timeline-area" />

    <!-- Graph Editor (collapsible) -->
    <GraphEditor
      v-if="uiStore.graphEditorVisible"
      class="graph-editor-area"
    />

    <!-- Export Dialog -->
    <ExportDialog
      v-model:visible="showExportDialog"
    />
  </div>
</template>

<script setup lang="ts">
import { ref } from 'vue';
import { useCompositorStore } from './stores/compositorStore';
import { useUIStore } from './stores/uiStore';

import CompositionCanvas from './components/canvas/CompositionCanvas.vue';
import TimelinePanel from './components/timeline/TimelinePanel.vue';
import PropertiesPanel from './components/properties/PropertiesPanel.vue';
import GraphEditor from './components/graph-editor/GraphEditor.vue';
import ExportDialog from './components/dialogs/ExportDialog.vue';

const compositorStore = useCompositorStore();
const uiStore = useUIStore();

const showExportDialog = ref(false);
</script>

<style scoped>
.weyl-compositor {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-family: system-ui, -apple-system, sans-serif;
}

.toolbar {
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 8px 12px;
  background: #2d2d2d;
  border-bottom: 1px solid #3d3d3d;
}

.tool-group {
  display: flex;
  align-items: center;
  gap: 4px;
}

.tool-group.right {
  margin-left: auto;
}

.frame-display {
  font-size: 12px;
  font-variant-numeric: tabular-nums;
  background: #1e1e1e;
  padding: 4px 8px;
  border-radius: 4px;
}

.main-content {
  display: flex;
  flex: 1;
  min-height: 0;
}

.canvas-area {
  flex: 1;
  min-width: 0;
}

.properties-panel {
  width: 280px;
  border-left: 1px solid #3d3d3d;
}

.timeline-area {
  height: 200px;
  border-top: 1px solid #3d3d3d;
}

.graph-editor-area {
  height: 180px;
  border-top: 1px solid #3d3d3d;
}

:deep(.p-button) {
  padding: 6px 8px;
}

:deep(.p-button.active) {
  background: #4a90d9;
}
</style>
```

---

# 9. STATE MANAGEMENT

## 9.1 Compositor Store (ui/src/stores/compositorStore.ts)

```typescript
/**
 * Main Compositor Store
 *
 * Manages project state, layers, playback, and ComfyUI communication.
 */
import { defineStore } from 'pinia';
import type {
  WeylProject,
  Layer,
  AnimatableProperty,
  Keyframe,
  SplineData,
  TextData
} from '@/types/project';
import { interpolateProperty } from '@/services/interpolation';

interface CompositorState {
  project: WeylProject | null;
  currentFrame: number;
  isPlaying: boolean;
  playbackStartTime: number | null;
  playbackStartFrame: number;
  comfyuiNodeId: string | null;
}

export const useCompositorStore = defineStore('compositor', {
  state: (): CompositorState => ({
    project: null,
    currentFrame: 0,
    isPlaying: false,
    playbackStartTime: null,
    playbackStartFrame: 0,
    comfyuiNodeId: null
  }),

  getters: {
    /**
     * Get current time in seconds
     */
    currentTime: (state): number => {
      if (!state.project) return 0;
      return state.currentFrame / state.project.composition.fps;
    },

    /**
     * Get all visible layers
     */
    visibleLayers: (state): Layer[] => {
      if (!state.project) return [];
      return state.project.layers.filter(l => l.visible);
    },

    /**
     * Get layers active at current frame
     */
    activeLayersAtCurrentFrame: (state): Layer[] => {
      if (!state.project) return [];
      return state.project.layers.filter(l =>
        l.visible &&
        state.currentFrame >= l.inPoint &&
        state.currentFrame <= l.outPoint
      );
    }
  },

  actions: {
    /**
     * Load inputs from ComfyUI node
     */
    loadInputs(inputs: {
      node_id: string;
      source_image: string;
      depth_map: string;
      width: number;
      height: number;
      frame_count: number;
    }): void {
      this.comfyuiNodeId = inputs.node_id;

      // Create new project
      this.project = {
        version: "1.0.0",
        meta: {
          name: "Untitled",
          created: new Date().toISOString(),
          modified: new Date().toISOString()
        },
        composition: {
          width: inputs.width,
          height: inputs.height,
          frameCount: inputs.frame_count as 81,
          fps: 16,
          duration: inputs.frame_count / 16,
          backgroundColor: '#000000'
        },
        assets: {
          source: {
            id: 'source',
            type: 'image',
            source: 'comfyui_node',
            nodeId: inputs.node_id,
            width: inputs.width,
            height: inputs.height,
            data: inputs.source_image
          },
          depth: {
            id: 'depth',
            type: 'depth_map',
            source: 'comfyui_node',
            nodeId: inputs.node_id,
            width: inputs.width,
            height: inputs.height,
            data: inputs.depth_map
          }
        },
        layers: [
          this.createDepthLayer()
        ],
        currentFrame: 0
      };
    },

    /**
     * Create default depth layer
     */
    createDepthLayer(): Layer {
      return {
        id: 'depth_layer',
        name: 'Depth Map',
        type: 'depth',
        visible: true,
        locked: true,
        solo: false,
        inPoint: 0,
        outPoint: 80,
        parentId: null,
        blendMode: 'normal',
        opacity: this.createAnimatableProperty('opacity', 0.5),
        transform: this.createDefaultTransform(),
        properties: [],
        data: null
      };
    },

    /**
     * Create a new spline layer
     */
    addSplineLayer(): Layer {
      const layer: Layer = {
        id: `spline_${Date.now()}`,
        name: `Spline ${(this.project?.layers.filter(l => l.type === 'spline').length || 0) + 1}`,
        type: 'spline',
        visible: true,
        locked: false,
        solo: false,
        inPoint: 0,
        outPoint: 80,
        parentId: null,
        blendMode: 'normal',
        opacity: this.createAnimatableProperty('opacity', 1),
        transform: this.createDefaultTransform(),
        properties: [],
        data: {
          pathData: '',
          controlPoints: [],
          closed: false,
          stroke: '#00ff00',
          strokeWidth: 2,
          fill: ''
        } as SplineData
      };

      this.project?.layers.push(layer);
      return layer;
    },

    /**
     * Create a new text layer
     */
    addTextLayer(text: string = 'Text'): Layer {
      const layer: Layer = {
        id: `text_${Date.now()}`,
        name: text.substring(0, 20),
        type: 'text',
        visible: true,
        locked: false,
        solo: false,
        inPoint: 0,
        outPoint: 80,
        parentId: null,
        blendMode: 'normal',
        opacity: this.createAnimatableProperty('opacity', 1),
        transform: this.createDefaultTransform(),
        properties: [
          this.createAnimatableProperty('fontSize', 48),
          this.createAnimatableProperty('letterSpacing', 0),
          this.createAnimatableProperty('pathOffset', 0)
        ],
        data: {
          text,
          fontFamily: 'Arial',
          fontSize: 48,
          fontWeight: '400',
          fontStyle: 'normal',
          fill: '#ffffff',
          stroke: '',
          strokeWidth: 0,
          letterSpacing: 0,
          lineHeight: 1.2,
          textAlign: 'left',
          pathLayerId: null,
          pathOffset: 0,
          pathAlign: 'left'
        } as TextData
      };

      this.project?.layers.push(layer);
      return layer;
    },

    /**
     * Create animatable property helper
     */
    createAnimatableProperty<T>(name: string, value: T): AnimatableProperty<T> {
      return {
        id: `prop_${name}_${Date.now()}`,
        name,
        type: typeof value === 'number' ? 'number' :
              typeof value === 'object' && value !== null && 'x' in value ? 'position' :
              'number',
        value,
        animated: false,
        keyframes: []
      };
    },

    /**
     * Create default transform
     */
    createDefaultTransform() {
      return {
        position: this.createAnimatableProperty('position', { x: 0, y: 0 }),
        anchor: { x: 0, y: 0 },
        scale: this.createAnimatableProperty('scale', { x: 1, y: 1 }),
        rotation: this.createAnimatableProperty('rotation', 0)
      };
    },

    /**
     * Add keyframe to property
     */
    addKeyframe(layerId: string, propertyPath: string, value: any): void {
      const layer = this.project?.layers.find(l => l.id === layerId);
      if (!layer) return;

      let property: AnimatableProperty<any> | undefined;

      // Handle transform properties
      if (propertyPath.startsWith('transform.')) {
        const transformProp = propertyPath.split('.')[1] as keyof typeof layer.transform;
        property = layer.transform[transformProp] as AnimatableProperty<any>;
      } else {
        property = layer.properties.find(p => p.name === propertyPath);
      }

      if (!property) return;

      // Enable animation
      property.animated = true;

      // Check for existing keyframe at this frame
      const existingIndex = property.keyframes.findIndex(k => k.frame === this.currentFrame);

      const newKeyframe: Keyframe<any> = {
        id: `kf_${Date.now()}`,
        frame: this.currentFrame,
        value,
        interpolation: 'bezier',
        inHandle: { x: 0.33, y: 0.33 },
        outHandle: { x: 0.33, y: 0.33 },
        handlesBroken: false
      };

      if (existingIndex >= 0) {
        property.keyframes[existingIndex] = newKeyframe;
      } else {
        property.keyframes.push(newKeyframe);
        property.keyframes.sort((a, b) => a.frame - b.frame);
      }
    },

    /**
     * Get interpolated property value at current frame
     */
    getPropertyValue<T>(property: AnimatableProperty<T>): T {
      return interpolateProperty(property, this.currentFrame);
    },

    /**
     * Playback controls
     */
    play(): void {
      this.isPlaying = true;
      this.playbackStartTime = performance.now();
      this.playbackStartFrame = this.currentFrame;

      this.playbackLoop();
    },

    pause(): void {
      this.isPlaying = false;
      this.playbackStartTime = null;
    },

    playbackLoop(): void {
      if (!this.isPlaying || !this.project) return;

      const elapsed = performance.now() - (this.playbackStartTime || 0);
      const fps = this.project.composition.fps;
      const frameCount = this.project.composition.frameCount;

      const elapsedFrames = Math.floor((elapsed / 1000) * fps);
      let newFrame = this.playbackStartFrame + elapsedFrames;

      // Loop
      if (newFrame >= frameCount) {
        newFrame = 0;
        this.playbackStartFrame = 0;
        this.playbackStartTime = performance.now();
      }

      this.currentFrame = newFrame;

      requestAnimationFrame(() => this.playbackLoop());
    },

    goToStart(): void {
      this.currentFrame = 0;
    },

    goToEnd(): void {
      this.currentFrame = (this.project?.composition.frameCount || 81) - 1;
    },

    setFrame(frame: number): void {
      if (!this.project) return;
      this.currentFrame = Math.max(0, Math.min(frame, this.project.composition.frameCount - 1));
    },

    /**
     * Save project to JSON
     */
    exportProjectJSON(): string {
      return JSON.stringify(this.project, null, 2);
    },

    /**
     * Load project from JSON
     */
    loadProject(json: string | object): void {
      this.project = typeof json === 'string' ? JSON.parse(json) : json;
    }
  }
});
```

## 9.2 History Store (ui/src/stores/historyStore.ts)

```typescript
/**
 * Undo/Redo History Store
 */
import { defineStore } from 'pinia';
import { useCompositorStore } from './compositorStore';

interface HistoryEntry {
  timestamp: number;
  description: string;
  snapshot: string;
}

export const useHistoryStore = defineStore('history', {
  state: () => ({
    past: [] as HistoryEntry[],
    future: [] as HistoryEntry[],
    maxHistory: 50
  }),

  getters: {
    canUndo: (state) => state.past.length > 0,
    canRedo: (state) => state.future.length > 0
  },

  actions: {
    /**
     * Push current state to history before making changes
     */
    pushState(description: string): void {
      const compositorStore = useCompositorStore();

      if (!compositorStore.project) return;

      this.past.push({
        timestamp: Date.now(),
        description,
        snapshot: JSON.stringify(compositorStore.project)
      });

      // Clear future on new action
      this.future = [];

      // Limit history size
      if (this.past.length > this.maxHistory) {
        this.past.shift();
      }
    },

    /**
     * Undo last action
     */
    undo(): void {
      if (this.past.length === 0) return;

      const compositorStore = useCompositorStore();

      // Save current to future
      if (compositorStore.project) {
        this.future.push({
          timestamp: Date.now(),
          description: 'Redo point',
          snapshot: JSON.stringify(compositorStore.project)
        });
      }

      // Restore previous
      const previous = this.past.pop()!;
      compositorStore.loadProject(previous.snapshot);
    },

    /**
     * Redo last undone action
     */
    redo(): void {
      if (this.future.length === 0) return;

      const compositorStore = useCompositorStore();

      // Save current to past
      if (compositorStore.project) {
        this.past.push({
          timestamp: Date.now(),
          description: 'Undo point',
          snapshot: JSON.stringify(compositorStore.project)
        });
      }

      // Restore future
      const next = this.future.pop()!;
      compositorStore.loadProject(next.snapshot);
    },

    /**
     * Clear all history
     */
    clear(): void {
      this.past = [];
      this.future = [];
    }
  }
});
```
