<template>
  <div class="view-options-toolbar">
    <!-- View Options Group -->
    <div class="toolbar-group">
      <button
        :class="{ active: viewOptions.showGrid }"
        @click="toggleOption('showGrid')"
        title="Toggle Grid (G)"
      >
        <span class="icon">⊞</span>
        <span class="label">Grid</span>
      </button>

      <button
        :class="{ active: viewOptions.show3DReferenceAxes }"
        @click="toggleOption('show3DReferenceAxes')"
        title="Toggle 3D Axes (Shift+A)"
      >
        <span class="icon">⊕</span>
        <span class="label">Axes</span>
      </button>

      <button
        :class="{ active: viewOptions.showRulers }"
        @click="toggleOption('showRulers')"
        title="Toggle Rulers"
      >
        <span class="icon">📏</span>
        <span class="label">Rulers</span>
      </button>

      <button
        :class="{ active: viewOptions.showCompositionBounds }"
        @click="toggleOption('showCompositionBounds')"
        title="Toggle Composition Bounds (C)"
      >
        <span class="icon">⬚</span>
        <span class="label">Bounds</span>
      </button>
    </div>

    <div class="separator" />

    <!-- Layer Options Group -->
    <div class="toolbar-group">
      <button
        :class="{ active: viewOptions.showLayerHandles }"
        @click="toggleOption('showLayerHandles')"
        title="Toggle Layer Handles (H)"
      >
        <span class="icon">◉</span>
        <span class="label">Handles</span>
      </button>

      <button
        :class="{ active: viewOptions.showLayerPaths }"
        @click="toggleOption('showLayerPaths')"
        title="Toggle Layer Motion Paths"
      >
        <span class="icon">⌇</span>
        <span class="label">Paths</span>
      </button>
    </div>

    <div class="separator" />

    <!-- Camera Options Group -->
    <div class="toolbar-group">
      <select
        :value="viewOptions.cameraWireframes"
        @change="setCameraWireframes(($event.target as HTMLSelectElement).value as WireframeVisibility)"
        title="Camera Wireframe Display"
        class="wireframe-select"
      >
        <option value="off">No Cam Wire</option>
        <option value="selected">Selected Cam</option>
        <option value="always">All Cameras</option>
      </select>

      <button
        :class="{ active: viewOptions.showFocalPlane }"
        @click="toggleOption('showFocalPlane')"
        title="Toggle Focal Plane"
      >
        <span class="icon">⌀</span>
        <span class="label">Focus</span>
      </button>
    </div>

    <div class="separator" />

    <!-- View Preset Buttons -->
    <div class="toolbar-group view-presets">
      <button @click="setView('front')" title="Front View (Numpad 1)">F</button>
      <button @click="setView('right')" title="Right View (Numpad 3)">R</button>
      <button @click="setView('top')" title="Top View (Numpad 7)">T</button>
      <button @click="setView('active-camera')" title="Camera View (Numpad 0)">C</button>
    </div>

    <div class="separator" />

    <!-- Reset Button -->
    <div class="toolbar-group">
      <button @click="resetView" title="Reset View (Home)">
        <span class="icon">⌂</span>
        <span class="label">Reset</span>
      </button>

      <button @click="focusSelected" title="Focus Selected (.)">
        <span class="icon">⌖</span>
        <span class="label">Focus</span>
      </button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import type {
  ViewOptions,
  ViewType,
  WireframeVisibility,
} from "@/types/camera";

const store = useCompositorStore();

const viewOptions = computed(() => store.viewOptions);
const viewportState = computed(() => store.viewportState);

type ViewOptionKey = keyof ViewOptions;

function _toggleOption(key: ViewOptionKey) {
  const current = viewOptions.value[key];
  if (typeof current === "boolean") {
    store.updateViewOptions({ [key]: !current });
  }
}

function _setCameraWireframes(value: WireframeVisibility) {
  store.updateViewOptions({ cameraWireframes: value });
}

function _setView(viewType: ViewType) {
  const newViews = [...viewportState.value.views];
  newViews[viewportState.value.activeViewIndex] = viewType;
  store.updateViewportState({ views: newViews });
}

function _resetView() {
  const activeView =
    viewportState.value.views[viewportState.value.activeViewIndex];
  if (activeView.startsWith("custom-")) {
    const customViewKey = activeView as "custom-1" | "custom-2" | "custom-3";
    store.updateViewportState({
      customViews: {
        ...viewportState.value.customViews,
        [customViewKey]: {
          orbitCenter: { x: store.width / 2, y: store.height / 2, z: 0 },
          orbitDistance: 2000,
          orbitPhi: 60,
          orbitTheta: 45,
          orthoZoom: 1,
          orthoOffset: { x: 0, y: 0 },
        },
      },
    });
  }
}

function _focusSelected() {
  const selectedLayer = store.layers.find((l) =>
    store.selectedLayerIds.includes(l.id),
  );
  if (!selectedLayer) return;

  const pos = selectedLayer.transform.position.value;
  const activeView =
    viewportState.value.views[viewportState.value.activeViewIndex];

  if (activeView.startsWith("custom-")) {
    const customViewKey = activeView as "custom-1" | "custom-2" | "custom-3";
    const currentView = viewportState.value.customViews[customViewKey];

    store.updateViewportState({
      customViews: {
        ...viewportState.value.customViews,
        [customViewKey]: {
          ...currentView,
          orbitCenter: { x: pos.x, y: pos.y, z: 0 },
          orbitDistance: Math.min(currentView.orbitDistance, 1000),
        },
      },
    });
  }
}
</script>

<style scoped>
.view-options-toolbar {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 8px;
  background: #1a1a1a;
  border-bottom: 1px solid #333;
  height: 32px;
}

.toolbar-group {
  display: flex;
  gap: 2px;
}

.separator {
  width: 1px;
  height: 20px;
  background: #444;
  margin: 0 4px;
}

button {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 8px;
  border: 1px solid transparent;
  border-radius: 3px;
  background: transparent;
  color: #888;
  cursor: pointer;
  font-size: 13px;
  transition: all 0.15s ease;
}

button:hover {
  background: #333;
  color: #e0e0e0;
}

button.active {
  background: #2a4a8a;
  border-color: #3a6aba;
  color: #fff;
}

button .icon {
  font-size: 12px;
}

button .label {
  font-size: 12px;
}

.view-presets button {
  width: 24px;
  height: 24px;
  padding: 0;
  justify-content: center;
  font-weight: bold;
  font-size: 12px;
}

.wireframe-select {
  background: #252525;
  border: 1px solid #444;
  border-radius: 3px;
  color: #888;
  font-size: 12px;
  padding: 2px 4px;
  cursor: pointer;
}

.wireframe-select:hover {
  border-color: #666;
  color: #e0e0e0;
}

.wireframe-select:focus {
  outline: none;
  border-color: #3a6aba;
}
</style>
