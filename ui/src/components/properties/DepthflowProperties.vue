<template>
  <div class="depthflow-properties">
    <!-- Source Selection -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('source')">
        <i class="pi" :class="expandedSections.has('source') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Source Selection</span>
      </div>
      <div v-if="expandedSections.has('source')" class="section-content">
        <div class="property-row">
          <label>Source Layer</label>
          <select
            :value="config.sourceLayerId"
            @change="updateConfig('sourceLayerId', ($event.target as HTMLSelectElement).value)"
          >
            <option value="">Select source...</option>
            <option
              v-for="layer in imageLayers"
              :key="layer.id"
              :value="layer.id"
            >
              {{ layer.name }}
            </option>
          </select>
        </div>
        <div class="property-row">
          <label>Depth Layer</label>
          <select
            :value="config.depthLayerId"
            @change="updateConfig('depthLayerId', ($event.target as HTMLSelectElement).value)"
          >
            <option value="">Select depth map...</option>
            <option
              v-for="layer in depthLayers"
              :key="layer.id"
              :value="layer.id"
            >
              {{ layer.name }}
            </option>
          </select>
        </div>
      </div>
    </div>

    <!-- Motion Preset -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('preset')">
        <i class="pi" :class="expandedSections.has('preset') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Motion Preset</span>
      </div>
      <div v-if="expandedSections.has('preset')" class="section-content">
        <div class="preset-grid">
          <button
            v-for="preset in presets"
            :key="preset.value"
            class="preset-btn"
            :class="{ active: depthflowConfig.preset === preset.value }"
            @click="selectPreset(preset.value)"
          >
            <i :class="preset.icon" />
            <span>{{ preset.label }}</span>
          </button>
        </div>
        <div class="property-row" v-if="depthflowConfig.preset !== 'static'">
          <label>Intensity</label>
          <input
            type="range"
            :value="presetIntensity"
            min="0.1"
            max="2"
            step="0.1"
            @input="updatePresetIntensity(Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ presetIntensity.toFixed(1) }}x</span>
        </div>
      </div>
    </div>

    <!-- Camera Controls -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('camera')">
        <i class="pi" :class="expandedSections.has('camera') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Camera Controls</span>
      </div>
      <div v-if="expandedSections.has('camera')" class="section-content">
        <div class="property-row">
          <label>Zoom</label>
          <KeyframeToggle
            v-if="config.animatedZoom"
            :property="config.animatedZoom"
            :layer-id="layer.id"
          />
          <input
            type="range"
            :value="depthflowConfig.zoom"
            min="0.5"
            max="2"
            step="0.01"
            @input="updateDepthflowConfig('zoom', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ depthflowConfig.zoom.toFixed(2) }}</span>
        </div>
        <div class="property-row">
          <label>Offset X</label>
          <KeyframeToggle
            v-if="config.animatedOffsetX"
            :property="config.animatedOffsetX"
            :layer-id="layer.id"
          />
          <input
            type="range"
            :value="depthflowConfig.offsetX"
            min="-1"
            max="1"
            step="0.01"
            @input="updateDepthflowConfig('offsetX', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ depthflowConfig.offsetX.toFixed(2) }}</span>
        </div>
        <div class="property-row">
          <label>Offset Y</label>
          <KeyframeToggle
            v-if="config.animatedOffsetY"
            :property="config.animatedOffsetY"
            :layer-id="layer.id"
          />
          <input
            type="range"
            :value="depthflowConfig.offsetY"
            min="-1"
            max="1"
            step="0.01"
            @input="updateDepthflowConfig('offsetY', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ depthflowConfig.offsetY.toFixed(2) }}</span>
        </div>
        <div class="property-row">
          <label>Rotation</label>
          <KeyframeToggle
            v-if="config.animatedRotation"
            :property="config.animatedRotation"
            :layer-id="layer.id"
          />
          <input
            type="range"
            :value="depthflowConfig.rotation"
            min="-180"
            max="180"
            step="1"
            @input="updateDepthflowConfig('rotation', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ depthflowConfig.rotation }}°</span>
        </div>
      </div>
    </div>

    <!-- Depth Settings -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('depth')">
        <i class="pi" :class="expandedSections.has('depth') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Depth Settings</span>
      </div>
      <div v-if="expandedSections.has('depth')" class="section-content">
        <div class="property-row">
          <label>Depth Scale</label>
          <KeyframeToggle
            v-if="config.animatedDepthScale"
            :property="config.animatedDepthScale"
            :layer-id="layer.id"
          />
          <input
            type="range"
            :value="depthflowConfig.depthScale"
            min="0"
            max="2"
            step="0.05"
            @input="updateDepthflowConfig('depthScale', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ depthflowConfig.depthScale.toFixed(2) }}</span>
        </div>
        <div class="property-row">
          <label>Focus Depth</label>
          <input
            type="range"
            :value="depthflowConfig.focusDepth"
            min="0"
            max="1"
            step="0.01"
            @input="updateDepthflowConfig('focusDepth', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ depthflowConfig.focusDepth.toFixed(2) }}</span>
        </div>
        <div class="depth-hint">
          Objects at focus depth stay stationary.<br/>
          Closer objects move more, distant objects move less.
        </div>
      </div>
    </div>

    <!-- Preset-Specific Settings -->
    <div
      v-if="showPresetSettings"
      class="property-section"
    >
      <div class="section-header" @click="toggleSection('presetSettings')">
        <i class="pi" :class="expandedSections.has('presetSettings') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>{{ presetSettingsTitle }}</span>
      </div>
      <div v-if="expandedSections.has('presetSettings')" class="section-content">
        <!-- Circle/Orbit settings -->
        <template v-if="isOrbitPreset">
          <div class="property-row">
            <label>Orbit Radius</label>
            <input
              type="range"
              :value="depthflowConfig.orbitRadius"
              min="0.01"
              max="0.5"
              step="0.01"
              @input="updateDepthflowConfig('orbitRadius', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ depthflowConfig.orbitRadius.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label>Orbit Speed</label>
            <input
              type="range"
              :value="depthflowConfig.orbitSpeed"
              min="1"
              max="720"
              step="1"
              @input="updateDepthflowConfig('orbitSpeed', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ depthflowConfig.orbitSpeed }}°</span>
          </div>
        </template>

        <!-- Swing settings -->
        <template v-if="isSwingPreset">
          <div class="property-row">
            <label>Amplitude</label>
            <input
              type="range"
              :value="depthflowConfig.swingAmplitude"
              min="0.01"
              max="0.5"
              step="0.01"
              @input="updateDepthflowConfig('swingAmplitude', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ depthflowConfig.swingAmplitude.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label>Frequency</label>
            <input
              type="range"
              :value="depthflowConfig.swingFrequency"
              min="0.1"
              max="5"
              step="0.1"
              @input="updateDepthflowConfig('swingFrequency', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ depthflowConfig.swingFrequency.toFixed(1) }} Hz</span>
          </div>
        </template>

        <!-- Dolly zoom settings -->
        <template v-if="isDollyPreset">
          <div class="property-row">
            <label>Dolly Rate</label>
            <input
              type="range"
              :value="depthflowConfig.dollyZoom"
              min="0"
              max="1"
              step="0.05"
              @input="updateDepthflowConfig('dollyZoom', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ depthflowConfig.dollyZoom.toFixed(2) }}</span>
          </div>
        </template>
      </div>
    </div>

    <!-- Quality Settings -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('quality')">
        <i class="pi" :class="expandedSections.has('quality') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Quality</span>
      </div>
      <div v-if="expandedSections.has('quality')" class="section-content">
        <div class="property-row">
          <label>Edge Dilation</label>
          <input
            type="range"
            :value="depthflowConfig.edgeDilation"
            min="0"
            max="50"
            step="1"
            @input="updateDepthflowConfig('edgeDilation', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ depthflowConfig.edgeDilation }}px</span>
        </div>
        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="depthflowConfig.inpaintEdges"
              @change="updateDepthflowConfig('inpaintEdges', ($event.target as HTMLInputElement).checked)"
            />
            Inpaint Edges
          </label>
        </div>
      </div>
    </div>

    <!-- Camera Sync -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('cameraSync')">
        <i class="pi" :class="expandedSections.has('cameraSync') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Camera Sync</span>
        <span v-if="config.cameraSyncEnabled" class="sync-badge">Active</span>
      </div>
      <div v-if="expandedSections.has('cameraSync')" class="section-content">
        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="config.cameraSyncEnabled ?? false"
              @change="updateConfig('cameraSyncEnabled', ($event.target as HTMLInputElement).checked)"
            />
            Enable Camera Sync
          </label>
        </div>

        <template v-if="config.cameraSyncEnabled">
          <div class="property-row">
            <label>Camera Layer</label>
            <select
              :value="config.cameraSyncLayerId ?? ''"
              @change="updateConfig('cameraSyncLayerId', ($event.target as HTMLSelectElement).value)"
            >
              <option value="">Select camera...</option>
              <option
                v-for="layer in cameraLayers"
                :key="layer.id"
                :value="layer.id"
              >
                {{ layer.name }}
              </option>
            </select>
          </div>

          <div class="sync-hint">
            Camera movement will drive parallax. Adjust sensitivity below.
          </div>

          <div class="property-row">
            <label>X Sensitivity</label>
            <input
              type="range"
              :value="cameraSyncConfig.sensitivityX"
              min="0"
              max="2"
              step="0.05"
              @input="updateCameraSyncConfig('sensitivityX', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ cameraSyncConfig.sensitivityX.toFixed(2) }}</span>
          </div>

          <div class="property-row">
            <label>Y Sensitivity</label>
            <input
              type="range"
              :value="cameraSyncConfig.sensitivityY"
              min="0"
              max="2"
              step="0.05"
              @input="updateCameraSyncConfig('sensitivityY', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ cameraSyncConfig.sensitivityY.toFixed(2) }}</span>
          </div>

          <div class="property-row">
            <label>Z Sensitivity</label>
            <input
              type="range"
              :value="cameraSyncConfig.sensitivityZ * 1000"
              min="0"
              max="10"
              step="0.1"
              @input="updateCameraSyncConfig('sensitivityZ', Number(($event.target as HTMLInputElement).value) / 1000)"
            />
            <span class="value-display">{{ (cameraSyncConfig.sensitivityZ * 1000).toFixed(1) }}</span>
          </div>

          <div class="property-row">
            <label>Rotation Sens.</label>
            <input
              type="range"
              :value="cameraSyncConfig.sensitivityRotation"
              min="0"
              max="2"
              step="0.05"
              @input="updateCameraSyncConfig('sensitivityRotation', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ cameraSyncConfig.sensitivityRotation.toFixed(2) }}</span>
          </div>

          <div class="property-row checkbox-row">
            <label>
              <input
                type="checkbox"
                :checked="cameraSyncConfig.invertX"
                @change="updateCameraSyncConfig('invertX', ($event.target as HTMLInputElement).checked)"
              />
              Invert X
            </label>
            <label style="margin-left: 16px;">
              <input
                type="checkbox"
                :checked="cameraSyncConfig.invertY"
                @change="updateCameraSyncConfig('invertY', ($event.target as HTMLInputElement).checked)"
              />
              Invert Y
            </label>
          </div>

          <div class="property-row">
            <label>Base Zoom</label>
            <input
              type="range"
              :value="cameraSyncConfig.baseZoom"
              min="0.5"
              max="2"
              step="0.05"
              @input="updateCameraSyncConfig('baseZoom', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ cameraSyncConfig.baseZoom.toFixed(2) }}</span>
          </div>
        </template>
      </div>
    </div>

    <!-- Preview -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('preview')">
        <i class="pi" :class="expandedSections.has('preview') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Preview</span>
      </div>
      <div v-if="expandedSections.has('preview')" class="section-content">
        <div class="preview-container">
          <canvas
            ref="previewCanvas"
            class="preview-canvas"
            :width="previewSize"
            :height="previewSize"
          />
        </div>
        <div class="preview-controls">
          <button
            class="preview-btn"
            :class="{ active: isPreviewPlaying }"
            @click="togglePreview"
          >
            <i :class="isPreviewPlaying ? 'pi pi-pause' : 'pi pi-play'" />
            {{ isPreviewPlaying ? 'Pause' : 'Play' }}
          </button>
          <span class="frame-indicator">
            Frame {{ previewFrame }} / {{ totalFrames - 1 }}
          </span>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted } from 'vue';
import type { Layer, DepthflowLayerData, DepthflowConfig, DepthflowPreset, CameraToDepthflowConfig } from '@/types/project';
import { useCompositorStore } from '@/stores/compositorStore';
import KeyframeToggle from './KeyframeToggle.vue';

const DEFAULT_CAMERA_SYNC_CONFIG: CameraToDepthflowConfig = {
  sensitivityX: 0.5,
  sensitivityY: 0.5,
  sensitivityZ: 0.001,
  sensitivityRotation: 1,
  baseZoom: 1,
  invertX: false,
  invertY: false,
  zoomClamp: { min: 0.5, max: 3 },
  offsetClamp: { min: -1, max: 1 }
};

interface Props {
  layer: Layer;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: 'update', data: Partial<DepthflowLayerData>): void;
}>();

const store = useCompositorStore();

// Refs
const previewCanvas = ref<HTMLCanvasElement | null>(null);
const isPreviewPlaying = ref(false);
const previewFrame = ref(0);
const previewAnimationId = ref<number | null>(null);

// UI State
const expandedSections = ref(new Set(['source', 'preset', 'camera']));
const presetIntensity = ref(1.0);
const previewSize = 200;

// Presets
const presets = [
  { value: 'static' as DepthflowPreset, label: 'Static', icon: 'pi pi-stop' },
  { value: 'zoom_in' as DepthflowPreset, label: 'Zoom In', icon: 'pi pi-search-plus' },
  { value: 'zoom_out' as DepthflowPreset, label: 'Zoom Out', icon: 'pi pi-search-minus' },
  { value: 'dolly_zoom_in' as DepthflowPreset, label: 'Dolly In', icon: 'pi pi-video' },
  { value: 'dolly_zoom_out' as DepthflowPreset, label: 'Dolly Out', icon: 'pi pi-video' },
  { value: 'pan_left' as DepthflowPreset, label: 'Pan Left', icon: 'pi pi-arrow-left' },
  { value: 'pan_right' as DepthflowPreset, label: 'Pan Right', icon: 'pi pi-arrow-right' },
  { value: 'pan_up' as DepthflowPreset, label: 'Pan Up', icon: 'pi pi-arrow-up' },
  { value: 'pan_down' as DepthflowPreset, label: 'Pan Down', icon: 'pi pi-arrow-down' },
  { value: 'circle_cw' as DepthflowPreset, label: 'Circle CW', icon: 'pi pi-replay' },
  { value: 'circle_ccw' as DepthflowPreset, label: 'Circle CCW', icon: 'pi pi-refresh' },
  { value: 'horizontal_swing' as DepthflowPreset, label: 'H Swing', icon: 'pi pi-arrows-h' },
  { value: 'vertical_swing' as DepthflowPreset, label: 'V Swing', icon: 'pi pi-arrows-v' },
  { value: 'custom' as DepthflowPreset, label: 'Custom', icon: 'pi pi-sliders-h' }
];

// Computed
const config = computed((): DepthflowLayerData => {
  const data = props.layer.data as DepthflowLayerData | null;
  return data || {
    sourceLayerId: '',
    depthLayerId: '',
    config: {
      preset: 'static',
      zoom: 1.0,
      offsetX: 0,
      offsetY: 0,
      rotation: 0,
      depthScale: 1.0,
      focusDepth: 0.5,
      dollyZoom: 0,
      orbitRadius: 0.1,
      orbitSpeed: 360,
      swingAmplitude: 0.1,
      swingFrequency: 1,
      edgeDilation: 5,
      inpaintEdges: true
    }
  };
});

const depthflowConfig = computed(() => config.value.config);
const totalFrames = computed(() => store.frameCount);

const imageLayers = computed(() =>
  store.layers.filter(l => l.type === 'image' || l.type === 'generated')
);

const depthLayers = computed(() =>
  store.layers.filter(l => l.type === 'depth' || l.type === 'generated')
);

const cameraLayers = computed(() =>
  store.layers.filter(l => l.type === 'camera')
);

const cameraSyncConfig = computed((): CameraToDepthflowConfig => {
  return config.value.cameraSyncConfig ?? DEFAULT_CAMERA_SYNC_CONFIG;
});

const isOrbitPreset = computed(() =>
  ['circle_cw', 'circle_ccw'].includes(depthflowConfig.value.preset)
);

const isSwingPreset = computed(() =>
  ['horizontal_swing', 'vertical_swing'].includes(depthflowConfig.value.preset)
);

const isDollyPreset = computed(() =>
  ['dolly_zoom_in', 'dolly_zoom_out'].includes(depthflowConfig.value.preset)
);

const showPresetSettings = computed(() =>
  isOrbitPreset.value || isSwingPreset.value || isDollyPreset.value
);

const presetSettingsTitle = computed(() => {
  if (isOrbitPreset.value) return 'Orbit Settings';
  if (isSwingPreset.value) return 'Swing Settings';
  if (isDollyPreset.value) return 'Dolly Zoom Settings';
  return 'Preset Settings';
});

// Methods
function toggleSection(section: string): void {
  if (expandedSections.value.has(section)) {
    expandedSections.value.delete(section);
  } else {
    expandedSections.value.add(section);
  }
}

function updateConfig(key: keyof DepthflowLayerData, value: any): void {
  emit('update', { [key]: value });
}

function updateDepthflowConfig(key: keyof DepthflowConfig, value: any): void {
  emit('update', {
    config: { ...depthflowConfig.value, [key]: value }
  });
}

function selectPreset(preset: DepthflowPreset): void {
  updateDepthflowConfig('preset', preset);
}

function updateCameraSyncConfig(key: keyof CameraToDepthflowConfig, value: any): void {
  emit('update', {
    cameraSyncConfig: { ...cameraSyncConfig.value, [key]: value }
  });
}

function updatePresetIntensity(intensity: number): void {
  presetIntensity.value = intensity;
  // Apply intensity to relevant parameters based on preset
  if (isOrbitPreset.value) {
    updateDepthflowConfig('orbitRadius', 0.1 * intensity);
  } else if (isSwingPreset.value) {
    updateDepthflowConfig('swingAmplitude', 0.1 * intensity);
  } else {
    updateDepthflowConfig('depthScale', 1.0 * intensity);
  }
}

function togglePreview(): void {
  isPreviewPlaying.value = !isPreviewPlaying.value;

  if (isPreviewPlaying.value) {
    playPreview();
  } else {
    if (previewAnimationId.value !== null) {
      cancelAnimationFrame(previewAnimationId.value);
      previewAnimationId.value = null;
    }
  }
}

function playPreview(): void {
  if (!isPreviewPlaying.value) return;

  previewFrame.value = (previewFrame.value + 1) % totalFrames.value;
  renderPreview();

  previewAnimationId.value = requestAnimationFrame(() => {
    setTimeout(playPreview, 1000 / store.fps);
  });
}

function renderPreview(): void {
  const canvas = previewCanvas.value;
  if (!canvas) return;

  const ctx = canvas.getContext('2d');
  if (!ctx) return;

  // Clear canvas
  ctx.fillStyle = '#1e1e1e';
  ctx.fillRect(0, 0, previewSize, previewSize);

  // Draw placeholder preview
  ctx.fillStyle = '#333';
  ctx.fillRect(10, 10, previewSize - 20, previewSize - 20);

  ctx.fillStyle = '#666';
  ctx.font = '12px sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText('Depthflow Preview', previewSize / 2, previewSize / 2);
  ctx.fillText(`Frame ${previewFrame.value}`, previewSize / 2, previewSize / 2 + 16);
}

// Lifecycle
onMounted(() => {
  renderPreview();
});

onUnmounted(() => {
  if (previewAnimationId.value !== null) {
    cancelAnimationFrame(previewAnimationId.value);
  }
});
</script>

<style scoped>
.depthflow-properties {
  font-size: 12px;
}

.property-section {
  border-bottom: 1px solid #333;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px;
  cursor: pointer;
  background: #2d2d2d;
  font-weight: 500;
}

.section-header:hover {
  background: #333;
}

.section-header i {
  font-size: 10px;
  width: 14px;
}

.section-content {
  padding: 8px;
  background: #252525;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.property-row label {
  width: 80px;
  flex-shrink: 0;
  color: #888;
  font-size: 11px;
}

.property-row input[type="range"] {
  flex: 1;
  min-width: 60px;
}

.property-row select {
  flex: 1;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 11px;
}

.value-display {
  width: 50px;
  text-align: right;
  font-variant-numeric: tabular-nums;
  color: #aaa;
  font-size: 10px;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  width: auto;
  cursor: pointer;
}

.preset-grid {
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  gap: 4px;
  margin-bottom: 8px;
}

.preset-btn {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 2px;
  padding: 6px 4px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  font-size: 9px;
}

.preset-btn i {
  font-size: 14px;
}

.preset-btn:hover {
  background: #333;
  color: #fff;
}

.preset-btn.active {
  background: rgba(74, 144, 217, 0.2);
  border-color: #4a90d9;
  color: #4a90d9;
}

.depth-hint {
  padding: 8px;
  background: #1e1e1e;
  border-radius: 4px;
  font-size: 10px;
  color: #666;
  line-height: 1.4;
}

.preview-container {
  display: flex;
  justify-content: center;
  margin-bottom: 8px;
}

.preview-canvas {
  border: 1px solid #3d3d3d;
  border-radius: 4px;
}

.preview-controls {
  display: flex;
  align-items: center;
  gap: 8px;
}

.preview-btn {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 12px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #aaa;
  border-radius: 4px;
  cursor: pointer;
  font-size: 11px;
}

.preview-btn:hover {
  background: #333;
  color: #fff;
}

.preview-btn.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.frame-indicator {
  font-size: 10px;
  color: #666;
  font-variant-numeric: tabular-nums;
}

/* Camera Sync */
.sync-badge {
  margin-left: auto;
  padding: 2px 6px;
  background: rgba(46, 204, 113, 0.2);
  color: #2ecc71;
  border-radius: 3px;
  font-size: 9px;
  font-weight: 600;
  text-transform: uppercase;
}

.sync-hint {
  padding: 8px;
  background: #1e1e1e;
  border-radius: 4px;
  font-size: 10px;
  color: #666;
  line-height: 1.4;
  margin-bottom: 8px;
}
</style>
