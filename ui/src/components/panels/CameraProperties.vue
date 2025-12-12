<template>
  <div class="camera-properties">
    <div class="panel-header">
      <span class="panel-title">Camera</span>
      <span class="camera-name">{{ camera?.name ?? 'No Camera' }}</span>
    </div>

    <div v-if="camera" class="properties-content">
      <!-- Camera Type -->
      <div class="property-section">
        <div class="section-header">Type</div>
        <div class="property-row">
          <select
            :value="camera.type"
            @change="updateProperty('type', ($event.target as HTMLSelectElement).value)"
            class="type-select"
          >
            <option value="one-node">One-Node Camera</option>
            <option value="two-node">Two-Node Camera</option>
          </select>
        </div>
      </div>

      <!-- Transform -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('transform')">
          <span class="toggle-icon">{{ expandedSections.transform ? '▼' : '►' }}</span>
          Transform
        </div>
        <div v-show="expandedSections.transform" class="section-content">
          <!-- Position -->
          <div class="property-group">
            <label>Position</label>
            <div class="xyz-inputs">
              <ScrubableNumber
                :modelValue="camera.position.x"
                @update:modelValue="v => updatePosition('x', v)"
                label="X"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.position.y"
                @update:modelValue="v => updatePosition('y', v)"
                label="Y"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.position.z"
                @update:modelValue="v => updatePosition('z', v)"
                label="Z"
                :precision="1"
              />
            </div>
          </div>

          <!-- Point of Interest (two-node only) -->
          <div v-if="camera.type === 'two-node'" class="property-group">
            <label>Point of Interest</label>
            <div class="xyz-inputs">
              <ScrubableNumber
                :modelValue="camera.pointOfInterest.x"
                @update:modelValue="v => updatePOI('x', v)"
                label="X"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.pointOfInterest.y"
                @update:modelValue="v => updatePOI('y', v)"
                label="Y"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.pointOfInterest.z"
                @update:modelValue="v => updatePOI('z', v)"
                label="Z"
                :precision="1"
              />
            </div>
          </div>

          <!-- Orientation -->
          <div class="property-group">
            <label>Orientation</label>
            <div class="xyz-inputs">
              <ScrubableNumber
                :modelValue="camera.orientation.x"
                @update:modelValue="v => updateOrientation('x', v)"
                label="X"
                unit="°"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.orientation.y"
                @update:modelValue="v => updateOrientation('y', v)"
                label="Y"
                unit="°"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.orientation.z"
                @update:modelValue="v => updateOrientation('z', v)"
                label="Z"
                unit="°"
                :precision="1"
              />
            </div>
          </div>

          <!-- Individual Rotations -->
          <div class="property-group">
            <label>X Rotation</label>
            <ScrubableNumber
              :modelValue="camera.xRotation"
              @update:modelValue="v => updateProperty('xRotation', v)"
              unit="°"
              :precision="1"
            />
          </div>
          <div class="property-group">
            <label>Y Rotation</label>
            <ScrubableNumber
              :modelValue="camera.yRotation"
              @update:modelValue="v => updateProperty('yRotation', v)"
              unit="°"
              :precision="1"
            />
          </div>
          <div class="property-group">
            <label>Z Rotation</label>
            <ScrubableNumber
              :modelValue="camera.zRotation"
              @update:modelValue="v => updateProperty('zRotation', v)"
              unit="°"
              :precision="1"
            />
          </div>
        </div>
      </div>

      <!-- Lens Settings -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('lens')">
          <span class="toggle-icon">{{ expandedSections.lens ? '▼' : '►' }}</span>
          Lens
        </div>
        <div v-show="expandedSections.lens" class="section-content">
          <!-- Preset buttons -->
          <div class="preset-row">
            <button
              v-for="preset in CAMERA_PRESETS"
              :key="preset.name"
              :class="{ active: Math.abs(camera.focalLength - preset.focalLength) < 0.5 }"
              @click="applyPreset(preset)"
            >
              {{ preset.name }}
            </button>
          </div>

          <div class="property-group">
            <label>Focal Length</label>
            <ScrubableNumber
              :modelValue="camera.focalLength"
              @update:modelValue="updateFocalLength"
              :min="1"
              :max="500"
              unit="mm"
              :precision="1"
            />
          </div>

          <div class="property-group">
            <label>Angle of View</label>
            <ScrubableNumber
              :modelValue="camera.angleOfView"
              @update:modelValue="updateAngleOfView"
              :min="1"
              :max="170"
              unit="°"
              :precision="1"
            />
          </div>

          <div class="property-group">
            <label>Film Size</label>
            <ScrubableNumber
              :modelValue="camera.filmSize"
              @update:modelValue="v => updateProperty('filmSize', v)"
              :min="1"
              :max="100"
              unit="mm"
              :precision="1"
            />
          </div>

          <div class="property-group">
            <label>Measure Film Size</label>
            <select
              :value="camera.measureFilmSize"
              @change="updateProperty('measureFilmSize', ($event.target as HTMLSelectElement).value)"
            >
              <option value="horizontal">Horizontal</option>
              <option value="vertical">Vertical</option>
              <option value="diagonal">Diagonal</option>
            </select>
          </div>
        </div>
      </div>

      <!-- Depth of Field -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('dof')">
          <span class="toggle-icon">{{ expandedSections.dof ? '▼' : '►' }}</span>
          Depth of Field
        </div>
        <div v-show="expandedSections.dof" class="section-content">
          <div class="property-group checkbox-group">
            <label>
              <input
                type="checkbox"
                :checked="camera.depthOfField.enabled"
                @change="updateDOF('enabled', ($event.target as HTMLInputElement).checked)"
              />
              Enable DOF
            </label>
          </div>

          <template v-if="camera.depthOfField.enabled">
            <div class="property-group">
              <label>Focus Distance</label>
              <ScrubableNumber
                :modelValue="camera.depthOfField.focusDistance"
                @update:modelValue="v => updateDOF('focusDistance', v)"
                :min="1"
                unit="px"
                :precision="0"
              />
            </div>

            <div class="property-group">
              <label>f-Stop</label>
              <ScrubableNumber
                :modelValue="camera.depthOfField.fStop"
                @update:modelValue="v => updateDOF('fStop', v)"
                :min="0.1"
                :max="64"
                :precision="1"
              />
            </div>

            <div class="property-group">
              <label>Blur Level</label>
              <SliderInput
                :modelValue="camera.depthOfField.blurLevel"
                @update:modelValue="v => updateDOF('blurLevel', v)"
                :min="0"
                :max="1"
                :step="0.01"
              />
            </div>

            <div class="property-group checkbox-group">
              <label>
                <input
                  type="checkbox"
                  :checked="camera.depthOfField.lockToZoom"
                  @change="updateDOF('lockToZoom', ($event.target as HTMLInputElement).checked)"
                />
                Lock to Zoom
              </label>
            </div>
          </template>
        </div>
      </div>

      <!-- Iris Properties -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('iris')">
          <span class="toggle-icon">{{ expandedSections.iris ? '▼' : '►' }}</span>
          Iris
        </div>
        <div v-show="expandedSections.iris" class="section-content">
          <div class="property-group">
            <label>Shape ({{ Math.round(camera.iris.shape) }}-gon)</label>
            <SliderInput
              :modelValue="camera.iris.shape"
              @update:modelValue="v => updateIris('shape', v)"
              :min="3"
              :max="10"
              :step="1"
            />
          </div>

          <div class="property-group">
            <label>Rotation</label>
            <AngleDial
              :modelValue="camera.iris.rotation"
              @update:modelValue="v => updateIris('rotation', v)"
              :size="48"
            />
          </div>

          <div class="property-group">
            <label>Roundness</label>
            <SliderInput
              :modelValue="camera.iris.roundness"
              @update:modelValue="v => updateIris('roundness', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Aspect Ratio</label>
            <SliderInput
              :modelValue="camera.iris.aspectRatio"
              @update:modelValue="v => updateIris('aspectRatio', v)"
              :min="0.5"
              :max="2"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Diffraction Fringe</label>
            <SliderInput
              :modelValue="camera.iris.diffractionFringe"
              @update:modelValue="v => updateIris('diffractionFringe', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>
        </div>
      </div>

      <!-- Highlight Properties -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('highlight')">
          <span class="toggle-icon">{{ expandedSections.highlight ? '▼' : '►' }}</span>
          Highlight
        </div>
        <div v-show="expandedSections.highlight" class="section-content">
          <div class="property-group">
            <label>Gain</label>
            <SliderInput
              :modelValue="camera.highlight.gain"
              @update:modelValue="v => updateHighlight('gain', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Threshold</label>
            <SliderInput
              :modelValue="camera.highlight.threshold"
              @update:modelValue="v => updateHighlight('threshold', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Saturation</label>
            <SliderInput
              :modelValue="camera.highlight.saturation"
              @update:modelValue="v => updateHighlight('saturation', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>
        </div>
      </div>

      <!-- Auto-Orient -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('autoOrient')">
          <span class="toggle-icon">{{ expandedSections.autoOrient ? '▼' : '►' }}</span>
          Auto-Orient
        </div>
        <div v-show="expandedSections.autoOrient" class="section-content">
          <div class="property-group">
            <select
              :value="camera.autoOrient"
              @change="updateProperty('autoOrient', ($event.target as HTMLSelectElement).value)"
            >
              <option value="off">Off</option>
              <option value="orient-along-path">Orient Along Path</option>
              <option value="orient-towards-poi">Orient Towards Point of Interest</option>
            </select>
          </div>
        </div>
      </div>

      <!-- Clipping -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('clipping')">
          <span class="toggle-icon">{{ expandedSections.clipping ? '▼' : '►' }}</span>
          Clipping
        </div>
        <div v-show="expandedSections.clipping" class="section-content">
          <div class="property-group">
            <label>Near Clip</label>
            <ScrubableNumber
              :modelValue="camera.nearClip"
              @update:modelValue="v => updateProperty('nearClip', v)"
              :min="0.1"
              :precision="1"
            />
          </div>

          <div class="property-group">
            <label>Far Clip</label>
            <ScrubableNumber
              :modelValue="camera.farClip"
              @update:modelValue="v => updateProperty('farClip', v)"
              :min="100"
              :precision="0"
            />
          </div>
        </div>
      </div>
    </div>

    <div v-else class="no-camera">
      <p>No camera selected</p>
      <button @click="createCamera">Create Camera</button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { reactive, computed } from 'vue';
import type { Camera3D } from '../../types/camera';
import { CAMERA_PRESETS } from '../../types/camera';
import { focalLengthToFOV, fovToFocalLength } from '../../services/math3d';
import { ScrubableNumber, SliderInput, AngleDial } from '../controls';
import { useCompositorStore } from '@/stores/compositorStore';

// Store connection
const store = useCompositorStore();

// Get camera from store (active camera or selected camera layer)
const camera = computed<Camera3D | null>(() => {
  // First, check if a camera layer is selected
  const selectedLayer = store.selectedLayer;
  if (selectedLayer?.type === 'camera' && selectedLayer.data) {
    const cameraData = selectedLayer.data as { cameraId: string };
    return store.getCamera(cameraData.cameraId);
  }
  // Otherwise, return the active camera
  return store.activeCamera;
});

const expandedSections = reactive({
  transform: true,
  lens: true,
  dof: false,
  iris: false,
  highlight: false,
  autoOrient: false,
  clipping: false
});

function toggleSection(section: keyof typeof expandedSections) {
  expandedSections[section] = !expandedSections[section];
}

function updateProperty<K extends keyof Camera3D>(key: K, value: Camera3D[K]) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, { [key]: value });
}

function updatePosition(axis: 'x' | 'y' | 'z', value: number) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, {
    position: { ...camera.value.position, [axis]: value }
  });
}

function updatePOI(axis: 'x' | 'y' | 'z', value: number) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, {
    pointOfInterest: { ...camera.value.pointOfInterest, [axis]: value }
  });
}

function updateOrientation(axis: 'x' | 'y' | 'z', value: number) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, {
    orientation: { ...camera.value.orientation, [axis]: value }
  });
}

function updateFocalLength(value: number) {
  if (!camera.value) return;
  const angleOfView = focalLengthToFOV(value, camera.value.filmSize);
  store.updateCamera(camera.value.id, {
    focalLength: value,
    angleOfView
  });
}

function updateAngleOfView(value: number) {
  if (!camera.value) return;
  const focalLength = fovToFocalLength(value, camera.value.filmSize);
  store.updateCamera(camera.value.id, {
    angleOfView: value,
    focalLength
  });
}

function updateDOF<K extends keyof Camera3D['depthOfField']>(key: K, value: Camera3D['depthOfField'][K]) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, {
    depthOfField: { ...camera.value.depthOfField, [key]: value }
  });
}

function updateIris<K extends keyof Camera3D['iris']>(key: K, value: Camera3D['iris'][K]) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, {
    iris: { ...camera.value.iris, [key]: value }
  });
}

function updateHighlight<K extends keyof Camera3D['highlight']>(key: K, value: Camera3D['highlight'][K]) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, {
    highlight: { ...camera.value.highlight, [key]: value }
  });
}

function applyPreset(preset: typeof CAMERA_PRESETS[number]) {
  if (!camera.value) return;
  store.updateCamera(camera.value.id, {
    focalLength: preset.focalLength,
    angleOfView: preset.angleOfView,
    zoom: preset.zoom
  });
}

function createCamera() {
  store.createCameraLayer();
}
</script>

<style scoped>
.camera-properties {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 12px;
  overflow: hidden;
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 12px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.panel-title {
  font-weight: 600;
}

.camera-name {
  color: #888;
  font-size: 11px;
}

.properties-content {
  flex: 1;
  overflow-y: auto;
  padding: 8px;
}

.property-section {
  margin-bottom: 8px;
  border: 1px solid #333;
  border-radius: 4px;
  overflow: hidden;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px;
  background: #252525;
  cursor: pointer;
  user-select: none;
}

.section-header:hover {
  background: #2a2a2a;
}

.toggle-icon {
  font-size: 8px;
  color: #666;
}

.section-content {
  padding: 8px;
}

.property-group {
  margin-bottom: 8px;
}

.property-group:last-child {
  margin-bottom: 0;
}

.property-group > label {
  display: block;
  color: #888;
  font-size: 10px;
  margin-bottom: 4px;
}

.xyz-inputs {
  display: grid;
  grid-template-columns: 1fr 1fr 1fr;
  gap: 4px;
}

.checkbox-group label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
}

.checkbox-group input[type="checkbox"] {
  width: 14px;
  height: 14px;
}

.type-select,
.property-group select,
select {
  width: 100%;
  padding: 6px 8px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 3px;
  color: #ddd;
  font-size: 12px;
  cursor: pointer;
}

.type-select option,
.property-group select option,
select option {
  background: #2a2a2a;
  color: #ddd;
}

.type-select:hover,
.property-group select:hover,
select:hover {
  border-color: #555;
}

.type-select:focus,
.property-group select:focus,
select:focus {
  outline: 1px solid #5a8fd9;
  border-color: #5a8fd9;
}

.preset-row {
  display: flex;
  flex-wrap: wrap;
  gap: 4px;
  margin-bottom: 12px;
}

.preset-row button {
  padding: 4px 8px;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
  background: #2a2a2a;
  color: #888;
  font-size: 10px;
  cursor: pointer;
  transition: all 0.1s;
}

.preset-row button:hover {
  background: #333;
  color: #e0e0e0;
}

.preset-row button.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}

.no-camera {
  flex: 1;
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 12px;
  color: #666;
}

.no-camera button {
  padding: 8px 16px;
  border: 1px solid #7c9cff;
  border-radius: 4px;
  background: transparent;
  color: #7c9cff;
  cursor: pointer;
  transition: all 0.2s;
}

.no-camera button:hover {
  background: #7c9cff;
  color: #fff;
}
</style>
