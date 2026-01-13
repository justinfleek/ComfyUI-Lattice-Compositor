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
            @change="updateProperty('type', ($event.target as HTMLSelectElement).value as CameraType)"
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
                @update:modelValue="(v: number) => updatePosition('x', v)"
                label="X"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.position.y"
                @update:modelValue="(v: number) => updatePosition('y', v)"
                label="Y"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.position.z"
                @update:modelValue="(v: number) => updatePosition('z', v)"
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
                @update:modelValue="(v: number) => updatePOI('x', v)"
                label="X"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.pointOfInterest.y"
                @update:modelValue="(v: number) => updatePOI('y', v)"
                label="Y"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.pointOfInterest.z"
                @update:modelValue="(v: number) => updatePOI('z', v)"
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
                @update:modelValue="(v: number) => updateOrientation('x', v)"
                label="X"
                unit="°"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.orientation.y"
                @update:modelValue="(v: number) => updateOrientation('y', v)"
                label="Y"
                unit="°"
                :precision="1"
              />
              <ScrubableNumber
                :modelValue="camera.orientation.z"
                @update:modelValue="(v: number) => updateOrientation('z', v)"
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
              @update:modelValue="(v: number) => updateProperty('xRotation', v)"
              unit="°"
              :precision="1"
            />
          </div>
          <div class="property-group">
            <label>Y Rotation</label>
            <ScrubableNumber
              :modelValue="camera.yRotation"
              @update:modelValue="(v: number) => updateProperty('yRotation', v)"
              unit="°"
              :precision="1"
            />
          </div>
          <div class="property-group">
            <label>Z Rotation</label>
            <ScrubableNumber
              :modelValue="camera.zRotation"
              @update:modelValue="(v: number) => updateProperty('zRotation', v)"
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
              @update:modelValue="(v: number) => updateProperty('filmSize', v)"
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
              @change="updateProperty('measureFilmSize', ($event.target as HTMLSelectElement).value as MeasureFilmSize)"
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
                @update:modelValue="(v: number) => updateDOF('focusDistance', v)"
                :min="1"
                unit="px"
                :precision="0"
              />
            </div>

            <div class="property-group">
              <label>f-Stop</label>
              <ScrubableNumber
                :modelValue="camera.depthOfField.fStop"
                @update:modelValue="(v: number) => updateDOF('fStop', v)"
                :min="0.1"
                :max="64"
                :precision="1"
              />
            </div>

            <div class="property-group">
              <label>Blur Level</label>
              <SliderInput
                :modelValue="camera.depthOfField.blurLevel"
                @update:modelValue="(v: number) => updateDOF('blurLevel', v)"
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
              @update:modelValue="(v: number) => updateIris('shape', v)"
              :min="3"
              :max="10"
              :step="1"
            />
          </div>

          <div class="property-group">
            <label>Rotation</label>
            <AngleDial
              :modelValue="camera.iris.rotation"
              @update:modelValue="(v: number) => updateIris('rotation', v)"
              :size="48"
            />
          </div>

          <div class="property-group">
            <label>Roundness</label>
            <SliderInput
              :modelValue="camera.iris.roundness"
              @update:modelValue="(v: number) => updateIris('roundness', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Aspect Ratio</label>
            <SliderInput
              :modelValue="camera.iris.aspectRatio"
              @update:modelValue="(v: number) => updateIris('aspectRatio', v)"
              :min="0.5"
              :max="2"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Diffraction Fringe</label>
            <SliderInput
              :modelValue="camera.iris.diffractionFringe"
              @update:modelValue="(v: number) => updateIris('diffractionFringe', v)"
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
              @update:modelValue="(v: number) => updateHighlight('gain', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Threshold</label>
            <SliderInput
              :modelValue="camera.highlight.threshold"
              @update:modelValue="(v: number) => updateHighlight('threshold', v)"
              :min="0"
              :max="1"
              :step="0.01"
            />
          </div>

          <div class="property-group">
            <label>Saturation</label>
            <SliderInput
              :modelValue="camera.highlight.saturation"
              @update:modelValue="(v: number) => updateHighlight('saturation', v)"
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
              @change="updateProperty('autoOrient', ($event.target as HTMLSelectElement).value as AutoOrientMode)"
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
              @update:modelValue="(v: number) => updateProperty('nearClip', v)"
              :min="0.1"
              :precision="1"
            />
          </div>

          <div class="property-group">
            <label>Far Clip</label>
            <ScrubableNumber
              :modelValue="camera.farClip"
              @update:modelValue="(v: number) => updateProperty('farClip', v)"
              :min="100"
              :precision="0"
            />
          </div>
        </div>
      </div>

      <!-- Camera Trajectory (Uni3C-style) -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('trajectory')">
          <span class="toggle-icon">{{ expandedSections.trajectory ? '▼' : '►' }}</span>
          Trajectory
        </div>
        <div v-show="expandedSections.trajectory" class="section-content">
          <!-- Trajectory Preset Selector -->
          <div class="property-group">
            <label>Motion Preset</label>
            <select v-model="trajectoryConfig.type" class="trajectory-select">
              <optgroup v-for="(types, category) in trajectoryTypesByCategory" :key="category" :label="category">
                <option v-for="type in types" :key="type" :value="type">
                  {{ formatTrajectoryName(type) }}
                </option>
              </optgroup>
            </select>
          </div>

          <!-- Trajectory Description -->
          <div class="trajectory-description">
            {{ trajectoryDescription }}
          </div>

          <!-- Duration -->
          <div class="property-group">
            <label>Duration (frames)</label>
            <ScrubableNumber
              :modelValue="trajectoryConfig.duration"
              @update:modelValue="(v: number) => trajectoryConfig.duration = v"
              :min="1"
              :max="600"
              :precision="0"
            />
          </div>

          <!-- Amplitude/Strength -->
          <div class="property-group">
            <label>Amplitude</label>
            <SliderInput
              :modelValue="Math.abs(trajectoryConfig.amplitude)"
              @update:modelValue="(v: number) => trajectoryConfig.amplitude = v * Math.sign(trajectoryConfig.amplitude || 1)"
              :min="0.1"
              :max="2"
              :step="0.1"
            />
          </div>

          <!-- Loops (for orbital/circular) -->
          <div v-if="isOrbitalTrajectory" class="property-group">
            <label>Loops</label>
            <ScrubableNumber
              :modelValue="trajectoryConfig.loops"
              @update:modelValue="(v: number) => trajectoryConfig.loops = v"
              :min="0.25"
              :max="5"
              :precision="2"
            />
          </div>

          <!-- Easing -->
          <div class="property-group">
            <label>Easing</label>
            <select v-model="trajectoryConfig.easing">
              <option value="linear">Linear</option>
              <option value="ease-in">Ease In</option>
              <option value="ease-out">Ease Out</option>
              <option value="ease-in-out">Ease In-Out</option>
              <option value="bounce">Bounce</option>
            </select>
          </div>

          <!-- Audio Reactive -->
          <div class="property-group checkbox-group">
            <label>
              <input
                type="checkbox"
                v-model="trajectoryConfig.audioReactive"
              />
              Audio Reactive
            </label>
          </div>

          <template v-if="trajectoryConfig.audioReactive">
            <div class="property-group">
              <label>Audio Feature</label>
              <select v-model="trajectoryConfig.audioFeature">
                <option value="amplitude">Amplitude</option>
                <option value="bass">Bass</option>
                <option value="mid">Mid</option>
                <option value="high">High</option>
                <option value="onsets">Onsets</option>
              </select>
            </div>

            <div class="property-group">
              <label>Sensitivity</label>
              <SliderInput
                :modelValue="trajectoryConfig.audioSensitivity ?? 1"
                @update:modelValue="(v: number) => trajectoryConfig.audioSensitivity = v"
                :min="0.1"
                :max="3"
                :step="0.1"
              />
            </div>
          </template>

          <!-- Action Buttons -->
          <div class="trajectory-actions">
            <button class="action-btn preview" @click="previewTrajectory">
              Preview
            </button>
            <button class="action-btn apply" @click="applyTrajectory">
              Apply Keyframes
            </button>
          </div>
        </div>
      </div>

      <!-- Camera Shake -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('shake')">
          <span class="toggle-icon">{{ expandedSections.shake ? '▼' : '►' }}</span>
          Camera Shake
        </div>
        <div v-show="expandedSections.shake" class="section-content">
          <!-- Shake Preset Selector -->
          <div class="property-group">
            <label>Preset</label>
            <select v-model="shakeConfig.type" @change="applyShakePreset(shakeConfig.type)">
              <option value="handheld">Handheld</option>
              <option value="subtle">Subtle</option>
              <option value="impact">Impact</option>
              <option value="earthquake">Earthquake</option>
              <option value="custom">Custom</option>
            </select>
          </div>

          <!-- Shake Description -->
          <div class="shake-description">
            <template v-if="shakeConfig.type === 'handheld'">Simulates natural handheld camera movement</template>
            <template v-else-if="shakeConfig.type === 'subtle'">Gentle shake for atmospheric tension</template>
            <template v-else-if="shakeConfig.type === 'impact'">Sharp, sudden shake for impacts or explosions</template>
            <template v-else-if="shakeConfig.type === 'earthquake'">Violent, sustained shaking</template>
            <template v-else>Custom shake parameters</template>
          </div>

          <!-- Intensity -->
          <div class="property-group">
            <label>Intensity</label>
            <SliderInput
              :modelValue="shakeConfig.intensity"
              @update:modelValue="(v: number) => shakeConfig.intensity = v"
              :min="0"
              :max="1"
              :step="0.05"
            />
          </div>

          <!-- Frequency -->
          <div class="property-group">
            <label>Frequency</label>
            <SliderInput
              :modelValue="shakeConfig.frequency"
              @update:modelValue="(v: number) => shakeConfig.frequency = v"
              :min="0.1"
              :max="5"
              :step="0.1"
            />
          </div>

          <!-- Duration -->
          <div class="property-group">
            <label>Duration (frames)</label>
            <ScrubableNumber
              :modelValue="shakeDuration"
              @update:modelValue="(v: number) => shakeDuration = v"
              :min="1"
              :max="600"
              :precision="0"
            />
          </div>

          <!-- Rotation Shake -->
          <div class="property-group checkbox-group">
            <label>
              <input
                type="checkbox"
                v-model="shakeConfig.rotationEnabled"
              />
              Rotation Shake
            </label>
          </div>

          <div v-if="shakeConfig.rotationEnabled" class="property-group">
            <label>Rotation Scale</label>
            <SliderInput
              :modelValue="shakeConfig.rotationScale"
              @update:modelValue="(v: number) => shakeConfig.rotationScale = v"
              :min="0"
              :max="2"
              :step="0.1"
            />
          </div>

          <!-- Decay -->
          <div class="property-group">
            <label>Decay</label>
            <SliderInput
              :modelValue="shakeConfig.decay"
              @update:modelValue="(v: number) => shakeConfig.decay = v"
              :min="0"
              :max="1"
              :step="0.05"
            />
          </div>

          <!-- Seed -->
          <div class="property-group">
            <label>Seed</label>
            <ScrubableNumber
              :modelValue="shakeConfig.seed"
              @update:modelValue="(v: number) => shakeConfig.seed = v"
              :min="0"
              :max="99999"
              :precision="0"
            />
          </div>

          <!-- Action Buttons -->
          <div class="shake-actions">
            <button class="action-btn preview" @click="previewShake">
              Preview
            </button>
            <button class="action-btn apply" @click="applyShakeKeyframes">
              Apply Keyframes
            </button>
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
import { computed, reactive, ref } from "vue";
import {
  type CameraShake,
  type CameraShakeConfig,
  createCameraShake,
  DEFAULT_SHAKE_CONFIG,
  SHAKE_PRESETS,
} from "@/services/cameraEnhancements";
import {
  DEFAULT_TRAJECTORY,
  generateTrajectoryKeyframes,
  getTrajectoryDescription,
  getTrajectoryPosition,
  getTrajectoryTypesByCategory,
  type TrajectoryConfig,
  type TrajectoryType,
} from "@/services/cameraTrajectory";
import { useCompositorStore } from "@/stores/compositorStore";
import { useCameraStore } from "@/stores/cameraStore";
import { useLayerStore } from "@/stores/layerStore";
import { focalLengthToFOV, fovToFocalLength } from "../../services/math3d";
import { CAMERA_PRESETS } from "../../types/camera";
import type { AutoOrientMode, Camera3D, CameraType, MeasureFilmSize } from "../../types/camera";

// Store connection
const store = useCompositorStore();
const cameraStore = useCameraStore();
const layerStore = useLayerStore();

// Get camera from store (active camera or selected camera layer)
const camera = computed<Camera3D | null>(() => {
  // First, check if a camera layer is selected
  const selectedLayer = store.selectedLayer;
  if (selectedLayer?.type === "camera" && selectedLayer.data) {
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
  clipping: false,
  trajectory: false,
  shake: false,
});

// Trajectory configuration
const trajectoryConfig = reactive<TrajectoryConfig>({
  ...DEFAULT_TRAJECTORY,
});

// Camera Shake configuration
const shakeConfig = reactive<CameraShakeConfig>({
  ...DEFAULT_SHAKE_CONFIG,
});
const shakeEnabled = ref(false);
const shakeDuration = ref(81); // Default composition length
let activeCameraShake: CameraShake | null = null;

// Get trajectory types grouped by category
const trajectoryTypesByCategory = computed(() =>
  getTrajectoryTypesByCategory(),
);

// Get description for current trajectory type
const trajectoryDescription = computed(() =>
  getTrajectoryDescription(trajectoryConfig.type),
);

// Check if current trajectory is orbital (shows loops control)
const isOrbitalTrajectory = computed(() => {
  const orbitalTypes: TrajectoryType[] = [
    "orbit",
    "orbit_reverse",
    "circle",
    "figure8",
    "spiral_in",
    "spiral_out",
  ];
  return orbitalTypes.includes(trajectoryConfig.type);
});

// Format trajectory name for display
function formatTrajectoryName(type: TrajectoryType): string {
  return type
    .split("_")
    .map((word) => word.charAt(0).toUpperCase() + word.slice(1))
    .join(" ");
}

// Preview animation timer
const previewAnimationId = ref<number | null>(null);

// Preview the trajectory motion
function previewTrajectory() {
  if (!camera.value) return;

  // Cancel any existing preview
  if (previewAnimationId.value !== null) {
    cancelAnimationFrame(previewAnimationId.value);
  }

  const startTime = performance.now();
  const duration = (trajectoryConfig.duration / 30) * 1000; // Convert frames to ms at 30fps

  // Use current camera position as center
  const config: TrajectoryConfig = {
    ...trajectoryConfig,
    center: { ...camera.value.pointOfInterest },
    baseDistance: Math.sqrt(
      (camera.value.position.x - camera.value.pointOfInterest.x) ** 2 +
        (camera.value.position.y - camera.value.pointOfInterest.y) ** 2 +
        (camera.value.position.z - camera.value.pointOfInterest.z) ** 2,
    ),
  };

  function animate() {
    const elapsed = performance.now() - startTime;
    const t = Math.min(elapsed / duration, 1);

    const { position, target } = getTrajectoryPosition(config, t);

    // Update camera position live
    if (camera.value?.id) {
      cameraStore.updateCamera(store, camera.value.id, {
        position,
        pointOfInterest: target,
      });
    }

    if (t < 1) {
      previewAnimationId.value = requestAnimationFrame(animate);
    } else {
      previewAnimationId.value = null;
    }
  }

  animate();
}

// Apply trajectory as keyframes
function applyTrajectory() {
  if (!camera.value) return;

  // Calculate base distance from current camera setup
  const baseDistance = Math.sqrt(
    (camera.value.position.x - camera.value.pointOfInterest.x) ** 2 +
      (camera.value.position.y - camera.value.pointOfInterest.y) ** 2 +
      (camera.value.position.z - camera.value.pointOfInterest.z) ** 2,
  );

  const config: TrajectoryConfig = {
    ...trajectoryConfig,
    center: { ...camera.value.pointOfInterest },
    baseDistance,
  };

  const keyframes = generateTrajectoryKeyframes(config, store.currentFrame);

  // Apply position keyframes
  for (const kf of keyframes.position) {
    cameraStore.addCameraKeyframe(store, camera.value.id, {
      frame: kf.frame,
      position: kf.position,
      spatialInterpolation: kf.spatialInterpolation,
      temporalInterpolation: kf.temporalInterpolation,
    });
  }

  // Apply point of interest keyframes
  for (const kf of keyframes.pointOfInterest) {
    cameraStore.addCameraKeyframe(store, camera.value.id, {
      frame: kf.frame,
      pointOfInterest: kf.pointOfInterest,
      spatialInterpolation: kf.spatialInterpolation,
      temporalInterpolation: kf.temporalInterpolation,
    });
  }

  // Apply zoom keyframes if present
  if (keyframes.zoom) {
    for (const kf of keyframes.zoom) {
      cameraStore.addCameraKeyframe(store, camera.value.id, {
        frame: kf.frame,
        zoom: kf.zoom,
        temporalInterpolation: kf.temporalInterpolation,
      });
    }
  }

  console.log(
    `Applied ${keyframes.position.length} camera trajectory keyframes`,
  );
}

// ============================================================================
// CAMERA SHAKE
// ============================================================================

function applyShakePreset(preset: CameraShakeConfig["type"]) {
  const presetConfig = SHAKE_PRESETS[preset];
  Object.assign(shakeConfig, presetConfig, { type: preset });
}

function previewShake() {
  if (!camera.value) return;

  // Create shake instance
  activeCameraShake = createCameraShake(
    shakeConfig.type,
    shakeConfig,
    store.currentFrame,
    shakeDuration.value,
  );

  // Store original camera position
  const originalPosition = { ...camera.value.position };
  const originalOrientation = { ...camera.value.orientation };

  // Preview animation
  const startTime = performance.now();
  const duration = (shakeDuration.value / 30) * 1000;

  function animate() {
    const elapsed = performance.now() - startTime;
    const frame = Math.floor((elapsed / 1000) * 30) + store.currentFrame;

    if (elapsed < duration && activeCameraShake) {
      const offset = activeCameraShake.getOffset(frame);

      if (camera.value?.id) {
        cameraStore.updateCamera(store, camera.value.id, {
          position: {
            x: originalPosition.x + offset.position.x,
            y: originalPosition.y + offset.position.y,
            z: originalPosition.z + offset.position.z,
          },
          orientation: {
            x: originalOrientation.x + offset.rotation.x,
            y: originalOrientation.y + offset.rotation.y,
            z: originalOrientation.z + offset.rotation.z,
          },
        });
      }

      requestAnimationFrame(animate);
    } else {
      // Restore original position
      if (camera.value?.id) {
        cameraStore.updateCamera(store, camera.value.id, {
          position: originalPosition,
          orientation: originalOrientation,
        });
      }
      activeCameraShake = null;
    }
  }

  requestAnimationFrame(animate);
}

function applyShakeKeyframes() {
  if (!camera.value) return;

  // Create shake instance
  const shake = createCameraShake(
    shakeConfig.type,
    shakeConfig,
    store.currentFrame,
    shakeDuration.value,
  );

  // Get existing keyframes for the camera (stored separately in store, not on Camera3D)
  const existingKeyframes = store.getCameraKeyframes(camera.value.id);

  // Generate shaken keyframes
  const shakenKeyframes = shake.generateKeyframes(existingKeyframes, 2); // Sample every 2 frames

  // Apply the shaken keyframes
  for (const kf of shakenKeyframes) {
    cameraStore.addCameraKeyframe(store, camera.value.id, kf);
  }

  console.log(`Applied ${shakenKeyframes.length} camera shake keyframes`);
}

function toggleSection(section: keyof typeof expandedSections) {
  expandedSections[section] = !expandedSections[section];
}

function updateProperty<K extends keyof Camera3D>(key: K, value: Camera3D[K]) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, { [key]: value });
}

function updatePosition(axis: "x" | "y" | "z", value: number) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, {
    position: { ...camera.value.position, [axis]: value },
  });
}

function updatePOI(axis: "x" | "y" | "z", value: number) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, {
    pointOfInterest: { ...camera.value.pointOfInterest, [axis]: value },
  });
}

function updateOrientation(axis: "x" | "y" | "z", value: number) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, {
    orientation: { ...camera.value.orientation, [axis]: value },
  });
}

function updateFocalLength(value: number) {
  if (!camera.value) return;
  // Convert focal length to FOV: focalLengthToFOV returns radians, store as degrees
  const angleOfViewRadians = focalLengthToFOV(value, camera.value.filmSize);
  const angleOfView = angleOfViewRadians * (180 / Math.PI);
  cameraStore.updateCamera(store, camera.value.id, {
    focalLength: value,
    angleOfView,
  });
}

function updateAngleOfView(value: number) {
  if (!camera.value) return;
  // Convert FOV from degrees (UI) to radians (math functions)
  const valueRadians = value * (Math.PI / 180);
  const focalLength = fovToFocalLength(valueRadians, camera.value.filmSize);
  cameraStore.updateCamera(store, camera.value.id, {
    angleOfView: value,
    focalLength,
  });
}

function updateDOF<K extends keyof Camera3D["depthOfField"]>(
  key: K,
  value: Camera3D["depthOfField"][K],
) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, {
    depthOfField: { ...camera.value.depthOfField, [key]: value },
  });
}

function updateIris<K extends keyof Camera3D["iris"]>(
  key: K,
  value: Camera3D["iris"][K],
) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, {
    iris: { ...camera.value.iris, [key]: value },
  });
}

function updateHighlight<K extends keyof Camera3D["highlight"]>(
  key: K,
  value: Camera3D["highlight"][K],
) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, {
    highlight: { ...camera.value.highlight, [key]: value },
  });
}

function applyPreset(preset: (typeof CAMERA_PRESETS)[number]) {
  if (!camera.value) return;
  cameraStore.updateCamera(store, camera.value.id, {
    focalLength: preset.focalLength,
    angleOfView: preset.angleOfView,
    zoom: preset.zoom,
  });
}

function createCamera() {
  layerStore.createCameraLayer(store);
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
  font-size: 13px;
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
  font-size: 11px;
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
  font-size: 12px;
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
  font-size: 12px;
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

/* Trajectory Section */
.trajectory-select {
  font-size: 13px;
}

.trajectory-description {
  padding: 8px;
  background: #252525;
  border-radius: 4px;
  color: #888;
  font-size: 12px;
  font-style: italic;
  margin-bottom: 12px;
  line-height: 1.4;
}

.trajectory-actions {
  display: flex;
  gap: 8px;
  margin-top: 12px;
}

.action-btn {
  flex: 1;
  padding: 8px 12px;
  border: 1px solid #444;
  border-radius: 4px;
  background: #2a2a2a;
  color: #ddd;
  font-size: 13px;
  cursor: pointer;
  transition: all 0.15s;
}

.action-btn:hover {
  background: #333;
  border-color: #555;
}

.action-btn.preview {
  border-color: #5a8fd9;
  color: #5a8fd9;
}

.action-btn.preview:hover {
  background: #5a8fd9;
  color: #fff;
}

.action-btn.apply {
  border-color: #4caf50;
  color: #4caf50;
}

.action-btn.apply:hover {
  background: #4caf50;
  color: #fff;
}

/* Camera Shake Styles */
.shake-description {
  padding: 8px;
  background: #252525;
  border-radius: 4px;
  color: #888;
  font-size: 12px;
  font-style: italic;
  margin-bottom: 12px;
  line-height: 1.4;
}

.shake-actions {
  display: flex;
  gap: 8px;
  margin-top: 12px;
}
</style>
