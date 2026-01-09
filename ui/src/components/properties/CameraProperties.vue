<template>
  <div class="camera-properties">
    <!-- Camera Settings Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('settings')">
        <span class="expand-icon">{{ expandedSections.includes('settings') ? '▼' : '►' }}</span>
        <span class="section-title">Camera Settings</span>
      </div>

      <div v-if="expandedSections.includes('settings')" class="section-content">
        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="cameraData.isActiveCamera"
              @change="update('isActiveCamera', ($event.target as HTMLInputElement).checked)"
            />
            Active Camera
          </label>
        </div>

        <div class="property-row">
          <label>FOV</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('FOV') ?? 50"
            @update:modelValue="(v: number) => updateAnimatable('FOV', v, 'animatedFov')"
            :min="10"
            :max="120"
            unit="°"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('FOV') }" @click="toggleKeyframe('FOV', 'animatedFov', 50)">◆</button>
        </div>

        <div class="property-row">
          <label>Focal Length</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Focal Length') ?? 50"
            @update:modelValue="(v: number) => updateAnimatable('Focal Length', v, 'animatedFocalLength')"
            :min="10"
            :max="300"
            unit="mm"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Focal Length') }" @click="toggleKeyframe('Focal Length', 'animatedFocalLength', 50)">◆</button>
        </div>
      </div>
    </div>

    <!-- Depth of Field Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('dof')">
        <span class="expand-icon">{{ expandedSections.includes('dof') ? '▼' : '►' }}</span>
        <span class="section-title">Depth of Field</span>
        <input
          type="checkbox"
          :checked="dofEnabled"
          @click.stop
          @change="toggleDOF"
          class="section-toggle"
        />
      </div>

      <div v-if="expandedSections.includes('dof') && dofEnabled" class="section-content">
        <div class="property-row">
          <label>Focus Distance</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Focus Distance') ?? depthOfField.focusDistance"
            @update:modelValue="(v: number) => updateDOFAnimatable('Focus Distance', v, 'focusDistance')"
            :min="0"
            :max="10000"
            unit="px"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Focus Distance') }" @click="toggleKeyframe('Focus Distance', 'animatedFocusDistance', depthOfField.focusDistance)">◆</button>
        </div>

        <div class="property-row">
          <label>Aperture</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Aperture') ?? depthOfField.aperture"
            @update:modelValue="(v: number) => updateDOFAnimatable('Aperture', v, 'aperture')"
            :min="0.5"
            :max="32"
            :step="0.1"
            unit="f/"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Aperture') }" @click="toggleKeyframe('Aperture', 'animatedAperture', depthOfField.aperture)">◆</button>
        </div>

        <div class="property-row">
          <label>Blur Level</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Blur Level') ?? depthOfField.blurLevel"
            @update:modelValue="(v: number) => updateDOFAnimatable('Blur Level', v, 'blurLevel')"
            :min="0"
            :max="100"
            unit="%"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Blur Level') }" @click="toggleKeyframe('Blur Level', 'animatedBlurLevel', depthOfField.blurLevel)">◆</button>
        </div>
      </div>
    </div>

    <!-- Path Following Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('path')">
        <span class="expand-icon">{{ expandedSections.includes('path') ? '▼' : '►' }}</span>
        <span class="section-title">Path Following</span>
        <input
          type="checkbox"
          :checked="pathFollowing.enabled"
          @click.stop
          @change="togglePathFollowing"
          class="section-toggle"
        />
      </div>

      <div v-if="expandedSections.includes('path') && pathFollowing.enabled" class="section-content">
        <div class="property-row">
          <label>Path Layer</label>
          <select
            class="path-select"
            :value="pathFollowing.pathLayerId"
            @change="updatePathLayer"
          >
            <option value="">Select Path...</option>
            <option
              v-for="layer in splineLayers"
              :key="layer.id"
              :value="layer.id"
            >
              {{ layer.type === 'path' ? '⤳ ' : '〰 ' }}{{ layer.name }}
            </option>
          </select>
        </div>

        <div class="property-row">
          <label>Position</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Path Position') ?? pathFollowing.parameter?.value ?? 0"
            @update:modelValue="(v: number) => updatePathProperty('parameter', v)"
            :min="0"
            :max="1"
            :step="0.001"
            :precision="3"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Path Position') }" @click="togglePathKeyframe('Path Position')">◆</button>
        </div>

        <div class="property-row">
          <label>Look Ahead</label>
          <ScrubableNumber
            :modelValue="pathFollowing.lookAhead ?? 0.05"
            @update:modelValue="(v: number) => updatePathConfig('lookAhead', v)"
            :min="0"
            :max="0.5"
            :step="0.01"
            :precision="2"
          />
        </div>

        <div class="property-row">
          <label>Banking</label>
          <ScrubableNumber
            :modelValue="pathFollowing.bankingStrength ?? 0"
            @update:modelValue="(v: number) => updatePathConfig('bankingStrength', v)"
            :min="0"
            :max="1"
            :step="0.05"
          />
        </div>

        <div class="property-row">
          <label>Height Offset</label>
          <ScrubableNumber
            :modelValue="pathFollowing.offsetY ?? 0"
            @update:modelValue="(v: number) => updatePathConfig('offsetY', v)"
            unit="px"
          />
        </div>

        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="pathFollowing.alignToPath"
              @change="updatePathConfig('alignToPath', ($event.target as HTMLInputElement).checked)"
            />
            Align to Path
          </label>
        </div>

        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="pathFollowing.autoAdvance"
              @change="updatePathConfig('autoAdvance', ($event.target as HTMLInputElement).checked)"
            />
            Auto Advance
          </label>
        </div>

        <div v-if="pathFollowing.autoAdvance" class="property-row">
          <label>Speed</label>
          <ScrubableNumber
            :modelValue="pathFollowing.autoAdvanceSpeed ?? 0.01"
            @update:modelValue="(v: number) => updatePathConfig('autoAdvanceSpeed', v)"
            :min="0.001"
            :max="0.1"
            :step="0.001"
            :precision="3"
          />
        </div>
      </div>
    </div>

    <!-- Camera Shake Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('shake')">
        <span class="expand-icon">{{ expandedSections.includes('shake') ? '▼' : '►' }}</span>
        <span class="section-title">Camera Shake</span>
        <input
          type="checkbox"
          :checked="cameraShake.enabled"
          @click.stop
          @change="toggleCameraShake"
          class="section-toggle"
        />
      </div>

      <div v-if="expandedSections.includes('shake') && cameraShake.enabled" class="section-content">
        <div class="property-row">
          <label>Type</label>
          <select
            class="path-select"
            :value="cameraShake.type"
            @change="updateShakeConfig('type', ($event.target as HTMLSelectElement).value)"
          >
            <option value="handheld">Handheld</option>
            <option value="impact">Impact</option>
            <option value="earthquake">Earthquake</option>
            <option value="subtle">Subtle</option>
          </select>
        </div>

        <div class="property-row">
          <label>Intensity</label>
          <ScrubableNumber
            :modelValue="cameraShake.intensity"
            @update:modelValue="(v: number) => updateShakeConfig('intensity', v)"
            :min="0"
            :max="1"
            :step="0.05"
            :precision="2"
          />
        </div>

        <div class="property-row">
          <label>Frequency</label>
          <ScrubableNumber
            :modelValue="cameraShake.frequency"
            @update:modelValue="(v: number) => updateShakeConfig('frequency', v)"
            :min="0.1"
            :max="5"
            :step="0.1"
          />
        </div>

        <div class="property-row">
          <label>Decay</label>
          <ScrubableNumber
            :modelValue="cameraShake.decay"
            @update:modelValue="(v: number) => updateShakeConfig('decay', v)"
            :min="0"
            :max="1"
            :step="0.05"
            :precision="2"
          />
        </div>

        <div class="property-row">
          <label>Start Frame</label>
          <ScrubableNumber
            :modelValue="cameraShake.startFrame"
            @update:modelValue="(v: number) => updateShakeConfig('startFrame', v)"
            :min="0"
            :step="1"
          />
        </div>

        <div class="property-row">
          <label>Duration</label>
          <ScrubableNumber
            :modelValue="cameraShake.duration"
            @update:modelValue="(v: number) => updateShakeConfig('duration', v)"
            :min="1"
            :step="1"
          />
        </div>

        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="cameraShake.rotationEnabled"
              @change="updateShakeConfig('rotationEnabled', ($event.target as HTMLInputElement).checked)"
            />
            Include Rotation
          </label>
        </div>
      </div>
    </div>

    <!-- Rack Focus Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('rackFocus')">
        <span class="expand-icon">{{ expandedSections.includes('rackFocus') ? '▼' : '►' }}</span>
        <span class="section-title">Rack Focus</span>
        <input
          type="checkbox"
          :checked="rackFocus.enabled"
          @click.stop
          @change="toggleRackFocus"
          class="section-toggle"
        />
      </div>

      <div v-if="expandedSections.includes('rackFocus') && rackFocus.enabled" class="section-content">
        <div class="property-row">
          <label>Start Distance</label>
          <ScrubableNumber
            :modelValue="rackFocus.startDistance"
            @update:modelValue="(v: number) => updateRackFocusConfig('startDistance', v)"
            :min="0"
            :max="10000"
            unit="px"
          />
        </div>

        <div class="property-row">
          <label>End Distance</label>
          <ScrubableNumber
            :modelValue="rackFocus.endDistance"
            @update:modelValue="(v: number) => updateRackFocusConfig('endDistance', v)"
            :min="0"
            :max="10000"
            unit="px"
          />
        </div>

        <div class="property-row">
          <label>Start Frame</label>
          <ScrubableNumber
            :modelValue="rackFocus.startFrame"
            @update:modelValue="(v: number) => updateRackFocusConfig('startFrame', v)"
            :min="0"
            :step="1"
          />
        </div>

        <div class="property-row">
          <label>Duration</label>
          <ScrubableNumber
            :modelValue="rackFocus.duration"
            @update:modelValue="(v: number) => updateRackFocusConfig('duration', v)"
            :min="1"
            :step="1"
          />
        </div>

        <div class="property-row">
          <label>Easing</label>
          <select
            class="path-select"
            :value="rackFocus.easing"
            @change="updateRackFocusConfig('easing', ($event.target as HTMLSelectElement).value)"
          >
            <option value="linear">Linear</option>
            <option value="ease-in">Ease In</option>
            <option value="ease-out">Ease Out</option>
            <option value="ease-in-out">Ease In/Out</option>
            <option value="snap">Snap</option>
          </select>
        </div>

        <div class="property-row">
          <label>Hold Start</label>
          <ScrubableNumber
            :modelValue="rackFocus.holdStart"
            @update:modelValue="(v: number) => updateRackFocusConfig('holdStart', v)"
            :min="0"
            :step="1"
          />
        </div>

        <div class="property-row">
          <label>Hold End</label>
          <ScrubableNumber
            :modelValue="rackFocus.holdEnd"
            @update:modelValue="(v: number) => updateRackFocusConfig('holdEnd', v)"
            :min="0"
            :step="1"
          />
        </div>
      </div>
    </div>

    <!-- Trajectory Presets Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('trajectory')">
        <span class="expand-icon">{{ expandedSections.includes('trajectory') ? '▼' : '►' }}</span>
        <span class="section-title">Trajectory Presets</span>
      </div>

      <div v-if="expandedSections.includes('trajectory')" class="section-content">
        <div class="trajectory-grid">
          <div class="trajectory-group">
            <div class="trajectory-group-title">Orbital</div>
            <button class="trajectory-btn" @click="applyTrajectory('orbit')">Orbit</button>
            <button class="trajectory-btn" @click="applyTrajectory('orbit_reverse')">Orbit Rev</button>
            <button class="trajectory-btn" @click="applyTrajectory('swing1')">Swing 1</button>
            <button class="trajectory-btn" @click="applyTrajectory('swing2')">Swing 2</button>
            <button class="trajectory-btn" @click="applyTrajectory('circle')">Circle</button>
            <button class="trajectory-btn" @click="applyTrajectory('figure8')">Figure 8</button>
          </div>

          <div class="trajectory-group">
            <div class="trajectory-group-title">Dolly/Zoom</div>
            <button class="trajectory-btn" @click="applyTrajectory('dolly_in')">Dolly In</button>
            <button class="trajectory-btn" @click="applyTrajectory('dolly_out')">Dolly Out</button>
            <button class="trajectory-btn" @click="applyTrajectory('spiral_in')">Spiral In</button>
            <button class="trajectory-btn" @click="applyTrajectory('spiral_out')">Spiral Out</button>
            <button class="trajectory-btn" @click="applyTrajectory('zoom_in')">Zoom In</button>
            <button class="trajectory-btn" @click="applyTrajectory('zoom_out')">Zoom Out</button>
          </div>

          <div class="trajectory-group">
            <div class="trajectory-group-title">Pan/Tilt</div>
            <button class="trajectory-btn" @click="applyTrajectory('pan_left')">Pan Left</button>
            <button class="trajectory-btn" @click="applyTrajectory('pan_right')">Pan Right</button>
            <button class="trajectory-btn" @click="applyTrajectory('tilt_up')">Tilt Up</button>
            <button class="trajectory-btn" @click="applyTrajectory('tilt_down')">Tilt Down</button>
          </div>

          <div class="trajectory-group">
            <div class="trajectory-group-title">Crane/Truck</div>
            <button class="trajectory-btn" @click="applyTrajectory('crane_up')">Crane Up</button>
            <button class="trajectory-btn" @click="applyTrajectory('crane_down')">Crane Down</button>
            <button class="trajectory-btn" @click="applyTrajectory('truck_left')">Truck Left</button>
            <button class="trajectory-btn" @click="applyTrajectory('truck_right')">Truck Right</button>
            <button class="trajectory-btn" @click="applyTrajectory('arc_left')">Arc Left</button>
            <button class="trajectory-btn" @click="applyTrajectory('arc_right')">Arc Right</button>
          </div>
        </div>
      </div>
    </div>

    <!-- Camera Position/Target Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('position')">
        <span class="expand-icon">{{ expandedSections.includes('position') ? '▼' : '►' }}</span>
        <span class="section-title">Position & Target</span>
      </div>

      <div v-if="expandedSections.includes('position')" class="section-content">
        <div class="property-row">
          <label>Position X</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Position', 'x')"
            @update:modelValue="(v: number) => updateVec3Property('Position', 'x', v, 'animatedPosition')"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Position') }" @click="toggleVec3Keyframe('Position', 'animatedPosition')">◆</button>
        </div>

        <div class="property-row">
          <label>Position Y</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Position', 'y')"
            @update:modelValue="(v: number) => updateVec3Property('Position', 'y', v, 'animatedPosition')"
          />
        </div>

        <div class="property-row">
          <label>Position Z</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Position', 'z')"
            @update:modelValue="(v: number) => updateVec3Property('Position', 'z', v, 'animatedPosition')"
          />
        </div>

        <div class="property-row separator">
          <span class="separator-line"></span>
        </div>

        <div class="property-row">
          <label>Target X</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Target', 'x')"
            @update:modelValue="(v: number) => updateVec3Property('Target', 'x', v, 'animatedTarget')"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Target') }" @click="toggleVec3Keyframe('Target', 'animatedTarget')">◆</button>
        </div>

        <div class="property-row">
          <label>Target Y</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Target', 'y')"
            @update:modelValue="(v: number) => updateVec3Property('Target', 'y', v, 'animatedTarget')"
          />
        </div>

        <div class="property-row">
          <label>Target Z</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Target', 'z')"
            @update:modelValue="(v: number) => updateVec3Property('Target', 'z', v, 'animatedTarget')"
          />
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import {
  createTrajectoryFromPreset,
  generateTrajectoryKeyframes,
  type TrajectoryType,
} from "@/services/cameraTrajectory";
import { useCompositorStore } from "@/stores/compositorStore";
import { createKeyframe } from "@/types/animation";
import type {
  AnimatableProperty,
  CameraDepthOfField,
  CameraLayerData,
  CameraPathFollowing,
  CameraRackFocusData,
  CameraShakeData,
  Layer,
  Vec3,
} from "@/types/project";

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

const expandedSections = ref<string[]>(["settings", "dof"]);

// Get camera data with defaults
const cameraData = computed<CameraLayerData>(() => {
  return (
    (props.layer.data as CameraLayerData) || {
      cameraId: "",
      isActiveCamera: false,
    }
  );
});

// Depth of field with defaults
const depthOfField = computed<CameraDepthOfField>(() => {
  return (
    cameraData.value.depthOfField || {
      enabled: false,
      focusDistance: 500,
      aperture: 2.8,
      blurLevel: 50,
    }
  );
});

const dofEnabled = computed(() => depthOfField.value.enabled);

// Path following with defaults
const pathFollowing = computed<CameraPathFollowing>(() => {
  return (
    cameraData.value.pathFollowing || {
      enabled: false,
      pathLayerId: "",
      parameter: {
        id: "",
        name: "Path Position",
        type: "number",
        value: 0,
        animated: false,
        keyframes: [],
        group: "Path Following",
      },
      lookAhead: 0.05,
      bankingStrength: 0,
      offsetY: 0,
      alignToPath: true,
      autoAdvance: false,
      autoAdvanceSpeed: 0.01,
    }
  );
});

// Get available spline and path layers for path following
// Camera can follow both visible shape splines (e.g., logo outline) and invisible path guides
const splineLayers = computed(() => {
  return store.layers.filter(
    (l) =>
      (l.type === "spline" || l.type === "path") && l.id !== props.layer.id,
  );
});

// Camera shake with defaults
const cameraShake = computed<CameraShakeData>(() => {
  return (
    cameraData.value.shake || {
      enabled: false,
      type: "handheld",
      intensity: 0.3,
      frequency: 1.0,
      rotationEnabled: true,
      rotationScale: 0.5,
      seed: Math.floor(Math.random() * 100000),
      decay: 0,
      startFrame: 0,
      duration: 81,
    }
  );
});

// Rack focus with defaults
const rackFocus = computed<CameraRackFocusData>(() => {
  return (
    cameraData.value.rackFocus || {
      enabled: false,
      startDistance: 500,
      endDistance: 2000,
      duration: 30,
      startFrame: 0,
      easing: "ease-in-out",
      holdStart: 0,
      holdEnd: 0,
    }
  );
});

// Toggle section visibility
function toggleSection(section: string) {
  const idx = expandedSections.value.indexOf(section);
  if (idx >= 0) {
    expandedSections.value.splice(idx, 1);
  } else {
    expandedSections.value.push(section);
  }
}

// Update camera data
function update(key: keyof CameraLayerData | string, value: any) {
  store.updateLayer(props.layer.id, {
    data: { ...cameraData.value, [key]: value },
  });
  emit("update");
}

// Toggle DOF
function toggleDOF(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  const newDOF = { ...depthOfField.value, enabled: checked };
  update("depthOfField", newDOF);
}

// Toggle path following
function togglePathFollowing(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  const newPath = { ...pathFollowing.value, enabled: checked };
  update("pathFollowing", newPath);
}

// Update path layer
function updatePathLayer(e: Event) {
  const layerId = (e.target as HTMLSelectElement).value;
  const newPath = { ...pathFollowing.value, pathLayerId: layerId };
  update("pathFollowing", newPath);
}

// Update path config value
function updatePathConfig(key: keyof CameraPathFollowing, value: any) {
  const newPath = { ...pathFollowing.value, [key]: value };
  update("pathFollowing", newPath);
}

// Toggle camera shake
function toggleCameraShake(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  const newShake = { ...cameraShake.value, enabled: checked };
  update("shake", newShake);
}

// Update shake config value
function updateShakeConfig(key: keyof CameraShakeData, value: any) {
  const newShake = { ...cameraShake.value, [key]: value };
  update("shake", newShake);
}

// Toggle rack focus
function toggleRackFocus(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  const newRackFocus = { ...rackFocus.value, enabled: checked };
  update("rackFocus", newRackFocus);

  // Enable DOF if enabling rack focus
  if (checked) {
    const newDOF = { ...depthOfField.value, enabled: true };
    update("depthOfField", newDOF);
  }
}

// Update rack focus config value
function updateRackFocusConfig(key: keyof CameraRackFocusData, value: any) {
  const newRackFocus = { ...rackFocus.value, [key]: value };
  update("rackFocus", newRackFocus);
}

// Apply trajectory preset
function applyTrajectory(trajectoryType: TrajectoryType) {
  const comp = store.getActiveComp();
  const compSettings = comp?.settings || {
    width: 1920,
    height: 1080,
    frameCount: 81,
  };

  // Create trajectory config
  const trajectoryConfig = createTrajectoryFromPreset(trajectoryType, {
    duration: compSettings.frameCount,
    center: {
      x: compSettings.width / 2,
      y: compSettings.height / 2,
      z: 0,
    },
  });

  // Generate keyframes
  const keyframes = generateTrajectoryKeyframes(trajectoryConfig, 0, 5);

  // Store trajectory keyframes in camera data
  update("trajectoryKeyframes", {
    position: keyframes.position,
    pointOfInterest: keyframes.pointOfInterest,
    zoom: keyframes.zoom,
  });

  emit("update");
}

// Update path parameter (animatable)
function updatePathProperty(_key: string, value: number) {
  const param = pathFollowing.value.parameter;
  const newParam = { ...param, value };
  const newPath = { ...pathFollowing.value, parameter: newParam };
  update("pathFollowing", newPath);

  // Also update in layer.properties if it exists (via store)
  const prop = getProperty("Path Position");
  if (prop) {
    const updatedProperties = (props.layer.properties || []).map((p) =>
      p.name === "Path Position" ? { ...p, value } : p,
    );
    store.updateLayer(props.layer.id, { properties: updatedProperties });
  }
}

// Get animatable property from layer.properties
function getProperty(name: string): AnimatableProperty<number> | undefined {
  return props.layer.properties?.find((p) => p.name === name) as
    | AnimatableProperty<number>
    | undefined;
}

// Get property value
function getPropertyValue(name: string): number | undefined {
  const prop = getProperty(name);
  return prop?.value;
}

// Check if animated
function isAnimated(name: string): boolean {
  const prop = getProperty(name);
  return prop?.animated ?? false;
}

// Update animatable property
function updateAnimatable(propName: string, value: number, dataKey: string) {
  // Update in layer.properties (via store)
  const prop = getProperty(propName);
  if (prop) {
    const updatedProperties = (props.layer.properties || []).map((p) =>
      p.name === propName ? { ...p, value } : p,
    );
    store.updateLayer(props.layer.id, { properties: updatedProperties });
  }

  // Update in camera data's animated property
  const animProp = (cameraData.value as any)[dataKey] as
    | AnimatableProperty<number>
    | undefined;
  if (animProp) {
    const updatedAnimProp = { ...animProp, value };
    update(dataKey, updatedAnimProp);
  }
  emit("update");
}

// Update DOF animatable property
function updateDOFAnimatable(
  propName: string,
  value: number,
  dofKey: keyof CameraDepthOfField,
) {
  const newDOF = { ...depthOfField.value, [dofKey]: value };
  update("depthOfField", newDOF);

  // Also update in layer.properties (via store)
  const prop = getProperty(propName);
  if (prop) {
    const updatedProperties = (props.layer.properties || []).map((p) =>
      p.name === propName ? { ...p, value } : p,
    );
    store.updateLayer(props.layer.id, { properties: updatedProperties });
  }
  emit("update");
}

// Ensure property exists in layer.properties
function ensureProperty(propName: string, defaultValue: number, group: string) {
  const existingProperties = props.layer.properties || [];
  const existing = existingProperties.find((p) => p.name === propName);

  if (!existing) {
    const newProperty = {
      id: `prop_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
      name: propName,
      type: "number",
      value: defaultValue,
      animated: false,
      keyframes: [],
      group,
    } as AnimatableProperty<number>;

    // Update via store to track in history
    store.updateLayer(props.layer.id, {
      properties: [...existingProperties, newProperty],
    });
  }
}

// Toggle keyframe
function toggleKeyframe(
  propName: string,
  _dataKey: string,
  defaultValue: number,
) {
  ensureProperty(
    propName,
    defaultValue,
    propName.includes("Focus") ||
      propName.includes("Aperture") ||
      propName.includes("Blur")
      ? "Depth of Field"
      : "Camera",
  );

  const prop = getProperty(propName);
  if (prop) {
    const frame = store.currentFrame;
    const hasKeyframeAtFrame = prop.keyframes.some((k) => k.frame === frame);

    let updatedKeyframes: typeof prop.keyframes;
    let updatedAnimated: boolean;

    if (hasKeyframeAtFrame) {
      updatedKeyframes = prop.keyframes.filter((k) => k.frame !== frame);
      updatedAnimated = updatedKeyframes.length > 0;
    } else {
      updatedKeyframes = [
        ...prop.keyframes,
        createKeyframe(frame, prop.value, "linear"),
      ];
      updatedAnimated = true;
    }

    // Update via store to track in history
    const updatedProperties = (props.layer.properties || []).map((p) =>
      p.name === propName
        ? { ...p, keyframes: updatedKeyframes, animated: updatedAnimated }
        : p,
    );
    store.updateLayer(props.layer.id, { properties: updatedProperties });
    emit("update");
  }
}

// Toggle path keyframe
function togglePathKeyframe(propName: string) {
  ensureProperty(
    propName,
    pathFollowing.value.parameter?.value ?? 0,
    "Path Following",
  );

  const prop = getProperty(propName);
  if (prop) {
    const frame = store.currentFrame;
    const hasKeyframeAtFrame = prop.keyframes.some((k) => k.frame === frame);

    let updatedKeyframes: typeof prop.keyframes;
    let updatedAnimated: boolean;

    if (hasKeyframeAtFrame) {
      updatedKeyframes = prop.keyframes.filter((k) => k.frame !== frame);
      updatedAnimated = updatedKeyframes.length > 0;
    } else {
      updatedKeyframes = [
        ...prop.keyframes,
        createKeyframe(frame, prop.value, "linear"),
      ];
      updatedAnimated = true;
    }

    // Update via store to track in history
    const updatedProperties = (props.layer.properties || []).map((p) =>
      p.name === propName
        ? { ...p, keyframes: updatedKeyframes, animated: updatedAnimated }
        : p,
    );
    store.updateLayer(props.layer.id, { properties: updatedProperties });
    emit("update");
  }
}

// Get Vec3 value
function getVec3Value(propName: string, axis: "x" | "y" | "z"): number {
  const dataKey =
    propName === "Position" ? "animatedPosition" : "animatedTarget";
  const animProp = (cameraData.value as any)[dataKey] as
    | AnimatableProperty<Vec3>
    | undefined;
  if (animProp?.value) {
    return animProp.value[axis] ?? 0;
  }
  return 0;
}

// Update Vec3 property
function updateVec3Property(
  propName: string,
  axis: "x" | "y" | "z",
  value: number,
  dataKey: string,
) {
  let animProp = (cameraData.value as any)[dataKey] as
    | AnimatableProperty<Vec3>
    | undefined;

  if (!animProp) {
    animProp = {
      id: `prop_${dataKey}_${Date.now()}`,
      name: propName,
      type: "vector3",
      value: { x: 0, y: 0, z: 0 },
      animated: false,
      keyframes: [],
      group: "Position & Target",
    };
  }

  const newValue = { ...animProp.value, [axis]: value };
  animProp.value = newValue;
  update(dataKey, animProp);
}

// Toggle Vec3 keyframe
function toggleVec3Keyframe(propName: string, dataKey: string) {
  let animProp = (cameraData.value as any)[dataKey] as
    | AnimatableProperty<Vec3>
    | undefined;

  if (!animProp) {
    animProp = {
      id: `prop_${dataKey}_${Date.now()}`,
      name: propName,
      type: "vector3",
      value: { x: 0, y: 0, z: 0 },
      animated: false,
      keyframes: [],
      group: "Position & Target",
    };
  }

  const frame = store.currentFrame;
  const hasKeyframeAtFrame = animProp.keyframes.some((k) => k.frame === frame);

  if (hasKeyframeAtFrame) {
    animProp.keyframes = animProp.keyframes.filter((k) => k.frame !== frame);
    animProp.animated = animProp.keyframes.length > 0;
  } else {
    animProp.keyframes.push(
      createKeyframe(frame, { ...animProp.value }, "linear"),
    );
    animProp.animated = true;
  }

  update(dataKey, animProp);
}
</script>

<style scoped>
.camera-properties {
  padding: 0;
}

.prop-section {
  border-bottom: 1px solid #2a2a2a;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 10px;
  cursor: pointer;
  user-select: none;
  background: #252525;
}

.section-header:hover {
  background: #2a2a2a;
}

.expand-icon {
  width: 10px;
  font-size: 11px;
  color: #666;
}

.section-title {
  flex: 1;
  font-weight: 600;
  font-size: 13px;
  color: #ccc;
}

.section-toggle {
  margin: 0;
  cursor: pointer;
}

.section-content {
  padding: 8px 10px;
  background: #1e1e1e;
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  min-height: 24px;
}

.property-row label {
  width: 80px;
  color: #888;
  font-size: 12px;
  flex-shrink: 0;
}

.property-row > :not(label):not(.keyframe-btn) {
  flex: 1;
}

.property-row.separator {
  margin: 4px 0;
}

.separator-line {
  flex: 1;
  height: 1px;
  background: #333;
}

.keyframe-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: #444;
  cursor: pointer;
  font-size: 12px;
  border-radius: 2px;
  flex-shrink: 0;
}

.keyframe-btn:hover {
  color: #888;
}

.keyframe-btn.active {
  color: #f0c040;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  width: auto;
  color: #ccc;
  font-size: 13px;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
}

.path-select {
  flex: 1;
  padding: 4px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 13px;
}

.path-select:focus {
  outline: none;
  border-color: #4a90d9;
}

.trajectory-grid {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.trajectory-group {
  display: flex;
  flex-wrap: wrap;
  gap: 4px;
}

.trajectory-group-title {
  width: 100%;
  font-size: 11px;
  color: #888;
  margin-bottom: 2px;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.trajectory-btn {
  padding: 4px 8px;
  background: #2a2a2a;
  border: 1px solid #3a3a3a;
  color: #ccc;
  border-radius: 3px;
  font-size: 11px;
  cursor: pointer;
  transition: all 0.15s;
}

.trajectory-btn:hover {
  background: #3a3a3a;
  border-color: #4a90d9;
  color: #fff;
}

.trajectory-btn:active {
  background: #4a90d9;
}
</style>
