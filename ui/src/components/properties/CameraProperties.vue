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
            @update:modelValue="v => updateAnimatable('FOV', v, 'animatedFov')"
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
            @update:modelValue="v => updateAnimatable('Focal Length', v, 'animatedFocalLength')"
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
            @update:modelValue="v => updateDOFAnimatable('Focus Distance', v, 'focusDistance')"
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
            @update:modelValue="v => updateDOFAnimatable('Aperture', v, 'aperture')"
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
            @update:modelValue="v => updateDOFAnimatable('Blur Level', v, 'blurLevel')"
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
              {{ layer.name }}
            </option>
          </select>
        </div>

        <div class="property-row">
          <label>Position</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Path Position') ?? pathFollowing.parameter?.value ?? 0"
            @update:modelValue="v => updatePathProperty('parameter', v)"
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
            @update:modelValue="v => updatePathConfig('lookAhead', v)"
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
            @update:modelValue="v => updatePathConfig('bankingStrength', v)"
            :min="0"
            :max="1"
            :step="0.05"
          />
        </div>

        <div class="property-row">
          <label>Height Offset</label>
          <ScrubableNumber
            :modelValue="pathFollowing.offsetY ?? 0"
            @update:modelValue="v => updatePathConfig('offsetY', v)"
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
            @update:modelValue="v => updatePathConfig('autoAdvanceSpeed', v)"
            :min="0.001"
            :max="0.1"
            :step="0.001"
            :precision="3"
          />
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
            @update:modelValue="v => updateVec3Property('Position', 'x', v, 'animatedPosition')"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Position') }" @click="toggleVec3Keyframe('Position', 'animatedPosition')">◆</button>
        </div>

        <div class="property-row">
          <label>Position Y</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Position', 'y')"
            @update:modelValue="v => updateVec3Property('Position', 'y', v, 'animatedPosition')"
          />
        </div>

        <div class="property-row">
          <label>Position Z</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Position', 'z')"
            @update:modelValue="v => updateVec3Property('Position', 'z', v, 'animatedPosition')"
          />
        </div>

        <div class="property-row separator">
          <span class="separator-line"></span>
        </div>

        <div class="property-row">
          <label>Target X</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Target', 'x')"
            @update:modelValue="v => updateVec3Property('Target', 'x', v, 'animatedTarget')"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Target') }" @click="toggleVec3Keyframe('Target', 'animatedTarget')">◆</button>
        </div>

        <div class="property-row">
          <label>Target Y</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Target', 'y')"
            @update:modelValue="v => updateVec3Property('Target', 'y', v, 'animatedTarget')"
          />
        </div>

        <div class="property-row">
          <label>Target Z</label>
          <ScrubableNumber
            :modelValue="getVec3Value('Target', 'z')"
            @update:modelValue="v => updateVec3Property('Target', 'z', v, 'animatedTarget')"
          />
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from 'vue';
import type { Layer, CameraLayerData, AnimatableProperty, CameraDepthOfField, CameraPathFollowing, Vec3 } from '@/types/project';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber } from '@/components/controls';

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

const expandedSections = ref<string[]>(['settings', 'dof']);

// Get camera data with defaults
const cameraData = computed<CameraLayerData>(() => {
  return (props.layer.data as CameraLayerData) || {
    cameraId: '',
    isActiveCamera: false,
  };
});

// Depth of field with defaults
const depthOfField = computed<CameraDepthOfField>(() => {
  return cameraData.value.depthOfField || {
    enabled: false,
    focusDistance: 500,
    aperture: 2.8,
    blurLevel: 50,
  };
});

const dofEnabled = computed(() => depthOfField.value.enabled);

// Path following with defaults
const pathFollowing = computed<CameraPathFollowing>(() => {
  return cameraData.value.pathFollowing || {
    enabled: false,
    pathLayerId: '',
    parameter: { id: '', name: 'Path Position', type: 'number', value: 0, animated: false, keyframes: [], group: 'Path Following' },
    lookAhead: 0.05,
    bankingStrength: 0,
    offsetY: 0,
    alignToPath: true,
    autoAdvance: false,
    autoAdvanceSpeed: 0.01,
  };
});

// Get available spline layers for path following
const splineLayers = computed(() => {
  return store.layers.filter(l => l.type === 'spline' && l.id !== props.layer.id);
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
    data: { ...cameraData.value, [key]: value }
  });
  emit('update');
}

// Toggle DOF
function toggleDOF(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  const newDOF = { ...depthOfField.value, enabled: checked };
  update('depthOfField', newDOF);
}

// Toggle path following
function togglePathFollowing(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  const newPath = { ...pathFollowing.value, enabled: checked };
  update('pathFollowing', newPath);
}

// Update path layer
function updatePathLayer(e: Event) {
  const layerId = (e.target as HTMLSelectElement).value;
  const newPath = { ...pathFollowing.value, pathLayerId: layerId };
  update('pathFollowing', newPath);
}

// Update path config value
function updatePathConfig(key: keyof CameraPathFollowing, value: any) {
  const newPath = { ...pathFollowing.value, [key]: value };
  update('pathFollowing', newPath);
}

// Update path parameter (animatable)
function updatePathProperty(key: string, value: number) {
  const param = pathFollowing.value.parameter;
  const newParam = { ...param, value };
  const newPath = { ...pathFollowing.value, parameter: newParam };
  update('pathFollowing', newPath);

  // Also update in layer.properties if it exists
  const prop = getProperty('Path Position');
  if (prop) {
    prop.value = value;
  }
}

// Get animatable property from layer.properties
function getProperty(name: string): AnimatableProperty<number> | undefined {
  return props.layer.properties?.find(p => p.name === name) as AnimatableProperty<number> | undefined;
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
  // Update in layer.properties
  const prop = getProperty(propName);
  if (prop) {
    prop.value = value;
  }

  // Update in camera data's animated property
  const animProp = (cameraData.value as any)[dataKey] as AnimatableProperty<number> | undefined;
  if (animProp) {
    animProp.value = value;
    update(dataKey, animProp);
  }
  emit('update');
}

// Update DOF animatable property
function updateDOFAnimatable(propName: string, value: number, dofKey: keyof CameraDepthOfField) {
  const newDOF = { ...depthOfField.value, [dofKey]: value };
  update('depthOfField', newDOF);

  // Also update in layer.properties
  const prop = getProperty(propName);
  if (prop) {
    prop.value = value;
  }
  emit('update');
}

// Ensure property exists in layer.properties
function ensureProperty(propName: string, defaultValue: number, group: string) {
  if (!props.layer.properties) {
    props.layer.properties = [];
  }

  const existing = props.layer.properties.find(p => p.name === propName);
  if (!existing) {
    props.layer.properties.push({
      id: `prop_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
      name: propName,
      type: 'number',
      value: defaultValue,
      animated: false,
      keyframes: [],
      group,
    } as AnimatableProperty<number>);
  }
}

// Toggle keyframe
function toggleKeyframe(propName: string, dataKey: string, defaultValue: number) {
  ensureProperty(propName, defaultValue, propName.includes('Focus') || propName.includes('Aperture') || propName.includes('Blur') ? 'Depth of Field' : 'Camera');

  const prop = getProperty(propName);
  if (prop) {
    const frame = store.currentFrame;
    const hasKeyframeAtFrame = prop.keyframes.some(k => k.frame === frame);

    if (hasKeyframeAtFrame) {
      prop.keyframes = prop.keyframes.filter(k => k.frame !== frame);
      prop.animated = prop.keyframes.length > 0;
    } else {
      prop.keyframes.push({
        id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
        frame,
        value: prop.value,
        easing: 'linear',
      });
      prop.animated = true;
    }
    emit('update');
  }
}

// Toggle path keyframe
function togglePathKeyframe(propName: string) {
  ensureProperty(propName, pathFollowing.value.parameter?.value ?? 0, 'Path Following');

  const prop = getProperty(propName);
  if (prop) {
    const frame = store.currentFrame;
    const hasKeyframeAtFrame = prop.keyframes.some(k => k.frame === frame);

    if (hasKeyframeAtFrame) {
      prop.keyframes = prop.keyframes.filter(k => k.frame !== frame);
      prop.animated = prop.keyframes.length > 0;
    } else {
      prop.keyframes.push({
        id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
        frame,
        value: prop.value,
        easing: 'linear',
      });
      prop.animated = true;
    }
    emit('update');
  }
}

// Get Vec3 value
function getVec3Value(propName: string, axis: 'x' | 'y' | 'z'): number {
  const dataKey = propName === 'Position' ? 'animatedPosition' : 'animatedTarget';
  const animProp = (cameraData.value as any)[dataKey] as AnimatableProperty<Vec3> | undefined;
  if (animProp?.value) {
    return animProp.value[axis] ?? 0;
  }
  return 0;
}

// Update Vec3 property
function updateVec3Property(propName: string, axis: 'x' | 'y' | 'z', value: number, dataKey: string) {
  let animProp = (cameraData.value as any)[dataKey] as AnimatableProperty<Vec3> | undefined;

  if (!animProp) {
    animProp = {
      id: `prop_${dataKey}_${Date.now()}`,
      name: propName,
      type: 'vector3',
      value: { x: 0, y: 0, z: 0 },
      animated: false,
      keyframes: [],
      group: 'Position & Target',
    };
  }

  const newValue = { ...animProp.value, [axis]: value };
  animProp.value = newValue;
  update(dataKey, animProp);
}

// Toggle Vec3 keyframe
function toggleVec3Keyframe(propName: string, dataKey: string) {
  let animProp = (cameraData.value as any)[dataKey] as AnimatableProperty<Vec3> | undefined;

  if (!animProp) {
    animProp = {
      id: `prop_${dataKey}_${Date.now()}`,
      name: propName,
      type: 'vector3',
      value: { x: 0, y: 0, z: 0 },
      animated: false,
      keyframes: [],
      group: 'Position & Target',
    };
  }

  const frame = store.currentFrame;
  const hasKeyframeAtFrame = animProp.keyframes.some(k => k.frame === frame);

  if (hasKeyframeAtFrame) {
    animProp.keyframes = animProp.keyframes.filter(k => k.frame !== frame);
    animProp.animated = animProp.keyframes.length > 0;
  } else {
    animProp.keyframes.push({
      id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
      frame,
      value: { ...animProp.value },
      easing: 'linear',
    });
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
</style>
