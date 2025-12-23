<template>
  <div class="properties-panel">
    <div class="panel-header">
      <span class="panel-title">Properties: {{ selectedLayer?.name || 'No Selection' }}</span>
    </div>

    <div class="panel-content" v-if="selectedLayer">
      <!-- Layer Transform Section (AE-style) -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('transform')">
          <span class="expand-icon">{{ expandedSections.includes('transform') ? '▼' : '►' }}</span>
          <span class="section-title">Layer Transform</span>
          <span class="reset-link" @click.stop="resetTransform">Reset</span>
        </div>

        <div v-if="expandedSections.includes('transform')" class="section-content">
          <!-- Solo Mode Indicator -->
          <div v-if="soloModeActive" class="solo-indicator">
            Showing: {{ soloedProperty === 'animated' ? 'Animated Properties' : soloedProperty?.charAt(0).toUpperCase() + soloedProperty?.slice(1) }}
            <span class="solo-hint">(Press same key to show all)</span>
          </div>

          <!-- Origin (transform pivot point) -->
          <div class="property-row" v-show="showAnchor">
            <span class="keyframe-toggle" :class="{ active: hasKeyframe('anchorPoint') }" @click="toggleKeyframe('anchorPoint')">◆</span>
            <label>Origin</label>
            <div class="value-group">
              <ScrubableNumber
                v-model="transform.anchorPoint.x"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.anchorPoint.y"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-if="selectedLayer?.threeD"
                v-model="transform.anchorPoint.z"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
            </div>
          </div>

          <!-- Position -->
          <div class="property-row" v-show="showPosition" :class="{ 'has-driver': hasDriver('transform.position.x') }">
            <span class="keyframe-toggle" :class="{ active: hasKeyframe('position') }" @click="toggleKeyframe('position')">◆</span>
            <PropertyLink
              v-if="selectedLayer"
              :layerId="selectedLayer.id"
              property="transform.position.x"
              :linkedTo="getDriverForProperty('transform.position.x')"
              @link="(target) => onPropertyLink('transform.position.x', target)"
              @unlink="() => onPropertyUnlink('transform.position.x')"
            />
            <label>Position</label>
            <div class="value-group">
              <ScrubableNumber
                v-model="transform.position.x"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.position.y"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-if="selectedLayer?.threeD"
                v-model="transform.position.z"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
            </div>
          </div>

          <!-- Scale -->
          <div class="property-row" v-show="showScale" :class="{ 'has-driver': hasDriver('transform.scale.x') || hasDriver('transform.scale.y') }">
            <span class="keyframe-toggle" :class="{ active: hasKeyframe('scale') }" @click="toggleKeyframe('scale')">◆</span>
            <label>Scale</label>
            <div class="value-group scale-group">
              <button
                class="link-btn"
                :class="{ active: scaleLocked }"
                @click="scaleLocked = !scaleLocked"
                title="Constrain Proportions"
              >
                {{ scaleLocked ? '🔗' : '⛓️‍💥' }}
              </button>
              <ScrubableNumber
                v-model="transform.scale.x"
                :min="0"
                :max="1000"
                suffix="%"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.scale.y"
                :min="0"
                :max="1000"
                suffix="%"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-if="selectedLayer?.threeD"
                v-model="transform.scale.z"
                :min="0"
                :max="1000"
                suffix="%"
                @update:modelValue="updateTransform"
              />
            </div>
          </div>

          <!-- 3D Rotations -->
          <template v-if="selectedLayer?.threeD">
            <div class="property-row" v-show="showRotation">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('orientation') }" @click="toggleKeyframe('orientation')">◆</span>
              <label>Orientation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.orientationX" suffix="°" @update:modelValue="updateTransform" />
                <ScrubableNumber v-model="transform.orientationY" suffix="°" @update:modelValue="updateTransform" />
                <ScrubableNumber v-model="transform.orientationZ" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
            <div class="property-row" v-show="showRotation">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('rotationX') }" @click="toggleKeyframe('rotationX')">◆</span>
              <label>X Rotation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.rotationX" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
            <div class="property-row" v-show="showRotation">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('rotationY') }" @click="toggleKeyframe('rotationY')">◆</span>
              <label>Y Rotation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.rotationY" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
            <div class="property-row" v-show="showRotation">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('rotationZ') }" @click="toggleKeyframe('rotationZ')">◆</span>
              <label>Z Rotation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.rotationZ" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
          </template>
          <!-- 2D Rotation -->
          <template v-else>
            <div class="property-row" v-show="showRotation" :class="{ 'has-driver': hasDriver('transform.rotation') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('rotation') }" @click="toggleKeyframe('rotation')">◆</span>
              <label>Rotation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.rotation" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
          </template>

          <!-- Opacity -->
          <div class="property-row" v-show="showOpacity" :class="{ 'has-driver': hasDriver('opacity') }">
            <span class="keyframe-toggle" :class="{ active: hasKeyframe('opacity') }" @click="toggleKeyframe('opacity')">◆</span>
            <label>Opacity</label>
            <div class="value-group opacity-value">
              <ScrubableNumber
                v-model="transform.opacity"
                :min="0"
                :max="100"
                suffix="%"
                @update:modelValue="updateTransform"
              />
            </div>
          </div>
        </div>
      </div>

      <!-- Layer Options Section -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('options')">
          <span class="expand-icon">{{ expandedSections.includes('options') ? '▼' : '►' }}</span>
          <span class="section-title">Layer Options</span>
        </div>

        <div v-if="expandedSections.includes('options')" class="section-content">
          <!-- Parent Layer -->
          <div class="property-row">
            <label>Parent</label>
            <select
              class="parent-select"
              :value="selectedLayer?.parentId || ''"
              @change="updateParent"
            >
              <option value="">None</option>
              <option
                v-for="parent in availableParents"
                :key="parent.id"
                :value="parent.id"
              >
                {{ parent.name }}
              </option>
            </select>
          </div>

          <!-- Blend Mode -->
          <div class="property-row">
            <label>Blend Mode</label>
            <select
              class="blend-select"
              v-model="blendMode"
              @change="updateBlendMode"
            >
              <option
                v-for="mode in blendModes"
                :key="mode.value"
                :value="mode.value"
              >
                {{ mode.label }}
              </option>
            </select>
          </div>

          <!-- 3D Layer Toggle -->
          <div class="property-row">
            <label>3D Layer</label>
            <input
              type="checkbox"
              :checked="selectedLayer?.threeD"
              @change="toggle3D"
              class="checkbox-input"
            />
          </div>
        </div>
      </div>

      <!-- Layer-specific properties -->
      <component
        v-if="layerPropertiesComponent"
        :is="layerPropertiesComponent"
        :layer="selectedLayer"
        @update="onLayerUpdate"
      />

      <!-- Layer Styles Section -->
      <div class="property-section" v-if="selectedLayer">
        <div class="section-header" @click="toggleSection('layerStyles')">
          <span class="expand-icon">{{ expandedSections.includes('layerStyles') ? '▼' : '►' }}</span>
          <span class="section-title">Layer Styles</span>
        </div>
        <div v-if="expandedSections.includes('layerStyles')" class="section-content layer-styles-content">
          <LayerStylesPanel />
        </div>
      </div>

      <!-- Physics Section -->
      <div class="property-section" v-if="selectedLayer">
        <div class="section-header" @click="toggleSection('physics')">
          <span class="expand-icon">{{ expandedSections.includes('physics') ? '▼' : '►' }}</span>
          <span class="section-title">Physics</span>
        </div>
        <div v-if="expandedSections.includes('physics')" class="section-content physics-content">
          <PhysicsProperties :layerId="selectedLayer.id" @update="onLayerUpdate" />
        </div>
      </div>

      <!-- Property Drivers -->
      <DriverList v-if="selectedLayer" :layerId="selectedLayer.id" />
    </div>

    <!-- No Selection -->
    <div v-else class="empty-state">
      <p>No layer selected</p>
      <p class="hint">Select a layer to edit its properties</p>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, markRaw, inject, type Component, type Ref } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';

// Inject soloedProperty from parent for P/S/R/T/A/U shortcuts
type SoloedProperty = 'position' | 'scale' | 'rotation' | 'opacity' | 'anchor' | 'animated' | null;
const soloedProperty = inject<Ref<SoloedProperty>>('soloedProperty', ref(null));
import { ScrubableNumber, SliderInput } from '@/components/controls';
import type { BlendMode } from '@/types/project';
import { createAnimatableProperty } from '@/types/project';

// Layer-specific property panels
import TextProperties from '@/components/properties/TextProperties.vue';
import ParticleProperties from '@/components/properties/ParticleProperties.vue';
import DepthflowProperties from '@/components/properties/DepthflowProperties.vue';
import LightProperties from '@/components/properties/LightProperties.vue';
import ShapeProperties from '@/components/properties/ShapeProperties.vue';
import ShapeLayerProperties from '@/components/properties/ShapeLayerProperties.vue';
import PathProperties from '@/components/properties/PathProperties.vue';
import VideoProperties from '@/components/properties/VideoProperties.vue';
import CameraProperties from '@/components/properties/CameraProperties.vue';
import NestedCompProperties from '@/components/properties/NestedCompProperties.vue';
import Model3DProperties from '@/components/panels/Model3DProperties.vue';
import AudioProperties from '@/components/properties/AudioProperties.vue';
import DepthProperties from '@/components/properties/DepthProperties.vue';
import NormalProperties from '@/components/properties/NormalProperties.vue';
import GeneratedProperties from '@/components/properties/GeneratedProperties.vue';
import GroupProperties from '@/components/properties/GroupProperties.vue';
import ControlProperties from '@/components/properties/ControlProperties.vue';
import MatteProperties from '@/components/properties/MatteProperties.vue';
import SolidProperties from '@/components/properties/SolidProperties.vue';
import PoseProperties from '@/components/properties/PoseProperties.vue';
import EffectControlsPanel from '@/components/panels/EffectControlsPanel.vue';
import PropertyLink from '@/components/controls/PropertyLink.vue';
import DriverList from '@/components/panels/DriverList.vue';
import LayerStylesPanel from '@/components/properties/styles/LayerStylesPanel.vue';
import PhysicsProperties from '@/components/properties/PhysicsProperties.vue';
import type { PropertyPath } from '@/services/propertyDriver';

const store = useCompositorStore();

// State
const expandedSections = ref<string[]>(['transform']);
const scaleLocked = ref(true);

const layerName = ref('');
const transform = ref({
  position: { x: 0, y: 0, z: 0 },
  scale: { x: 100, y: 100, z: 100 },
  rotation: 0,
  anchorPoint: { x: 0, y: 0, z: 0 },
  opacity: 100,
  // 3D properties
  orientationX: 0,
  orientationY: 0,
  orientationZ: 0,
  rotationX: 0,
  rotationY: 0,
  rotationZ: 0
});
const blendMode = ref('normal');
const keyframes = ref<string[]>([]);

// Blend modes
const blendModes = [
  { label: 'Normal', value: 'normal' },
  { label: 'Multiply', value: 'multiply' },
  { label: 'Screen', value: 'screen' },
  { label: 'Overlay', value: 'overlay' },
  { label: 'Soft Light', value: 'soft-light' },
  { label: 'Hard Light', value: 'hard-light' },
  { label: 'Color Dodge', value: 'color-dodge' },
  { label: 'Color Burn', value: 'color-burn' },
  { label: 'Darken', value: 'darken' },
  { label: 'Lighten', value: 'lighten' },
  { label: 'Difference', value: 'difference' },
  { label: 'Exclusion', value: 'exclusion' },
  { label: 'Hue', value: 'hue' },
  { label: 'Saturation', value: 'saturation' },
  { label: 'Color', value: 'color' },
  { label: 'Luminosity', value: 'luminosity' },
  { label: 'Add', value: 'add' }
];

// Computed
const selectedLayer = computed(() => store.selectedLayer);

// Property solo visibility - determines which properties are shown based on P/S/R/T/A/U shortcuts
const showAnchor = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === 'anchor') return true;
  if (solo === 'animated') {
    // Show if this property has keyframes
    return selectedLayer.value?.transform?.anchorPoint?.animated || false;
  }
  return false;
});

const showPosition = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === 'position') return true;
  if (solo === 'animated') {
    return selectedLayer.value?.transform?.position?.animated || false;
  }
  return false;
});

const showScale = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === 'scale') return true;
  if (solo === 'animated') {
    return selectedLayer.value?.transform?.scale?.animated || false;
  }
  return false;
});

const showRotation = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === 'rotation') return true;
  if (solo === 'animated') {
    const t = selectedLayer.value?.transform;
    return t?.rotation?.animated || t?.rotationX?.animated || t?.rotationY?.animated || t?.rotationZ?.animated || t?.orientation?.animated || false;
  }
  return false;
});

const showOpacity = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === 'opacity') return true;
  if (solo === 'animated') {
    return selectedLayer.value?.opacity?.animated || false;
  }
  return false;
});

// Show indicator when in solo mode
const soloModeActive = computed(() => soloedProperty.value !== null);

// Get layers that can be parents (exclude self and children to prevent cycles)
const availableParents = computed(() => {
  if (!selectedLayer.value) return [];

  const selfId = selectedLayer.value.id;

  // Get all descendant IDs to prevent circular parenting
  const getDescendantIds = (layerId: string): string[] => {
    const children = store.layers.filter(l => l.parentId === layerId);
    let ids = children.map(c => c.id);
    for (const child of children) {
      ids = ids.concat(getDescendantIds(child.id));
    }
    return ids;
  };

  const descendantIds = new Set(getDescendantIds(selfId));

  return store.layers.filter(l =>
    l.id !== selfId &&
    !descendantIds.has(l.id) &&
    l.type !== 'camera' // Camera layers shouldn't be parents
  );
});

const layerPropertiesComponent = computed<Component | null>(() => {
  if (!selectedLayer.value) return null;

  switch (selectedLayer.value.type) {
    case 'text':
      return markRaw(TextProperties);
    case 'particles':
    case 'particle':
      return markRaw(ParticleProperties);
    case 'depthflow':
      return markRaw(DepthflowProperties);
    case 'light':
      return markRaw(LightProperties);
    case 'spline':
      return markRaw(ShapeProperties);
    case 'path':
      return markRaw(PathProperties);
    case 'video':
      return markRaw(VideoProperties);
    case 'camera':
      return markRaw(CameraProperties);
    case 'nestedComp':
      return markRaw(NestedCompProperties);
    case 'model':
    case 'pointcloud':
      return markRaw(Model3DProperties);
    case 'shape':
      return markRaw(ShapeLayerProperties);
    case 'audio':
      return markRaw(AudioProperties);
    case 'depth':
      return markRaw(DepthProperties);
    case 'normal':
      return markRaw(NormalProperties);
    case 'generated':
      return markRaw(GeneratedProperties);
    case 'group':
      return markRaw(GroupProperties);
    case 'control':
      return markRaw(ControlProperties);
    case 'matte':
      return markRaw(MatteProperties);
    case 'solid':
      return markRaw(SolidProperties);
    case 'pose':
      return markRaw(PoseProperties);
    case 'effectLayer':
    case 'adjustment': // Deprecated, use 'effectLayer'
      return markRaw(EffectControlsPanel);
    case 'image':
    case 'null':
      // These use default transform controls only
      return null;
    default:
      return null;
  }
});

// Helper to sync transform from layer to local state
function syncTransformFromLayer(layer: typeof selectedLayer.value) {
  if (!layer) return;
  layerName.value = layer.name;
  const t = layer.transform;
  transform.value = {
    position: {
      x: t?.position?.value?.x ?? 0,
      y: t?.position?.value?.y ?? 0,
      z: t?.position?.value?.z ?? 0
    },
    scale: { x: t?.scale?.value?.x ?? 100, y: t?.scale?.value?.y ?? 100, z: t?.scale?.value?.z ?? 100 },
    rotation: t?.rotation?.value ?? 0,
    anchorPoint: { x: t?.anchorPoint?.value?.x ?? 0, y: t?.anchorPoint?.value?.y ?? 0, z: t?.anchorPoint?.value?.z ?? 0 },
    opacity: layer.opacity?.value ?? 100,
    // 3D properties
    orientationX: t?.orientation?.value?.x ?? 0,
    orientationY: t?.orientation?.value?.y ?? 0,
    orientationZ: t?.orientation?.value?.z ?? 0,
    rotationX: t?.rotationX?.value ?? 0,
    rotationY: t?.rotationY?.value ?? 0,
    rotationZ: t?.rotationZ?.value ?? 0
  };
  blendMode.value = layer.blendMode || 'normal';
}

// Watch selected layer for selection changes
watch(selectedLayer, (layer) => {
  syncTransformFromLayer(layer);
}, { immediate: true });

// Deep watch the layer's transform to sync when it changes from other sources (e.g. timeline panel)
watch(
  () => selectedLayer.value?.transform,
  () => {
    syncTransformFromLayer(selectedLayer.value);
  },
  { deep: true }
);

// Also watch opacity separately since it's not in transform
watch(
  () => selectedLayer.value?.opacity?.value,
  (newVal) => {
    if (newVal !== undefined) {
      transform.value.opacity = newVal;
    }
  }
);

// Watch scale lock
watch(() => transform.value.scale.x, (newX, oldX) => {
  if (scaleLocked.value && newX !== oldX) {
    const ratio = newX / oldX;
    transform.value.scale.y = Math.round(transform.value.scale.y * ratio * 10) / 10;
  }
});

// Methods
function toggleSection(section: string) {
  const index = expandedSections.value.indexOf(section);
  if (index >= 0) {
    expandedSections.value.splice(index, 1);
  } else {
    expandedSections.value.push(section);
  }
}

function updateLayerName() {
  if (selectedLayer.value && layerName.value) {
    selectedLayer.value.name = layerName.value;
  }
}

function updateTransform() {
  if (!selectedLayer.value) return;
  const t = selectedLayer.value.transform;
  const v = transform.value;

  if (t?.position) {
    t.position.value = { x: v.position.x, y: v.position.y, z: v.position.z };
  }
  if (t?.scale) {
    t.scale.value = { x: v.scale.x, y: v.scale.y, z: v.scale.z };
  }
  if (t?.rotation) {
    t.rotation.value = v.rotation;
  }
  if (t?.anchorPoint) {
    t.anchorPoint.value = { x: v.anchorPoint.x, y: v.anchorPoint.y, z: v.anchorPoint.z };
  }
  if (selectedLayer.value.opacity) {
    selectedLayer.value.opacity.value = v.opacity;
  }

  // 3D properties
  if (selectedLayer.value.threeD) {
    if (t?.orientation) {
      t.orientation.value = { x: v.orientationX, y: v.orientationY, z: v.orientationZ };
    }
    if (t?.rotationX) t.rotationX.value = v.rotationX;
    if (t?.rotationY) t.rotationY.value = v.rotationY;
    if (t?.rotationZ) t.rotationZ.value = v.rotationZ;
  }

  onLayerUpdate();
}

function updateBlendMode() {
  if (selectedLayer.value) {
    selectedLayer.value.blendMode = blendMode.value as BlendMode;
  }
}

function toggle3D(event: Event) {
  if (!selectedLayer.value) return;
  const threeD = (event.target as HTMLInputElement).checked;
  store.updateLayer(selectedLayer.value.id, { threeD });

  // Initialize 3D properties when enabling 3D mode
  if (threeD && selectedLayer.value.transform) {
    const t = selectedLayer.value.transform;

    // Initialize Z values for position/scale/anchorPoint
    if (t.position.value.z === undefined) {
      t.position.value.z = 0;
    }
    if (t.scale.value.z === undefined) {
      t.scale.value.z = 100;
    }
    if (t.anchorPoint.value.z === undefined) {
      t.anchorPoint.value.z = 0;
    }

    // Initialize 3D rotation properties if they don't exist
    if (!t.orientation) {
      t.orientation = createAnimatableProperty('orientation', { x: 0, y: 0, z: 0 }, 'vector3');
    }
    if (!t.rotationX) {
      t.rotationX = createAnimatableProperty('rotationX', 0, 'number');
    }
    if (!t.rotationY) {
      t.rotationY = createAnimatableProperty('rotationY', 0, 'number');
    }
    if (!t.rotationZ) {
      t.rotationZ = createAnimatableProperty('rotationZ', 0, 'number');
    }
  }
}

function hasKeyframe(property: string): boolean {
  return keyframes.value.includes(property);
}

function toggleKeyframe(property: string) {
  const index = keyframes.value.indexOf(property);
  if (index >= 0) {
    keyframes.value.splice(index, 1);
  } else {
    keyframes.value.push(property);
    console.log(`Added keyframe for ${property} at frame ${store.currentFrame}`);
  }
}

function onLayerUpdate(dataUpdates?: Record<string, any>) {
  if (!selectedLayer.value) return;

  // If data updates are provided, apply them via store
  if (dataUpdates && Object.keys(dataUpdates).length > 0) {
    store.updateLayerData(selectedLayer.value.id, dataUpdates);
  } else {
    store.project.meta.modified = new Date().toISOString();
  }
}

function updateParent(event: Event) {
  if (!selectedLayer.value) return;
  const parentId = (event.target as HTMLSelectElement).value || null;
  store.setLayerParent(selectedLayer.value.id, parentId);
}

// ============================================================
// PROPERTY DRIVER / PICKWHIP FUNCTIONS
// ============================================================

/**
 * Get the driver linked to a property, if any
 */
function getDriverForProperty(property: PropertyPath): { layerId: string; property: PropertyPath } | null {
  if (!selectedLayer.value) return null;

  const drivers = store.getDriversForLayer(selectedLayer.value.id);
  const driver = drivers.find(d => d.targetProperty === property && d.sourceType === 'property');

  if (driver && driver.sourceLayerId && driver.sourceProperty) {
    return {
      layerId: driver.sourceLayerId,
      property: driver.sourceProperty
    };
  }
  return null;
}

/**
 * Handle property link event
 */
function onPropertyLink(
  targetProperty: PropertyPath,
  source: { layerId: string; property: PropertyPath }
) {
  if (!selectedLayer.value) return;

  // Create the property link
  store.createPropertyLink(
    selectedLayer.value.id,
    targetProperty,
    source.layerId,
    source.property,
    { blendMode: 'add' }
  );

  console.log(`[PropertiesPanel] Linked ${selectedLayer.value.id}.${targetProperty} <- ${source.layerId}.${source.property}`);
}

/**
 * Handle property unlink event
 */
function onPropertyUnlink(targetProperty: PropertyPath) {
  if (!selectedLayer.value) return;

  // Find and remove the driver
  const drivers = store.getDriversForLayer(selectedLayer.value.id);
  const driver = drivers.find(d => d.targetProperty === targetProperty && d.sourceType === 'property');

  if (driver) {
    store.removePropertyDriver(driver.id);
    console.log(`[PropertiesPanel] Unlinked ${selectedLayer.value.id}.${targetProperty}`);
  }
}

/**
 * Format rotation value in AE style: 0x+0°
 * e.g., 450 degrees = 1x+90°
 */
function formatRotation(degrees: number): string {
  const revolutions = Math.floor(Math.abs(degrees) / 360);
  const remainder = Math.abs(degrees) % 360;
  const sign = degrees < 0 ? '-' : '';
  return `${sign}${revolutions}x+${remainder.toFixed(1)}°`;
}

/**
 * Reset all transform values to defaults
 */
function resetTransform() {
  if (!selectedLayer.value) return;

  const comp = store.getActiveComp();
  if (!comp) return;

  const centerX = comp.settings.width / 2;
  const centerY = comp.settings.height / 2;

  // Fix: Use transform.value since transform is a ref
  transform.value.anchorPoint.x = centerX;
  transform.value.anchorPoint.y = centerY;
  transform.value.anchorPoint.z = 0;
  transform.value.position.x = centerX;
  transform.value.position.y = centerY;
  transform.value.position.z = 0;
  transform.value.scale.x = 100;
  transform.value.scale.y = 100;
  transform.value.scale.z = 100;
  transform.value.rotation = 0;
  transform.value.rotationX = 0;
  transform.value.rotationY = 0;
  transform.value.rotationZ = 0;
  transform.value.orientationX = 0;
  transform.value.orientationY = 0;
  transform.value.orientationZ = 0;
  transform.value.opacity = 100;

  updateTransform();
}

/**
 * Check if a property has a driver
 */
function hasDriver(property: PropertyPath): boolean {
  if (!selectedLayer.value) return false;
  const drivers = store.getDriversForLayer(selectedLayer.value.id);
  return drivers.some(d => d.targetProperty === property && d.enabled);
}
</script>

<style scoped>
.properties-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--weyl-surface-1, #141414);
  color: var(--weyl-text-primary, #E5E5E5);
  font-size: var(--weyl-text-base, 12px);
}

.panel-header {
  padding: 8px 12px;
  background: var(--weyl-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--weyl-border-subtle, #1a1a1a);
}

.panel-title {
  font-weight: 500;
  font-size: var(--weyl-text-sm, 11px);
  color: var(--weyl-text-secondary, #9CA3AF);
}

/* Solo mode indicator */
.solo-indicator {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 10px;
  margin-bottom: 8px;
  background: rgba(139, 92, 246, 0.15);
  border: 1px solid rgba(139, 92, 246, 0.4);
  border-radius: 4px;
  font-size: 11px;
  color: #c4b5fd;
}

.solo-hint {
  color: #888;
  font-size: 10px;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  padding: 8px 0;
}

.property-section {
  border-bottom: 1px solid var(--weyl-border-subtle, #1a1a1a);
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 12px;
  cursor: pointer;
  user-select: none;
}

.section-header:hover {
  background: var(--weyl-surface-3, #222222);
}

.expand-icon {
  width: 10px;
  font-size: 10px;
  color: var(--weyl-text-muted, #6B7280);
}

.section-title {
  font-weight: 500;
  font-size: var(--weyl-text-sm, 11px);
  flex: 1;
}

.reset-link {
  font-size: var(--weyl-text-xs, 10px);
  color: var(--weyl-accent, #8B5CF6);
  cursor: pointer;
  padding: 2px 8px;
}

.reset-link:hover {
  color: var(--weyl-accent-hover, #9D7AFA);
  text-decoration: underline;
}

.keyframe-toggle {
  width: 16px;
  font-size: 11px;
  color: var(--weyl-text-muted, #6B7280);
  cursor: pointer;
  flex-shrink: 0;
}

.keyframe-toggle:hover {
  color: var(--weyl-text-secondary, #9CA3AF);
}

.keyframe-toggle.active {
  color: var(--weyl-timeline-video, #FFD700);
}

.value-group {
  display: flex;
  align-items: center;
  gap: 4px;
  flex: 1;
}

.value-group.scale-group .link-btn {
  font-size: 11px;
  background: transparent;
  border: none;
  cursor: pointer;
  padding: 2px;
  opacity: 0.6;
}

.value-group.scale-group .link-btn:hover {
  opacity: 1;
}

.value-group.scale-group .link-btn.active {
  opacity: 1;
  color: var(--weyl-accent, #8B5CF6);
}

.rotation-display {
  color: var(--weyl-accent, #8B5CF6);
  font-family: var(--weyl-font-mono, 'JetBrains Mono', monospace);
  font-size: var(--weyl-text-base, 12px);
}

.threeD-toggle {
  display: flex;
  align-items: center;
  gap: 4px;
  cursor: pointer;
  padding: 2px 6px;
  background: var(--weyl-surface-3, #222222);
  border-radius: var(--weyl-radius-sm, 2px);
  font-size: var(--weyl-text-sm, 11px);
}

.threeD-toggle:hover {
  background: var(--weyl-surface-4, #2a2a2a);
}

.threeD-toggle input {
  margin: 0;
  cursor: pointer;
}

.threeD-toggle .toggle-label {
  color: var(--weyl-text-secondary, #9CA3AF);
  font-weight: 500;
}

.threeD-toggle input:checked + .toggle-label {
  color: var(--weyl-accent, #8B5CF6);
}

.section-content {
  padding: 4px 10px 8px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 12px;
  min-height: 26px;
}

.property-row.has-driver {
  background: var(--weyl-accent-muted, rgba(139, 92, 246, 0.15));
  border-left: 2px solid var(--weyl-accent, #8B5CF6);
}

.property-row.has-driver label {
  color: var(--weyl-accent, #8B5CF6);
}

.property-row label {
  width: 80px;
  color: var(--weyl-text-secondary, #9CA3AF);
  font-size: var(--weyl-text-sm, 11px);
  flex-shrink: 0;
}

.single-value {
  flex: 1;
}

.multi-value {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 4px;
}

.multi-value > * {
  flex: 1;
}

.link-btn {
  flex: 0 0 auto !important;
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: var(--weyl-text-muted, #6B7280);
  cursor: pointer;
  border-radius: var(--weyl-radius-sm, 2px);
  font-size: 11px;
}

.link-btn:hover {
  background: var(--weyl-surface-3, #222222);
}

.link-btn.active {
  color: var(--weyl-accent, #8B5CF6);
}

.keyframe-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: var(--weyl-text-muted, #6B7280);
  cursor: pointer;
  font-size: 11px;
  border-radius: var(--weyl-radius-sm, 2px);
}

.keyframe-btn:hover {
  color: var(--weyl-text-secondary, #9CA3AF);
}

.keyframe-btn.active {
  color: var(--weyl-timeline-video, #FFD700);
}

.layer-name-input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid var(--weyl-border-default, #2a2a2a);
  background: var(--weyl-surface-2, #1a1a1a);
  color: var(--weyl-text-primary, #E5E5E5);
  border-radius: var(--weyl-radius-sm, 2px);
  font-size: var(--weyl-text-sm, 11px);
  font-weight: 500;
}

.layer-name-input:focus {
  outline: none;
  border-color: var(--weyl-accent, #8B5CF6);
}

.blend-select,
.parent-select {
  flex: 1;
  padding: 4px 8px;
  background: var(--weyl-surface-2, #1a1a1a);
  border: 1px solid var(--weyl-border-default, #2a2a2a);
  color: var(--weyl-text-primary, #E5E5E5);
  border-radius: var(--weyl-radius-sm, 2px);
  font-size: var(--weyl-text-sm, 11px);
}

.blend-select:focus,
.parent-select:focus {
  outline: none;
  border-color: var(--weyl-accent, #8B5CF6);
}

.checkbox-input {
  width: 16px;
  height: 16px;
  cursor: pointer;
  accent-color: var(--weyl-accent, #8B5CF6);
}

.empty-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  padding: 24px;
  text-align: center;
  color: var(--weyl-text-muted, #6B7280);
}

.empty-state .hint {
  font-size: var(--weyl-text-sm, 11px);
  margin-top: 4px;
}

.layer-styles-content {
  padding: 0 !important;
  max-height: 400px;
  overflow-y: auto;
}

.physics-content {
  padding: 0 !important;
  max-height: 500px;
  overflow-y: auto;
}
</style>
