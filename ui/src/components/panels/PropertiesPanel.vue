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
          <!-- Anchor Point -->
          <div class="property-row">
            <span class="stopwatch" :class="{ active: hasKeyframe('anchorPoint') }" @click="toggleKeyframe('anchorPoint')">⏱</span>
            <label>Anchor Point</label>
            <div class="value-group">
              <ScrubableNumber
                v-model="transform.anchorPoint.x"
                :precision="1"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.anchorPoint.y"
                :precision="1"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-if="selectedLayer?.threeD"
                v-model="transform.anchorPoint.z"
                :precision="1"
                @update:modelValue="updateTransform"
              />
            </div>
          </div>

          <!-- Position -->
          <div class="property-row" :class="{ 'has-driver': hasDriver('transform.position.x') }">
            <span class="stopwatch" :class="{ active: hasKeyframe('position') }" @click="toggleKeyframe('position')">⏱</span>
            <Pickwhip
              v-if="selectedLayer"
              :layerId="selectedLayer.id"
              property="transform.position.x"
              :linkedTo="getDriverForProperty('transform.position.x')"
              @link="(target) => onPickwhipLink('transform.position.x', target)"
              @unlink="() => onPickwhipUnlink('transform.position.x')"
            />
            <label>Position</label>
            <div class="value-group">
              <ScrubableNumber
                v-model="transform.position.x"
                :precision="1"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-model="transform.position.y"
                :precision="1"
                @update:modelValue="updateTransform"
              />
              <ScrubableNumber
                v-if="selectedLayer?.threeD"
                v-model="transform.position.z"
                :precision="1"
                @update:modelValue="updateTransform"
              />
            </div>
          </div>

          <!-- Scale -->
          <div class="property-row" :class="{ 'has-driver': hasDriver('transform.scale.x') || hasDriver('transform.scale.y') }">
            <span class="stopwatch" :class="{ active: hasKeyframe('scale') }" @click="toggleKeyframe('scale')">⏱</span>
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
            <div class="property-row">
              <span class="stopwatch" :class="{ active: hasKeyframe('orientation') }" @click="toggleKeyframe('orientation')">⏱</span>
              <label>Orientation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.orientationX" suffix="°" @update:modelValue="updateTransform" />
                <ScrubableNumber v-model="transform.orientationY" suffix="°" @update:modelValue="updateTransform" />
                <ScrubableNumber v-model="transform.orientationZ" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
            <div class="property-row">
              <span class="stopwatch" :class="{ active: hasKeyframe('rotationX') }" @click="toggleKeyframe('rotationX')">⏱</span>
              <label>X Rotation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.rotationX" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
            <div class="property-row">
              <span class="stopwatch" :class="{ active: hasKeyframe('rotationY') }" @click="toggleKeyframe('rotationY')">⏱</span>
              <label>Y Rotation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.rotationY" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
            <div class="property-row">
              <span class="stopwatch" :class="{ active: hasKeyframe('rotationZ') }" @click="toggleKeyframe('rotationZ')">⏱</span>
              <label>Z Rotation</label>
              <div class="value-group">
                <ScrubableNumber v-model="transform.rotationZ" suffix="°" @update:modelValue="updateTransform" />
              </div>
            </div>
          </template>
          <!-- 2D Rotation -->
          <template v-else>
            <div class="property-row" :class="{ 'has-driver': hasDriver('transform.rotation') }">
              <span class="stopwatch" :class="{ active: hasKeyframe('rotation') }" @click="toggleKeyframe('rotation')">⏱</span>
              <label>Rotation</label>
              <div class="value-group rotation-value">
                <span class="rotation-display">{{ formatRotation(transform.rotation) }}</span>
              </div>
            </div>
          </template>

          <!-- Opacity -->
          <div class="property-row" :class="{ 'has-driver': hasDriver('opacity') }">
            <span class="stopwatch" :class="{ active: hasKeyframe('opacity') }" @click="toggleKeyframe('opacity')">⏱</span>
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

      <!-- Layer-specific properties -->
      <component
        v-if="layerPropertiesComponent"
        :is="layerPropertiesComponent"
        :layer="selectedLayer"
        @update="onLayerUpdate"
      />

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
import { ref, computed, watch, markRaw, type Component } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber, SliderInput } from '@/components/controls';
import type { BlendMode } from '@/types/project';
import { createAnimatableProperty } from '@/types/project';

// Layer-specific property panels
import TextProperties from '@/components/properties/TextProperties.vue';
import ParticleProperties from '@/components/properties/ParticleProperties.vue';
import DepthflowProperties from '@/components/properties/DepthflowProperties.vue';
import LightProperties from '@/components/properties/LightProperties.vue';
import ShapeProperties from '@/components/properties/ShapeProperties.vue';
import VideoProperties from '@/components/properties/VideoProperties.vue';
import CameraProperties from '@/components/properties/CameraProperties.vue';
import PrecompProperties from '@/components/properties/PrecompProperties.vue';
import Pickwhip from '@/components/controls/Pickwhip.vue';
import DriverList from '@/components/panels/DriverList.vue';
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
      return markRaw(ParticleProperties);
    case 'depthflow':
      return markRaw(DepthflowProperties);
    case 'light':
      return markRaw(LightProperties);
    case 'spline':
      return markRaw(ShapeProperties);
    case 'video':
      return markRaw(VideoProperties);
    case 'camera':
      return markRaw(CameraProperties);
    case 'precomp':
      return markRaw(PrecompProperties);
    default:
      return null;
  }
});

// Watch selected layer
watch(selectedLayer, (layer) => {
  if (layer) {
    layerName.value = layer.name;
    const t = layer.transform;
    transform.value = {
      position: {
        x: t?.position?.value?.x || 0,
        y: t?.position?.value?.y || 0,
        z: t?.position?.value?.z || 0
      },
      scale: { x: t?.scale?.value?.x || 100, y: t?.scale?.value?.y || 100, z: t?.scale?.value?.z || 100 },
      rotation: t?.rotation?.value || 0,
      anchorPoint: { x: t?.anchorPoint?.value?.x || 0, y: t?.anchorPoint?.value?.y || 0, z: t?.anchorPoint?.value?.z || 0 },
      opacity: layer.opacity?.value || 100,
      // 3D properties
      orientationX: t?.orientation?.value?.x || 0,
      orientationY: t?.orientation?.value?.y || 0,
      orientationZ: t?.orientation?.value?.z || 0,
      rotationX: t?.rotationX?.value || 0,
      rotationY: t?.rotationY?.value || 0,
      rotationZ: t?.rotationZ?.value || 0
    };
    blendMode.value = layer.blendMode || 'normal';
  }
}, { immediate: true });

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
 * Handle pickwhip link event
 */
function onPickwhipLink(
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
 * Handle pickwhip unlink event
 */
function onPickwhipUnlink(targetProperty: PropertyPath) {
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

  transform.anchorPoint.x = centerX;
  transform.anchorPoint.y = centerY;
  transform.anchorPoint.z = 0;
  transform.position.x = centerX;
  transform.position.y = centerY;
  transform.position.z = 0;
  transform.scale.x = 100;
  transform.scale.y = 100;
  transform.scale.z = 100;
  transform.rotation = 0;
  transform.rotationX = 0;
  transform.rotationY = 0;
  transform.rotationZ = 0;
  transform.orientationX = 0;
  transform.orientationY = 0;
  transform.orientationZ = 0;
  transform.opacity = 100;

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
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 11px;
}

.panel-header {
  padding: 8px 10px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.panel-title {
  font-weight: 600;
  font-size: 12px;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  padding: 8px 0;
}

.property-section {
  border-bottom: 1px solid #2a2a2a;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 10px;
  cursor: pointer;
  user-select: none;
}

.section-header:hover {
  background: #252525;
}

.expand-icon {
  width: 10px;
  font-size: 8px;
  color: #666;
}

.section-title {
  font-weight: 500;
  flex: 1;
}

.reset-link {
  font-size: 10px;
  color: #4a90d9;
  cursor: pointer;
  padding: 2px 8px;
}

.reset-link:hover {
  color: #6bb3ff;
  text-decoration: underline;
}

.stopwatch {
  width: 16px;
  font-size: 10px;
  color: #555;
  cursor: pointer;
  flex-shrink: 0;
}

.stopwatch:hover {
  color: #888;
}

.stopwatch.active {
  color: #f0c040;
}

.value-group {
  display: flex;
  align-items: center;
  gap: 4px;
  flex: 1;
}

.value-group.scale-group .link-btn {
  font-size: 10px;
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
  color: #4a90d9;
}

.rotation-display {
  color: #4a90d9;
  font-family: 'Consolas', monospace;
  font-size: 11px;
}

.threeD-toggle {
  display: flex;
  align-items: center;
  gap: 4px;
  cursor: pointer;
  padding: 2px 6px;
  background: #333;
  border-radius: 3px;
  font-size: 10px;
}

.threeD-toggle:hover {
  background: #444;
}

.threeD-toggle input {
  margin: 0;
  cursor: pointer;
}

.threeD-toggle .toggle-label {
  color: #888;
  font-weight: 500;
}

.threeD-toggle input:checked + .toggle-label {
  color: #4a90d9;
}

.section-content {
  padding: 4px 10px 8px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 10px;
  min-height: 26px;
}

.property-row.has-driver {
  background: rgba(46, 204, 113, 0.1);
  border-left: 2px solid #2ecc71;
}

.property-row.has-driver label {
  color: #2ecc71;
}

.property-row label {
  width: 80px;
  color: #888;
  font-size: 10px;
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
  color: #555;
  cursor: pointer;
  border-radius: 3px;
  font-size: 10px;
}

.link-btn:hover {
  background: #333;
}

.link-btn.active {
  color: #4a90d9;
}

.keyframe-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: #444;
  cursor: pointer;
  font-size: 10px;
  border-radius: 2px;
}

.keyframe-btn:hover {
  color: #888;
}

.keyframe-btn.active {
  color: #f0c040;
}

.layer-name-input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid #3a3a3a;
  background: #1a1a1a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 12px;
  font-weight: 500;
}

.layer-name-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.blend-select,
.parent-select {
  flex: 1;
  padding: 4px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 11px;
}

.empty-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  padding: 24px;
  text-align: center;
  color: #555;
}

.empty-state .hint {
  font-size: 10px;
  margin-top: 4px;
}
</style>
