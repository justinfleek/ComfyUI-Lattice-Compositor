<template>
  <div class="properties-panel">
    <div class="panel-header" v-if="selectedLayer">
      <span class="panel-title">{{ selectedLayer.name }}</span>
      <span class="layer-type">{{ selectedLayer.type }}</span>
    </div>

    <div class="panel-content" v-if="selectedLayer">
      <!-- Layer Transform Section -->
      <div class="property-section">
        <div class="section-header" @click="toggleSection('transform')">
          <span class="expand-icon">{{ expandedSections.includes('transform') ? '▼' : '►' }}</span>
          <span class="section-title">Layer Transform</span>
          <span class="reset-link" @click.stop="resetTransform">Reset</span>
        </div>

        <div v-if="expandedSections.includes('transform')" class="section-content">
          <!-- Solo Mode Indicator -->
          <div v-if="soloModeActive" class="solo-indicator">
            Showing: {{ soloedProperty === 'animated' ? 'Animated Properties' : (soloedProperty ? soloedProperty.charAt(0).toUpperCase() + soloedProperty.slice(1) : '') }}
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
                v-if="isLayer3D"
                v-model="transform.anchorPoint.z"
                :precision="1"
                unit="px"
                @update:modelValue="updateTransform"
              />
            </div>
          </div>

          <!-- Position (Combined or Separated) -->
          <template v-if="!positionSeparated">
            <!-- Combined Position -->
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
              <button
                class="dimension-sep-btn"
                @click="togglePositionSeparation"
                title="Separate X, Y, Z dimensions for independent keyframing"
              >⊞</button>
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
                  v-if="isLayer3D"
                  v-model="transform.position.z"
                  :precision="1"
                  unit="px"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
          </template>
          <template v-else>
            <!-- Separated Position X -->
            <div class="property-row" v-show="showPosition" :class="{ 'has-driver': hasDriver('transform.position.x') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('positionX') }" @click="toggleKeyframe('positionX')">◆</span>
              <label class="x-label">X Position</label>
              <button
                class="dimension-sep-btn active"
                @click="togglePositionSeparation"
                title="Link X, Y, Z dimensions back into combined property"
              >⊟</button>
              <div class="value-group">
                <ScrubableNumber
                  v-model="transform.position.x"
                  :precision="1"
                  unit="px"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
            <!-- Separated Position Y -->
            <div class="property-row" v-show="showPosition" :class="{ 'has-driver': hasDriver('transform.position.y') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('positionY') }" @click="toggleKeyframe('positionY')">◆</span>
              <label class="y-label">Y Position</label>
              <div class="dimension-sep-spacer"></div>
              <div class="value-group">
                <ScrubableNumber
                  v-model="transform.position.y"
                  :precision="1"
                  unit="px"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
            <!-- Separated Position Z (3D only) -->
            <div class="property-row" v-if="isLayer3D" v-show="showPosition" :class="{ 'has-driver': hasDriver('transform.position.z') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('positionZ') }" @click="toggleKeyframe('positionZ')">◆</span>
              <label class="z-label">Z Position</label>
              <div class="dimension-sep-spacer"></div>
              <div class="value-group">
                <ScrubableNumber
                  v-model="transform.position.z"
                  :precision="1"
                  unit="px"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
          </template>

          <!-- Scale (Combined or Separated) -->
          <template v-if="!scaleSeparated">
            <!-- Combined Scale -->
            <div class="property-row" v-show="showScale" :class="{ 'has-driver': hasDriver('transform.scale.x') || hasDriver('transform.scale.y') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('scale') }" @click="toggleKeyframe('scale')">◆</span>
              <label>Scale</label>
              <button
                class="dimension-sep-btn"
                @click="toggleScaleSeparation"
                title="Separate X, Y, Z dimensions for independent keyframing"
              >⊞</button>
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
                  v-if="isLayer3D"
                  v-model="transform.scale.z"
                  :min="0"
                  :max="1000"
                  suffix="%"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
          </template>
          <template v-else>
            <!-- Separated Scale X -->
            <div class="property-row" v-show="showScale" :class="{ 'has-driver': hasDriver('transform.scale.x') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('scaleX') }" @click="toggleKeyframe('scaleX')">◆</span>
              <label class="x-label">X Scale</label>
              <button
                class="dimension-sep-btn active"
                @click="toggleScaleSeparation"
                title="Link X, Y, Z dimensions back into combined property"
              >⊟</button>
              <div class="value-group">
                <ScrubableNumber
                  v-model="transform.scale.x"
                  :min="0"
                  :max="1000"
                  suffix="%"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
            <!-- Separated Scale Y -->
            <div class="property-row" v-show="showScale" :class="{ 'has-driver': hasDriver('transform.scale.y') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('scaleY') }" @click="toggleKeyframe('scaleY')">◆</span>
              <label class="y-label">Y Scale</label>
              <div class="dimension-sep-spacer"></div>
              <div class="value-group">
                <ScrubableNumber
                  v-model="transform.scale.y"
                  :min="0"
                  :max="1000"
                  suffix="%"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
            <!-- Separated Scale Z (3D only) -->
            <div class="property-row" v-if="isLayer3D" v-show="showScale" :class="{ 'has-driver': hasDriver('transform.scale.z') }">
              <span class="keyframe-toggle" :class="{ active: hasKeyframe('scaleZ') }" @click="toggleKeyframe('scaleZ')">◆</span>
              <label class="z-label">Z Scale</label>
              <div class="dimension-sep-spacer"></div>
              <div class="value-group">
                <ScrubableNumber
                  v-model="transform.scale.z"
                  :min="0"
                  :max="1000"
                  suffix="%"
                  @update:modelValue="updateTransform"
                />
              </div>
            </div>
          </template>

          <!-- 3D Rotations -->
          <template v-if="isLayer3D">
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
              :value="layerParentId"
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
              :checked="isLayer3D"
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

      <!-- Audio Path Animation Section -->
      <div class="property-section" v-if="selectedLayer">
        <div class="section-header" @click="toggleSection('audioPathAnimation')">
          <span class="expand-icon">{{ expandedSections.includes('audioPathAnimation') ? '▼' : '►' }}</span>
          <span class="section-title">Audio Path Animation</span>
        </div>
        <div v-if="expandedSections.includes('audioPathAnimation')" class="section-content audio-path-content">
          <!-- Enable Toggle -->
          <div class="property-row">
            <label>Enabled</label>
            <input
              type="checkbox"
              :checked="audioPathAnimation.enabled"
              @change="updateAudioPathEnabled"
              class="checkbox-input"
            />
          </div>

          <!-- SVG Path Data -->
          <div class="property-row path-data-row" v-if="audioPathAnimation.enabled">
            <label>Path Data</label>
            <textarea
              class="path-data-input"
              :value="audioPathAnimation.pathData"
              @input="updateAudioPathData"
              placeholder="M 0 0 L 100 100 C 150 50 200 150 300 100"
              rows="2"
            />
          </div>

          <!-- Movement Mode -->
          <div class="property-row" v-if="audioPathAnimation.enabled">
            <label>Mode</label>
            <select
              class="blend-select"
              :value="audioPathAnimation.movementMode"
              @change="updateAudioPathMode"
            >
              <option value="amplitude">Amplitude (volume = position)</option>
              <option value="accumulate">Accumulate (travel forward)</option>
            </select>
          </div>

          <!-- Sensitivity -->
          <div class="property-row" v-if="audioPathAnimation.enabled">
            <label>Sensitivity</label>
            <div class="value-group">
              <ScrubableNumber
                :modelValue="audioPathAnimation.sensitivity"
                @update:modelValue="(v: number) => updateAudioPathConfig('sensitivity', v)"
                :min="0.1"
                :max="5"
                :precision="2"
              />
            </div>
          </div>

          <!-- Smoothing -->
          <div class="property-row" v-if="audioPathAnimation.enabled">
            <label>Smoothing</label>
            <div class="value-group">
              <ScrubableNumber
                :modelValue="audioPathAnimation.smoothing"
                @update:modelValue="(v: number) => updateAudioPathConfig('smoothing', v)"
                :min="0"
                :max="1"
                :precision="2"
              />
            </div>
          </div>

          <!-- Release (amplitude mode) -->
          <div class="property-row" v-if="audioPathAnimation.enabled && audioPathAnimation.movementMode === 'amplitude'">
            <label>Release</label>
            <div class="value-group">
              <ScrubableNumber
                :modelValue="audioPathAnimation.release"
                @update:modelValue="(v: number) => updateAudioPathConfig('release', v)"
                :min="0"
                :max="1"
                :precision="2"
              />
            </div>
          </div>

          <!-- Amplitude Curve (amplitude mode) -->
          <div class="property-row" v-if="audioPathAnimation.enabled && audioPathAnimation.movementMode === 'amplitude'">
            <label>Curve</label>
            <div class="value-group">
              <ScrubableNumber
                :modelValue="audioPathAnimation.amplitudeCurve"
                @update:modelValue="(v: number) => updateAudioPathConfig('amplitudeCurve', v)"
                :min="0.5"
                :max="3"
                :precision="2"
              />
            </div>
          </div>

          <!-- Flip on Beat (accumulate mode) -->
          <div class="property-row" v-if="audioPathAnimation.enabled && audioPathAnimation.movementMode === 'accumulate'">
            <label>Flip on Beat</label>
            <input
              type="checkbox"
              :checked="audioPathAnimation.flipOnBeat"
              @change="(e) => updateAudioPathConfig('flipOnBeat', (e.target as HTMLInputElement).checked)"
              class="checkbox-input"
            />
          </div>

          <!-- Beat Threshold (accumulate mode) -->
          <div class="property-row" v-if="audioPathAnimation.enabled && audioPathAnimation.movementMode === 'accumulate'">
            <label>Beat Threshold</label>
            <div class="value-group">
              <ScrubableNumber
                :modelValue="audioPathAnimation.beatThreshold"
                @update:modelValue="(v: number) => updateAudioPathConfig('beatThreshold', v)"
                :min="0.01"
                :max="0.5"
                :precision="3"
              />
            </div>
          </div>

          <!-- Auto Orient -->
          <div class="property-row" v-if="audioPathAnimation.enabled">
            <label>Auto Orient</label>
            <input
              type="checkbox"
              :checked="audioPathAnimation.autoOrient"
              @change="(e) => updateAudioPathConfig('autoOrient', (e.target as HTMLInputElement).checked)"
              class="checkbox-input"
            />
          </div>

          <!-- Rotation Offset (when auto-orient enabled) -->
          <div class="property-row" v-if="audioPathAnimation.enabled && audioPathAnimation.autoOrient">
            <label>Rotation Offset</label>
            <div class="value-group">
              <ScrubableNumber
                :modelValue="audioPathAnimation.rotationOffset"
                @update:modelValue="(v: number) => updateAudioPathConfig('rotationOffset', v)"
                suffix="°"
              />
            </div>
          </div>
        </div>
      </div>

      <!-- Property Drivers -->
      <DriverList v-if="selectedLayer" :layerId="selectedLayer.id" />
    </div>

    <!-- No Selection -->
    <div v-else class="empty-state">
      <div class="empty-icon">📋</div>
      <p class="empty-title">No Layer Selected</p>
      <p class="empty-hint">Click a layer in the timeline or canvas to view and edit its properties</p>
    </div>
  </div>
</template>

<script setup lang="ts">
import {
  type Component,
  computed,
  inject,
  markRaw,
  type Ref,
  ref,
  watch,
} from "vue";
import { useAnimationStore } from "@/stores/animationStore";
import { useLayerStore } from "@/stores/layerStore";
import { useExpressionStore } from "@/stores/expressionStore";

// Inject soloedProperty from parent for P/S/R/T/A/U shortcuts
type SoloedProperty =
  | "position"
  | "scale"
  | "rotation"
  | "opacity"
  | "anchor"
  | "animated"
  | null;
const soloedProperty = inject<Ref<SoloedProperty>>("soloedProperty", ref(null));

import EffectControlsPanel from "@/components/panels/EffectControlsPanel.vue";
import Model3DProperties from "@/components/panels/Model3DProperties.vue";
import AudioProperties from "@/components/properties/AudioProperties.vue";
import CameraProperties from "@/components/properties/CameraProperties.vue";
import ControlProperties from "@/components/properties/ControlProperties.vue";
import DepthflowProperties from "@/components/properties/DepthflowProperties.vue";
import DepthProperties from "@/components/properties/DepthProperties.vue";
import GeneratedProperties from "@/components/properties/GeneratedProperties.vue";
import GroupProperties from "@/components/properties/GroupProperties.vue";
import LightProperties from "@/components/properties/LightProperties.vue";
import MatteProperties from "@/components/properties/MatteProperties.vue";
import NestedCompProperties from "@/components/properties/NestedCompProperties.vue";
import NormalProperties from "@/components/properties/NormalProperties.vue";
import ParticleProperties from "@/components/properties/ParticleProperties.vue";
import PathProperties from "@/components/properties/PathProperties.vue";
import PoseProperties from "@/components/properties/PoseProperties.vue";
import ShapeLayerProperties from "@/components/properties/ShapeLayerProperties.vue";
import ShapeProperties from "@/components/properties/ShapeProperties.vue";
import SolidProperties from "@/components/properties/SolidProperties.vue";
// Layer-specific property panels
import TextProperties from "@/components/properties/TextProperties.vue";
import VideoProperties from "@/components/properties/VideoProperties.vue";
import { isFiniteNumber, hasXY } from "@/utils/typeGuards";
import type { PropertyPath } from "@/services/propertyDriver";
import type { AudioPathAnimation, BlendMode, LayerDataUnion } from "@/types/project";
import { createAnimatableProperty } from "@/types/project";

const animationStore = useAnimationStore();
const layerStore = useLayerStore();
const expressionStore = useExpressionStore();

// State
const expandedSections = ref<string[]>(["transform"]);
const scaleLocked = ref(true);

const layerName = ref("");

// Audio Path Animation state
const audioPathAnimation = ref({
  enabled: false,
  pathData: "",
  movementMode: "amplitude" as "amplitude" | "accumulate",
  sensitivity: 1.0,
  smoothing: 0.3,
  release: 0.5,
  amplitudeCurve: 1.0,
  flipOnBeat: true,
  beatThreshold: 0.05,
  autoOrient: false,
  rotationOffset: 0,
});
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
  rotationZ: 0,
});
const blendMode = ref("normal");
const keyframes = ref<string[]>([]);

// Blend modes
const blendModes = [
  { label: "Normal", value: "normal" },
  { label: "Multiply", value: "multiply" },
  { label: "Screen", value: "screen" },
  { label: "Overlay", value: "overlay" },
  { label: "Soft Light", value: "soft-light" },
  { label: "Hard Light", value: "hard-light" },
  { label: "Color Dodge", value: "color-dodge" },
  { label: "Color Burn", value: "color-burn" },
  { label: "Darken", value: "darken" },
  { label: "Lighten", value: "lighten" },
  { label: "Difference", value: "difference" },
  { label: "Exclusion", value: "exclusion" },
  { label: "Hue", value: "hue" },
  { label: "Saturation", value: "saturation" },
  { label: "Color", value: "color" },
  { label: "Luminosity", value: "luminosity" },
  { label: "Add", value: "add" },
];

// Computed
const selectedLayer = computed(() => store.selectedLayer);

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
// Computed property for selectedLayer.threeD check
const isLayer3D = computed(() => {
  const layer = selectedLayer.value;
  return (layer != null && typeof layer === "object" && "threeD" in layer && typeof layer.threeD === "boolean") ? layer.threeD : false;
});

// Computed property for selectedLayer.parentId
const layerParentId = computed(() => {
  const layer = selectedLayer.value;
  return (layer != null && typeof layer === "object" && "parentId" in layer && (layer.parentId == null || typeof layer.parentId === "string")) ? layer.parentId : "";
});

// Property solo visibility - determines which properties are shown based on P/S/R/T/A/U shortcuts
const showAnchor = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === "anchor") return true;
  if (solo === "animated") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const layer = selectedLayer.value;
    if (layer == null || typeof layer !== "object" || !("transform" in layer)) return false;
    const transform = layer.transform;
    if (transform == null || typeof transform !== "object" || !("anchorPoint" in transform)) return false;
    const anchorPoint = transform.anchorPoint;
    if (anchorPoint == null || typeof anchorPoint !== "object" || !("animated" in anchorPoint)) return false;
    return typeof anchorPoint.animated === "boolean" ? anchorPoint.animated : false;
  }
  return false;
});

const showPosition = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === "position") return true;
  if (solo === "animated") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const layer = selectedLayer.value;
    if (layer == null || typeof layer !== "object" || !("transform" in layer)) return false;
    const transform = layer.transform;
    if (transform === null || transform === undefined || typeof transform !== "object" || !("position" in transform)) return false;
    const position = transform.position;
    if (position == null || typeof position !== "object" || !("animated" in position)) return false;
    return typeof position.animated === "boolean" ? position.animated : false;
  }
  return false;
});

const showScale = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === "scale") return true;
  if (solo === "animated") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const layer = selectedLayer.value;
    if (layer == null || typeof layer !== "object" || !("transform" in layer)) return false;
    const transform = layer.transform;
    if (transform === null || transform === undefined || typeof transform !== "object" || !("scale" in transform)) return false;
    const scale = transform.scale;
    if (scale == null || typeof scale !== "object" || !("animated" in scale)) return false;
    return typeof scale.animated === "boolean" ? scale.animated : false;
  }
  return false;
});

const showRotation = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === "rotation") return true;
  if (solo === "animated") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const layer = selectedLayer.value;
    if (layer == null || typeof layer !== "object" || !("transform" in layer)) return false;
    const t = layer.transform;
    if (t == null || typeof t !== "object") return false;
    
    // Check rotation.animated
    if ("rotation" in t && t.rotation != null && typeof t.rotation === "object" && "animated" in t.rotation && typeof t.rotation.animated === "boolean" && t.rotation.animated) return true;
    // Check rotationX.animated
    if ("rotationX" in t && t.rotationX != null && typeof t.rotationX === "object" && "animated" in t.rotationX && typeof t.rotationX.animated === "boolean" && t.rotationX.animated) return true;
    // Check rotationY.animated
    if ("rotationY" in t && t.rotationY != null && typeof t.rotationY === "object" && "animated" in t.rotationY && typeof t.rotationY.animated === "boolean" && t.rotationY.animated) return true;
    // Check rotationZ.animated
    if ("rotationZ" in t && t.rotationZ != null && typeof t.rotationZ === "object" && "animated" in t.rotationZ && typeof t.rotationZ.animated === "boolean" && t.rotationZ.animated) return true;
    // Check orientation.animated
    if ("orientation" in t && t.orientation != null && typeof t.orientation === "object" && "animated" in t.orientation && typeof t.orientation.animated === "boolean" && t.orientation.animated) return true;
    
    return false;
  }
  return false;
});

const showOpacity = computed(() => {
  const solo = soloedProperty.value;
  if (!solo) return true;
  if (solo === "opacity") return true;
  if (solo === "animated") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const layer = selectedLayer.value;
    if (layer == null || typeof layer !== "object" || !("opacity" in layer)) return false;
    const opacity = layer.opacity;
    if (opacity == null || typeof opacity !== "object" || !("animated" in opacity)) return false;
    return typeof opacity.animated === "boolean" ? opacity.animated : false;
  }
  return false;
});

// Dimension separation state for position and scale
const positionSeparated = computed(() => {
  if (!selectedLayer.value) return false;
  return store.hasPositionSeparated(selectedLayer.value.id);
});

const scaleSeparated = computed(() => {
  if (!selectedLayer.value) return false;
  return store.hasScaleSeparated(selectedLayer.value.id);
});

// Show indicator when in solo mode
const soloModeActive = computed(() => soloedProperty.value !== null);

// Get layers that can be parents (exclude self and children to prevent cycles)
const availableParents = computed(() => {
  if (!selectedLayer.value) return [];

  const selfId = selectedLayer.value.id;

  // Get all descendant IDs to prevent circular parenting
  const getDescendantIds = (layerId: string): string[] => {
    const children = store.layers.filter((l) => l.parentId === layerId);
    let ids = children.map((c) => c.id);
    for (const child of children) {
      ids = ids.concat(getDescendantIds(child.id));
    }
    return ids;
  };

  const descendantIds = new Set(getDescendantIds(selfId));

  return store.layers.filter(
    (l) => l.id !== selfId && !descendantIds.has(l.id) && l.type !== "camera", // Camera layers shouldn't be parents
  );
});

// System F/Omega: Computed property that throws explicit errors instead of returning null
const layerPropertiesComponentRaw = computed<Component>(() => {
  if (!selectedLayer.value) {
    throw new Error(
      `[PropertiesPanel] Cannot get layer properties component: No layer selected. ` +
      `Select a layer first to view its properties.`
    );
  }

  switch (selectedLayer.value.type) {
    case "text":
      return markRaw(TextProperties);
    case "particles":
    case "particle":
      return markRaw(ParticleProperties);
    case "depthflow":
      return markRaw(DepthflowProperties);
    case "light":
      return markRaw(LightProperties);
    case "spline":
      return markRaw(ShapeProperties);
    case "path":
      return markRaw(PathProperties);
    case "video":
      return markRaw(VideoProperties);
    case "camera":
      return markRaw(CameraProperties);
    case "nestedComp":
      return markRaw(NestedCompProperties);
    case "model":
    case "pointcloud":
      return markRaw(Model3DProperties);
    case "shape":
      return markRaw(ShapeLayerProperties);
    case "audio":
      return markRaw(AudioProperties);
    case "depth":
      return markRaw(DepthProperties);
    case "normal":
      return markRaw(NormalProperties);
    case "generated":
      return markRaw(GeneratedProperties);
    case "group":
      return markRaw(GroupProperties);
    case "control":
      return markRaw(ControlProperties);
    case "matte":
      return markRaw(MatteProperties);
    case "solid":
      return markRaw(SolidProperties);
    case "pose":
      return markRaw(PoseProperties);
    case "effectLayer":
    case "adjustment": // Deprecated, use 'effectLayer'
      return markRaw(EffectControlsPanel);
    case "image":
    case "null":
      // System F/Omega: Throw explicit error - these layer types use default transform controls only
      throw new Error(
        `[PropertiesPanel] Cannot get layer properties component: Layer type "${selectedLayer.value.type}" has no custom properties component. ` +
        `Layer ID: ${selectedLayer.value.id}, name: ${selectedLayer.value.name}. ` +
        `This layer type uses default transform controls only. Wrap in try/catch if "no component" is an expected state.`
      );
    default:
      // System F/Omega: Throw explicit error for unknown layer types
      throw new Error(
        `[PropertiesPanel] Cannot get layer properties component: Unknown layer type. ` +
        `Layer type: "${selectedLayer.value.type}", layer ID: ${selectedLayer.value.id}, name: ${selectedLayer.value.name}. ` +
        `Layer type must be a recognized type. Wrap in try/catch if "unknown type" is an expected state.`
      );
  }
});

// Wrapper computed property for template use - catches errors and returns null for conditional rendering
// System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
// The main computed property (layerPropertiesComponentRaw) throws explicit errors per System F/Omega
// This is a necessary exception for Vue template conditional rendering with v-if
const layerPropertiesComponent = computed<Component | null>(() => {
  try {
    return layerPropertiesComponentRaw.value;
  } catch {
    // System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
    // Template uses v-if="layerPropertiesComponent" which requires null for conditional rendering
    // This is the ONLY place where null is returned - all other code throws explicit errors
    return null;
  }
});

// Helper to sync transform from layer to local state
function syncTransformFromLayer(layer: typeof selectedLayer.value) {
  if (!layer) return;
  layerName.value = layer.name;
  const t = layer.transform;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  // Type proof: position.x/y/z ∈ ℝ ∪ {undefined} → ℝ
  const posXValue = (t != null && typeof t === "object" && "position" in t && t.position != null && typeof t.position === "object" && "value" in t.position && t.position.value != null && typeof t.position.value === "object" && "x" in t.position.value && typeof t.position.value.x === "number") ? t.position.value.x : undefined;
  const posX = isFiniteNumber(posXValue) ? posXValue : 0;
  const posYValue = (t != null && typeof t === "object" && "position" in t && t.position != null && typeof t.position === "object" && "value" in t.position && t.position.value != null && typeof t.position.value === "object" && "y" in t.position.value && typeof t.position.value.y === "number") ? t.position.value.y : undefined;
  const posY = isFiniteNumber(posYValue) ? posYValue : 0;
  const posZValue = (t != null && typeof t === "object" && "position" in t && t.position != null && typeof t.position === "object" && "value" in t.position && t.position.value != null && typeof t.position.value === "object" && "z" in t.position.value && typeof t.position.value.z === "number") ? t.position.value.z : undefined;
  const posZ = isFiniteNumber(posZValue) ? posZValue : 0;
  // Type proof: scale.x/y/z ∈ ℝ ∪ {undefined} → ℝ
  const scaleXValue = (t != null && typeof t === "object" && "scale" in t && t.scale != null && typeof t.scale === "object" && "value" in t.scale && t.scale.value != null && typeof t.scale.value === "object" && "x" in t.scale.value && typeof t.scale.value.x === "number") ? t.scale.value.x : undefined;
  const scaleX = isFiniteNumber(scaleXValue) ? scaleXValue : 100;
  const scaleYValue = (t != null && typeof t === "object" && "scale" in t && t.scale != null && typeof t.scale === "object" && "value" in t.scale && t.scale.value != null && typeof t.scale.value === "object" && "y" in t.scale.value && typeof t.scale.value.y === "number") ? t.scale.value.y : undefined;
  const scaleY = isFiniteNumber(scaleYValue) ? scaleYValue : 100;
  const scaleZValue = (t != null && typeof t === "object" && "scale" in t && t.scale != null && typeof t.scale === "object" && "value" in t.scale && t.scale.value != null && typeof t.scale.value === "object" && "z" in t.scale.value && typeof t.scale.value.z === "number") ? t.scale.value.z : undefined;
  const scaleZ = isFiniteNumber(scaleZValue) ? scaleZValue : 100;
  // Type proof: rotation ∈ ℝ ∪ {undefined} → ℝ
  const rotationValue = (t != null && typeof t === "object" && "rotation" in t && t.rotation != null && typeof t.rotation === "object" && "value" in t.rotation && typeof t.rotation.value === "number") ? t.rotation.value : undefined;
  const rotation = isFiniteNumber(rotationValue) ? rotationValue : 0;
  // Type proof: anchorPoint.x/y/z ∈ ℝ ∪ {undefined} → ℝ
  const anchorXValue = (t != null && typeof t === "object" && "anchorPoint" in t && t.anchorPoint != null && typeof t.anchorPoint === "object" && "value" in t.anchorPoint && t.anchorPoint.value != null && typeof t.anchorPoint.value === "object" && "x" in t.anchorPoint.value && typeof t.anchorPoint.value.x === "number") ? t.anchorPoint.value.x : undefined;
  const anchorX = isFiniteNumber(anchorXValue) ? anchorXValue : 0;
  const anchorYValue = (t != null && typeof t === "object" && "anchorPoint" in t && t.anchorPoint != null && typeof t.anchorPoint === "object" && "value" in t.anchorPoint && t.anchorPoint.value != null && typeof t.anchorPoint.value === "object" && "y" in t.anchorPoint.value && typeof t.anchorPoint.value.y === "number") ? t.anchorPoint.value.y : undefined;
  const anchorY = isFiniteNumber(anchorYValue) ? anchorYValue : 0;
  const anchorZValue = (t != null && typeof t === "object" && "anchorPoint" in t && t.anchorPoint != null && typeof t.anchorPoint === "object" && "value" in t.anchorPoint && t.anchorPoint.value != null && typeof t.anchorPoint.value === "object" && "z" in t.anchorPoint.value && typeof t.anchorPoint.value.z === "number") ? t.anchorPoint.value.z : undefined;
  const anchorZ = isFiniteNumber(anchorZValue) ? anchorZValue : 0;
  // Type proof: opacity ∈ ℝ ∪ {undefined} → ℝ
  const opacityValue = (layer != null && typeof layer === "object" && "opacity" in layer && layer.opacity != null && typeof layer.opacity === "object" && "value" in layer.opacity && typeof layer.opacity.value === "number") ? layer.opacity.value : undefined;
  const opacity = isFiniteNumber(opacityValue) ? opacityValue : 100;
  // Type proof: orientation.x/y/z ∈ ℝ ∪ {undefined} → ℝ
  const orientXValue = (t != null && typeof t === "object" && "orientation" in t && t.orientation != null && typeof t.orientation === "object" && "value" in t.orientation && t.orientation.value != null && typeof t.orientation.value === "object" && "x" in t.orientation.value && typeof t.orientation.value.x === "number") ? t.orientation.value.x : undefined;
  const orientX = isFiniteNumber(orientXValue) ? orientXValue : 0;
  const orientYValue = (t != null && typeof t === "object" && "orientation" in t && t.orientation != null && typeof t.orientation === "object" && "value" in t.orientation && t.orientation.value != null && typeof t.orientation.value === "object" && "y" in t.orientation.value && typeof t.orientation.value.y === "number") ? t.orientation.value.y : undefined;
  const orientY = isFiniteNumber(orientYValue) ? orientYValue : 0;
  const orientZValue = (t != null && typeof t === "object" && "orientation" in t && t.orientation != null && typeof t.orientation === "object" && "value" in t.orientation && t.orientation.value != null && typeof t.orientation.value === "object" && "z" in t.orientation.value && typeof t.orientation.value.z === "number") ? t.orientation.value.z : undefined;
  const orientZ = isFiniteNumber(orientZValue) ? orientZValue : 0;
  // Type proof: rotationX/Y/Z ∈ ℝ ∪ {undefined} → ℝ
  const rotXValue = (t != null && typeof t === "object" && "rotationX" in t && t.rotationX != null && typeof t.rotationX === "object" && "value" in t.rotationX && typeof t.rotationX.value === "number") ? t.rotationX.value : undefined;
  const rotX = isFiniteNumber(rotXValue) ? rotXValue : 0;
  const rotYValue = (t != null && typeof t === "object" && "rotationY" in t && t.rotationY != null && typeof t.rotationY === "object" && "value" in t.rotationY && typeof t.rotationY.value === "number") ? t.rotationY.value : undefined;
  const rotY = isFiniteNumber(rotYValue) ? rotYValue : 0;
  const rotZValue = (t != null && typeof t === "object" && "rotationZ" in t && t.rotationZ != null && typeof t.rotationZ === "object" && "value" in t.rotationZ && typeof t.rotationZ.value === "number") ? t.rotationZ.value : undefined;
  const rotZ = isFiniteNumber(rotZValue) ? rotZValue : 0;
  transform.value = {
    position: {
      x: posX,
      y: posY,
      z: posZ,
    },
    scale: {
      x: scaleX,
      y: scaleY,
      z: scaleZ,
    },
    rotation,
    anchorPoint: {
      x: anchorX,
      y: anchorY,
      z: anchorZ,
    },
    opacity,
    // 3D properties
    orientationX: orientX,
    orientationY: orientY,
    orientationZ: orientZ,
    rotationX: rotX,
    rotationY: rotY,
    rotationZ: rotZ,
  };
  blendMode.value = layer.blendMode || "normal";
}

// Watch selected layer for selection changes
watch(
  selectedLayer,
  (layer) => {
    syncTransformFromLayer(layer);
    syncAudioPathAnimationFromLayer(layer);
  },
  { immediate: true },
);

// Sync audioPathAnimation from layer
function syncAudioPathAnimationFromLayer(layer: typeof selectedLayer.value) {
  if (!layer) return;
  const apa = layer.audioPathAnimation;
  if (apa) {
    // Type proof: enabled, autoOrient, flipOnBeat ∈ boolean | undefined → boolean
    const enabled = typeof apa.enabled === "boolean" ? apa.enabled : false;
    // Type proof: pathData ∈ string | undefined → string
    const pathData = typeof apa.pathData === "string" ? apa.pathData : "";
    // Type proof: movementMode ∈ string | undefined → string
    const movementMode = typeof apa.movementMode === "string" ? apa.movementMode : "amplitude";
    // Type proof: sensitivity, smoothing, release, amplitudeCurve, beatThreshold, rotationOffset ∈ ℝ ∧ finite → ℝ
    const sensitivity = isFiniteNumber(apa.sensitivity) && apa.sensitivity > 0 ? apa.sensitivity : 1.0;
    const smoothing = isFiniteNumber(apa.smoothing) && apa.smoothing >= 0 && apa.smoothing <= 1 ? apa.smoothing : 0.3;
    const release = isFiniteNumber(apa.release) && apa.release >= 0 && apa.release <= 1 ? apa.release : 0.5;
    const amplitudeCurve = isFiniteNumber(apa.amplitudeCurve) && apa.amplitudeCurve > 0 ? apa.amplitudeCurve : 1.0;
    const flipOnBeat = typeof apa.flipOnBeat === "boolean" ? apa.flipOnBeat : true;
    const beatThreshold = isFiniteNumber(apa.beatThreshold) && apa.beatThreshold >= 0 ? apa.beatThreshold : 0.05;
    const autoOrient = typeof apa.autoOrient === "boolean" ? apa.autoOrient : false;
    const rotationOffset = isFiniteNumber(apa.rotationOffset) ? apa.rotationOffset : 0;
    audioPathAnimation.value = {
      enabled,
      pathData,
      movementMode,
      sensitivity,
      smoothing,
      release,
      amplitudeCurve,
      flipOnBeat,
      beatThreshold,
      autoOrient,
      rotationOffset,
    };
  } else {
    // Reset to defaults
    audioPathAnimation.value = {
      enabled: false,
      pathData: "",
      movementMode: "amplitude",
      sensitivity: 1.0,
      smoothing: 0.3,
      release: 0.5,
      amplitudeCurve: 1.0,
      flipOnBeat: true,
      beatThreshold: 0.05,
      autoOrient: false,
      rotationOffset: 0,
    };
  }
}

// Deep watch the layer's transform to sync when it changes from other sources (e.g. timeline panel)
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
watch(
  () => {
    const layer = selectedLayer.value;
    return (layer != null && typeof layer === "object" && "transform" in layer) ? layer.transform : undefined;
  },
  () => {
    syncTransformFromLayer(selectedLayer.value);
  },
  { deep: true },
);

// Also watch opacity separately since it's not in transform
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
watch(
  () => {
    const layer = selectedLayer.value;
    if (layer == null || typeof layer !== "object" || !("opacity" in layer)) return undefined;
    const opacity = layer.opacity;
    return (opacity != null && typeof opacity === "object" && "value" in opacity && typeof opacity.value === "number") ? opacity.value : undefined;
  },
  (newVal) => {
    if (newVal !== undefined) {
      transform.value.opacity = newVal;
    }
  },
);

// Watch scale lock
watch(
  () => transform.value.scale.x,
  (newX, oldX) => {
    if (scaleLocked.value && newX !== oldX) {
      const ratio = newX / oldX;
      transform.value.scale.y =
        Math.round(transform.value.scale.y * ratio * 10) / 10;
    }
  },
);

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

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (t != null && typeof t === "object" && "position" in t && t.position != null && typeof t.position === "object" && "value" in t.position) {
    t.position.value = { x: v.position.x, y: v.position.y, z: v.position.z };
  }
  if (t != null && typeof t === "object" && "scale" in t && t.scale != null && typeof t.scale === "object" && "value" in t.scale) {
    t.scale.value = { x: v.scale.x, y: v.scale.y, z: v.scale.z };
  }
  if (t != null && typeof t === "object" && "rotation" in t && t.rotation != null && typeof t.rotation === "object" && "value" in t.rotation) {
    t.rotation.value = v.rotation;
  }
  if (t != null && typeof t === "object" && "anchorPoint" in t && t.anchorPoint != null && typeof t.anchorPoint === "object" && "value" in t.anchorPoint) {
    t.anchorPoint.value = {
      x: v.anchorPoint.x,
      y: v.anchorPoint.y,
      z: v.anchorPoint.z,
    };
  }
  if (selectedLayer.value.opacity != null && typeof selectedLayer.value.opacity === "object" && "value" in selectedLayer.value.opacity) {
    selectedLayer.value.opacity.value = v.opacity;
  }

  // 3D properties
  if (selectedLayer.value.threeD) {
    if (t != null && typeof t === "object" && "orientation" in t && t.orientation != null && typeof t.orientation === "object" && "value" in t.orientation) {
      t.orientation.value = {
        x: v.orientationX,
        y: v.orientationY,
        z: v.orientationZ,
      };
    }
    if (t != null && typeof t === "object" && "rotationX" in t && t.rotationX != null && typeof t.rotationX === "object" && "value" in t.rotationX) {
      t.rotationX.value = v.rotationX;
    }
    if (t != null && typeof t === "object" && "rotationY" in t && t.rotationY != null && typeof t.rotationY === "object" && "value" in t.rotationY) {
      t.rotationY.value = v.rotationY;
    }
    if (t != null && typeof t === "object" && "rotationZ" in t && t.rotationZ != null && typeof t.rotationZ === "object" && "value" in t.rotationZ) {
      t.rotationZ.value = v.rotationZ;
    }
  }

  onLayerUpdate();
}

function updateBlendMode() {
  if (selectedLayer.value) {
    layerStore.updateLayer(selectedLayer.value.id, {
      blendMode: blendMode.value as BlendMode,
    });
  }
}

function toggle3D(event: Event) {
  if (!selectedLayer.value) return;
  const threeD = (event.target as HTMLInputElement).checked;
  layerStore.updateLayer(selectedLayer.value.id, { threeD });

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
    if (t.anchorPoint && t.anchorPoint.value.z === undefined) {
      t.anchorPoint.value.z = 0;
    }

    // Initialize 3D rotation properties if they don't exist
    if (!t.orientation) {
      t.orientation = createAnimatableProperty(
        "orientation",
        { x: 0, y: 0, z: 0 },
        "vector3",
      );
    }
    if (!t.rotationX) {
      t.rotationX = createAnimatableProperty("rotationX", 0, "number");
    }
    if (!t.rotationY) {
      t.rotationY = createAnimatableProperty("rotationY", 0, "number");
    }
    if (!t.rotationZ) {
      t.rotationZ = createAnimatableProperty("rotationZ", 0, "number");
    }
  }
}

// ============================================================
// DIMENSION SEPARATION METHODS
// ============================================================

/**
 * Toggle position dimension separation.
 * When separated, X, Y, Z can have independent keyframes.
 */
function togglePositionSeparation() {
  if (!selectedLayer.value) return;

  if (positionSeparated.value) {
    store.linkPositionDimensions(selectedLayer.value.id);
  } else {
    store.separatePositionDimensions(selectedLayer.value.id);
  }
}

/**
 * Toggle scale dimension separation.
 * When separated, X, Y, Z can have independent keyframes.
 */
function toggleScaleSeparation() {
  if (!selectedLayer.value) return;

  if (scaleSeparated.value) {
    store.linkScaleDimensions(selectedLayer.value.id);
  } else {
    store.separateScaleDimensions(selectedLayer.value.id);
  }
}

// ============================================================
// AUDIO PATH ANIMATION METHODS
// ============================================================

function updateAudioPathEnabled(event: Event) {
  if (!selectedLayer.value) return;
  const enabled = (event.target as HTMLInputElement).checked;
  audioPathAnimation.value.enabled = enabled;

  // Initialize audioPathAnimation on layer if it doesn't exist
  if (!selectedLayer.value.audioPathAnimation) {
    selectedLayer.value.audioPathAnimation = {
      enabled,
      pathData: audioPathAnimation.value.pathData,
      movementMode: audioPathAnimation.value.movementMode,
      sensitivity: audioPathAnimation.value.sensitivity,
      smoothing: audioPathAnimation.value.smoothing,
      release: audioPathAnimation.value.release,
      amplitudeCurve: audioPathAnimation.value.amplitudeCurve,
      flipOnBeat: audioPathAnimation.value.flipOnBeat,
      beatThreshold: audioPathAnimation.value.beatThreshold,
      autoOrient: audioPathAnimation.value.autoOrient,
      rotationOffset: audioPathAnimation.value.rotationOffset,
    };
  } else {
    selectedLayer.value.audioPathAnimation.enabled = enabled;
  }
  onLayerUpdate();
}

function updateAudioPathData(event: Event) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layer = selectedLayer.value;
  if (layer == null || typeof layer !== "object" || !("audioPathAnimation" in layer) || layer.audioPathAnimation == null || typeof layer.audioPathAnimation !== "object") return;
  const pathData = (event.target as HTMLTextAreaElement).value;
  audioPathAnimation.value.pathData = pathData;
  layer.audioPathAnimation.pathData = pathData;
  onLayerUpdate();
}

function updateAudioPathMode(event: Event) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layer = selectedLayer.value;
  if (layer == null || typeof layer !== "object" || !("audioPathAnimation" in layer) || layer.audioPathAnimation == null || typeof layer.audioPathAnimation !== "object") return;
  const mode = (event.target as HTMLSelectElement).value as
    | "amplitude"
    | "accumulate";
  audioPathAnimation.value.movementMode = mode;
  layer.audioPathAnimation.movementMode = mode;
  onLayerUpdate();
}

function updateAudioPathConfig(
  key: keyof AudioPathAnimation,
  value: number | boolean,
) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layer = selectedLayer.value;
  if (layer == null || typeof layer !== "object" || !("audioPathAnimation" in layer) || layer.audioPathAnimation == null || typeof layer.audioPathAnimation !== "object") return;
  if (audioPathAnimation.value == null || typeof audioPathAnimation.value !== "object") return;
  audioPathAnimation.value[key] = value;
  layer.audioPathAnimation[key] = value;
  onLayerUpdate();
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
    console.log(
      `Added keyframe for ${property} at frame ${animationStore.currentFrame}`,
    );
  }
}

function onLayerUpdate(dataUpdates?: Partial<LayerDataUnion>) {
  if (!selectedLayer.value) return;

  // If data updates are provided, apply them via store
  if (dataUpdates && Object.keys(dataUpdates).length > 0) {
    layerStore.updateLayerData(selectedLayer.value.id, dataUpdates);
  } else {
    store.project.meta.modified = new Date().toISOString();
  }
}

function updateParent(event: Event) {
  if (!selectedLayer.value) return;
  const parentId = (event.target as HTMLSelectElement).value || null;
  layerStore.setLayerParent(selectedLayer.value.id, parentId);
}

// ============================================================
// PROPERTY DRIVER / PICKWHIP FUNCTIONS
// ============================================================

/**
 * Get the driver linked to a property, if any
 * 
 * System F/Omega proof: Explicit error throwing - never return null
 * Type proof: property ∈ PropertyPath → { layerId: string; property: PropertyPath } (non-nullable)
 * Mathematical proof: Driver lookup must succeed or throw explicit error
 * Pattern proof: Missing driver is an explicit error condition
 */
function getDriverForPropertyRaw(
  property: PropertyPath,
): { layerId: string; property: PropertyPath } {
  if (!selectedLayer.value) {
    throw new Error(
      `[PropertiesPanel] Cannot get driver for property: No layer selected. ` +
      `Property: ${property}. ` +
      `Select a layer first to check for property drivers.`
    );
  }

  const drivers = expressionStore.getDriversForLayer(selectedLayer.value.id);
  const driver = drivers.find(
    (d) => d.targetProperty === property && d.sourceType === "property",
  );

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  if (driver != null && typeof driver === "object" && "sourceLayerId" in driver && typeof driver.sourceLayerId === "string" && driver.sourceLayerId !== "" && "sourceProperty" in driver && driver.sourceProperty != null) {
    return {
      layerId: driver.sourceLayerId,
      property: driver.sourceProperty,
    };
  }
  
  // System F/Omega: Throw explicit error when no driver is found
  throw new Error(
    `[PropertiesPanel] Cannot get driver for property: No driver linked. ` +
    `Property: ${property}, layer ID: ${selectedLayer.value.id}, layer name: ${selectedLayer.value.name}. ` +
    `No property driver is linked to this property. Wrap in try/catch if "no driver" is an expected state.`
  );
}

// Wrapper function for template use - catches errors and returns null for PropertyLink component
// System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
// PropertyLink component expects linkedTo?: { layerId: string; property: PropertyPath } | null
// This is a necessary exception for Vue component prop compatibility
function getDriverForProperty(
  property: PropertyPath,
): { layerId: string; property: PropertyPath } | null {
  try {
    return getDriverForPropertyRaw(property);
  } catch {
    // System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
    // PropertyLink component accepts null for "no link" state
    // This is the ONLY place where null is returned - all other code throws explicit errors
    return null;
  }
}

/**
 * Handle property link event
 */
function onPropertyLink(
  targetProperty: PropertyPath,
  source: { layerId: string; property: PropertyPath },
) {
  if (!selectedLayer.value) return;

  // Create the property link
  expressionStore.createPropertyLinkDriver(
    store,
    selectedLayer.value.id,
    targetProperty,
    source.layerId,
    source.property,
    { blendMode: "add" },
  );

  console.log(
    `[PropertiesPanel] Linked ${selectedLayer.value.id}.${targetProperty} <- ${source.layerId}.${source.property}`,
  );
}

/**
 * Handle property unlink event
 */
function onPropertyUnlink(targetProperty: PropertyPath) {
  if (!selectedLayer.value) return;

  // Find and remove the driver
  const drivers = expressionStore.getDriversForLayer(selectedLayer.value.id);
  const driver = drivers.find(
    (d) => d.targetProperty === targetProperty && d.sourceType === "property",
  );

  if (driver) {
    expressionStore.removePropertyDriver(driver.id);
    console.log(
      `[PropertiesPanel] Unlinked ${selectedLayer.value.id}.${targetProperty}`,
    );
  }
}

/**
 * Format rotation value: 0x+0°
 * e.g., 450 degrees = 1x+90°
 */
function formatRotation(degrees: number): string {
  const revolutions = Math.floor(Math.abs(degrees) / 360);
  const remainder = Math.abs(degrees) % 360;
  const sign = degrees < 0 ? "-" : "";
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
  const drivers = expressionStore.getDriversForLayer(selectedLayer.value.id);
  return drivers.some((d) => d.targetProperty === property && d.enabled);
}
</script>

<style scoped>
.properties-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #141414);
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: var(--lattice-text-base, 12px);
}

.panel-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 10px 12px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-bottom: 1px solid var(--lattice-border-default, #2a2a2a);
}

.panel-title {
  font-weight: 500;
  font-size: var(--lattice-text-sm, 11px);
  color: var(--lattice-text-secondary, #9CA3AF);
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
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
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
  background: var(--lattice-surface-3, #222222);
}

.expand-icon {
  width: 10px;
  font-size: 10px;
  color: var(--lattice-text-muted, #6B7280);
}

.section-title {
  font-weight: 500;
  font-size: var(--lattice-text-sm, 11px);
  flex: 1;
}

.reset-link {
  font-size: var(--lattice-text-xs, 10px);
  color: var(--lattice-accent, #8B5CF6);
  cursor: pointer;
  padding: 2px 8px;
}

.reset-link:hover {
  color: var(--lattice-accent-hover, #9D7AFA);
  text-decoration: underline;
}

.keyframe-toggle {
  width: 16px;
  font-size: 11px;
  color: var(--lattice-text-muted, #6B7280);
  cursor: pointer;
  flex-shrink: 0;
}

.keyframe-toggle:hover {
  color: var(--lattice-text-secondary, #9CA3AF);
}

.keyframe-toggle.active {
  color: var(--lattice-timeline-video, #FFD700);
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
  color: var(--lattice-accent, #8B5CF6);
}

.rotation-display {
  color: var(--lattice-accent, #8B5CF6);
  font-family: var(--lattice-font-mono, 'JetBrains Mono', monospace);
  font-size: var(--lattice-text-base, 12px);
}

.threeD-toggle {
  display: flex;
  align-items: center;
  gap: 4px;
  cursor: pointer;
  padding: 2px 6px;
  background: var(--lattice-surface-3, #222222);
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: var(--lattice-text-sm, 11px);
}

.threeD-toggle:hover {
  background: var(--lattice-surface-4, #2a2a2a);
}

.threeD-toggle input {
  margin: 0;
  cursor: pointer;
}

.threeD-toggle .toggle-label {
  color: var(--lattice-text-secondary, #9CA3AF);
  font-weight: 500;
}

.threeD-toggle input:checked + .toggle-label {
  color: var(--lattice-accent, #8B5CF6);
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
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
  border-left: 2px solid var(--lattice-accent, #8B5CF6);
}

.property-row.has-driver label {
  color: var(--lattice-accent, #8B5CF6);
}

.property-row label {
  width: 80px;
  color: var(--lattice-text-secondary, #9CA3AF);
  font-size: var(--lattice-text-sm, 11px);
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
  color: var(--lattice-text-muted, #6B7280);
  cursor: pointer;
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: 11px;
}

.link-btn:hover {
  background: var(--lattice-surface-3, #222222);
}

.link-btn.active {
  color: var(--lattice-accent, #8B5CF6);
}

/* Dimension separation button */
.dimension-sep-btn {
  flex: 0 0 auto;
  width: 18px;
  height: 18px;
  padding: 0;
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-muted, #6B7280);
  cursor: pointer;
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: 10px;
  line-height: 1;
  display: flex;
  align-items: center;
  justify-content: center;
}

.dimension-sep-btn:hover {
  background: var(--lattice-surface-3, #222222);
  border-color: var(--lattice-accent, #8B5CF6);
  color: var(--lattice-text-primary, #E5E5E5);
}

.dimension-sep-btn.active {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
  border-color: var(--lattice-accent, #8B5CF6);
  color: var(--lattice-accent, #8B5CF6);
}

/* Spacer for aligned separated dimension rows */
.dimension-sep-spacer {
  width: 18px;
  flex: 0 0 auto;
}

/* Color labels for separated dimensions */
.property-row label.x-label {
  color: #ff6b6b;
}

.property-row label.y-label {
  color: #51cf66;
}

.property-row label.z-label {
  color: #4dabf7;
}

.keyframe-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: var(--lattice-text-muted, #6B7280);
  cursor: pointer;
  font-size: 11px;
  border-radius: var(--lattice-radius-sm, 2px);
}

.keyframe-btn:hover {
  color: var(--lattice-text-secondary, #9CA3AF);
}

.keyframe-btn.active {
  color: var(--lattice-timeline-video, #FFD700);
}

.layer-name-input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-primary, #E5E5E5);
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: var(--lattice-text-sm, 11px);
  font-weight: 500;
}

.layer-name-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.blend-select,
.parent-select {
  flex: 1;
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  color: var(--lattice-text-primary, #E5E5E5);
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: var(--lattice-text-sm, 11px);
}

.blend-select:focus,
.parent-select:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.checkbox-input {
  width: 16px;
  height: 16px;
  cursor: pointer;
  accent-color: var(--lattice-accent, #8B5CF6);
}

.layer-type {
  font-size: 11px;
  color: var(--lattice-text-muted, #6B7280);
  text-transform: capitalize;
  background: var(--lattice-surface-2, #1a1a1a);
  padding: 2px 8px;
  border-radius: 4px;
}

.empty-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  padding: 24px;
  text-align: center;
  color: var(--lattice-text-muted, #6B7280);
}

.empty-icon {
  font-size: 32px;
  margin-bottom: 12px;
  opacity: 0.5;
}

.empty-title {
  font-size: 14px;
  font-weight: 600;
  color: var(--lattice-text-secondary, #9CA3AF);
  margin: 0 0 8px 0;
}

.empty-hint {
  font-size: 12px;
  color: var(--lattice-text-muted, #6B7280);
  max-width: 200px;
  line-height: 1.4;
  margin: 0;
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

.audio-path-content {
  padding: 8px 12px !important;
  max-height: 400px;
  overflow-y: auto;
}

.path-data-row {
  flex-direction: column;
  align-items: flex-start !important;
  gap: 4px !important;
}

.path-data-input {
  width: 100%;
  min-height: 50px;
  padding: 6px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  color: var(--lattice-text-primary, #E5E5E5);
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: var(--lattice-text-sm, 11px);
  font-family: var(--lattice-font-mono, 'JetBrains Mono', monospace);
  resize: vertical;
}

.path-data-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.path-data-input::placeholder {
  color: var(--lattice-text-muted, #6B7280);
}
</style>
