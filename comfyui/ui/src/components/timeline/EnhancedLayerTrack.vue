<template>
  <div class="track-wrapper" v-if="layer">
    <template v-if="layoutMode === 'sidebar'">
      <div class="sidebar-row"
           :class="{ selected: isSelected, 'drag-over': isDragTarget }"
           @mousedown="selectLayer"
           @contextmenu.prevent="showContextMenu"
           draggable="true"
           @dragstart="onDragStart"
           @dragend="onDragEnd"
           @dragover.prevent="onDragOver"
           @dragleave="onDragLeave"
           @drop="onDrop"
      >
        <!-- AV Features (visibility, audio, isolate, lock) -->
        <div class="av-features">
          <div class="icon-col" @mousedown.stop="toggleVis" :title="layer.visible ? 'Hide' : 'Show'">
            <PhEye v-if="layer.visible" :size="14" />
            <PhEyeSlash v-else :size="14" class="inactive" />
          </div>
          <div class="icon-col" v-if="hasAudioCapability" @mousedown.stop="toggleAudio" :title="layer.audioEnabled !== false ? 'Mute Audio' : 'Enable Audio'">
            <PhSpeakerHigh v-if="layer.audioEnabled !== false" :size="14" />
            <PhSpeakerSlash v-else :size="14" class="inactive" />
          </div>
          <div class="icon-col placeholder" v-else></div>
          <div class="icon-col" @mousedown.stop="toggleIsolate" :title="layer.isolate ? 'Unisolate' : 'Isolate'">
            <span :class="{ active: layer.isolate }">●</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleLock" :title="layer.locked ? 'Unlock' : 'Lock'">
            <PhLock v-if="layer.locked" :size="14" class="active" />
            <PhLockOpen v-else :size="14" />
          </div>
        </div>

        <!-- Layer info: label color, number, expand arrow, name -->
        <div class="layer-info">
          <div class="label-box" @mousedown.stop="toggleColorPicker" :style="{ background: layer.labelColor || '#999' }"></div>
          <div class="layer-id">{{ index }}</div>
          <div class="arrow-col" @mousedown.stop="toggleExpand">
            <span class="arrow">{{ isExpanded ? '▼' : '▶' }}</span>
          </div>
          <div class="layer-name-col" @dblclick.stop="handleDoubleClick">
            <span class="type-icon">{{ getLayerIcon(layer.type) }}</span>
            <span v-if="!isRenaming" class="name-text">{{ layer.name }}</span>
            <input v-else v-model="renameVal" @blur="saveRename" @keydown.enter="saveRename" class="rename-input" ref="renameInput" />
          </div>
        </div>

        <!-- Switches (minimized, collapse, quality, fx, frame blend, motion blur, adjustment, 3D) -->
        <div class="layer-switches">
          <div class="icon-col" @mousedown.stop="toggleMinimized" :title="layer.minimized ? 'Unminimize' : 'Minimize (hide when filter enabled)'">
            <PhEyeSlash :size="14" :class="{ active: layer.minimized }" />
          </div>
          <div class="icon-col" @mousedown.stop="toggleFlattenTransform" :title="layer.flattenTransform ? 'Disable Flatten Transform' : 'Flatten Transform'">
            <PhSun :size="14" :class="{ active: layer.flattenTransform }" />
          </div>
          <div class="icon-col" @mousedown.stop="toggleQuality" :title="layer.quality === 'best' ? 'Draft Quality' : 'Best Quality'">
            <span :class="{ active: layer.quality === 'best' }">◐</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleEffects" :title="layer.effectsEnabled !== false ? 'Disable Effects' : 'Enable Effects'">
            <span :class="{ active: layer.effectsEnabled !== false, inactive: layer.effectsEnabled === false }">fx</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleFrameBlend" :title="layer.frameBlending ? 'Disable Frame Blending' : 'Enable Frame Blending'">
            <span :class="{ active: layer.frameBlending }">⊞</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleMotionBlur" :title="layer.motionBlur ? 'Disable Motion Blur' : 'Enable Motion Blur'">
            <span :class="{ active: layer.motionBlur }">◔</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleEffectLayer" :title="(layer.effectLayer || layer.adjustmentLayer) ? 'Disable Effect Layer' : 'Make Effect Layer'">
            <span :class="{ active: layer.effectLayer || layer.adjustmentLayer }">◐</span>
          </div>
          <div class="icon-col" @mousedown.stop="layerStore.toggleLayer3D(layer.id)" :title="layer.threeD ? 'Make 2D Layer' : 'Make 3D Layer'">
            <span :class="{ active: layer.threeD }">⬡</span>
          </div>
        </div>

        <!-- Parent & Link -->
        <div class="col-parent">
          <select :value="layer.parentId || ''" class="mini-select" @change="setParent" @mousedown.stop>
            <option value="">None</option>
            <option v-for="p in availableParents" :key="p.id" :value="p.id">{{ p.index }}. {{ p.name }}</option>
          </select>
        </div>
      </div>

      <div v-if="isExpanded" class="children-container">
        <div v-for="(groupProps, groupName) in groupedProperties" :key="groupName" class="property-group">
          <div class="group-header sidebar-row" :style="gridStyle" @mousedown.stop="toggleGroup(String(groupName))">
             <div class="arrow-col"><span class="arrow">{{ expandedGroups.includes(String(groupName)) ? '▼' : '▶' }}</span></div>
             <div class="group-label">
               {{ groupName }}
               <span v-if="String(groupName) === 'Transform'" class="reset-link" @click.stop="resetTransform">Reset</span>
             </div>
          </div>
          <div v-if="expandedGroups.includes(String(groupName))">
             <PropertyTrack v-for="prop in groupProps" :key="prop.path"
               :layerId="layer.id" :propertyPath="prop.path" :name="prop.name" :property="prop.property"
               layoutMode="sidebar" :gridStyle="gridStyle" :pixelsPerFrame="pixelsPerFrame"
             />
          </div>
        </div>
      </div>
    </template>

    <template v-else>
      <div class="layer-row track-bg" @mousedown="selectLayer">
        <div class="duration-bar" :style="barStyle" @mousedown.stop="startDrag">
           <div class="bar-handle bar-handle-left" @mousedown.stop="startResizeLeft"></div>
           <div class="bar-fill" :style="{ background: layer.labelColor || '#777' }">
             <!-- Audio Waveform Canvas -->
             <canvas
               v-if="isAudioLayer && waveformData"
               ref="waveformCanvasRef"
               class="waveform-canvas"
             />
           </div>
           <div class="bar-handle bar-handle-right" @mousedown.stop="startResizeRight"></div>
        </div>
      </div>
      <div v-if="isExpanded" class="children-container">
        <div v-for="(groupProps, groupName) in groupedProperties" :key="groupName" class="property-group">
           <div class="group-header track-bg"></div>
           <div v-if="expandedGroups.includes(String(groupName))">
              <PropertyTrack v-for="prop in groupProps" :key="prop.path"
               :layerId="layer.id" :propertyPath="prop.path" :name="prop.name" :property="prop.property"
               layoutMode="track" :pixelsPerFrame="pixelsPerFrame"
             />
           </div>
        </div>
      </div>
    </template>

    <!-- Context Menu -->
    <Teleport to="body">
      <div
        v-if="contextMenuVisible"
        class="layer-context-menu"
        :style="{ left: contextMenuX + 'px', top: contextMenuY + 'px' }"
        @click.stop
      >
        <button @click="duplicateLayer">Duplicate Layer</button>
        <button @click="renameFromMenu">Rename</button>
        <hr />
        <button @click="toggleLayerVisibility">{{ layer.visible ? 'Hide' : 'Show' }} Layer</button>
        <button @click="toggleLayerLock">{{ layer.locked ? 'Unlock' : 'Lock' }} Layer</button>
        <button @click="toggleLayer3D">{{ layer.threeD ? 'Make 2D' : 'Make 3D' }}</button>
        <hr />
        <button v-if="isTextLayer" @click="convertToSplines">Convert to Splines</button>
        <button @click="nestLayer">Nest Layers...</button>
        <hr />
        <button @click="deleteLayer" class="danger">Delete Layer</button>
      </div>
    </Teleport>

    <!-- Layer Color Picker -->
    <Teleport to="body">
      <div
        v-if="showColorPicker"
        class="layer-color-picker"
        :style="{ left: colorPickerX + 'px', top: colorPickerY + 'px' }"
        @click.stop
      >
        <div class="color-grid">
          <button
            v-for="color in labelColors"
            :key="color"
            class="color-swatch"
            :style="{ backgroundColor: color }"
            :class="{ active: layer.labelColor === color }"
            @click="setLabelColor(color)"
          />
        </div>
      </div>
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import { computed, nextTick, onMounted, onUnmounted, ref, watch } from "vue";
import type { AnimatableProperty, Layer, PropertyValue } from "@/types/project";
import {
  createWaveformData,
  getWaveformData,
  renderTimelineWaveform,
  type WaveformData,
} from "@/services/timelineWaveform";
import { assertDefined } from "@/utils/typeGuards";
import { useAudioStore } from "@/stores/audioStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useCompositionStore } from "@/stores/compositionStore";

const props = defineProps([
  "layer",
  "index",
  "layoutMode",
  "isExpandedExternal",
  "allLayers",
  "frameCount",
  "pixelsPerFrame",
  "gridStyle",
]);
const emit = defineEmits(["toggleExpand", "select", "updateLayer"]);
const layerStore = useLayerStore();
const audioStore = useAudioStore();
const animationStore = useAnimationStore();
const projectStore = useProjectStore();
const selectionStore = useSelectionStore();
const compositionStore = useCompositionStore();

// Helper function to create AnimationStoreAccess
function getAnimationStoreAccess() {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    currentFrame: animationStore.currentFrame,
    fps: projectStore.getFps(),
    frameCount: projectStore.getFrameCount(),
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// Helper function to create CompositionStoreAccess
function getCompositionStoreAccess() {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    openCompositionIds: projectStore.openCompositionIds,
    compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    switchComposition: (id: string) => compositionStore.switchComposition(getCompositionStoreAccess(), id),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// Waveform state
const waveformCanvasRef = ref<HTMLCanvasElement | null>(null);
const waveformData = ref<WaveformData | null>(null);

// Check if layer is an audio layer type
const isAudioLayer = computed(
  () => props.layer.type === "audio" || props.layer.type === "video",
);

// System F/Omega: Computed property that throws explicit errors instead of returning null
const audioAssetIdRaw = computed(() => {
  if (props.layer.type === "audio") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const data = props.layer.data;
    const assetId = (data != null && typeof data === "object" && "assetId" in data && typeof data.assetId === "string") ? data.assetId : undefined;
    return assetId || props.layer.id;
  }
  if (props.layer.type === "video") {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const data = props.layer.data;
    const audioAssetId = (data != null && typeof data === "object" && "audioAssetId" in data && typeof data.audioAssetId === "string") ? data.audioAssetId : undefined;
    // System F/Omega: Throw explicit error if video layer has no audio asset ID
    if (!audioAssetId) {
      throw new Error(
        `[EnhancedLayerTrack] Cannot get audio asset ID: Video layer has no audio asset. ` +
        `Layer ID: ${props.layer.id}, name: ${props.layer.name}. ` +
        `Video layer must have an audioAssetId in its data. Wrap in try/catch if "no audio" is an expected state.`
      );
    }
    return audioAssetId;
  }
  
  // System F/Omega: Throw explicit error for non-audio/video layers
  throw new Error(
    `[EnhancedLayerTrack] Cannot get audio asset ID: Layer is not audio or video type. ` +
    `Layer type: "${props.layer.type}", layer ID: ${props.layer.id}, name: ${props.layer.name}. ` +
    `Only audio and video layers have audio asset IDs. Wrap in try/catch if "no audio asset" is an expected state.`
  );
});

// Wrapper computed property for template use - catches errors and returns null for conditional rendering
// System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
// Template uses v-if and null checks which require null for conditional rendering
const audioAssetId = computed<string | null>(() => {
  try {
    return audioAssetIdRaw.value;
  } catch {
    // System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
    // Template uses v-if and null checks which require null for conditional rendering
    // This is the ONLY place where null is returned - all other code throws explicit errors
    return null;
  }
});

const localExpanded = ref(false);
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
// Pattern match: isExpandedExternal ∈ boolean | undefined → boolean (fallback to localExpanded)
const isExpanded = computed(() => {
  return (typeof props.isExpandedExternal === "boolean") ? props.isExpandedExternal : localExpanded.value;
});
const isSelected = computed(() =>
  selectionStore.selectedLayerIds.includes(props.layer.id),
);

// Drag reorder state
const isDragTarget = ref(false);

function onDragStart(event: DragEvent) {
  if (!event.dataTransfer) return;
  event.dataTransfer.setData("application/layer-reorder", props.layer.id);
  event.dataTransfer.effectAllowed = "move";
}

function onDragEnd() {
  isDragTarget.value = false;
}

function onDragOver(event: DragEvent) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  const data = (dataTransfer != null && typeof dataTransfer === "object" && "types" in dataTransfer && dataTransfer.types != null && typeof dataTransfer.types.includes === "function") ? dataTransfer.types.includes("application/layer-reorder") : false;
  if (data) {
    isDragTarget.value = true;
  }
}

function onDragLeave() {
  isDragTarget.value = false;
}

function onDrop(event: DragEvent) {
  isDragTarget.value = false;

  // Check for Alt+drag asset replacement
  if (event.altKey) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
    const projectItemData = (dataTransfer != null && typeof dataTransfer === "object" && typeof dataTransfer.getData === "function") ? dataTransfer.getData(
      "application/project-item",
    ) : undefined;
    if (projectItemData) {
      try {
        const item = JSON.parse(projectItemData);
        if (item && (item.type === "asset" || item.type === "composition")) {
          // Replace layer source with new asset
          layerStore.replaceLayerSource(props.layer.id, item);
          console.log(
            `[Lattice] Replaced layer source: ${props.layer.name} → ${item.name}`,
          );
          return;
        }
      } catch (e) {
        console.error(
          "[Lattice] Failed to parse project item for replacement:",
          e,
        );
      }
    }
  }

  // Normal layer reorder handling
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  const draggedLayerId = (dataTransfer != null && typeof dataTransfer === "object" && typeof dataTransfer.getData === "function") ? dataTransfer.getData(
    "application/layer-reorder",
  ) : undefined;
  if (!draggedLayerId || draggedLayerId === props.layer.id) return;

  // Find the indices
  const layers = projectStore.getActiveCompLayers();
  const draggedIndex = layers.findIndex((l) => l.id === draggedLayerId);
  const targetIndex = layers.findIndex((l) => l.id === props.layer.id);

  if (
    draggedIndex !== -1 &&
    targetIndex !== -1 &&
    draggedIndex !== targetIndex
  ) {
    layerStore.moveLayer(draggedLayerId, targetIndex);
    console.log(
      `[Lattice] Moved layer from index ${draggedIndex} to ${targetIndex}`,
    );
  }
}

// Only video and audio layers have audio capability
const hasAudioCapability = computed(() =>
  ["video", "audio", "nestedComp"].includes(props.layer.type),
);
// Check if layer is a text layer (for Convert to Splines feature)
const isTextLayer = computed(() => props.layer.type === "text");
const expandedGroups = ref<string[]>([
  "Transform",
  "Text",
  "More Options",
  "Stroke",
  "Fill",
  "Trim Paths",
  "Path Options",
]);
const isRenaming = ref(false);
const renameVal = ref("");
const renameInput = ref<HTMLInputElement | null>(null);

// Context menu state
const contextMenuVisible = ref(false);
const contextMenuX = ref(0);
const contextMenuY = ref(0);

// Color picker state
const showColorPicker = ref(false);
const colorPickerX = ref(0);
const colorPickerY = ref(0);

// Layer label colors
const labelColors = [
  "#999999", // None (gray)
  "#e24b4b", // Red
  "#f5c343", // Yellow
  "#c8e04d", // Lime
  "#4be08e", // Sea Green
  "#4bcde0", // Aqua
  "#5b8ef0", // Blue
  "#9d70e8", // Purple
  "#e070d0", // Pink
  "#e0a070", // Peach
  "#e07070", // Light Red
  "#70e0a0", // Mint
  "#7090e0", // Sky Blue
  "#a070e0", // Violet
  "#e07090", // Rose
  "#90c8e0", // Pale Blue
];

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
const availableParents = computed(() => {
  const allLayers = props.allLayers as Layer[] | undefined;
  const filtered = (allLayers !== null && allLayers !== undefined && Array.isArray(allLayers)) ? allLayers.filter((l: Layer) => l.id !== props.layer.id) : undefined;
  return (filtered !== null && filtered !== undefined && Array.isArray(filtered)) ? filtered : [];
});

// Grouping Logic
const groupedProperties = computed(() => {
  const groups: Record<string, Array<{ path: string; name: string; property: AnimatableProperty<PropertyValue> }>> = {};
  const t = props.layer.transform;
  const transformProps: Array<{ path: string; name: string; property: AnimatableProperty<PropertyValue> }> = [];

  // Helper to safely add props
  const add = (path: string, name: string, prop: AnimatableProperty<PropertyValue> | undefined) => {
    if (prop) transformProps.push({ path, name, property: prop });
  };

  add("transform.anchorPoint", "Origin", t.anchorPoint);
  add("transform.position", "Position", t.position);

  // Z Position: Use 'transform.position' path - PropertyTrack handles Z extraction based on name
  if (props.layer.threeD && t.position) {
    transformProps.push({
      path: "transform.position",
      name: "Z Position",
      property: t.position, // Pass full position property, PropertyTrack handles .z
    });
  }

  add("transform.scale", "Scale", t.scale);

  if (props.layer.threeD) {
    if (t.orientation)
      transformProps.push({
        path: "transform.orientation",
        name: "Orientation",
        property: t.orientation,
      });
    if (t.rotationX)
      transformProps.push({
        path: "transform.rotationX",
        name: "X Rotation",
        property: t.rotationX,
      });
    if (t.rotationY)
      transformProps.push({
        path: "transform.rotationY",
        name: "Y Rotation",
        property: t.rotationY,
      });
    if (t.rotationZ)
      transformProps.push({
        path: "transform.rotationZ",
        name: "Z Rotation",
        property: t.rotationZ,
      });
  } else {
    if (t.rotation)
      transformProps.push({
        path: "transform.rotation",
        name: "Rotation",
        property: t.rotation,
      });
  }
  if (props.layer.opacity)
    transformProps.push({
      path: "opacity",
      name: "Opacity",
      property: props.layer.opacity,
    });

  groups.Transform = transformProps;

  // Geometry Options (for 3D layers)
  if (props.layer.threeD) {
    groups["Geometry Options"] = [
      {
        path: "geometry.renderer",
        name: "Renderer",
        property: { value: "Classic 3D", type: "dropdown" },
      },
    ];
  }

  // Material Options (for 3D layers)
  if (props.layer.threeD) {
    const mat = props.layer.materialOptions || {
      castsShadows: "off",
      lightTransmission: 0,
      acceptsShadows: true,
      acceptsLights: true,
      ambient: 100,
      diffuse: 50,
      specularIntensity: 50,
      specularShininess: 5,
      metal: 100,
    };
    groups["Material Options"] = [
      {
        path: "materialOptions.castsShadows",
        name: "Casts Shadows",
        property: { value: mat.castsShadows, type: "dropdown" },
      },
      {
        path: "materialOptions.lightTransmission",
        name: "Light Transmission",
        property: { value: mat.lightTransmission, type: "percent" },
      },
      {
        path: "materialOptions.acceptsShadows",
        name: "Accepts Shadows",
        property: { value: mat.acceptsShadows, type: "boolean" },
      },
      {
        path: "materialOptions.acceptsLights",
        name: "Accepts Lights",
        property: { value: mat.acceptsLights, type: "boolean" },
      },
      {
        path: "materialOptions.ambient",
        name: "Ambient",
        property: { value: mat.ambient, type: "percent" },
      },
      {
        path: "materialOptions.diffuse",
        name: "Diffuse",
        property: { value: mat.diffuse, type: "percent" },
      },
      {
        path: "materialOptions.specularIntensity",
        name: "Specular Intensity",
        property: { value: mat.specularIntensity, type: "percent" },
      },
      {
        path: "materialOptions.specularShininess",
        name: "Specular Shininess",
        property: { value: mat.specularShininess, type: "percent" },
      },
      {
        path: "materialOptions.metal",
        name: "Metal",
        property: { value: mat.metal, type: "percent" },
      },
    ];
  }

  // Path Options (for spline layers) - Closed is NOT animatable
  if (props.layer.type === "spline" && props.layer.data) {
    const splineData = props.layer.data as import("@/types/project").SplineData;
    groups["Path Options"] = [
      {
        path: "data.closed",
        name: "Closed",
        property: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          // Pattern match: splineData.closed ∈ boolean | undefined → boolean (default false)
          value: (typeof splineData.closed === "boolean") ? splineData.closed : false,
          type: "boolean",
          animatable: false,
        },
      },
    ];

    // More Options: Line Cap, Line Join, Dashes (non-animatable)
    groups["More Options"] = [
      {
        path: "data.lineCap",
        name: "Line Cap",
        property: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          // Pattern match: splineData.lineCap ∈ string | undefined → string (default "round")
          value: (typeof splineData.lineCap === "string" && splineData.lineCap.length > 0) ? splineData.lineCap : "round",
          type: "dropdown",
          options: ["butt", "round", "square"],
          animatable: false,
        },
      },
      {
        path: "data.lineJoin",
        name: "Line Join",
        property: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          // Pattern match: splineData.lineJoin ∈ string | undefined → string (default "round")
          value: (typeof splineData.lineJoin === "string" && splineData.lineJoin.length > 0) ? splineData.lineJoin : "round",
          type: "dropdown",
          options: ["miter", "round", "bevel"],
          animatable: false,
        },
      },
      {
        path: "data.dashArray",
        name: "Dashes",
        property: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          // Pattern match: splineData.dashArray ∈ string | undefined → string (default "")
          value: (typeof splineData.dashArray === "string") ? splineData.dashArray : "",
          type: "string",
          placeholder: "10, 5",
          animatable: false,
        },
      },
      {
        path: "data.dashOffset",
        name: "Dash Offset",
        property: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          // Pattern match: splineData.dashOffset ∈ number | undefined → number (default 0)
          value: (typeof splineData.dashOffset === "number" && Number.isFinite(splineData.dashOffset)) ? splineData.dashOffset : 0,
          type: "number",
          animatable: false,
        },
      },
    ];
  }

  // Custom Properties (Text, etc.)
  if (props.layer.properties) {
    props.layer.properties.forEach((p: AnimatableProperty<PropertyValue>) => {
      const g = p.group || "Properties";
      if (!groups[g]) groups[g] = [];
      groups[g].push({ path: p.name, name: p.name, property: p });
    });
  }
  return groups;
});

const barStyle = computed(() => {
  const frameCount = props.frameCount || 81;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.inPoint ∈ number | undefined → number (default 0)
  const inPoint = (typeof props.layer.inPoint === "number" && Number.isFinite(props.layer.inPoint)) ? props.layer.inPoint : 0;
  // Pattern match: layer.outPoint ∈ number | undefined → number (default frameCount - 1)
  const outPoint = (typeof props.layer.outPoint === "number" && Number.isFinite(props.layer.outPoint)) ? props.layer.outPoint : frameCount - 1;

  // Use CSS percentages - positions relative to parent container width
  // This ensures layer bar fills viewport when layer spans full composition
  const leftPct = Math.max(0, (inPoint / frameCount) * 100);
  const widthPct = Math.max(1, ((outPoint - inPoint + 1) / frameCount) * 100); // Minimum 1% width

  return {
    left: `${leftPct}%`,
    width: `${widthPct}%`,
  };
});

function selectLayer() {
  emit("select", props.layer.id);
}
function toggleExpand() {
  emit("toggleExpand", props.layer.id, !isExpanded.value);
}
function toggleGroup(g: string) {
  if (expandedGroups.value.includes(g))
    expandedGroups.value = expandedGroups.value.filter((x) => x !== g);
  else expandedGroups.value.push(g);
}
function getLayerIcon(t: string) {
  return (
    {
      text: "T",
      solid: "■",
      camera: "◎",
      nestedComp: "▣",
      image: "▧",
      video: "▶",
    }[t] || "•"
  );
}

// Double-click: enter nested comp or start rename
function handleDoubleClick() {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const data = props.layer.data;
  const compositionId = (data != null && typeof data === "object" && "compositionId" in data && typeof data.compositionId === "string") ? data.compositionId : undefined;
  if (props.layer.type === "nestedComp" && compositionId) {
    // Enter the nested composition
    compositionStore.enterNestedComp(getCompositionStoreAccess(), compositionId);
  } else {
    // Start rename for other layer types
    startRename();
  }
}

function startRename() {
  isRenaming.value = true;
  renameVal.value = props.layer.name;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  nextTick(() => {
    const renameInputVal = renameInput.value;
    if (renameInputVal != null && typeof renameInputVal === "object" && typeof renameInputVal.focus === "function") {
      renameInputVal.focus();
    }
  });
}
function saveRename() {
  emit("updateLayer", props.layer.id, { name: renameVal.value });
  isRenaming.value = false;
}
function setParent(e: Event) {
  emit("updateLayer", props.layer.id, {
    parentId: (e.target as HTMLSelectElement).value || null,
  });
}
function setBlendMode(e: Event) {
  emit("updateLayer", props.layer.id, {
    blendMode: (e.target as HTMLSelectElement).value,
  });
}
// Layer bar drag/resize state
const isDragging = ref(false);
const isResizingLeft = ref(false);
const isResizingRight = ref(false);
const dragStartX = ref(0);
const dragStartInPoint = ref(0);
const dragStartOutPoint = ref(0);

// Timeline snap functionality (Shift key enables snapping)
const SNAP_TOLERANCE = 5; // frames

function getSnapTargets(): number[] {
  const targets: number[] = [];

  // Add playhead position
  targets.push(animationStore.getCurrentFrame(getAnimationStoreAccess()));

  // Add all other layer in/out points
  const layers = props.allLayers || projectStore.getActiveCompLayers();
  for (const layer of layers) {
    if (layer.id === props.layer.id) continue; // Skip self
    if (layer.inPoint !== undefined) targets.push(layer.inPoint);
    if (layer.outPoint !== undefined) targets.push(layer.outPoint);
  }

  // Add composition start/end
  targets.push(0);
  targets.push(props.frameCount - 1);

  // Add markers if available
  const composition = projectStore.getActiveComp();
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const markers = (composition != null && typeof composition === "object" && "markers" in composition && composition.markers != null && Array.isArray(composition.markers)) ? composition.markers : undefined;
  if (markers) {
    for (const marker of markers) {
      targets.push(marker.frame);
    }
  }

  return [...new Set(targets)]; // Remove duplicates
}

function snapToNearest(value: number, targets: number[]): number {
  let nearest = value;
  let minDist = SNAP_TOLERANCE + 1;

  for (const target of targets) {
    const dist = Math.abs(value - target);
    if (dist < minDist) {
      minDist = dist;
      nearest = target;
    }
  }

  return minDist <= SNAP_TOLERANCE ? nearest : value;
}

function startDrag(e: MouseEvent) {
  isDragging.value = true;
  dragStartX.value = e.clientX;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.inPoint ∈ number | undefined → number (default 0)
  dragStartInPoint.value = (typeof props.layer.inPoint === "number" && Number.isFinite(props.layer.inPoint)) ? props.layer.inPoint : 0;
  // Pattern match: layer.outPoint ∈ number | undefined → number (default frameCount - 1)
  dragStartOutPoint.value = (typeof props.layer.outPoint === "number" && Number.isFinite(props.layer.outPoint)) ? props.layer.outPoint : props.frameCount - 1;
  document.addEventListener("mousemove", onDrag);
  document.addEventListener("mouseup", stopDrag);
}

function startResizeLeft(e: MouseEvent) {
  isResizingLeft.value = true;
  dragStartX.value = e.clientX;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.inPoint ∈ number | undefined → number (default 0)
  dragStartInPoint.value = (typeof props.layer.inPoint === "number" && Number.isFinite(props.layer.inPoint)) ? props.layer.inPoint : 0;
  document.addEventListener("mousemove", onResizeLeft);
  document.addEventListener("mouseup", stopDrag);
}

function startResizeRight(e: MouseEvent) {
  isResizingRight.value = true;
  dragStartX.value = e.clientX;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.outPoint ∈ number | undefined → number (default frameCount - 1)
  dragStartOutPoint.value = (typeof props.layer.outPoint === "number" && Number.isFinite(props.layer.outPoint)) ? props.layer.outPoint : props.frameCount - 1;
  document.addEventListener("mousemove", onResizeRight);
  document.addEventListener("mouseup", stopDrag);
}

function onDrag(e: MouseEvent) {
  const dx = e.clientX - dragStartX.value;
  const framesDelta = Math.round(dx / props.pixelsPerFrame);
  const duration = dragStartOutPoint.value - dragStartInPoint.value;

  let newInPoint = dragStartInPoint.value + framesDelta;
  let newOutPoint = newInPoint + duration;

  // Snap when Shift is held
  if (e.shiftKey) {
    const targets = getSnapTargets();
    const snappedIn = snapToNearest(newInPoint, targets);
    const snappedOut = snapToNearest(newOutPoint, targets);

    // Prefer snapping to whichever edge is closer to a target
    const inDist = Math.abs(snappedIn - newInPoint);
    const outDist = Math.abs(snappedOut - newOutPoint);

    if (inDist <= outDist && inDist <= SNAP_TOLERANCE) {
      newInPoint = snappedIn;
      newOutPoint = snappedIn + duration;
    } else if (outDist <= SNAP_TOLERANCE) {
      newOutPoint = snappedOut;
      newInPoint = snappedOut - duration;
    }
  }

  // Clamp to valid range
  if (newInPoint < 0) {
    newInPoint = 0;
    newOutPoint = duration;
  }
  if (newOutPoint >= props.frameCount) {
    newOutPoint = props.frameCount - 1;
    newInPoint = newOutPoint - duration;
  }

  emit("updateLayer", props.layer.id, {
    inPoint: newInPoint,
    outPoint: newOutPoint,
  });
}

function onResizeLeft(e: MouseEvent) {
  const dx = e.clientX - dragStartX.value;
  const framesDelta = Math.round(dx / props.pixelsPerFrame);
  let newInPoint = dragStartInPoint.value + framesDelta;

  // Snap when Shift is held
  if (e.shiftKey) {
    const targets = getSnapTargets();
    newInPoint = snapToNearest(newInPoint, targets);
  }

  // Clamp: can't go below 0 or past outPoint
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.outPoint ∈ number | undefined → number (default frameCount - 1)
  const outPoint = (typeof props.layer.outPoint === "number" && Number.isFinite(props.layer.outPoint)) ? props.layer.outPoint : props.frameCount - 1;
  newInPoint = Math.max(0, Math.min(newInPoint, outPoint - 1));

  emit("updateLayer", props.layer.id, { inPoint: newInPoint });
}

function onResizeRight(e: MouseEvent) {
  const dx = e.clientX - dragStartX.value;
  const framesDelta = Math.round(dx / props.pixelsPerFrame);
  let newOutPoint = dragStartOutPoint.value + framesDelta;

  // Snap when Shift is held
  if (e.shiftKey) {
    const targets = getSnapTargets();
    newOutPoint = snapToNearest(newOutPoint, targets);
  }

  // Clamp: can't go past frameCount or before inPoint
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.inPoint ∈ number | undefined → number (default 0)
  const inPoint = (typeof props.layer.inPoint === "number" && Number.isFinite(props.layer.inPoint)) ? props.layer.inPoint : 0;
  newOutPoint = Math.max(
    inPoint + 1,
    Math.min(newOutPoint, props.frameCount - 1),
  );

  emit("updateLayer", props.layer.id, { outPoint: newOutPoint });
}

function stopDrag() {
  isDragging.value = false;
  isResizingLeft.value = false;
  isResizingRight.value = false;
  document.removeEventListener("mousemove", onDrag);
  document.removeEventListener("mousemove", onResizeLeft);
  document.removeEventListener("mousemove", onResizeRight);
  document.removeEventListener("mouseup", stopDrag);
}
function toggleVis() {
  emit("updateLayer", props.layer.id, { visible: !props.layer.visible });
}
function toggleLock() {
  emit("updateLayer", props.layer.id, { locked: !props.layer.locked });
}
function toggleAudio() {
  emit("updateLayer", props.layer.id, {
    audioEnabled: props.layer.audioEnabled === false,
  });
}
function toggleIsolate() {
  emit("updateLayer", props.layer.id, { isolate: !props.layer.isolate });
}
function toggleMinimized() {
  emit("updateLayer", props.layer.id, { minimized: !props.layer.minimized });
}
function toggleFlattenTransform() {
  emit("updateLayer", props.layer.id, {
    flattenTransform: !props.layer.flattenTransform,
  });
}
function toggleQuality() {
  emit("updateLayer", props.layer.id, {
    quality: props.layer.quality === "best" ? "draft" : "best",
  });
}
function toggleEffects() {
  emit("updateLayer", props.layer.id, {
    effectsEnabled: props.layer.effectsEnabled === false,
  });
}
function toggleFrameBlend() {
  emit("updateLayer", props.layer.id, {
    frameBlending: !props.layer.frameBlending,
  });
}
function toggleMotionBlur() {
  emit("updateLayer", props.layer.id, { motionBlur: !props.layer.motionBlur });
}
function toggleEffectLayer() {
  const currentState = props.layer.effectLayer || props.layer.adjustmentLayer;
  emit("updateLayer", props.layer.id, {
    effectLayer: !currentState,
    adjustmentLayer: !currentState,
  });
}
function toggleColorPicker(e: MouseEvent) {
  const rect = (e.target as HTMLElement).getBoundingClientRect();
  colorPickerX.value = rect.left;
  colorPickerY.value = rect.bottom + 4;
  showColorPicker.value = !showColorPicker.value;
}

function setLabelColor(color: string) {
  emit("updateLayer", props.layer.id, { labelColor: color });
  showColorPicker.value = false;
}

function closeColorPicker() {
  showColorPicker.value = false;
}

// Reset transform to default values
function resetTransform() {
  const comp = projectStore.getActiveComp();
  if (!comp) return;

  // Default values
  const defaultTransform = {
    anchorPoint: { x: comp.settings.width / 2, y: comp.settings.height / 2 },
    position: { x: comp.settings.width / 2, y: comp.settings.height / 2, z: 0 },
    scale: { x: 100, y: 100, z: 100 },
    rotation: 0,
    rotationX: 0,
    rotationY: 0,
    rotationZ: 0,
    orientation: { x: 0, y: 0, z: 0 },
    opacity: 100,
  };

  // Reset each transform property value (keep keyframes but update current value)
  const t = props.layer.transform;
  if (t.anchorPoint) t.anchorPoint.value = { ...defaultTransform.anchorPoint };
  if (t.position)
    t.position.value = props.layer.threeD
      ? { ...defaultTransform.position }
      : { x: defaultTransform.position.x, y: defaultTransform.position.y };
  if (t.scale)
    t.scale.value = {
      x: defaultTransform.scale.x,
      y: defaultTransform.scale.y,
    };
  if (t.rotation) t.rotation.value = defaultTransform.rotation;
  if (t.rotationX) t.rotationX.value = defaultTransform.rotationX;
  if (t.rotationY) t.rotationY.value = defaultTransform.rotationY;
  if (t.rotationZ) t.rotationZ.value = defaultTransform.rotationZ;
  if (t.orientation) t.orientation.value = { ...defaultTransform.orientation };
  if (props.layer.opacity) props.layer.opacity.value = defaultTransform.opacity;

  projectStore.project.meta.modified = new Date().toISOString();
  console.log(
    "[EnhancedLayerTrack] Reset transform for layer:",
    props.layer.name,
  );
}

// Context menu functions
function showContextMenu(e: MouseEvent) {
  contextMenuX.value = e.clientX;
  contextMenuY.value = e.clientY;
  contextMenuVisible.value = true;
  // Select the layer when showing context menu
  if (!isSelected.value) {
    emit("select", props.layer.id);
  }
}

function hideContextMenu() {
  contextMenuVisible.value = false;
}

function duplicateLayer() {
  layerStore.duplicateLayer(props.layer.id);
  hideContextMenu();
}

function renameFromMenu() {
  hideContextMenu();
  nextTick(() => {
    isRenaming.value = true;
    renameVal.value = props.layer.name;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    nextTick(() => {
      const renameInputVal = renameInput.value;
      if (renameInputVal != null && typeof renameInputVal === "object" && typeof renameInputVal.focus === "function") {
        renameInputVal.focus();
      }
    });
  });
}

function toggleLayerVisibility() {
  emit("updateLayer", props.layer.id, { visible: !props.layer.visible });
  hideContextMenu();
}

function toggleLayerLock() {
  emit("updateLayer", props.layer.id, { locked: !props.layer.locked });
  hideContextMenu();
}

function toggleLayer3D() {
  layerStore.toggleLayer3D(props.layer.id);
  hideContextMenu();
}

function nestLayer() {
  layerStore.selectLayer(props.layer.id);
  compositionStore.nestSelectedLayers(`${props.layer.name} Nested`);
  hideContextMenu();
}

async function convertToSplines() {
  hideContextMenu();
  if (props.layer.type !== "text") return;

  try {
    const result = await layerStore.convertTextLayerToSplines(props.layer.id, {
      perCharacter: true,
      groupCharacters: true,
      keepOriginal: true,
    });

    if (result) {
      console.log("[EnhancedLayerTrack] Text converted to splines:", result);
    }
  } catch (error) {
    console.error(
      "[EnhancedLayerTrack] Failed to convert text to splines:",
      error,
    );
  }
}

function deleteLayer() {
  layerStore.deleteLayer(props.layer.id);
  hideContextMenu();
}

// Close context menu and color picker on outside click
function handleOutsideClick(e: MouseEvent) {
  if (contextMenuVisible.value) {
    hideContextMenu();
  }
  if (showColorPicker.value) {
    // Check if click was inside color picker
    const target = e.target as HTMLElement;
    const colorPicker = document.querySelector(".layer-color-picker");
    const labelBox = target.closest(".label-box");
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const containsTarget = (colorPicker != null && typeof colorPicker === "object" && typeof colorPicker.contains === "function") ? colorPicker.contains(target) : false;
    if (containsTarget || labelBox) {
      return; // Don't close if clicked inside picker or on label box
    }
    closeColorPicker();
  }
}

// ============================================================
// WAVEFORM RENDERING
// ============================================================

/**
 * Initialize waveform data from audio buffer
 */
async function initializeWaveform() {
  if (!isAudioLayer.value || !audioAssetId.value) return;

  // Check if waveform already cached
  const cached = getWaveformData(audioAssetId.value);
  if (cached) {
    waveformData.value = cached;
    renderWaveformToCanvas();
    return;
  }

  // Get audio buffer from audio store
  const audioBuffer = audioStore.getAudioBuffer(audioAssetId.value);
  if (!audioBuffer) return;

  // Get beat markers if available
  const beats = audioStore.getBeats(audioAssetId.value);
  const bpm = audioStore.getBPM(audioAssetId.value);

  // Create waveform data
  waveformData.value = await createWaveformData(
    audioAssetId.value,
    audioBuffer,
    beats,
    bpm,
  );

  renderWaveformToCanvas();
}

/**
 * Render waveform to the canvas element
 */
function renderWaveformToCanvas() {
  if (!waveformCanvasRef.value || !waveformData.value) return;

  const canvas = waveformCanvasRef.value;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const parentElement = (canvas != null && typeof canvas === "object" && "parentElement" in canvas && canvas.parentElement != null && typeof canvas.parentElement === "object") ? canvas.parentElement : undefined;
  const parentWidth = (parentElement != null && typeof parentElement === "object" && typeof parentElement.clientWidth === "number") ? parentElement.clientWidth : 200;
  const parentHeight = (parentElement != null && typeof parentElement === "object" && typeof parentElement.clientHeight === "number") ? parentElement.clientHeight : 24;

  const frameCount = props.frameCount || 81;
  const projectStore = useProjectStore();
  const fps = projectStore.getFps();
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: layer.inPoint ∈ number | undefined → number (fallback chain: startFrame → 0)
  const inPointValue = (typeof props.layer.inPoint === "number" && Number.isFinite(props.layer.inPoint)) ? props.layer.inPoint : ((typeof props.layer.startFrame === "number" && Number.isFinite(props.layer.startFrame)) ? props.layer.startFrame : 0);
  const inPoint = inPointValue;
  // Pattern match: layer.outPoint ∈ number | undefined → number (fallback chain: endFrame → frameCount - 1)
  const outPointValue = (typeof props.layer.outPoint === "number" && Number.isFinite(props.layer.outPoint)) ? props.layer.outPoint : ((typeof props.layer.endFrame === "number" && Number.isFinite(props.layer.endFrame)) ? props.layer.endFrame : frameCount - 1);
  const outPoint = outPointValue;

  // visibleStart/visibleEnd match layer timing (canvas shows layer bar, not full timeline)
  // Type proof: audioAssetId is guaranteed non-null by isAudioLayer check and initializeWaveform guard
  assertDefined(audioAssetId.value, "audioAssetId must exist when rendering waveform for audio layer");
  renderTimelineWaveform(canvas, waveformData.value, {
    layerId: props.layer.id,
    audioId: audioAssetId.value,
    layerColor: props.layer.labelColor || "#D4A574",
    startFrame: inPoint,
    endFrame: outPoint,
    visibleStart: inPoint,
    visibleEnd: outPoint,
    fps,
    trackWidth: parentWidth,
    trackHeight: parentHeight,
  });
}

// Watch for changes that require waveform re-render
watch(
  () => [
    props.frameCount,
    props.pixelsPerFrame,
    props.layer.inPoint,
    props.layer.outPoint,
  ],
  () => {
    if (waveformData.value) {
      nextTick(() => renderWaveformToCanvas());
    }
  },
);

// Watch for audio buffer availability
watch(
  () => audioAssetId.value && audioStore.hasAudioBuffer(audioAssetId.value),
  (hasBuffer) => {
    if (hasBuffer && !waveformData.value) {
      initializeWaveform();
    }
  },
  { immediate: true },
);

onMounted(() => {
  document.addEventListener("click", handleOutsideClick);
  // Initialize waveform if audio layer
  if (isAudioLayer.value && audioAssetId.value) {
    initializeWaveform();
  }
});

onUnmounted(() => {
  document.removeEventListener("click", handleOutsideClick);
});
</script>

<style scoped>
.track-wrapper { display: flex; flex-direction: column; width: 100%; }

/* Sidebar row - flex layout */
.sidebar-row {
  display: flex;
  align-items: stretch;
  height: 32px;
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
  background: var(--lattice-surface-1, #0f0f0f);
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: 13px;
  user-select: none;
  cursor: pointer;
}
.sidebar-row.selected { background: var(--lattice-surface-3, #1e1e1e); color: var(--lattice-text-primary, #fff); border-left: 2px solid var(--lattice-accent, #8B5CF6); }
.sidebar-row.drag-over {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
  border-top: 2px solid var(--lattice-accent, #8B5CF6);
  margin-top: -2px;
}
.sidebar-row:hover:not(.drag-over) { background: var(--lattice-surface-2, #161616); }

/* AV Features section (visibility, audio, isolate, lock) */
.av-features {
  display: flex;
  align-items: center;
  border-right: 1px solid var(--lattice-border-subtle, #1a1a1a);
  flex-shrink: 0;
}

/* Layer info section (color, number, arrow, name) */
.layer-info {
  display: flex;
  align-items: center;
  flex: 1;
  min-width: 0;
  gap: 4px;
  padding: 0 4px;
}

/* Switches section */
.layer-switches {
  display: flex;
  align-items: center;
  border-left: 1px solid var(--lattice-border-subtle, #1a1a1a);
  flex-shrink: 0;
}

/* Icon columns */
.icon-col {
  display: flex;
  justify-content: center;
  align-items: center;
  width: 26px;
  height: 100%;
  cursor: pointer;
  font-size: 14px;
}
.icon-col span { color: var(--lattice-text-muted, #6B7280); transition: color 0.15s; }
.icon-col:hover span { color: var(--lattice-text-secondary, #9CA3AF); }
.icon-col span.active { color: var(--lattice-accent, #8B5CF6); }
.icon-col span.inactive { opacity: 0.3; }
.icon-col.placeholder { cursor: default; }

/* Arrow column */
.arrow-col {
  display: flex;
  justify-content: center;
  align-items: center;
  width: 16px;
  cursor: pointer;
}
.arrow { color: var(--lattice-text-muted, #6B7280); font-size: 11px; }
.arrow-col:hover .arrow { color: var(--lattice-text-secondary, #9CA3AF); }

/* Label color box */
.label-box {
  width: 12px;
  height: 12px;
  border: 1px solid rgba(0,0,0,0.4);
  border-radius: 2px;
  cursor: pointer;
  flex-shrink: 0;
}
.label-box:hover { border-color: #fff; }

/* Layer number */
.layer-id {
  font-size: 12px;
  color: var(--lattice-text-muted, #6B7280);
  min-width: 16px;
  text-align: center;
  flex-shrink: 0;
}

/* Layer name */
.layer-name-col {
  display: flex;
  align-items: center;
  flex: 1;
  min-width: 0;
  overflow: hidden;
}
.type-icon { margin-right: 4px; font-size: 12px; opacity: 0.7; }
.name-text { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 12px; }
.rename-input { background: var(--lattice-surface-0, #080808); border: 1px solid var(--lattice-accent, #8B5CF6); color: var(--lattice-text-primary, #fff); padding: 2px 4px; font-size: 12px; width: 100%; }

/* Parent column */
.col-parent {
  display: flex;
  align-items: center;
  padding: 0 4px;
  border-left: 1px solid var(--lattice-border-subtle, #1a1a1a);
  min-width: 80px;
}
.mini-select {
  width: 100%;
  background: transparent;
  border: none;
  color: var(--lattice-text-muted, #6B7280);
  font-size: 12px;
  cursor: pointer;
}
.mini-select:hover { color: var(--lattice-text-secondary, #9CA3AF); }

/* Children/properties container */
.children-container { background: var(--lattice-surface-0, #080808); }
.group-header { background: var(--lattice-surface-2, #161616); font-weight: 600; color: var(--lattice-text-muted, #6B7280); cursor: pointer; }
.group-label {
  grid-column: 7 / -1;
  padding-left: 4px;
  font-size: 12px;
  display: flex;
  align-items: center;
  gap: 12px;
}
.reset-link {
  font-size: 12px;
  color: var(--lattice-accent, #8B5CF6);
  cursor: pointer;
  font-weight: normal;
}
.reset-link:hover {
  color: var(--lattice-accent-hover, #9D7AFA);
  text-decoration: underline;
}

/* Track mode */
.track-bg { height: 28px; background: var(--lattice-surface-0, #080808); border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); position: relative; width: 100%; }
.duration-bar {
  position: absolute;
  height: 22px;
  top: 3px;
  border: 1px solid rgba(0,0,0,0.6);
  border-radius: 6px;
  background: var(--lattice-timeline-video, #FFD700);
  cursor: move;
  display: flex;
  align-items: center;
}
.duration-bar:hover { box-shadow: 0 0 6px rgba(255,255,255,0.3); }
.bar-handle {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 8px;
  background: rgba(255,255,255,0.15);
  cursor: ew-resize;
  z-index: 2;
  transition: background 0.15s;
}
.bar-handle:hover { background: rgba(255,255,255,0.4); }
.bar-handle-left {
  left: 0;
  border-radius: 6px 0 0 6px;
  border-right: 1px solid rgba(0,0,0,0.3);
}
.bar-handle-right {
  right: 0;
  border-radius: 0 6px 6px 0;
  border-left: 1px solid rgba(0,0,0,0.3);
}
.bar-fill {
  flex: 1;
  height: 100%;
  border-radius: 5px;
  margin: 0 8px;
  position: relative;
  overflow: hidden;
}

.waveform-canvas {
  position: absolute;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  pointer-events: none;
  opacity: 0.8;
}

/* Context Menu - must NOT be scoped to work with Teleport */
</style>

<style>
.layer-context-menu {
  position: fixed;
  background: var(--lattice-surface-2, #161616);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  border-radius: 6px;
  box-shadow: 0 4px 16px rgba(0, 0, 0, 0.5);
  z-index: 9999;
  min-width: 180px;
  padding: 4px 0;
}

.layer-context-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  border: none;
  background: transparent;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 12px;
  text-align: left;
  cursor: pointer;
}

.layer-context-menu button:hover {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
}

.layer-context-menu button.danger {
  color: var(--lattice-error, #F43F5E);
}

.layer-context-menu button.danger:hover {
  background: var(--lattice-error-bg, rgba(244, 63, 94, 0.15));
  color: var(--lattice-error, #F43F5E);
}

.layer-context-menu hr {
  border: none;
  border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);
  margin: 4px 0;
}

/* Layer Color Picker */
.layer-color-picker {
  position: fixed;
  background: var(--lattice-surface-2, #161616);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  border-radius: 6px;
  box-shadow: 0 4px 16px rgba(0, 0, 0, 0.5);
  z-index: 9999;
  padding: 8px;
}

.layer-color-picker .color-grid {
  display: grid;
  grid-template-columns: repeat(8, 1fr);
  gap: 4px;
}

.layer-color-picker .color-swatch {
  width: 20px;
  height: 20px;
  border: 1px solid rgba(0, 0, 0, 0.3);
  border-radius: 2px;
  cursor: pointer;
  padding: 0;
}

.layer-color-picker .color-swatch:hover {
  transform: scale(1.15);
  border-color: #fff;
}

.layer-color-picker .color-swatch.active {
  border: 2px solid #fff;
  box-shadow: 0 0 4px rgba(255, 255, 255, 0.5);
}
</style>
