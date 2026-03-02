<template>
  <div class="path-properties">
    <!-- Guide Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('guide')">
        <span class="expand-icon">{{ expandedSections.includes('guide') ? '▼' : '►' }}</span>
        <span class="section-title">Guide Line</span>
        <input
          type="checkbox"
          :checked="pathData.showGuide"
          @click.stop
          @change="toggleGuide"
          class="section-toggle"
          title="Show/hide guide line in editor"
        />
      </div>

      <div v-if="expandedSections.includes('guide') && pathData.showGuide" class="section-content">
        <div class="property-row">
          <label>Color</label>
          <div class="color-input-wrapper">
            <input
              type="color"
              :value="pathData.guideColor || '#00FFFF'"
              @input="e => update('guideColor', (e.target as HTMLInputElement).value)"
            />
            <span class="color-hex">{{ pathData.guideColor || '#00FFFF' }}</span>
          </div>
        </div>

        <div class="property-row">
          <label>Dash</label>
          <ScrubableNumber
            :modelValue="dashValue"
            @update:modelValue="(v: number) => updateDash(v)"
            :min="1"
            :max="50"
            unit="px"
          />
        </div>

        <div class="property-row">
          <label>Gap</label>
          <ScrubableNumber
            :modelValue="gapValue"
            @update:modelValue="(v: number) => updateGap(v)"
            :min="1"
            :max="50"
            unit="px"
          />
        </div>

        <div class="property-row preset-row">
          <label>Presets</label>
          <div class="preset-buttons">
            <button
              v-for="preset in guidePresets"
              :key="preset.name"
              :class="{ active: isPresetActive(preset) }"
              @click="applyPreset(preset)"
              :title="preset.name"
            >
              {{ preset.icon }}
            </button>
          </div>
        </div>
      </div>
    </div>

    <!-- Path Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('path')">
        <span class="expand-icon">{{ expandedSections.includes('path') ? '▼' : '►' }}</span>
        <span class="section-title">Path</span>
      </div>

      <div v-if="expandedSections.includes('path')" class="section-content">
        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="pathData.closed"
              @change="update('closed', ($event.target as HTMLInputElement).checked)"
            />
            Closed Path
          </label>
        </div>

        <div class="property-row info-row">
          <span class="info-label">Points:</span>
          <span class="info-value">{{ getControlPointCount() }}</span>
        </div>

        <div class="property-row info-row">
          <span class="info-label">Animated:</span>
          <span class="info-value">{{ pathData.animated ? 'Yes' : 'No' }}</span>
        </div>
      </div>
    </div>

    <!-- Attached Elements Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('attached')">
        <span class="expand-icon">{{ expandedSections.includes('attached') ? '▼' : '►' }}</span>
        <span class="section-title">Attached Elements</span>
        <span class="attached-count" v-if="attachedLayers.length > 0">{{ attachedLayers.length }}</span>
      </div>

      <div v-if="expandedSections.includes('attached')" class="section-content">
        <div v-if="attachedLayers.length === 0" class="no-attached">
          No layers are using this path.
        </div>
        <div v-else class="attached-list">
          <div
            v-for="attached in attachedLayers"
            :key="attached.id"
            class="attached-item"
            @click="selectLayer(attached.id)"
          >
            <span class="attached-icon">{{ getLayerIcon(attached.type) }}</span>
            <span class="attached-name">{{ attached.name }}</span>
            <span class="attached-usage">{{ attached.usage }}</span>
          </div>
        </div>
      </div>
    </div>

    <!-- Usage Hints -->
    <div class="usage-hints">
      <p class="hint-title">Path Layer</p>
      <p class="hint-text">
        Motion paths are invisible guides used for:
      </p>
      <ul class="hint-list">
        <li>Text on path</li>
        <li>Camera trajectories</li>
        <li>Particle emitter paths</li>
      </ul>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { safeNonNegativeDefault } from "@/utils/typeGuards";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "@/stores/projectStore";
import type { Layer, PathLayerData } from "@/types/project";
import type { JSONValue } from "@/types/dataAsset";
import type { PropertyValue } from "@/types/animation";

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(["update"]);
const layerStore = useLayerStore();
const projectStore = useProjectStore();

const expandedSections = ref<string[]>(["guide", "path"]);

// Guide presets
const guidePresets = [
  { name: "Solid", color: "#00FFFF", dash: 0, gap: 0, icon: "―" },
  { name: "Dotted", color: "#00FFFF", dash: 2, gap: 4, icon: "··" },
  { name: "Dashed", color: "#00FFFF", dash: 10, gap: 5, icon: "- -" },
  { name: "Long Dash", color: "#00FFFF", dash: 20, gap: 10, icon: "——" },
];

const pathData = computed<PathLayerData>(() => {
  return (
    (props.layer.data as PathLayerData) || {
      pathData: "",
      controlPoints: [],
      closed: false,
      showGuide: true,
      guideColor: "#00FFFF",
      guideDashPattern: [10, 5],
    }
  );
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
const dashValue = computed(() => {
  const dashPattern = pathData.value.guideDashPattern;
  if (Array.isArray(dashPattern) && dashPattern.length > 0 && typeof dashPattern[0] === "number" && Number.isFinite(dashPattern[0])) {
    return dashPattern[0];
  }
  return 10;
});
const gapValue = computed(() => {
  const dashPattern = pathData.value.guideDashPattern;
  if (Array.isArray(dashPattern) && dashPattern.length > 1 && typeof dashPattern[1] === "number" && Number.isFinite(dashPattern[1])) {
    return dashPattern[1];
  }
  return 5;
});

// Type proof: controlPoints.length ∈ number | undefined → number (≥ 0, count)
function getControlPointCount(): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const controlPoints = (pathData.value != null && typeof pathData.value === "object" && "controlPoints" in pathData.value && Array.isArray(pathData.value.controlPoints)) ? pathData.value.controlPoints : undefined;
  const controlPointsLength = (controlPoints != null && Array.isArray(controlPoints)) ? controlPoints.length : undefined;
  return safeNonNegativeDefault(controlPointsLength, 0, "pathData.controlPoints.length");
}

// Find layers that reference this path
const attachedLayers = computed(() => {
  const layerId = props.layer.id;
  const attached: Array<{
    id: string;
    name: string;
    type: string;
    usage: string;
  }> = [];

  for (const layer of projectStore.getActiveCompLayers()) {
    // Check text layers for path reference
    if (layer.type === "text") {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/null checks
      const textData = (typeof layer.data === "object" && layer.data !== null) ? layer.data as { pathLayerId?: string } : {};
      if (typeof textData === "object" && textData !== null && "pathLayerId" in textData && typeof textData.pathLayerId === "string" && textData.pathLayerId === layerId) {
        attached.push({
          id: layer.id,
          name: layer.name,
          type: layer.type,
          usage: "Text on path",
        });
      }
    }

    // Check camera layers for spline path
    if (layer.type === "camera") {
      const cameraData = layer.data as {
        trajectory?: { splineLayerId?: string };
      } | null;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const trajectory = (cameraData != null && typeof cameraData === "object" && "trajectory" in cameraData && cameraData.trajectory != null && typeof cameraData.trajectory === "object") ? cameraData.trajectory : undefined;
      const splineLayerId = (trajectory != null && typeof trajectory === "object" && "splineLayerId" in trajectory && typeof trajectory.splineLayerId === "string") ? trajectory.splineLayerId : undefined;
      if (splineLayerId === layerId) {
        attached.push({
          id: layer.id,
          name: layer.name,
          type: layer.type,
          usage: "Camera path",
        });
      }
    }

    // Check particle layers for spline emission
    if (layer.type === "particles") {
      const particleData = layer.data as {
        emitters?: Array<{ shape?: string; splinePath?: { layerId?: string } }>;
      } | null;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const emitters = (particleData != null && typeof particleData === "object" && "emitters" in particleData && Array.isArray(particleData.emitters)) ? particleData.emitters : undefined;
      if (
        emitters != null &&
        emitters.some(
          (e) => {
            const shape = (e != null && typeof e === "object" && "shape" in e && typeof e.shape === "string") ? e.shape : undefined;
            const splinePath = (e != null && typeof e === "object" && "splinePath" in e && e.splinePath != null && typeof e.splinePath === "object") ? e.splinePath : undefined;
            const splinePathLayerId = (splinePath != null && typeof splinePath === "object" && "layerId" in splinePath && typeof splinePath.layerId === "string") ? splinePath.layerId : undefined;
            return shape === "spline" && splinePathLayerId === layerId;
          },
        )
      ) {
        attached.push({
          id: layer.id,
          name: layer.name,
          type: layer.type,
          usage: "Particle emitter",
        });
      }
    }
  }

  return attached;
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

// Update layer data
function update(key: keyof PathLayerData | string, value: PropertyValue | JSONValue) {
  layerStore.updateLayer(props.layer.id, {
    data: { ...pathData.value, [key]: value },
  });
  emit("update");
}

// Toggle guide visibility
function toggleGuide(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  update("showGuide", checked);
}

// Update dash pattern
function updateDash(value: number) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  const dashPattern = pathData.value.guideDashPattern;
  const gapValue = (Array.isArray(dashPattern) && dashPattern.length > 1 && typeof dashPattern[1] === "number" && Number.isFinite(dashPattern[1])) ? dashPattern[1] : 5;
  const pattern: [number, number] = [
    value,
    gapValue,
  ];
  update("guideDashPattern", pattern);
}

function updateGap(value: number) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  const dashPattern = pathData.value.guideDashPattern;
  const dashValue = (Array.isArray(dashPattern) && dashPattern.length > 0 && typeof dashPattern[0] === "number" && Number.isFinite(dashPattern[0])) ? dashPattern[0] : 10;
  const pattern: [number, number] = [
    dashValue,
    value,
  ];
  update("guideDashPattern", pattern);
}

// Apply guide preset
function applyPreset(preset: (typeof guidePresets)[0]) {
  update("guideColor", preset.color);
  if (preset.dash === 0 && preset.gap === 0) {
    update("guideDashPattern", [1, 0]); // Solid line
  } else {
    update("guideDashPattern", [preset.dash, preset.gap]);
  }
}

function isPresetActive(preset: (typeof guidePresets)[0]): boolean {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  const dashPattern = pathData.value.guideDashPattern;
  const dash = (Array.isArray(dashPattern) && dashPattern.length > 0 && typeof dashPattern[0] === "number" && Number.isFinite(dashPattern[0])) ? dashPattern[0] : 10;
  const gap = (Array.isArray(dashPattern) && dashPattern.length > 1 && typeof dashPattern[1] === "number" && Number.isFinite(dashPattern[1])) ? dashPattern[1] : 5;
  if (preset.dash === 0 && preset.gap === 0) {
    return gap === 0;
  }
  return dash === preset.dash && gap === preset.gap;
}

// Get layer icon
function getLayerIcon(type: string): string {
  const icons: Record<string, string> = {
    text: "T",
    camera: "🎥",
    particles: "✨",
  };
  return icons[type] || "◇";
}

// Select attached layer
function selectLayer(layerId: string) {
  layerStore.selectLayer(layerId);
}
</script>

<style scoped>
.path-properties {
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
  width: 60px;
  color: #888;
  font-size: 12px;
  flex-shrink: 0;
}

.property-row > :not(label) {
  flex: 1;
}

.color-input-wrapper {
  display: flex;
  align-items: center;
  gap: 8px;
}

.color-input-wrapper input[type="color"] {
  width: 40px;
  height: 24px;
  border: 1px solid #444;
  border-radius: 3px;
  padding: 0;
  cursor: pointer;
}

.color-hex {
  font-size: 11px;
  color: #666;
  font-family: monospace;
}

.preset-row {
  margin-top: 4px;
}

.preset-buttons {
  display: flex;
  gap: 4px;
}

.preset-buttons button {
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  border-radius: 3px;
  color: #888;
  padding: 4px 8px;
  font-size: 11px;
  cursor: pointer;
}

.preset-buttons button:hover {
  background: #333;
  color: #ccc;
}

.preset-buttons button.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
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

.info-row {
  color: #666;
  font-size: 12px;
}

.info-label {
  margin-right: 4px;
}

.info-value {
  color: #999;
}

/* Attached Elements */
.attached-count {
  background: #4a90d9;
  color: #fff;
  font-size: 10px;
  padding: 1px 5px;
  border-radius: 8px;
  margin-left: auto;
}

.no-attached {
  color: #666;
  font-size: 12px;
  text-align: center;
  padding: 12px;
  font-style: italic;
}

.attached-list {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.attached-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 8px;
  background: #252525;
  border-radius: 4px;
  cursor: pointer;
}

.attached-item:hover {
  background: #333;
}

.attached-icon {
  font-size: 12px;
}

.attached-name {
  flex: 1;
  font-size: 12px;
  color: #ccc;
}

.attached-usage {
  font-size: 11px;
  color: #666;
}

/* Usage Hints */
.usage-hints {
  padding: 12px;
  background: linear-gradient(180deg, #1a1a1a 0%, transparent 100%);
  border-top: 1px solid #2a2a2a;
}

.hint-title {
  color: #00FFFF;
  font-size: 12px;
  font-weight: 600;
  margin: 0 0 4px 0;
}

.hint-text {
  color: #666;
  font-size: 11px;
  margin: 0 0 6px 0;
}

.hint-list {
  color: #888;
  font-size: 11px;
  margin: 0;
  padding-left: 16px;
}

.hint-list li {
  margin: 2px 0;
}
</style>
