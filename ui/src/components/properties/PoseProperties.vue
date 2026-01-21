<template>
  <div class="pose-properties">
    <!-- Skeleton Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('skeleton')">
        <i class="pi" :class="expandedSections.has('skeleton') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Skeleton</span>
      </div>
      <div v-if="expandedSections.has('skeleton')" class="section-content">
        <div class="property-row">
          <label>Format</label>
          <select :value="poseData.format" @change="updatePoseData('format', ($event.target as HTMLSelectElement).value as PoseFormat)">
            <option v-for="fmt in poseFormats" :key="fmt" :value="fmt">{{ formatPoseFormat(fmt) }}</option>
          </select>
        </div>
        <div class="property-row">
          <label>Poses</label>
          <span class="value-display">{{ getPoseCount() }}</span>
        </div>
        <div class="property-row">
          <button class="action-btn" @click="addPose">
            <i class="pi pi-plus" /> Add Pose
          </button>
          <button
            class="action-btn"
            :disabled="!poseData.poses || poseData.poses.length <= 1"
            @click="removePose"
          >
            <i class="pi pi-minus" /> Remove
          </button>
        </div>
      </div>
    </div>

    <!-- Display Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('display')">
        <i class="pi" :class="expandedSections.has('display') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Display</span>
      </div>
      <div v-if="expandedSections.has('display')" class="section-content">
        <div class="property-row">
          <label>
            <input
              type="checkbox"
              :checked="poseData.showBones"
              @change="updatePoseData('showBones', ($event.target as HTMLInputElement).checked)"
            />
            Show Bones
          </label>
        </div>
        <div class="property-row">
          <label>
            <input
              type="checkbox"
              :checked="poseData.showKeypoints"
              @change="updatePoseData('showKeypoints', ($event.target as HTMLInputElement).checked)"
            />
            Show Keypoints
          </label>
        </div>
        <div class="property-row">
          <label>
            <input
              type="checkbox"
              :checked="poseData.showLabels"
              @change="updatePoseData('showLabels', ($event.target as HTMLInputElement).checked)"
            />
            Show Labels
          </label>
        </div>
        <div class="property-row">
          <label>Bone Width</label>
          <input
            type="range"
            :value="getBoneWidth"
            min="1"
            max="20"
            step="1"
            @input="updatePoseData('boneWidth', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ getBoneWidth }}px</span>
        </div>
        <div class="property-row">
          <label>Keypoint Size</label>
          <input
            type="range"
            :value="getKeypointRadius"
            min="1"
            max="20"
            step="1"
            @input="updatePoseData('keypointRadius', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ getKeypointRadius }}px</span>
        </div>
      </div>
    </div>

    <!-- Colors Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('colors')">
        <i class="pi" :class="expandedSections.has('colors') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Colors</span>
      </div>
      <div v-if="expandedSections.has('colors')" class="section-content">
        <div class="property-row">
          <label>
            <input
              type="checkbox"
              :checked="poseData.useDefaultColors"
              @change="updatePoseData('useDefaultColors', ($event.target as HTMLInputElement).checked)"
            />
            Use OpenPose Colors
          </label>
        </div>
        <template v-if="!poseData.useDefaultColors">
          <div class="property-row">
            <label>Bone Color</label>
            <input
              type="color"
              :value="getCustomBoneColor"
              @change="updatePoseData('customBoneColor', ($event.target as HTMLInputElement).value)"
            />
          </div>
          <div class="property-row">
            <label>Keypoint Color</label>
            <input
              type="color"
              :value="getCustomKeypointColor"
              @change="updatePoseData('customKeypointColor', ($event.target as HTMLInputElement).value)"
            />
          </div>
        </template>
        <div v-else class="info-note">
          OpenPose uses standard colors: yellow head, green torso, red/blue limbs.
        </div>
      </div>
    </div>

    <!-- Keypoint Editing Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('editing')">
        <i class="pi" :class="expandedSections.has('editing') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Keypoint Editing</span>
      </div>
      <div v-if="expandedSections.has('editing')" class="section-content">
        <div class="property-row">
          <label>Selected Pose</label>
          <select
            :value="getSelectedPose"
            @change="updatePoseData('selectedPose', Number(($event.target as HTMLSelectElement).value))"
          >
            <option
              v-for="(pose, idx) in poseData.poses"
              :key="pose.id"
              :value="idx"
            >
              Pose {{ idx + 1 }}
            </option>
          </select>
        </div>
        <div class="property-row">
          <label>Selected Keypoint</label>
          <select
            :value="getSelectedKeypoint"
            @change="updatePoseData('selectedKeypoint', Number(($event.target as HTMLSelectElement).value))"
          >
            <option value="-1">None</option>
            <option v-for="(kp, idx) in keypointNames" :key="idx" :value="idx">
              {{ kp }}
            </option>
          </select>
        </div>
        <template v-if="selectedKeypoint">
          <div class="property-row">
            <label>X Position</label>
            <input
              type="number"
              :value="selectedKeypoint.x.toFixed(3)"
              min="0"
              max="1"
              step="0.01"
              @change="updateKeypointPosition('x', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label>Y Position</label>
            <input
              type="number"
              :value="selectedKeypoint.y.toFixed(3)"
              min="0"
              max="1"
              step="0.01"
              @change="updateKeypointPosition('y', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label>Confidence</label>
            <input
              type="range"
              :value="selectedKeypoint.confidence"
              min="0"
              max="1"
              step="0.1"
              @input="updateKeypointPosition('confidence', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ (selectedKeypoint.confidence * 100).toFixed(0) }}%</span>
          </div>
        </template>
      </div>
    </div>

    <!-- Export Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('export')">
        <i class="pi" :class="expandedSections.has('export') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Export</span>
      </div>
      <div v-if="expandedSections.has('export')" class="section-content">
        <div class="property-row">
          <button class="action-btn primary" @click="exportOpenPoseJSON">
            <i class="pi pi-download" /> Export OpenPose JSON
          </button>
        </div>
        <div class="property-row">
          <button class="action-btn" @click="exportControlNetImage">
            <i class="pi pi-image" /> Export ControlNet Image
          </button>
        </div>
        <div class="info-note">
          Export poses for use with ControlNet OpenPose conditioning.
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, reactive } from "vue";
import {
  safeArrayDefault,
  safeNonNegativeDefault,
} from "@/utils/typeGuards";
import { useLayerStore } from "@/stores/layerStore";
import { useProjectStore } from "@/stores/projectStore";
import type { PoseFormat, PoseLayerData } from "@/types/project";

const props = defineProps<{
  layerId: string;
}>();

const emit = defineEmits<(e: "update", data: Partial<PoseLayerData>) => void>();

const layerStore = useLayerStore();
const projectStore = useProjectStore();

// COCO 18 keypoint names
const keypointNames = [
  "Nose",
  "Neck",
  "R.Shoulder",
  "R.Elbow",
  "R.Wrist",
  "L.Shoulder",
  "L.Elbow",
  "L.Wrist",
  "R.Hip",
  "R.Knee",
  "R.Ankle",
  "L.Hip",
  "L.Knee",
  "L.Ankle",
  "R.Eye",
  "L.Eye",
  "R.Ear",
  "L.Ear",
];

// Typed array validates pose formats at compile time
const poseFormats: PoseFormat[] = ["coco18", "body25", "custom"];

// Expanded sections
const expandedSections = reactive(
  new Set<string>(["skeleton", "display", "colors"]),
);

function toggleSection(section: string) {
  if (expandedSections.has(section)) {
    expandedSections.delete(section);
  } else {
    expandedSections.add(section);
  }
}

// Computed pose data
const poseData = computed(() => {
  const layer = projectStore.getActiveCompLayers().find((l) => l.id === props.layerId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layerData = (layer != null && typeof layer === "object" && "data" in layer && layer.data != null) ? layer.data as PoseLayerData : undefined;
  return (
    layerData || {
      poses: [],
      format: "coco18",
      normalized: true,
      boneWidth: 4,
      keypointRadius: 4,
      showKeypoints: true,
      showBones: true,
      showLabels: false,
      useDefaultColors: true,
      customBoneColor: "#FFFFFF",
      customKeypointColor: "#FF0000",
      selectedKeypoint: -1,
      selectedPose: 0,
    }
  );
});

// Type proof: poses.length ∈ number | undefined → number (≥ 0, count)
function getPoseCount(): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const poses = (poseData.value != null && typeof poseData.value === "object" && "poses" in poseData.value && poseData.value.poses != null && Array.isArray(poseData.value.poses)) ? poseData.value.poses : undefined;
  const posesLength = poses != null ? poses.length : undefined;
  return safeNonNegativeDefault(posesLength, 0, "poseData.poses.length");
}

// Selected keypoint for editing
const selectedKeypoint = computed(() => {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: selectedPose ∈ number | undefined → number (default 0)
  const poseIdx = (typeof poseData.value.selectedPose === "number" && Number.isFinite(poseData.value.selectedPose)) ? poseData.value.selectedPose : 0;
  // Pattern match: selectedKeypoint ∈ number | undefined → number (default -1)
  const kpIdx = (typeof poseData.value.selectedKeypoint === "number" && Number.isFinite(poseData.value.selectedKeypoint)) ? poseData.value.selectedKeypoint : -1;
  // System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
  // Template uses v-if="selectedKeypoint" which requires null for conditional rendering
  // This is the ONLY place where null is returned - all other code throws explicit errors
  if (kpIdx < 0) return null;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
  // Pattern match: poses[poseIdx] ∈ Pose | undefined → Pose | null
  const posesArray = (poseData.value.poses !== null && typeof poseData.value.poses === "object" && Array.isArray(poseData.value.poses)) ? poseData.value.poses : [];
  const pose = (poseIdx >= 0 && poseIdx < posesArray.length) ? posesArray[poseIdx] : undefined;
  // System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
  // Template uses v-if="selectedKeypoint" which requires null for conditional rendering
  if (pose === undefined) return null;
  // Pattern match: pose.keypoints[kpIdx] ∈ Keypoint | undefined → Keypoint | null
  const keypointsArray = (pose.keypoints !== null && typeof pose.keypoints === "object" && Array.isArray(pose.keypoints)) ? pose.keypoints : [];
  const keypoint = (kpIdx >= 0 && kpIdx < keypointsArray.length) ? keypointsArray[kpIdx] : undefined;
  return (keypoint !== undefined) ? keypoint : null;
});

// Update pose layer data
function updatePoseData<K extends keyof PoseLayerData>(
  key: K,
  value: PoseLayerData[K],
) {
  layerStore.updateLayerData(props.layerId, { [key]: value });
  emit("update", { [key]: value });
}

// Format pose format for display
const poseFormatLabels: Record<PoseFormat, string> = {
  coco18: "COCO 18-point",
  body25: "Body 25-point",
  custom: "Custom",
};

function formatPoseFormat(fmt: PoseFormat): string {
  return poseFormatLabels[fmt];
}

// Lean4/PureScript/Haskell: Computed properties for Vue template bindings - explicit pattern matching with memoization
// PERFORMANCE: Using computed() for memoization - critical for timeline scrubbing with multiple pose layers
// Pattern match: boneWidth ∈ number | undefined → number (default 4)
const getBoneWidth = computed(() => {
  return (typeof poseData.value.boneWidth === "number" && Number.isFinite(poseData.value.boneWidth)) ? poseData.value.boneWidth : 4;
});

// Pattern match: keypointRadius ∈ number | undefined → number (default 4)
const getKeypointRadius = computed(() => {
  return (typeof poseData.value.keypointRadius === "number" && Number.isFinite(poseData.value.keypointRadius)) ? poseData.value.keypointRadius : 4;
});

// Pattern match: customBoneColor ∈ string | undefined → string (default '#FFFFFF')
const getCustomBoneColor = computed(() => {
  return (typeof poseData.value.customBoneColor === "string" && poseData.value.customBoneColor.length > 0) ? poseData.value.customBoneColor : "#FFFFFF";
});

// Pattern match: customKeypointColor ∈ string | undefined → string (default '#FF0000')
const getCustomKeypointColor = computed(() => {
  return (typeof poseData.value.customKeypointColor === "string" && poseData.value.customKeypointColor.length > 0) ? poseData.value.customKeypointColor : "#FF0000";
});

// Pattern match: selectedPose ∈ number | undefined → number (default 0)
const getSelectedPose = computed(() => {
  return (typeof poseData.value.selectedPose === "number" && Number.isFinite(poseData.value.selectedPose)) ? poseData.value.selectedPose : 0;
});

// Pattern match: selectedKeypoint ∈ number | undefined → number (default -1)
const getSelectedKeypoint = computed(() => {
  return (typeof poseData.value.selectedKeypoint === "number" && Number.isFinite(poseData.value.selectedKeypoint)) ? poseData.value.selectedKeypoint : -1;
});

// Update selected keypoint position
function updateKeypointPosition(
  axis: "x" | "y" | "confidence",
  value: number,
) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: selectedPose ∈ number | undefined → number (default 0)
  const poseIdx = (typeof poseData.value.selectedPose === "number" && Number.isFinite(poseData.value.selectedPose)) ? poseData.value.selectedPose : 0;
  // Pattern match: selectedKeypoint ∈ number | undefined → number (default -1)
  const kpIdx = (typeof poseData.value.selectedKeypoint === "number" && Number.isFinite(poseData.value.selectedKeypoint)) ? poseData.value.selectedKeypoint : -1;
  if (kpIdx < 0) return;

  // System F/Omega: Use safeArrayDefault instead of lazy || [] fallback
  const poses = [
    ...safeArrayDefault(poseData.value.poses, [], "poseData.poses"),
  ];
  if (!poses[poseIdx]) return;

  const keypoints = [...poses[poseIdx].keypoints];
  keypoints[kpIdx] = { ...keypoints[kpIdx], [axis]: value };
  poses[poseIdx] = { ...poses[poseIdx], keypoints };

  layerStore.updateLayerData(props.layerId, { poses });
  emit("update", { poses });
}

// Add a new pose (copy of current)
function addPose() {
  // System F/Omega: Use safeArrayDefault instead of lazy || [] fallback
  const poses = [
    ...safeArrayDefault(poseData.value.poses, [], "poseData.poses"),
  ];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: selectedPose ∈ number | undefined → number (default 0)
  const selectedPoseValue = (typeof poseData.value.selectedPose === "number" && Number.isFinite(poseData.value.selectedPose)) ? poseData.value.selectedPose : 0;
  const currentPose = poses[selectedPoseValue];
  if (currentPose) {
    poses.push({
      id: `pose-${Date.now()}`,
      format: currentPose.format,
      keypoints: currentPose.keypoints.map((kp) => ({ ...kp })),
    });
    layerStore.updateLayerData(props.layerId, {
      poses,
      selectedPose: poses.length - 1,
    });
    emit("update", { poses });
  }
}

// Remove selected pose
function removePose() {
  // System F/Omega: Use safeArrayDefault instead of lazy || [] fallback
  const poses = [
    ...safeArrayDefault(poseData.value.poses, [], "poseData.poses"),
  ];
  if (poses.length <= 1) return;

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  // Pattern match: selectedPose ∈ number | undefined → number (default 0)
  const idx = (typeof poseData.value.selectedPose === "number" && Number.isFinite(poseData.value.selectedPose)) ? poseData.value.selectedPose : 0;
  poses.splice(idx, 1);
  const newSelected = Math.min(idx, poses.length - 1);

  layerStore.updateLayerData(props.layerId, { poses, selectedPose: newSelected });
  emit("update", { poses, selectedPose: newSelected });
}

// Export to OpenPose JSON
async function exportOpenPoseJSON() {
  try {
    const { exportToOpenPoseJSON } = await import(
      "@/services/export/poseExport"
    );
    // System F/Omega: Use safeArrayDefault instead of lazy ?? [] fallback
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const posesValue = (poseData.value != null && typeof poseData.value === "object" && "poses" in poseData.value && poseData.value.poses != null && Array.isArray(poseData.value.poses)) ? poseData.value.poses : undefined;
    const mappedPoses = posesValue != null ? posesValue.map((p) => ({
      id: p.id,
      format: p.format,
      keypoints: p.keypoints,
    })) : undefined;
    const poses = safeArrayDefault(
      mappedPoses,
      [],
      "poseData.poses (mapped)",
    );

    const json = exportToOpenPoseJSON(poses);
    const blob = new Blob([JSON.stringify(json, null, 2)], {
      type: "application/json",
    });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = "openpose.json";
    a.click();
    URL.revokeObjectURL(url);
  } catch (err) {
    console.error("Failed to export OpenPose JSON:", err);
  }
}

// Export ControlNet image
async function exportControlNetImage() {
  try {
    const { exportPoseForControlNet } = await import(
      "@/services/export/poseExport"
    );
    const comp = projectStore.getActiveComp();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: comp.settings.width ∈ number | undefined → number (default 512)
    const widthValue = (comp !== null && typeof comp === "object" && "settings" in comp && comp.settings !== null && typeof comp.settings === "object" && "width" in comp.settings && typeof comp.settings.width === "number" && Number.isFinite(comp.settings.width)) ? comp.settings.width : 512;
    // Pattern match: comp.settings.height ∈ number | undefined → number (default 512)
    const heightValue = (comp !== null && typeof comp === "object" && "settings" in comp && comp.settings !== null && typeof comp.settings === "object" && "height" in comp.settings && typeof comp.settings.height === "number" && Number.isFinite(comp.settings.height)) ? comp.settings.height : 512;
    const width = widthValue;
    const height = heightValue;

    // System F/Omega: Use safeArrayDefault instead of lazy ?? [] fallback
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const posesValue = (poseData.value != null && typeof poseData.value === "object" && "poses" in poseData.value && poseData.value.poses != null && Array.isArray(poseData.value.poses)) ? poseData.value.poses : undefined;
    const mappedPoses = posesValue != null ? posesValue.map((p) => ({
      id: p.id,
      format: p.format,
      keypoints: p.keypoints,
    })) : undefined;
    const poses = safeArrayDefault(
      mappedPoses,
      [],
      "poseData.poses (mapped)",
    );

    const result = exportPoseForControlNet(poses, width, height);

    // Download canvas as PNG
    const dataUrl = result.canvas.toDataURL("image/png");
    const a = document.createElement("a");
    a.href = dataUrl;
    a.download = "controlnet_pose.png";
    a.click();
  } catch (err) {
    console.error("Failed to export ControlNet image:", err);
  }
}
</script>

<style scoped>
.pose-properties {
  display: flex;
  flex-direction: column;
}

.property-section {
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.section-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  cursor: pointer;
  font-weight: 500;
  color: var(--lattice-text-primary, #e0e0e0);
  user-select: none;
}

.section-header:hover {
  background: var(--lattice-surface-2, #1a1a1a);
}

.section-content {
  padding: 8px 12px 12px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.property-row label {
  min-width: 100px;
  color: var(--lattice-text-secondary, #a0a0a0);
  font-size: 12px;
}

.property-row input[type="number"],
.property-row input[type="text"],
.property-row select {
  flex: 1;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 4px;
  padding: 4px 8px;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 12px;
}

.property-row input[type="range"] {
  flex: 1;
}

.property-row input[type="color"] {
  width: 32px;
  height: 24px;
  border: none;
  border-radius: 4px;
  cursor: pointer;
}

.property-row input[type="checkbox"] {
  margin-right: 8px;
}

.value-display {
  min-width: 50px;
  text-align: right;
  color: var(--lattice-text-secondary, #a0a0a0);
  font-size: 11px;
}

.action-btn {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 6px 12px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 4px;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 12px;
  cursor: pointer;
  transition: background 0.15s;
}

.action-btn:hover:not(:disabled) {
  background: var(--lattice-surface-4, #2a2a2a);
}

.action-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.action-btn.primary {
  background: var(--lattice-accent, #8B5CF6);
  border-color: var(--lattice-accent, #8B5CF6);
}

.action-btn.primary:hover:not(:disabled) {
  background: var(--lattice-accent-hover, #A78BFA);
}

.info-note {
  padding: 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 4px;
  font-size: 11px;
  color: var(--lattice-text-muted, #666);
  line-height: 1.4;
}

.pi {
  font-size: 12px;
}
</style>
