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
          <span class="value-display">{{ poseData.poses?.length || 0 }}</span>
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
            :value="poseData.boneWidth ?? 4"
            min="1"
            max="20"
            step="1"
            @input="updatePoseData('boneWidth', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ poseData.boneWidth ?? 4 }}px</span>
        </div>
        <div class="property-row">
          <label>Keypoint Size</label>
          <input
            type="range"
            :value="poseData.keypointRadius ?? 4"
            min="1"
            max="20"
            step="1"
            @input="updatePoseData('keypointRadius', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ poseData.keypointRadius ?? 4 }}px</span>
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
              :value="poseData.customBoneColor ?? '#FFFFFF'"
              @change="updatePoseData('customBoneColor', ($event.target as HTMLInputElement).value)"
            />
          </div>
          <div class="property-row">
            <label>Keypoint Color</label>
            <input
              type="color"
              :value="poseData.customKeypointColor ?? '#FF0000'"
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
            :value="poseData.selectedPose ?? 0"
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
            :value="poseData.selectedKeypoint ?? -1"
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
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import type { PoseFormat, PoseLayerData } from "@/types/project";

const props = defineProps<{
  layerId: string;
}>();

const emit = defineEmits<(e: "update", data: Partial<PoseLayerData>) => void>();

const store = useCompositorStore();
const layerStore = useLayerStore();

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
  const layer = store.layers.find((l) => l.id === props.layerId);
  return (
    (layer?.data as PoseLayerData) || {
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

// Selected keypoint for editing
const selectedKeypoint = computed(() => {
  const poseIdx = poseData.value.selectedPose ?? 0;
  const kpIdx = poseData.value.selectedKeypoint ?? -1;
  if (kpIdx < 0) return null;
  const pose = poseData.value.poses?.[poseIdx];
  return pose?.keypoints?.[kpIdx] ?? null;
});

// Update pose layer data
function updatePoseData<K extends keyof PoseLayerData>(
  key: K,
  value: PoseLayerData[K],
) {
  layerStore.updateLayerData(store, props.layerId, { [key]: value });
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

// Update selected keypoint position
function updateKeypointPosition(
  axis: "x" | "y" | "confidence",
  value: number,
) {
  const poseIdx = poseData.value.selectedPose ?? 0;
  const kpIdx = poseData.value.selectedKeypoint ?? -1;
  if (kpIdx < 0) return;

  const poses = [...(poseData.value.poses || [])];
  if (!poses[poseIdx]) return;

  const keypoints = [...poses[poseIdx].keypoints];
  keypoints[kpIdx] = { ...keypoints[kpIdx], [axis]: value };
  poses[poseIdx] = { ...poses[poseIdx], keypoints };

  layerStore.updateLayerData(store, props.layerId, { poses });
  emit("update", { poses });
}

// Add a new pose (copy of current)
function addPose() {
  const poses = [...(poseData.value.poses || [])];
  const currentPose = poses[poseData.value.selectedPose ?? 0];
  if (currentPose) {
    poses.push({
      id: `pose-${Date.now()}`,
      format: currentPose.format,
      keypoints: currentPose.keypoints.map((kp) => ({ ...kp })),
    });
    layerStore.updateLayerData(store, props.layerId, {
      poses,
      selectedPose: poses.length - 1,
    });
    emit("update", { poses });
  }
}

// Remove selected pose
function removePose() {
  const poses = [...(poseData.value.poses || [])];
  if (poses.length <= 1) return;

  const idx = poseData.value.selectedPose ?? 0;
  poses.splice(idx, 1);
  const newSelected = Math.min(idx, poses.length - 1);

  layerStore.updateLayerData(store, props.layerId, { poses, selectedPose: newSelected });
  emit("update", { poses, selectedPose: newSelected });
}

// Export to OpenPose JSON
async function exportOpenPoseJSON() {
  try {
    const { exportToOpenPoseJSON } = await import(
      "@/services/export/poseExport"
    );
    const poses =
      poseData.value.poses?.map((p) => ({
        id: p.id,
        format: p.format,
        keypoints: p.keypoints,
      })) || [];

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
    const comp = store.getActiveComp();
    const width = comp?.settings.width ?? 512;
    const height = comp?.settings.height ?? 512;

    const poses =
      poseData.value.poses?.map((p) => ({
        id: p.id,
        format: p.format,
        keypoints: p.keypoints,
      })) || [];

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
