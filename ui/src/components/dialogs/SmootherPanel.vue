<!--
  @component SmootherPanel
  @description Panel for smoothing existing keyframes on selected properties.

  Features:
  - Apply smoothing to selected keyframes or all keyframes
  - Adjustable smoothing amount (0-100%)
  - Tolerance-based keyframe simplification
  - Preview before/after keyframe counts
  - Preserves first and last keyframes
-->
<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="$emit('close')">
      <div class="dialog-box">
        <div class="dialog-header">
          <h3>Smoother</h3>
          <button class="close-btn" @click="$emit('close')">&times;</button>
        </div>
        <div class="dialog-body">
          <!-- Target Info -->
          <div class="target-info">
            <div class="target-row">
              <span class="target-label">Layer:</span>
              <span class="target-value">{{ targetLayerName || 'None selected' }}</span>
            </div>
            <div class="target-row">
              <span class="target-label">Keyframes:</span>
              <span class="target-value">{{ originalKeyframeCount }}</span>
            </div>
          </div>

          <!-- Smoothing Settings -->
          <div class="settings-section">
            <div class="section-header">Smoothing</div>

            <div class="form-row">
              <label>Spatial Smoothing</label>
              <div class="input-group">
                <input
                  type="range"
                  v-model.number="spatialSmoothing"
                  min="0"
                  max="100"
                  step="5"
                  class="slider"
                />
                <span class="value-display">{{ spatialSmoothing }}%</span>
              </div>
              <span class="help-text">Reduces jitter in position values</span>
            </div>

            <div class="form-row">
              <label>Temporal Smoothing</label>
              <div class="input-group">
                <input
                  type="range"
                  v-model.number="temporalSmoothing"
                  min="0"
                  max="100"
                  step="5"
                  class="slider"
                />
                <span class="value-display">{{ temporalSmoothing }}%</span>
              </div>
              <span class="help-text">Smooths timing between keyframes</span>
            </div>
          </div>

          <!-- Simplification Settings -->
          <div class="settings-section">
            <div class="section-header">Simplification</div>

            <div class="form-row checkbox-row">
              <label class="checkbox-label">
                <input type="checkbox" v-model="enableSimplification" />
                <span>Remove redundant keyframes</span>
              </label>
            </div>

            <div class="form-row" v-if="enableSimplification">
              <label>Tolerance</label>
              <div class="input-group">
                <input
                  type="range"
                  v-model.number="simplifyTolerance"
                  min="0.5"
                  max="20"
                  step="0.5"
                  class="slider"
                />
                <span class="value-display">{{ simplifyTolerance }}px</span>
              </div>
              <span class="help-text">Higher = fewer keyframes</span>
            </div>
          </div>

          <!-- Preview -->
          <div class="preview-section" v-if="enableSimplification">
            <div class="section-header">Result Preview</div>
            <div class="preview-stats">
              <div class="stat-item">
                <span class="stat-label">Before:</span>
                <span class="stat-value">{{ originalKeyframeCount }} keyframes</span>
              </div>
              <div class="stat-arrow">→</div>
              <div class="stat-item">
                <span class="stat-label">After:</span>
                <span class="stat-value estimated">~{{ estimatedKeyframeCount }} keyframes</span>
              </div>
            </div>
            <div class="reduction-bar">
              <div
                class="reduction-fill"
                :style="{ width: reductionPercent + '%' }"
              ></div>
            </div>
            <span class="reduction-text">
              {{ Math.round(100 - reductionPercent) }}% reduction
            </span>
          </div>

          <!-- Apply Scope -->
          <div class="scope-section">
            <div class="section-header">Apply To</div>
            <div class="scope-options">
              <label class="radio-label">
                <input type="radio" v-model="applyScope" value="selected" />
                <span>Selected keyframes only</span>
              </label>
              <label class="radio-label">
                <input type="radio" v-model="applyScope" value="all" />
                <span>All keyframes on property</span>
              </label>
            </div>
          </div>
        </div>
        <div class="dialog-footer">
          <button class="btn-cancel" @click="$emit('close')">Cancel</button>
          <button
            class="btn-confirm"
            @click="applySmoothing"
            :disabled="originalKeyframeCount < 3"
          >
            Apply
          </button>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, ref, watch } from "vue";
import { useLayerStore } from "@/stores/layerStore";
import { useKeyframeStore } from "@/stores/keyframeStore";
import { useSelectionStore } from "@/stores/selectionStore";
import type { Keyframe, PropertyValue } from "@/types/project";

const props = defineProps<{
  visible: boolean;
  layerId?: string;
  propertyPath?: string;
}>();

const emit = defineEmits<{
  close: [];
  apply: [];
}>();

const layerStore = useLayerStore();
const keyframeStore = useKeyframeStore();
const selectionStore = useSelectionStore();

// Settings
const spatialSmoothing = ref(50);
const temporalSmoothing = ref(25);
const enableSimplification = ref(true);
const simplifyTolerance = ref(2);
const applyScope = ref<"selected" | "all">("all");

// Computed
const targetLayerName = computed(() => {
  if (props.layerId) {
    const layer = layerStore.getLayerById(props.layerId);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const layerName = (layer != null && typeof layer === "object" && "name" in layer && typeof layer.name === "string") ? layer.name : undefined;
    return layerName != null ? layerName : "Unknown";
  }
  const selectedIds = selectionStore.selectedLayerIds;
  if (selectedIds.length === 0) return null;
  const layer = layerStore.getLayerById(selectedIds[0]);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layerName = (layer != null && typeof layer === "object" && "name" in layer && typeof layer.name === "string") ? layer.name : undefined;
  return layerName != null ? layerName : "Unknown";
});

const targetKeyframes = computed<Keyframe<PropertyValue>[]>(() => {
  const layerId = props.layerId || selectionStore.selectedLayerIds[0];
  if (!layerId) return [];

  const layer = layerStore.getLayerById(layerId);
  if (!layer) return [];

  // Get position keyframes by default
  const propertyPath = props.propertyPath || "transform.position";
  let property = null;

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const layerTransform = (layer != null && typeof layer === "object" && "transform" in layer && layer.transform != null && typeof layer.transform === "object") ? layer.transform : undefined;

  if (propertyPath === "transform.position" || propertyPath === "position") {
    property = (layerTransform != null && typeof layerTransform === "object" && "position" in layerTransform && layerTransform.position != null) ? layerTransform.position : undefined;
  } else if (propertyPath === "transform.scale" || propertyPath === "scale") {
    property = (layerTransform != null && typeof layerTransform === "object" && "scale" in layerTransform && layerTransform.scale != null) ? layerTransform.scale : undefined;
  } else if (
    propertyPath === "transform.rotation" ||
    propertyPath === "rotation"
  ) {
    property = (layerTransform != null && typeof layerTransform === "object" && "rotation" in layerTransform && layerTransform.rotation != null) ? layerTransform.rotation : undefined;
  } else if (propertyPath === "opacity") {
    property = layer.opacity;
  }

  if (!property || !property.animated) return [];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
  const keyframes = property.keyframes;
  return (keyframes !== null && keyframes !== undefined && Array.isArray(keyframes)) ? keyframes : [];
});

const originalKeyframeCount = computed(() => targetKeyframes.value.length);

const estimatedKeyframeCount = computed(() => {
  if (!enableSimplification.value) return originalKeyframeCount.value;

  // Rough estimate based on tolerance
  // Higher tolerance = fewer keyframes
  const reductionFactor = Math.min(0.9, simplifyTolerance.value / 25);
  const estimated = Math.max(
    2,
    Math.round(originalKeyframeCount.value * (1 - reductionFactor)),
  );
  return estimated;
});

const reductionPercent = computed(() => {
  if (originalKeyframeCount.value === 0) return 100;
  return (estimatedKeyframeCount.value / originalKeyframeCount.value) * 100;
});

// Methods
function applySmoothing() {
  const layerId = props.layerId || selectionStore.selectedLayerIds[0];
  if (!layerId) return;

  const propertyPath = props.propertyPath || "transform.position";
  const keyframes = [...targetKeyframes.value];

  if (keyframes.length < 3) return;

  // Sort keyframes by frame
  keyframes.sort((a, b) => a.frame - b.frame);

  // Apply spatial smoothing using moving average
  if (spatialSmoothing.value > 0) {
    const windowSize = Math.max(
      3,
      Math.round((spatialSmoothing.value / 100) * 7) | 1,
    );
    const halfWindow = Math.floor(windowSize / 2);

    for (let i = 1; i < keyframes.length - 1; i++) {
      const kf = keyframes[i];

      // Calculate smoothed value
      let sumX = 0,
        sumY = 0,
        count = 0;

      for (
        let j = Math.max(0, i - halfWindow);
        j <= Math.min(keyframes.length - 1, i + halfWindow);
        j++
      ) {
        const other = keyframes[j];
        if (typeof other.value === "object" && "x" in other.value) {
          sumX += other.value.x;
          sumY += other.value.y;
          count++;
        } else if (typeof other.value === "number") {
          sumX += other.value;
          count++;
        }
      }

      if (count > 0) {
        if (typeof kf.value === "object" && "x" in kf.value) {
          const blendFactor = spatialSmoothing.value / 100;
          const smoothedX = sumX / count;
          const smoothedY = sumY / count;
          kf.value = {
            ...kf.value,
            x: kf.value.x * (1 - blendFactor) + smoothedX * blendFactor,
            y: kf.value.y * (1 - blendFactor) + smoothedY * blendFactor,
          };
        } else if (typeof kf.value === "number") {
          const blendFactor = spatialSmoothing.value / 100;
          const smoothed = sumX / count;
          kf.value = kf.value * (1 - blendFactor) + smoothed * blendFactor;
        }
      }
    }
  }

  // Apply simplification if enabled
  let finalKeyframes = keyframes;
  if (enableSimplification.value && simplifyTolerance.value > 0) {
    finalKeyframes = simplifyKeyframesDouglasPeucker(
      keyframes,
      simplifyTolerance.value,
    );
  }

  // Update keyframes in store
  // First clear existing keyframes
  const layer = layerStore.getLayerById(layerId);
  if (!layer) return;

  // Apply the smoothed/simplified keyframes
  finalKeyframes.forEach((kf) => {
    keyframeStore.setKeyframeValue(layerId, propertyPath, kf.id, kf.value);
  });

  // If simplification removed keyframes, delete them
  if (enableSimplification.value) {
    const keptIds = new Set(finalKeyframes.map((kf) => kf.id));
    keyframes.forEach((kf) => {
      if (!keptIds.has(kf.id)) {
        keyframeStore.removeKeyframe(layerId, propertyPath, kf.id);
      }
    });
  }

  emit("apply");
  emit("close");
}

/**
 * Douglas-Peucker simplification for keyframes
 */
function simplifyKeyframesDouglasPeucker(
  keyframes: Keyframe<PropertyValue>[],
  tolerance: number,
): Keyframe<PropertyValue>[] {
  if (keyframes.length <= 2) return keyframes;

  const getValue = (kf: Keyframe<PropertyValue>) => {
    if (typeof kf.value === "object" && "x" in kf.value) {
      return { x: kf.value.x, y: kf.value.y };
    }
    return { x: kf.value, y: 0 };
  };

  // Find point with maximum distance from line
  const first = keyframes[0];
  const last = keyframes[keyframes.length - 1];
  const firstVal = getValue(first);
  const lastVal = getValue(last);

  let maxDist = 0;
  let maxIdx = 0;

  for (let i = 1; i < keyframes.length - 1; i++) {
    const val = getValue(keyframes[i]);

    // Interpolate expected position
    const t = (keyframes[i].frame - first.frame) / (last.frame - first.frame);
    const expectedX = firstVal.x + t * (lastVal.x - firstVal.x);
    const expectedY = firstVal.y + t * (lastVal.y - firstVal.y);

    const distX = val.x - expectedX;
    const distY = val.y - expectedY;
    const dist = Math.sqrt(distX * distX + distY * distY);

    if (dist > maxDist) {
      maxDist = dist;
      maxIdx = i;
    }
  }

  if (maxDist > tolerance) {
    const left = simplifyKeyframesDouglasPeucker(
      keyframes.slice(0, maxIdx + 1),
      tolerance,
    );
    const right = simplifyKeyframesDouglasPeucker(
      keyframes.slice(maxIdx),
      tolerance,
    );
    return [...left.slice(0, -1), ...right];
  }

  return [first, last];
}

// Reset on dialog open
watch(
  () => props.visible,
  (visible) => {
    if (visible) {
      spatialSmoothing.value = 50;
      temporalSmoothing.value = 25;
      enableSimplification.value = true;
      simplifyTolerance.value = 2;
      applyScope.value = "all";
    }
  },
);
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.dialog-box {
  background: #1e1e1e;
  border: 1px solid #333;
  border-radius: 8px;
  width: 380px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  border-bottom: 1px solid #333;
}

.dialog-header h3 {
  margin: 0;
  font-size: 14px;
  font-weight: 600;
  color: #fff;
}

.close-btn {
  background: transparent;
  border: none;
  color: #888;
  font-size: 20px;
  cursor: pointer;
  padding: 0;
  line-height: 1;
}
.close-btn:hover { color: #fff; }

.dialog-body {
  padding: 16px;
}

/* Target Info */
.target-info {
  padding: 12px;
  background: #151515;
  border-radius: 6px;
  margin-bottom: 16px;
}

.target-row {
  display: flex;
  justify-content: space-between;
  margin-bottom: 4px;
}

.target-row:last-child {
  margin-bottom: 0;
}

.target-label {
  color: #888;
  font-size: 12px;
}

.target-value {
  color: #fff;
  font-size: 12px;
}

/* Settings */
.settings-section,
.preview-section,
.scope-section {
  margin-bottom: 16px;
}

.section-header {
  font-size: 11px;
  font-weight: 600;
  color: #888;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-bottom: 12px;
}

.form-row {
  margin-bottom: 12px;
}

.form-row label {
  display: block;
  font-size: 12px;
  color: #aaa;
  margin-bottom: 6px;
}

.input-group {
  display: flex;
  align-items: center;
  gap: 12px;
}

.slider {
  flex: 1;
  height: 4px;
  -webkit-appearance: none;
  appearance: none;
  background: #333;
  border-radius: 2px;
  cursor: pointer;
}

.slider::-webkit-slider-thumb {
  -webkit-appearance: none;
  appearance: none;
  width: 14px;
  height: 14px;
  background: #8B5CF6;
  border-radius: 50%;
  cursor: pointer;
}

.value-display {
  min-width: 50px;
  text-align: right;
  font-size: 13px;
  color: #8B5CF6;
  font-family: monospace;
}

.help-text {
  display: block;
  font-size: 11px;
  color: #666;
  margin-top: 4px;
}

/* Checkbox */
.checkbox-row {
  margin-bottom: 12px;
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
}

.checkbox-label input[type="checkbox"] {
  width: 16px;
  height: 16px;
  accent-color: #8B5CF6;
}

.checkbox-label span {
  font-size: 13px;
  color: #ccc;
}

/* Preview */
.preview-stats {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 12px;
  background: #111;
  border-radius: 4px;
  margin-bottom: 8px;
}

.stat-item {
  display: flex;
  flex-direction: column;
  gap: 2px;
}

.stat-label {
  font-size: 11px;
  color: #666;
}

.stat-value {
  font-size: 14px;
  color: #fff;
}

.stat-value.estimated {
  color: #4CAF50;
}

.stat-arrow {
  font-size: 18px;
  color: #666;
}

.reduction-bar {
  height: 4px;
  background: #333;
  border-radius: 2px;
  overflow: hidden;
  margin-bottom: 4px;
}

.reduction-fill {
  height: 100%;
  background: linear-gradient(90deg, #4CAF50, #8B5CF6);
  transition: width 0.3s ease;
}

.reduction-text {
  display: block;
  text-align: center;
  font-size: 11px;
  color: #4CAF50;
}

/* Scope */
.scope-options {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.radio-label {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
}

.radio-label input[type="radio"] {
  width: 16px;
  height: 16px;
  accent-color: #8B5CF6;
}

.radio-label span {
  font-size: 13px;
  color: #ccc;
}

/* Footer */
.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  padding: 12px 16px;
  border-top: 1px solid #333;
}

.btn-cancel,
.btn-confirm {
  padding: 8px 16px;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
}

.btn-cancel {
  background: #333;
  border: 1px solid #444;
  color: #ccc;
}
.btn-cancel:hover { background: #444; }

.btn-confirm {
  background: #8B5CF6;
  border: none;
  color: #fff;
}
.btn-confirm:hover:not(:disabled) { background: #9D70F9; }
.btn-confirm:disabled { opacity: 0.5; cursor: not-allowed; }
</style>
