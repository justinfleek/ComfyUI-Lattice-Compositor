<!--
  @component MotionSketchPanel
  @description Panel for motion sketch recording - draw motion paths in real-time.

  Features:
  - Real-time motion recording during mouse drag
  - Adjustable recording speed (slow-mo/fast-mo capture)
  - Smoothing amount control
  - Keyframe simplification tolerance
  - Preview of recorded path
-->
<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="$emit('close')">
      <div class="dialog-box">
        <div class="dialog-header">
          <h3>Motion Sketch</h3>
          <button class="close-btn" @click="$emit('close')">&times;</button>
        </div>
        <div class="dialog-body">
          <!-- Recording Status -->
          <div class="status-section" :class="{ recording: isRecording }">
            <div class="status-indicator">
              <span class="status-dot"></span>
              <span class="status-text">{{ statusText }}</span>
            </div>
            <div v-if="recordedMotion" class="motion-stats">
              <span>{{ recordedMotion.samples.length }} samples</span>
              <span>{{ formatDuration(motionDuration) }}</span>
            </div>
          </div>

          <!-- Recording Settings -->
          <div class="settings-section">
            <div class="section-header">Recording Settings</div>

            <div class="form-row">
              <label>Capture Speed</label>
              <div class="input-group">
                <input
                  type="range"
                  v-model.number="captureSpeed"
                  min="0.25"
                  max="4"
                  step="0.25"
                  class="slider"
                />
                <span class="value-display">{{ captureSpeed }}x</span>
              </div>
              <span class="help-text">
                {{ captureSpeed < 1 ? 'Slow motion capture' : captureSpeed > 1 ? 'Fast motion capture' : 'Real-time' }}
              </span>
            </div>

            <div class="form-row">
              <label>Smoothing</label>
              <div class="input-group">
                <input
                  type="range"
                  v-model.number="smoothing"
                  min="0"
                  max="100"
                  step="5"
                  class="slider"
                />
                <span class="value-display">{{ smoothing }}%</span>
              </div>
            </div>

            <div class="form-row">
              <label>Simplify Tolerance</label>
              <div class="input-group">
                <input
                  type="range"
                  v-model.number="simplifyTolerance"
                  min="0"
                  max="20"
                  step="1"
                  class="slider"
                />
                <span class="value-display">{{ simplifyTolerance }}px</span>
              </div>
            </div>
          </div>

          <!-- Target Layer -->
          <div class="target-section">
            <div class="section-header">Target</div>
            <div class="target-info">
              <span v-if="targetLayerName" class="layer-name">{{ targetLayerName }}</span>
              <span v-else class="no-layer">No layer selected</span>
            </div>
            <div class="target-property">
              <span class="property-label">Property:</span>
              <span class="property-value">Position</span>
            </div>
          </div>

          <!-- Motion Preview -->
          <div class="preview-section" v-if="recordedMotion && recordedMotion.samples.length > 1">
            <div class="section-header">Preview</div>
            <svg class="motion-preview" viewBox="0 0 200 120">
              <!-- Background -->
              <rect x="0" y="0" width="200" height="120" fill="#111" />

              <!-- Motion path -->
              <path
                :d="previewPath"
                fill="none"
                stroke="#8B5CF6"
                stroke-width="2"
                stroke-linecap="round"
                stroke-linejoin="round"
              />

              <!-- Start point -->
              <circle
                v-if="previewPoints.length > 0"
                :cx="previewPoints[0].x"
                :cy="previewPoints[0].y"
                r="4"
                fill="#4CAF50"
              />

              <!-- End point -->
              <circle
                v-if="previewPoints.length > 1"
                :cx="previewPoints[previewPoints.length - 1].x"
                :cy="previewPoints[previewPoints.length - 1].y"
                r="4"
                fill="#f44336"
              />
            </svg>
            <div class="preview-stats">
              <span>Path length: {{ Math.round(pathLength) }}px</span>
              <span>Avg speed: {{ Math.round(avgSpeed) }}px/s</span>
            </div>
          </div>

          <!-- Instructions -->
          <div class="instructions" v-if="!isRecording && !recordedMotion">
            <p>Click "Start Recording" then drag on the canvas to record motion.</p>
            <p>The motion will be applied to the selected layer's position.</p>
          </div>
        </div>
        <div class="dialog-footer">
          <button
            v-if="!isRecording"
            class="btn-record"
            @click="startRecording"
            :disabled="!targetLayerName"
          >
            Start Recording
          </button>
          <button
            v-else
            class="btn-stop"
            @click="stopRecording"
          >
            Stop Recording
          </button>

          <div class="footer-right">
            <button class="btn-cancel" @click="$emit('close')">Cancel</button>
            <button
              class="btn-confirm"
              @click="applyMotion"
              :disabled="!recordedMotion || recordedMotion.samples.length < 2"
            >
              Apply
            </button>
          </div>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, onUnmounted, ref, watch } from "vue";
import {
  convertMotionToKeyframes,
  getMotionAverageSpeed,
  getMotionBounds,
  getMotionPathLength,
  MotionRecorder,
  type RecordedMotion,
  simplifyKeyframes,
  smoothMotion,
} from "@/services/motionRecording";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import { useKeyframeStore } from "@/stores/keyframeStore";

const props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<{
  close: [];
  startCapture: [];
  stopCapture: [];
  apply: [keyframes: Array<{ id: string; frame: number; value: unknown }>];
}>();

const store = useCompositorStore();
const layerStore = useLayerStore();

// Settings
const captureSpeed = ref(1.0);
const smoothing = ref(50);
const simplifyTolerance = ref(2);

// Recording state
const isRecording = ref(false);
const recordedMotion = ref<RecordedMotion | null>(null);
let recorder: MotionRecorder | null = null;

// Computed
const targetLayerName = computed(() => {
  const layers = store.selectedLayerIds;
  if (layers.length === 0) return null;
  const layer = layerStore.getLayerById(store, layers[0]);
  return layer?.name || "Unknown Layer";
});

const statusText = computed(() => {
  if (isRecording.value) return "Recording...";
  if (recordedMotion.value) return "Motion recorded";
  return "Ready to record";
});

const motionDuration = computed(() => {
  if (!recordedMotion.value || recordedMotion.value.samples.length < 2)
    return 0;
  const samples = recordedMotion.value.samples;
  return samples[samples.length - 1].time - samples[0].time;
});

const pathLength = computed(() => {
  if (!recordedMotion.value) return 0;
  return getMotionPathLength(recordedMotion.value);
});

const avgSpeed = computed(() => {
  if (!recordedMotion.value) return 0;
  return getMotionAverageSpeed(recordedMotion.value);
});

const previewPoints = computed(() => {
  if (!recordedMotion.value || recordedMotion.value.samples.length < 2)
    return [];

  const bounds = getMotionBounds(recordedMotion.value);
  const padding = 10;
  const previewW = 200 - padding * 2;
  const previewH = 120 - padding * 2;

  // Scale to fit preview
  const scaleX = bounds.width > 0 ? previewW / bounds.width : 1;
  const scaleY = bounds.height > 0 ? previewH / bounds.height : 1;
  const scale = Math.min(scaleX, scaleY, 1);

  const offsetX = padding + (previewW - bounds.width * scale) / 2;
  const offsetY = padding + (previewH - bounds.height * scale) / 2;

  return recordedMotion.value.samples.map((s) => ({
    x: (s.x - bounds.minX) * scale + offsetX,
    y: (s.y - bounds.minY) * scale + offsetY,
  }));
});

const previewPath = computed(() => {
  const points = previewPoints.value;
  if (points.length < 2) return "";

  let d = `M ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    d += ` L ${points[i].x} ${points[i].y}`;
  }
  return d;
});

// Methods
function formatDuration(ms: number): string {
  const seconds = ms / 1000;
  return `${seconds.toFixed(2)}s`;
}

function startRecording() {
  const layerId = store.selectedLayerIds[0];
  if (!layerId) return;

  recorder = new MotionRecorder(layerId, {
    speed: captureSpeed.value,
    smoothing: smoothing.value,
    minSampleInterval: 16,
  });

  isRecording.value = true;
  recordedMotion.value = null;
  emit("startCapture");
}

function stopRecording() {
  if (recorder) {
    recordedMotion.value = recorder.stop();
    recorder = null;
  }
  isRecording.value = false;
  emit("stopCapture");
}

// Called from parent when mouse moves during recording
function addSample(x: number, y: number) {
  if (recorder && isRecording.value) {
    recorder.addSample(x, y);
  }
}

// Called from parent when recording starts (first mouse down)
function initRecording(x: number, y: number) {
  if (recorder) {
    recorder.start(x, y);
  }
}

function applyMotion() {
  if (!recordedMotion.value || recordedMotion.value.samples.length < 2) return;

  const layerId = store.selectedLayerIds[0];
  if (!layerId) return;

  // Process motion: smooth -> convert -> simplify
  const smoothed = smoothMotion(recordedMotion.value, smoothing.value);
  const fps = store.fps || 30;
  const startFrame = store.currentFrame;
  const keyframes = convertMotionToKeyframes(smoothed, fps, startFrame);
  const simplified = simplifyKeyframes(keyframes, simplifyTolerance.value);

  // Apply keyframes to layer position
  simplified.forEach((kf) => {
    keyframeStore.addKeyframe(store, layerId, "transform.position", kf.value, kf.frame);
  });

  emit("apply", simplified);
  emit("close");
}

// Cleanup
onUnmounted(() => {
  if (recorder) {
    recorder.stop();
    recorder = null;
  }
});

// Reset when dialog opens
watch(
  () => props.visible,
  (visible) => {
    if (visible) {
      recordedMotion.value = null;
      isRecording.value = false;
    }
  },
);

// Expose methods for parent component
defineExpose({
  addSample,
  initRecording,
  stopRecording,
});
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
  width: 360px;
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

/* Status Section */
.status-section {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px;
  background: #151515;
  border-radius: 6px;
  margin-bottom: 16px;
}

.status-section.recording {
  background: rgba(244, 67, 54, 0.15);
  border: 1px solid rgba(244, 67, 54, 0.3);
}

.status-indicator {
  display: flex;
  align-items: center;
  gap: 8px;
}

.status-dot {
  width: 8px;
  height: 8px;
  border-radius: 50%;
  background: #666;
}

.status-section.recording .status-dot {
  background: #f44336;
  animation: pulse 1s infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.5; }
}

.status-text {
  font-size: 13px;
  color: #ccc;
}

.motion-stats {
  display: flex;
  gap: 12px;
  font-size: 12px;
  color: #888;
}

/* Settings Section */
.settings-section,
.target-section,
.preview-section {
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

/* Target Section */
.target-info {
  padding: 8px 12px;
  background: #111;
  border-radius: 4px;
  margin-bottom: 8px;
}

.layer-name {
  color: #fff;
  font-size: 13px;
}

.no-layer {
  color: #666;
  font-size: 13px;
  font-style: italic;
}

.target-property {
  display: flex;
  gap: 8px;
  font-size: 12px;
}

.property-label {
  color: #666;
}

.property-value {
  color: #8B5CF6;
}

/* Preview Section */
.motion-preview {
  width: 100%;
  height: 120px;
  background: #111;
  border-radius: 4px;
  border: 1px solid #333;
}

.preview-stats {
  display: flex;
  justify-content: space-between;
  margin-top: 8px;
  font-size: 11px;
  color: #666;
}

/* Instructions */
.instructions {
  padding: 12px;
  background: #151515;
  border-radius: 4px;
  border: 1px dashed #333;
}

.instructions p {
  margin: 0 0 8px 0;
  font-size: 12px;
  color: #888;
  line-height: 1.4;
}

.instructions p:last-child {
  margin-bottom: 0;
}

/* Footer */
.dialog-footer {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  border-top: 1px solid #333;
}

.footer-right {
  display: flex;
  gap: 8px;
}

.btn-record,
.btn-stop,
.btn-cancel,
.btn-confirm {
  padding: 8px 16px;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
  border: none;
}

.btn-record {
  background: #4CAF50;
  color: #fff;
}
.btn-record:hover:not(:disabled) { background: #5CBF60; }
.btn-record:disabled { opacity: 0.5; cursor: not-allowed; }

.btn-stop {
  background: #f44336;
  color: #fff;
}
.btn-stop:hover { background: #ff5252; }

.btn-cancel {
  background: #333;
  border: 1px solid #444;
  color: #ccc;
}
.btn-cancel:hover { background: #444; }

.btn-confirm {
  background: #8B5CF6;
  color: #fff;
}
.btn-confirm:hover:not(:disabled) { background: #9D70F9; }
.btn-confirm:disabled { opacity: 0.5; cursor: not-allowed; }
</style>
