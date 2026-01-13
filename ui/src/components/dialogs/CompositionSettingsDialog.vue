<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="cancel">
      <div class="dialog-container">
        <div class="dialog-header">
          <span class="dialog-title">Composition Settings</span>
          <button class="close-btn" @click="cancel">&times;</button>
        </div>

        <div class="dialog-content">
          <!-- Composition Name -->
          <div class="form-row">
            <label>Composition Name:</label>
            <input
              type="text"
              v-model="settings.name"
              class="text-input full-width"
            />
          </div>

          <!-- Tabs -->
          <div class="tabs">
            <button
              :class="{ active: activeTab === 'basic' }"
              @click="activeTab = 'basic'"
            >Basic</button>
            <button
              :class="{ active: activeTab === 'advanced' }"
              @click="activeTab = 'advanced'"
            >Advanced</button>
          </div>

          <!-- Basic Tab -->
          <div v-if="activeTab === 'basic'" class="tab-content">
            <!-- Preset -->
            <div class="form-row">
              <label>Preset:</label>
              <select v-model="selectedPreset" @change="applyPreset" class="select-input">
                <option value="custom">Custom</option>
                <optgroup label="Video">
                  <option value="1080p30">HD 1080p 30fps (1920x1080)</option>
                  <option value="1080p60">HD 1080p 60fps (1920x1080)</option>
                  <option value="720p30">HD 720p 30fps (1280x720)</option>
                  <option value="4k30">4K UHD 30fps (3840x2160)</option>
                </optgroup>
                <optgroup label="Social Media">
                  <option value="instagram_square">Instagram Square (1080x1080)</option>
                  <option value="instagram_story">Instagram Story (1080x1920)</option>
                  <option value="tiktok">TikTok/Reels (1080x1920)</option>
                  <option value="youtube_short">YouTube Short (1080x1920)</option>
                </optgroup>
                <optgroup label="AI Video (ComfyUI)">
                  <option value="sd15_512">SD 1.5 (512x512)</option>
                  <option value="sd15_768">SD 1.5 (768x512)</option>
                  <option value="sdxl_1024">SDXL (1024x1024)</option>
                  <option value="wan_480p">Wan 2.1 480p (832x480)</option>
                  <option value="wan_720p">Wan 2.1 720p (1280x720)</option>
                  <option value="wan22_480p">Wan 2.2 480p (832x480)</option>
                  <option value="wan22_720p">Wan 2.2 720p (1280x720)</option>
                  <option value="hunyuan_720p">Hunyuan 720p (1280x720)</option>
                  <option value="hunyuan_540p">Hunyuan 540p (960x540)</option>
                </optgroup>
              </select>
              <div v-if="isAIPreset" class="help-text ai-help">
                <span class="info-icon">ℹ</span>
                AI video models require <strong>4n+1</strong> frames (17, 33, 49, 65, 81...) at 16fps.
                Dimensions must be divisible by 8.
              </div>
            </div>

            <!-- Width / Height -->
            <div class="form-row dimensions-row">
              <div class="dimension-group">
                <label>Width:</label>
                <input
                  type="number"
                  v-model.number="settings.width"
                  :step="8"
                  min="64"
                  max="8192"
                  class="number-input"
                  @change="onDimensionChange('width')"
                />
                <span class="unit">px</span>
              </div>
              <button
                class="lock-btn"
                :class="{ locked: lockAspectRatio }"
                @click="lockAspectRatio = !lockAspectRatio"
                title="Lock Aspect Ratio"
              >
                {{ lockAspectRatio ? '🔒' : '🔓' }}
              </button>
              <div class="dimension-group">
                <label>Height:</label>
                <input
                  type="number"
                  v-model.number="settings.height"
                  :step="8"
                  min="64"
                  max="8192"
                  class="number-input"
                  @change="onDimensionChange('height')"
                />
                <span class="unit">px</span>
              </div>
            </div>

            <!-- Pixel Aspect Ratio - Always 1:1 for digital video -->
            <div class="form-row">
              <label>Pixel Aspect Ratio:</label>
              <span class="fixed-value">Square Pixels (1:1)</span>
              <span class="aspect-info">Frame Aspect Ratio: {{ frameAspectRatio }}</span>
            </div>

            <!-- Frame Rate -->
            <div class="form-row">
              <label>Frame Rate:</label>
              <select v-model.number="settings.fps" class="select-input short">
                <option :value="8">8</option>
                <option :value="12">12</option>
                <option :value="15">15</option>
                <option :value="16">16</option>
                <option :value="23.976">23.976</option>
                <option :value="24">24</option>
                <option :value="25">25</option>
                <option :value="29.97">29.97</option>
                <option :value="30">30</option>
                <option :value="50">50</option>
                <option :value="59.94">59.94</option>
                <option :value="60">60</option>
              </select>
              <span class="unit">frames per second</span>
            </div>

            <!-- Resolution -->
            <div class="form-row">
              <label>Resolution:</label>
              <select v-model="settings.resolution" class="select-input short">
                <option value="full">Full</option>
                <option value="half">Half</option>
                <option value="third">Third</option>
                <option value="quarter">Quarter</option>
              </select>
              <span class="resolution-info">{{ resolutionInfo }}</span>
            </div>

            <!-- Duration Preset (for AI models) -->
            <div class="form-row">
              <label>Duration Preset:</label>
              <select v-model="selectedDurationPreset" @change="applyDurationPreset" class="select-input">
                <option value="custom">Custom</option>
                <optgroup label="Wan/AI Models (16fps, 4n+1)">
                  <option v-for="preset in WAN_DURATION_PRESETS" :key="preset.frameCount" :value="preset.frameCount">
                    {{ preset.label }} ({{ preset.frameCount }} frames){{ preset.isDefault ? ' ★' : '' }}
                  </option>
                </optgroup>
              </select>
            </div>

            <!-- Duration -->
            <div class="form-row">
              <label>Duration:</label>
              <div class="duration-inputs">
                <input
                  type="text"
                  v-model="durationTimecode"
                  class="timecode-input"
                  placeholder="00:00:00:00"
                  @blur="parseDuration"
                />
                <span class="duration-helper">
                  {{ settings.frameCount }} frames = {{ durationSeconds.toFixed(2) }}s
                </span>
              </div>
            </div>

            <!-- Frame count warning for AI models -->
            <div v-if="settings.fps === 16 && !isValidFrameCount" class="form-row warning-row">
              <span class="warning-icon">⚠️</span>
              <span class="warning-text">
                Frame count {{ settings.frameCount }} doesn't follow 4n+1 pattern.
                Nearest valid: {{ nearestValidFrameCount }} frames.
              </span>
            </div>

            <!-- Background Color -->
            <div class="form-row">
              <label>Background Color:</label>
              <div class="color-picker-row">
                <input
                  type="color"
                  v-model="settings.backgroundColor"
                  class="color-input"
                />
                <span class="color-label">{{ settings.backgroundColor }}</span>
              </div>
            </div>
          </div>

          <!-- Advanced Tab -->
          <div v-if="activeTab === 'advanced'" class="tab-content">
            <div class="form-row">
              <label>
                <input type="checkbox" v-model="settings.autoResizeToContent" />
                Auto-resize composition when importing video
              </label>
            </div>

            <div class="form-row">
              <label>Start Timecode:</label>
              <input
                type="text"
                v-model="settings.startTimecode"
                class="timecode-input"
                placeholder="00:00:00:00"
              />
            </div>

            <div class="form-row">
              <label>Motion Blur:</label>
              <div class="motion-blur-settings">
                <label>
                  <input type="checkbox" v-model="settings.motionBlurEnabled" />
                  Enable Motion Blur
                </label>
                <div v-if="settings.motionBlurEnabled" class="motion-blur-params">
                  <div class="param-row">
                    <label>Shutter Angle:</label>
                    <input
                      type="number"
                      v-model.number="settings.shutterAngle"
                      min="0"
                      max="720"
                      class="number-input short"
                    />
                    <span class="unit">°</span>
                  </div>
                  <div class="param-row">
                    <label>Shutter Phase:</label>
                    <input
                      type="number"
                      v-model.number="settings.shutterPhase"
                      min="-360"
                      max="360"
                      class="number-input short"
                    />
                    <span class="unit">°</span>
                  </div>
                </div>
              </div>
            </div>
          </div>
        </div>

        <div class="dialog-footer">
          <div class="preview-toggle">
            <label>
              <input type="checkbox" v-model="previewChanges" />
              Preview
            </label>
          </div>
          <div class="dialog-actions">
            <button class="btn btn-secondary" @click="cancel">Cancel</button>
            <button class="btn btn-primary" @click="confirm">OK</button>
          </div>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref, watch } from "vue";
import {
  isValidWanFrameCount,
  WAN_DURATION_PRESETS,
} from "@/config/exportPresets";
import { useCompositorStore } from "@/stores/compositorStore";

interface CompositionDialogSettings {
  name: string;
  width: number;
  height: number;
  pixelAspectRatio: number;
  fps: number;
  frameCount: number;
  resolution: "full" | "half" | "third" | "quarter";
  backgroundColor: string;
  autoResizeToContent: boolean;
  startTimecode: string;
  motionBlurEnabled: boolean;
  shutterAngle: number;
  shutterPhase: number;
}

const props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<{
  (e: "close"): void;
  (e: "confirm", settings: CompositionDialogSettings): void;
}>();

const store = useCompositorStore();

// State
const activeTab = ref<"basic" | "advanced">("basic");
const selectedPreset = ref("custom");
const selectedDurationPreset = ref<string | number>("custom");
const lockAspectRatio = ref(false);
const aspectRatio = ref(16 / 9);
const previewChanges = ref(false);

const settings = ref<CompositionDialogSettings>({
  name: "Main Comp",
  width: 832,
  height: 480,
  pixelAspectRatio: 1,
  fps: 16,
  frameCount: 81,
  resolution: "full",
  backgroundColor: "#000000",
  autoResizeToContent: true,
  startTimecode: "00:00:00:00",
  motionBlurEnabled: false,
  shutterAngle: 180,
  shutterPhase: -90,
});

// Computed
const frameAspectRatio = computed(() => {
  const ratio =
    (settings.value.width / settings.value.height) *
    settings.value.pixelAspectRatio;
  // Common ratios
  if (Math.abs(ratio - 16 / 9) < 0.01) return "16:9 (1.78)";
  if (Math.abs(ratio - 4 / 3) < 0.01) return "4:3 (1.33)";
  if (Math.abs(ratio - 1) < 0.01) return "1:1 (1.0)";
  if (Math.abs(ratio - 9 / 16) < 0.01) return "9:16 (0.56)";
  if (Math.abs(ratio - 21 / 9) < 0.01) return "21:9 (2.33)";
  return `${ratio.toFixed(2)}`;
});

const durationSeconds = computed(() => {
  return settings.value.frameCount / settings.value.fps;
});

const durationTimecode = ref("00:00:10:00");

// Frame count validation for 4n+1 pattern (Wan/AI models)
const isValidFrameCount = computed(() => {
  return isValidWanFrameCount(settings.value.frameCount);
});

const nearestValidFrameCount = computed(() => {
  const n = Math.round((settings.value.frameCount - 1) / 4);
  return n * 4 + 1;
});

const resolutionInfo = computed(() => {
  const divisors = { full: 1, half: 2, third: 3, quarter: 4 };
  const d = divisors[settings.value.resolution];
  const w = Math.floor(settings.value.width / d);
  const h = Math.floor(settings.value.height / d);
  const mb = ((w * h * 4) / (1024 * 1024)).toFixed(1);
  return `${w} x ${h}, ${mb} MB per 8bpc frame`;
});

const isAIPreset = computed(() => {
  const aiPrefixes = ["sd15_", "sdxl_", "wan_", "wan22_", "hunyuan_"];
  return aiPrefixes.some((prefix) => selectedPreset.value.startsWith(prefix));
});

// Presets
const presets: Record<string, Partial<CompositionDialogSettings>> = {
  "1080p30": { width: 1920, height: 1080, fps: 30, frameCount: 300 },
  "1080p60": { width: 1920, height: 1080, fps: 60, frameCount: 600 },
  "720p30": { width: 1280, height: 720, fps: 30, frameCount: 300 },
  "4k30": { width: 3840, height: 2160, fps: 30, frameCount: 300 },
  instagram_square: { width: 1080, height: 1080, fps: 30, frameCount: 300 },
  instagram_story: { width: 1080, height: 1920, fps: 30, frameCount: 300 },
  tiktok: { width: 1080, height: 1920, fps: 30, frameCount: 300 },
  youtube_short: { width: 1080, height: 1920, fps: 60, frameCount: 600 },
  sd15_512: { width: 512, height: 512, fps: 8, frameCount: 16 },
  sd15_768: { width: 768, height: 512, fps: 8, frameCount: 16 },
  sdxl_1024: { width: 1024, height: 1024, fps: 8, frameCount: 16 },
  wan_480p: { width: 832, height: 480, fps: 16, frameCount: 81 },
  wan_720p: { width: 1280, height: 720, fps: 16, frameCount: 81 },
  wan22_480p: { width: 832, height: 480, fps: 16, frameCount: 81 },
  wan22_720p: { width: 1280, height: 720, fps: 16, frameCount: 81 },
  hunyuan_720p: { width: 1280, height: 720, fps: 24, frameCount: 96 },
  hunyuan_540p: { width: 960, height: 540, fps: 24, frameCount: 96 },
};

// Methods
function applyPreset() {
  const preset = presets[selectedPreset.value];
  if (preset) {
    if (preset.width) settings.value.width = preset.width;
    if (preset.height) settings.value.height = preset.height;
    if (preset.fps) settings.value.fps = preset.fps;
    if (preset.frameCount) settings.value.frameCount = preset.frameCount;
    aspectRatio.value = settings.value.width / settings.value.height;
    updateDurationTimecode();
    // Update duration preset selection if it matches a Wan preset
    updateDurationPresetSelection();
  }
}

function applyDurationPreset() {
  if (selectedDurationPreset.value === "custom") return;

  const frameCount = Number(selectedDurationPreset.value);
  const preset = WAN_DURATION_PRESETS.find((p) => p.frameCount === frameCount);

  if (preset) {
    settings.value.frameCount = preset.frameCount;
    settings.value.fps = 16; // Wan models use 16fps
    updateDurationTimecode();
  }
}

function updateDurationPresetSelection() {
  // Check if current frameCount matches a Wan preset
  const matchingPreset = WAN_DURATION_PRESETS.find(
    (p) => p.frameCount === settings.value.frameCount,
  );
  if (matchingPreset && settings.value.fps === 16) {
    selectedDurationPreset.value = matchingPreset.frameCount;
  } else {
    selectedDurationPreset.value = "custom";
  }
}

function onDimensionChange(changed: "width" | "height") {
  // Ensure divisible by 8
  settings.value.width = Math.round(settings.value.width / 8) * 8;
  settings.value.height = Math.round(settings.value.height / 8) * 8;

  if (lockAspectRatio.value) {
    if (changed === "width") {
      settings.value.height =
        Math.round(settings.value.width / aspectRatio.value / 8) * 8;
    } else {
      settings.value.width =
        Math.round((settings.value.height * aspectRatio.value) / 8) * 8;
    }
  } else {
    aspectRatio.value = settings.value.width / settings.value.height;
  }

  selectedPreset.value = "custom";
}

function parseDuration() {
  // Parse timecode format HH:MM:SS:FF
  const parts = durationTimecode.value
    .split(":")
    .map((p) => parseInt(p, 10) || 0);
  if (parts.length === 4) {
    const [hours, minutes, seconds, frames] = parts;
    const totalSeconds = hours * 3600 + minutes * 60 + seconds;
    settings.value.frameCount =
      Math.round(totalSeconds * settings.value.fps) + frames;
  } else if (parts.length === 1) {
    // Just frames
    settings.value.frameCount = parts[0];
  }
}

function updateDurationTimecode() {
  const totalFrames = settings.value.frameCount;
  const fps = settings.value.fps;
  const totalSeconds = Math.floor(totalFrames / fps);
  const frames = totalFrames % Math.round(fps);
  const hours = Math.floor(totalSeconds / 3600);
  const minutes = Math.floor((totalSeconds % 3600) / 60);
  const seconds = totalSeconds % 60;
  durationTimecode.value = `${pad(hours)}:${pad(minutes)}:${pad(seconds)}:${pad(frames)}`;
}

function pad(n: number): string {
  return n.toString().padStart(2, "0");
}

function loadCurrentSettings() {
  // Get active composition's name, not project meta name
  const activeComp = store.activeComposition;
  settings.value = {
    name: activeComp?.name || "Main Comp",
    width: store.width,
    height: store.height,
    pixelAspectRatio: 1,
    fps: store.fps,
    frameCount: store.frameCount,
    resolution: "full",
    backgroundColor: activeComp?.settings.backgroundColor || "#000000",
    autoResizeToContent: activeComp?.settings.autoResizeToContent ?? true,
    startTimecode: "00:00:00:00",
    motionBlurEnabled: false,
    shutterAngle: 180,
    shutterPhase: -90,
  };
  aspectRatio.value = settings.value.width / settings.value.height;
  updateDurationTimecode();
  updateDurationPresetSelection();
}

function cancel() {
  emit("close");
}

function confirm() {
  emit("confirm", { ...settings.value });
  emit("close");
}

// Keyboard handler
function handleKeydown(e: KeyboardEvent) {
  if (e.key === "Escape") {
    cancel();
  } else if (e.key === "Enter" && !e.shiftKey) {
    confirm();
  }
}

// Watch for visibility changes to load current settings
watch(
  () => props.visible,
  (visible) => {
    if (visible) {
      loadCurrentSettings();
    }
  },
);

// Preview changes
watch(
  settings,
  () => {
    if (previewChanges.value && props.visible) {
      // Apply changes temporarily for preview
      store.resizeComposition(
        settings.value.width,
        settings.value.height,
        settings.value.frameCount,
      );
    }
  },
  { deep: true },
);

onMounted(() => {
  window.addEventListener("keydown", handleKeydown);
});

onUnmounted(() => {
  window.removeEventListener("keydown", handleKeydown);
});
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.dialog-container {
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 6px;
  width: 520px;
  max-height: 90vh;
  display: flex;
  flex-direction: column;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  background: #333;
  border-bottom: 1px solid #444;
  border-radius: 6px 6px 0 0;
}

.dialog-title {
  font-size: 14px;
  font-weight: 600;
  color: #e0e0e0;
}

.close-btn {
  width: 24px;
  height: 24px;
  border: none;
  background: transparent;
  color: #888;
  font-size: 18px;
  cursor: pointer;
  border-radius: 4px;
}

.close-btn:hover {
  background: #444;
  color: #fff;
}

.dialog-content {
  padding: 16px;
  overflow-y: auto;
  flex: 1;
}

.tabs {
  display: flex;
  gap: 4px;
  margin-bottom: 16px;
  border-bottom: 1px solid #444;
  padding-bottom: 8px;
}

.tabs button {
  padding: 6px 16px;
  border: none;
  background: transparent;
  color: #888;
  font-size: 12px;
  cursor: pointer;
  border-radius: 4px 4px 0 0;
}

.tabs button:hover {
  color: #e0e0e0;
}

.tabs button.active {
  background: #3a5070;
  color: #fff;
}

.tab-content {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.form-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.form-row > label:first-child {
  width: 130px;
  flex-shrink: 0;
  color: #aaa;
  font-size: 12px;
}

.text-input,
.select-input,
.number-input,
.timecode-input {
  padding: 6px 10px;
  border: 1px solid #444;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
}

.text-input:focus,
.select-input:focus,
.number-input:focus,
.timecode-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.full-width {
  flex: 1;
}

.select-input {
  min-width: 200px;
}

.select-input.short {
  min-width: 100px;
}

.number-input {
  width: 80px;
}

.number-input.short {
  width: 60px;
}

.timecode-input {
  width: 100px;
  font-family: monospace;
}

.unit {
  color: #666;
  font-size: 13px;
}

.dimensions-row {
  display: flex;
  align-items: center;
  gap: 12px;
}

.dimension-group {
  display: flex;
  align-items: center;
  gap: 6px;
}

.dimension-group label {
  width: auto !important;
  color: #aaa;
  font-size: 12px;
}

.lock-btn {
  width: 28px;
  height: 28px;
  border: 1px solid #444;
  background: #333;
  border-radius: 4px;
  cursor: pointer;
  font-size: 14px;
}

.lock-btn.locked {
  background: #3a5070;
  border-color: #4a90d9;
}

.fixed-value {
  color: #aaa;
  font-size: 13px;
  padding: 6px 12px;
  background: #2a2a2a;
  border-radius: 4px;
}

.aspect-info,
.resolution-info {
  color: #666;
  font-size: 13px;
  margin-left: auto;
}

.duration-inputs {
  display: flex;
  align-items: center;
  gap: 12px;
  flex: 1;
}

.duration-helper {
  color: #666;
  font-size: 13px;
}

.color-picker-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.color-input {
  width: 40px;
  height: 28px;
  padding: 0;
  border: 1px solid #444;
  border-radius: 4px;
  cursor: pointer;
}

.color-label {
  color: #888;
  font-size: 13px;
  font-family: monospace;
}

.motion-blur-settings {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.motion-blur-params {
  margin-left: 20px;
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.param-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.param-row label {
  width: 100px;
  color: #888;
  font-size: 13px;
}

.dialog-footer {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  background: #333;
  border-top: 1px solid #444;
  border-radius: 0 0 6px 6px;
}

.preview-toggle {
  display: flex;
  align-items: center;
  gap: 6px;
  color: #888;
  font-size: 12px;
}

.preview-toggle input {
  margin: 0;
}

.dialog-actions {
  display: flex;
  gap: 8px;
}

.btn {
  padding: 8px 20px;
  border: none;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.btn-secondary {
  background: #444;
  color: #e0e0e0;
}

.btn-secondary:hover {
  background: #555;
}

.btn-primary {
  background: #4a90d9;
  color: #fff;
}

.btn-primary:hover {
  background: #5a9fe9;
}

/* Warning row for invalid frame counts */
.warning-row {
  background: rgba(255, 152, 0, 0.1);
  border: 1px solid rgba(255, 152, 0, 0.3);
  border-radius: 4px;
  padding: 8px 12px;
  margin-top: -4px;
}

.warning-icon {
  font-size: 14px;
}

.warning-text {
  color: #ffb74d;
  font-size: 11px;
}

/* AI preset help text */
.help-text {
  font-size: 11px;
  color: var(--lattice-text-muted, #888);
  margin-top: 8px;
  padding: 8px 12px;
  background: rgba(139, 92, 246, 0.1);
  border: 1px solid rgba(139, 92, 246, 0.2);
  border-radius: 4px;
}

.ai-help {
  display: flex;
  align-items: flex-start;
  gap: 8px;
}

.info-icon {
  color: var(--lattice-accent, #8B5CF6);
  font-size: 14px;
  flex-shrink: 0;
}

.help-text strong {
  color: var(--lattice-accent, #8B5CF6);
}
</style>
