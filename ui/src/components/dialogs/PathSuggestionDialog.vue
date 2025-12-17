<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="cancel">
      <div class="dialog-container">
        <div class="dialog-header">
          <span class="dialog-title">AI Path Suggestion</span>
          <button class="close-btn" @click="cancel">&times;</button>
        </div>

        <div class="dialog-content">
          <!-- Model Selection -->
          <div class="form-section">
            <label class="section-label">Vision Model</label>
            <div class="form-row">
              <select v-model="selectedModel" class="select-input">
                <option value="rule-based">Rule-Based (Offline)</option>
                <optgroup label="Cloud Models">
                  <option value="gpt-4o">OpenAI GPT-4o</option>
                  <option value="gpt-4v">OpenAI GPT-4V</option>
                  <option value="claude-vision">Claude Vision</option>
                </optgroup>
                <optgroup label="Local Models">
                  <option value="qwen2-vl">Qwen2-VL</option>
                  <option value="qwen-vl">Qwen-VL</option>
                  <option value="llava">LLaVA</option>
                  <option value="local-vlm">Custom Local VLM</option>
                </optgroup>
              </select>
            </div>

            <!-- API Key (for cloud models) -->
            <div v-if="requiresApiKey" class="form-row api-key-row">
              <label>API Key:</label>
              <input
                type="password"
                v-model="apiKey"
                class="text-input"
                :placeholder="apiKeyPlaceholder"
              />
              <button class="btn btn-small" @click="testConnection">Test</button>
            </div>

            <!-- Local Endpoint (for local models) -->
            <div v-if="isLocalModel" class="form-row">
              <label>Endpoint:</label>
              <input
                type="text"
                v-model="localEndpoint"
                class="text-input"
                placeholder="http://localhost:8188/api/vlm"
              />
            </div>
          </div>

          <!-- Prompt Section -->
          <div class="form-section">
            <label class="section-label">Motion Description</label>
            <div class="prompt-presets">
              <button
                v-for="preset in promptPresets"
                :key="preset.id"
                class="preset-btn"
                :class="{ active: selectedPreset === preset.id }"
                @click="selectPreset(preset)"
              >
                {{ preset.label }}
              </button>
            </div>
            <textarea
              v-model="prompt"
              class="prompt-input"
              rows="3"
              placeholder="Describe the motion you want, e.g., 'dolly in slowly' or 'orbit around the subject'"
            ></textarea>
          </div>

          <!-- Status Section -->
          <div class="form-section" v-if="status !== 'idle'">
            <div class="status-bar" :class="status">
              <span v-if="status === 'loading'" class="spinner"></span>
              <span class="status-text">{{ statusMessage }}</span>
            </div>
          </div>

          <!-- Results Section -->
          <div v-if="suggestions.length > 0" class="form-section">
            <label class="section-label">Suggested Paths</label>
            <div class="suggestions-list">
              <div
                v-for="(suggestion, index) in suggestions"
                :key="index"
                class="suggestion-item"
                :class="{ selected: selectedSuggestion === index }"
                @click="selectedSuggestion = index"
              >
                <div class="suggestion-header">
                  <span class="suggestion-type">{{ suggestion.type }}</span>
                  <span class="suggestion-confidence">
                    {{ Math.round(suggestion.confidence * 100) }}%
                  </span>
                </div>
                <div class="suggestion-description">{{ suggestion.description }}</div>
                <div class="suggestion-details">
                  <span v-if="suggestion.points">{{ suggestion.points.length }} points</span>
                  <span v-if="suggestion.duration">{{ suggestion.duration }} frames</span>
                </div>
              </div>
            </div>
          </div>

          <!-- Preview Toggle -->
          <div class="form-section preview-section">
            <label>
              <input type="checkbox" v-model="showPreview" />
              Show preview on canvas
            </label>
          </div>
        </div>

        <div class="dialog-footer">
          <div class="footer-left">
            <button
              class="btn btn-secondary"
              @click="suggestPaths"
              :disabled="status === 'loading'"
            >
              <span v-if="status === 'loading'" class="spinner-small"></span>
              {{ status === 'loading' ? 'Analyzing...' : 'Suggest Paths' }}
            </button>
          </div>
          <div class="dialog-actions">
            <button class="btn btn-secondary" @click="cancel">Cancel</button>
            <button
              class="btn btn-primary"
              @click="acceptSuggestion"
              :disabled="selectedSuggestion === null"
            >
              Accept
            </button>
          </div>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import {
  motionIntentResolver,
  motionIntentTranslator,
  type VisionModelId,
  type MotionIntentResult,
  type SceneContext,
  type SplineMotionIntent,
  type CameraMotionIntent,
} from '@/services/visionAuthoring';

interface SuggestionItem {
  type: 'camera' | 'spline' | 'particle' | 'layer';
  description: string;
  confidence: number;
  points?: Array<{ x: number; y: number; depth?: number }>;
  duration?: number;
  intent: CameraMotionIntent | SplineMotionIntent;
}

interface PromptPreset {
  id: string;
  label: string;
  prompt: string;
}

const props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<{
  (e: 'close'): void;
  (e: 'accept', result: { keyframes: any[]; splines: any[] }): void;
  (e: 'preview', suggestions: SuggestionItem[]): void;
}>();

const store = useCompositorStore();

// Model configuration
const selectedModel = ref<VisionModelId>('rule-based');
const apiKey = ref('');
const localEndpoint = ref('http://localhost:8188/api/vlm');

// Prompt
const prompt = ref('');
const selectedPreset = ref<string | null>(null);

// Status
const status = ref<'idle' | 'loading' | 'success' | 'error'>('idle');
const statusMessage = ref('');

// Results
const suggestions = ref<SuggestionItem[]>([]);
const selectedSuggestion = ref<number | null>(null);
const showPreview = ref(true);

// Prompt presets
const promptPresets: PromptPreset[] = [
  { id: 'dolly', label: 'Dolly', prompt: 'Gentle dolly in towards the subject' },
  { id: 'orbit', label: 'Orbit', prompt: 'Slow orbit around the center point' },
  { id: 'drift', label: 'Drift', prompt: 'Subtle floating drift movement' },
  { id: 'handheld', label: 'Handheld', prompt: 'Organic handheld camera shake' },
  { id: 'pan', label: 'Pan', prompt: 'Smooth horizontal pan across the scene' },
  { id: 'crane', label: 'Crane', prompt: 'Vertical crane movement' },
];

// Computed
const requiresApiKey = computed(() => {
  return ['gpt-4v', 'gpt-4o', 'claude-vision'].includes(selectedModel.value);
});

const isLocalModel = computed(() => {
  return ['qwen-vl', 'qwen2-vl', 'llava', 'local-vlm'].includes(selectedModel.value);
});

const apiKeyPlaceholder = computed(() => {
  if (selectedModel.value.startsWith('gpt-')) return 'sk-...';
  if (selectedModel.value === 'claude-vision') return 'sk-ant-...';
  return 'API Key';
});

// Methods
function selectPreset(preset: PromptPreset) {
  selectedPreset.value = preset.id;
  prompt.value = preset.prompt;
}

async function testConnection() {
  status.value = 'loading';
  statusMessage.value = 'Testing connection...';

  try {
    // Configure the resolver
    motionIntentResolver.setConfig({
      modelId: selectedModel.value,
      apiKey: apiKey.value || undefined,
      apiEndpoint: isLocalModel.value ? localEndpoint.value : undefined,
    });

    // Try a simple test
    const testContext: SceneContext = {
      compositionId: store.activeCompositionId,
      width: store.width,
      height: store.height,
      frameCount: store.frameCount,
      fps: store.fps,
      selectedLayerIds: [],
      currentFrame: store.currentFrame,
    };

    await motionIntentResolver.resolve('test', testContext, selectedModel.value);
    status.value = 'success';
    statusMessage.value = 'Connection successful!';
  } catch (error) {
    status.value = 'error';
    statusMessage.value = `Connection failed: ${error instanceof Error ? error.message : 'Unknown error'}`;
  }
}

/**
 * Load depth map image and convert to Float32Array for depth sampling
 */
async function loadDepthMapAsFloat32Array(depthMapUrl: string | null): Promise<Float32Array | undefined> {
  if (!depthMapUrl) return undefined;

  try {
    const img = new Image();
    img.crossOrigin = 'anonymous';
    await new Promise<void>((resolve, reject) => {
      img.onload = () => resolve();
      img.onerror = reject;
      img.src = depthMapUrl;
    });

    const canvas = document.createElement('canvas');
    canvas.width = img.width;
    canvas.height = img.height;
    const ctx = canvas.getContext('2d');
    if (!ctx) return undefined;

    ctx.drawImage(img, 0, 0);
    const imageData = ctx.getImageData(0, 0, img.width, img.height);

    // Convert to Float32Array (use grayscale value as depth 0-1)
    const depthArray = new Float32Array(img.width * img.height);
    for (let i = 0; i < depthArray.length; i++) {
      // Average RGB channels and normalize to 0-1
      const r = imageData.data[i * 4];
      const g = imageData.data[i * 4 + 1];
      const b = imageData.data[i * 4 + 2];
      depthArray[i] = (r + g + b) / (3 * 255);
    }

    return depthArray;
  } catch (error) {
    console.warn('[PathSuggestionDialog] Failed to load depth map:', error);
    return undefined;
  }
}

/**
 * Capture current frame from the ThreeCanvas for VLM analysis
 */
async function captureCurrentFrameImage(): Promise<ImageData | undefined> {
  try {
    // Try to get the canvas element from the viewport
    const canvas = document.querySelector('.viewport-content canvas') as HTMLCanvasElement;
    if (!canvas) return undefined;

    const ctx = canvas.getContext('2d') || canvas.getContext('webgl2') || canvas.getContext('webgl');
    if (!ctx) return undefined;

    // For WebGL context, we need to read pixels differently
    if (ctx instanceof WebGLRenderingContext || ctx instanceof WebGL2RenderingContext) {
      const width = canvas.width;
      const height = canvas.height;
      const pixels = new Uint8Array(width * height * 4);
      ctx.readPixels(0, 0, width, height, ctx.RGBA, ctx.UNSIGNED_BYTE, pixels);

      // WebGL reads bottom-to-top, so flip vertically
      const imageData = new ImageData(width, height);
      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const srcIdx = ((height - 1 - y) * width + x) * 4;
          const dstIdx = (y * width + x) * 4;
          imageData.data[dstIdx] = pixels[srcIdx];
          imageData.data[dstIdx + 1] = pixels[srcIdx + 1];
          imageData.data[dstIdx + 2] = pixels[srcIdx + 2];
          imageData.data[dstIdx + 3] = pixels[srcIdx + 3];
        }
      }
      return imageData;
    }

    // For 2D context
    if (ctx instanceof CanvasRenderingContext2D) {
      return ctx.getImageData(0, 0, canvas.width, canvas.height);
    }

    return undefined;
  } catch (error) {
    console.warn('[PathSuggestionDialog] Failed to capture frame:', error);
    return undefined;
  }
}

async function suggestPaths() {
  if (!prompt.value.trim()) {
    status.value = 'error';
    statusMessage.value = 'Please enter a motion description';
    return;
  }

  status.value = 'loading';
  statusMessage.value = 'Analyzing scene and generating suggestions...';
  suggestions.value = [];
  selectedSuggestion.value = null;

  try {
    // Configure the resolver
    motionIntentResolver.setConfig({
      modelId: selectedModel.value,
      apiKey: apiKey.value || undefined,
      apiEndpoint: isLocalModel.value ? localEndpoint.value : undefined,
    });

    // Build scene context with depth map and frame image
    const depthMap = await loadDepthMapAsFloat32Array(store.depthMap);
    const frameImage = await captureCurrentFrameImage();

    const context: SceneContext = {
      compositionId: store.activeCompositionId,
      width: store.width,
      height: store.height,
      frameCount: store.frameCount,
      fps: store.fps,
      selectedLayerIds: store.selectedLayerIds,
      currentFrame: store.currentFrame,
      depthMap,
      frameImage,
    };

    // Get suggestions from the AI
    const result = await motionIntentResolver.resolve(prompt.value, context, selectedModel.value);

    // Convert result to suggestion items
    const items: SuggestionItem[] = [];

    // Camera intents
    if (result.cameraIntents) {
      for (const intent of result.cameraIntents) {
        items.push({
          type: 'camera',
          description: `${intent.type} motion - ${intent.intensity}`,
          confidence: 0.8,
          duration: intent.durationFrames,
          intent,
        });
      }
    }

    // Spline intents
    if (result.splineIntents) {
      for (const intent of result.splineIntents) {
        items.push({
          type: 'spline',
          description: `${intent.usage} - ${intent.suggestedPoints.length} point path`,
          confidence: 0.9,
          points: intent.suggestedPoints.map(p => ({ x: p.x, y: p.y, depth: p.depth })),
          intent: intent as any,
        });
      }
    }

    suggestions.value = items;
    status.value = 'success';
    statusMessage.value = `Found ${items.length} suggestion${items.length !== 1 ? 's' : ''}`;

    // Auto-select first suggestion
    if (items.length > 0) {
      selectedSuggestion.value = 0;
    }

    // Emit preview if enabled
    if (showPreview.value) {
      emit('preview', suggestions.value);
    }
  } catch (error) {
    status.value = 'error';
    statusMessage.value = `Analysis failed: ${error instanceof Error ? error.message : 'Unknown error'}`;
  }
}

function acceptSuggestion() {
  if (selectedSuggestion.value === null) return;

  const suggestion = suggestions.value[selectedSuggestion.value];
  const result = {
    keyframes: [] as any[],
    splines: [] as any[],
  };

  // Translate the intent to keyframes
  if (suggestion.type === 'camera') {
    const translation = motionIntentTranslator.translateCameraIntent(
      suggestion.intent as CameraMotionIntent,
      store.width,
      store.height,
      store.frameCount
    );
    result.keyframes = translation.keyframeBatches;
  } else if (suggestion.type === 'spline') {
    const translation = motionIntentTranslator.translateSplineIntent(
      suggestion.intent as SplineMotionIntent,
      store.width,
      store.height
    );
    result.splines = translation.newSplines || [];
  }

  emit('accept', result);
  emit('close');
}

function cancel() {
  emit('close');
}

// Watch for preview toggle
watch(showPreview, (show) => {
  if (show && suggestions.value.length > 0) {
    emit('preview', suggestions.value);
  } else {
    emit('preview', []);
  }
});

// Keyboard handler
function handleKeydown(e: KeyboardEvent) {
  if (e.key === 'Escape') {
    cancel();
  } else if (e.key === 'Enter' && e.ctrlKey) {
    suggestPaths();
  }
}

onMounted(() => {
  window.addEventListener('keydown', handleKeydown);
});

onUnmounted(() => {
  window.removeEventListener('keydown', handleKeydown);
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
  background: linear-gradient(135deg, #3a4a6a, #2a3a5a);
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
  background: rgba(255, 255, 255, 0.1);
  color: #fff;
}

.dialog-content {
  padding: 16px;
  overflow-y: auto;
  flex: 1;
}

.form-section {
  margin-bottom: 16px;
}

.section-label {
  display: block;
  color: #aaa;
  font-size: 11px;
  font-weight: 600;
  text-transform: uppercase;
  margin-bottom: 8px;
}

.form-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.form-row > label {
  width: 80px;
  flex-shrink: 0;
  color: #888;
  font-size: 12px;
}

.text-input,
.select-input {
  padding: 6px 10px;
  border: 1px solid #444;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
  flex: 1;
}

.text-input:focus,
.select-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.api-key-row {
  margin-top: 8px;
}

/* Prompt presets */
.prompt-presets {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
  margin-bottom: 8px;
}

.preset-btn {
  padding: 4px 10px;
  border: 1px solid #444;
  background: #333;
  color: #aaa;
  border-radius: 12px;
  font-size: 11px;
  cursor: pointer;
  transition: all 0.15s;
}

.preset-btn:hover {
  background: #3a3a3a;
  color: #e0e0e0;
}

.preset-btn.active {
  background: #3a5070;
  border-color: #4a90d9;
  color: #fff;
}

.prompt-input {
  width: 100%;
  padding: 10px;
  border: 1px solid #444;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
  font-family: inherit;
  resize: vertical;
}

.prompt-input:focus {
  outline: none;
  border-color: #4a90d9;
}

/* Status bar */
.status-bar {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  border-radius: 4px;
  font-size: 12px;
}

.status-bar.loading {
  background: rgba(74, 144, 217, 0.2);
  color: #4a90d9;
}

.status-bar.success {
  background: rgba(74, 177, 74, 0.2);
  color: #4ab14a;
}

.status-bar.error {
  background: rgba(217, 74, 74, 0.2);
  color: #d94a4a;
}

.spinner {
  width: 14px;
  height: 14px;
  border: 2px solid transparent;
  border-top-color: currentColor;
  border-radius: 50%;
  animation: spin 0.8s linear infinite;
}

.spinner-small {
  width: 12px;
  height: 12px;
  border: 2px solid transparent;
  border-top-color: currentColor;
  border-radius: 50%;
  animation: spin 0.8s linear infinite;
  display: inline-block;
  margin-right: 6px;
}

@keyframes spin {
  to { transform: rotate(360deg); }
}

/* Suggestions list */
.suggestions-list {
  display: flex;
  flex-direction: column;
  gap: 8px;
  max-height: 200px;
  overflow-y: auto;
}

.suggestion-item {
  padding: 10px 12px;
  border: 1px solid #444;
  background: #333;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.15s;
}

.suggestion-item:hover {
  background: #3a3a3a;
  border-color: #555;
}

.suggestion-item.selected {
  background: #3a5070;
  border-color: #4a90d9;
}

.suggestion-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 4px;
}

.suggestion-type {
  font-size: 11px;
  font-weight: 600;
  text-transform: uppercase;
  color: #4a90d9;
}

.suggestion-confidence {
  font-size: 10px;
  color: #888;
  background: rgba(0, 0, 0, 0.3);
  padding: 2px 6px;
  border-radius: 8px;
}

.suggestion-description {
  font-size: 12px;
  color: #e0e0e0;
  margin-bottom: 4px;
}

.suggestion-details {
  display: flex;
  gap: 12px;
  font-size: 10px;
  color: #666;
}

/* Preview section */
.preview-section {
  display: flex;
  align-items: center;
  gap: 8px;
  color: #888;
  font-size: 12px;
}

.preview-section input {
  margin: 0;
}

/* Footer */
.dialog-footer {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  background: #333;
  border-top: 1px solid #444;
  border-radius: 0 0 6px 6px;
}

.footer-left {
  display: flex;
  gap: 8px;
}

.dialog-actions {
  display: flex;
  gap: 8px;
}

.btn {
  padding: 8px 16px;
  border: none;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
}

.btn-small {
  padding: 4px 10px;
  font-size: 11px;
}

.btn-secondary {
  background: #444;
  color: #e0e0e0;
}

.btn-secondary:hover:not(:disabled) {
  background: #555;
}

.btn-primary {
  background: #4a90d9;
  color: #fff;
}

.btn-primary:hover:not(:disabled) {
  background: #5a9fe9;
}

.btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}
</style>
