<template>
  <div class="audio-properties">
    <!-- Peak Detection Settings -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('peaks')">
        <i class="pi" :class="expandedSections.has('peaks') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Peak Detection</span>
      </div>
      <div v-if="expandedSections.has('peaks')" class="section-content">
        <div class="property-row">
          <label>Threshold</label>
          <input
            type="range"
            v-model.number="peakConfig.threshold"
            min="0"
            max="1"
            step="0.01"
          />
          <span class="value-display">{{ peakConfig.threshold.toFixed(2) }}</span>
        </div>
        <div class="property-row">
          <label>Min Peak Distance</label>
          <input
            type="range"
            v-model.number="peakConfig.minPeaksDistance"
            min="1"
            max="60"
            step="1"
          />
          <span class="value-display">{{ peakConfig.minPeaksDistance }} frames</span>
        </div>
        <div class="property-row">
          <label>Multiply</label>
          <input
            type="range"
            v-model.number="peakConfig.multiply"
            min="0.1"
            max="5"
            step="0.1"
          />
          <span class="value-display">{{ peakConfig.multiply.toFixed(1) }}x</span>
        </div>
        <div class="property-row">
          <button class="action-btn" @click="detectPeaks">
            <i class="pi pi-bolt" />
            Detect Peaks
          </button>
          <span v-if="peakData" class="peak-count">
            {{ peakData.count }} peaks found
          </span>
        </div>
      </div>
    </div>

    <!-- Audio Mappings -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('mappings')">
        <i class="pi" :class="expandedSections.has('mappings') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Audio Mappings</span>
        <span class="mapping-count">{{ mappings.length }}</span>
      </div>
      <div v-if="expandedSections.has('mappings')" class="section-content">
        <button class="action-btn add-mapping-btn" @click="addMapping">
          <i class="pi pi-plus" />
          Add Mapping
        </button>

        <div v-for="mapping in mappings" :key="mapping.id" class="mapping-item">
          <div class="mapping-header">
            <label class="mapping-enabled">
              <input type="checkbox" v-model="mapping.enabled" />
            </label>
            <span class="mapping-name">
              {{ getFeatureDisplayName(mapping.feature) }} → {{ getTargetDisplayName(mapping.target) }}
            </span>
            <button class="delete-btn" @click="removeMapping(mapping.id)">
              <i class="pi pi-times" />
            </button>
          </div>

          <div v-if="expandedMappings.has(mapping.id)" class="mapping-details">
            <!-- Feature Selection (Categorized) -->
            <div class="property-row">
              <label>Feature</label>
              <select v-model="mapping.feature">
                <optgroup v-for="(feats, category) in featuresByCategory" :key="category" :label="category">
                  <option v-for="feat in feats" :key="feat" :value="feat">
                    {{ getFeatureDisplayName(feat) }}
                  </option>
                </optgroup>
              </select>
            </div>

            <!-- Target Selection -->
            <div class="property-row">
              <label>Target</label>
              <select v-model="mapping.target">
                <optgroup v-for="(targets, category) in targetsByCategory" :key="category" :label="category">
                  <option v-for="target in targets" :key="target" :value="target">
                    {{ getTargetDisplayName(target) }}
                  </option>
                </optgroup>
              </select>
            </div>

            <!-- Target Layer Selection -->
            <div class="property-row">
              <label>Layer</label>
              <select v-model="mapping.targetLayerId" @change="onTargetLayerChange(mapping)">
                <option :value="undefined">All Layers</option>
                <option v-for="layer in allLayers" :key="layer.id" :value="layer.id">
                  {{ layer.name }}
                </option>
              </select>
            </div>

            <!-- Target Emitter Selection (only for particle layers) -->
            <div class="property-row" v-if="isParticleLayer(mapping.targetLayerId)">
              <label>Emitter</label>
              <select v-model="mapping.targetEmitterId">
                <option :value="undefined">All Emitters</option>
                <option v-for="emitter in getEmittersForLayer(mapping.targetLayerId)" :key="emitter.id" :value="emitter.id">
                  {{ emitter.name || emitter.id }}
                </option>
              </select>
            </div>

            <div class="subsection-header">Basic Controls</div>

            <div class="property-row">
              <label>Sensitivity</label>
              <input
                type="range"
                v-model.number="mapping.sensitivity"
                min="0.1"
                max="5"
                step="0.1"
              />
              <span class="value-display">{{ mapping.sensitivity.toFixed(1) }}x</span>
            </div>

            <div class="property-row">
              <label>Threshold</label>
              <input
                type="range"
                v-model.number="mapping.threshold"
                min="0"
                max="1"
                step="0.01"
              />
              <span class="value-display">{{ mapping.threshold.toFixed(2) }}</span>
            </div>

            <div class="property-row">
              <label>Smoothing</label>
              <input
                type="range"
                v-model.number="mapping.smoothing"
                min="0"
                max="0.99"
                step="0.01"
              />
              <span class="value-display">{{ mapping.smoothing.toFixed(2) }}</span>
            </div>

            <div class="property-row">
              <label>Min/Max</label>
              <input
                type="number"
                v-model.number="mapping.min"
                step="0.1"
                class="small-input"
              />
              <span class="separator">-</span>
              <input
                type="number"
                v-model.number="mapping.max"
                step="0.1"
                class="small-input"
              />
            </div>

            <div class="subsection-header">ATI-Style Effects</div>

            <!-- Amplitude Curve (Expander/Compressor) -->
            <div class="property-row">
              <label title="&gt;1 = expander (emphasize loud), &lt;1 = compressor (boost quiet)">Amp Curve</label>
              <input
                type="range"
                v-model.number="mapping.amplitudeCurve"
                min="0.1"
                max="4"
                step="0.1"
              />
              <span class="value-display">{{ mapping.amplitudeCurve?.toFixed(1) || '1.0' }}</span>
            </div>

            <!-- Release Envelope -->
            <div class="property-row">
              <label title="How slowly the value decays after a peak (0=instant, 1=slow)">Release</label>
              <input
                type="range"
                v-model.number="mapping.release"
                min="0"
                max="1"
                step="0.01"
              />
              <span class="value-display">{{ mapping.release?.toFixed(2) || '0.50' }}</span>
            </div>

            <!-- Value Curve Shaping -->
            <div class="property-row">
              <label>Curve</label>
              <select v-model="mapping.curve" class="curve-select">
                <option value="linear">Linear</option>
                <option value="exponential">Exponential</option>
                <option value="logarithmic">Logarithmic</option>
                <option value="smoothstep">Smoothstep</option>
                <option value="bounce">Bounce</option>
              </select>
            </div>

            <div class="subsection-header">Beat Response</div>

            <!-- Beat Response Mode -->
            <div class="property-row">
              <label>On Beat</label>
              <select v-model="mapping.beatResponse" class="beat-select">
                <option value="none">None</option>
                <option value="flip">Flip (reverse direction)</option>
                <option value="pulse">Pulse (spike to max)</option>
                <option value="toggle">Toggle (0/1 switch)</option>
              </select>
            </div>

            <!-- Beat Threshold -->
            <div class="property-row" v-if="mapping.beatResponse !== 'none'">
              <label title="Lower = more sensitive to quieter beats">Beat Sens.</label>
              <input
                type="range"
                v-model.number="mapping.beatThreshold"
                min="0.01"
                max="1"
                step="0.01"
              />
              <span class="value-display">{{ mapping.beatThreshold?.toFixed(2) || '0.50' }}</span>
            </div>

            <div class="property-row checkbox-row">
              <label>
                <input type="checkbox" v-model="mapping.invert" />
                Invert Output
              </label>
            </div>
          </div>

          <button
            class="expand-btn"
            @click="toggleMappingExpanded(mapping.id)"
          >
            <i class="pi" :class="expandedMappings.has(mapping.id) ? 'pi-chevron-up' : 'pi-chevron-down'" />
          </button>
        </div>
      </div>
    </div>

    <!-- Feature Visualizer -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('visualizer')">
        <i class="pi" :class="expandedSections.has('visualizer') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Feature Visualizer</span>
      </div>
      <div v-if="expandedSections.has('visualizer')" class="section-content">
        <div class="property-row">
          <label>Feature</label>
          <select v-model="visualizerFeature">
            <option v-for="feat in allFeatures" :key="feat" :value="feat">
              {{ getFeatureDisplayName(feat) }}
            </option>
          </select>
        </div>
        <div class="visualizer-canvas-container">
          <canvas
            ref="visualizerCanvas"
            class="visualizer-canvas"
            width="240"
            height="60"
          />
          <div
            class="visualizer-playhead"
            :style="{ left: `${playheadPosition}%` }"
          />
        </div>
        <div class="visualizer-value">
          Current: {{ currentFeatureValue.toFixed(3) }}
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, ref, watch } from "vue";
import {
  detectPeaks as detectAudioPeaks,
  getFeatureAtFrame,
  type PeakData,
  type PeakDetectionConfig,
} from "@/services/audioFeatures";
import {
  type AudioFeature,
  type AudioMapping,
  createDefaultAudioMapping,
  getAllFeatures,
  getFeaturesByCategory,
  getTargetsByCategory,
  getFeatureDisplayName,
  getTargetDisplayName,
} from "@/services/audioReactiveMapping";
import { useCompositorStore } from "@/stores/compositorStore";
import { useAudioStore } from "@/stores/audioStore";

const store = useCompositorStore();
const audioStore = useAudioStore();

// UI State
const expandedSections = ref(new Set(["peaks", "mappings"]));
const expandedMappings = ref(new Set<string>());

// Peak detection config
const peakConfig = ref<PeakDetectionConfig>({
  threshold: 0.3,
  minPeaksDistance: 10,
  multiply: 1.0,
});

// Peak data
const peakData = ref<PeakData | null>(null);

// Audio mappings
const mappings = ref<AudioMapping[]>([]);

// Visualizer state
const visualizerFeature = ref<AudioFeature>("amplitude");
const visualizerCanvas = ref<HTMLCanvasElement | null>(null);

// Computed
const allFeatures = computed(() => getAllFeatures());
const featuresByCategory = computed(() => getFeaturesByCategory());
const targetsByCategory = computed(() => getTargetsByCategory());

const playheadPosition = computed(
  () => (store.currentFrame / store.frameCount) * 100,
);

const currentFeatureValue = computed(() => {
  if (!audioStore.audioAnalysis) return 0;
  return getFeatureAtFrame(
    audioStore.audioAnalysis,
    visualizerFeature.value,
    store.currentFrame,
  );
});

// Layer and emitter selection helpers for per-emitter audio targeting UI
const allLayers = computed(() => store.layers);

function isParticleLayer(layerId: string | undefined): boolean {
  if (!layerId) return false;
  const layer = store.layers.find((l) => l.id === layerId);
  return layer?.type === "particles";
}

function getEmittersForLayer(
  layerId: string | undefined,
): Array<{ id: string; name: string }> {
  if (!layerId) return [];
  const layer = store.layers.find((l) => l.id === layerId);
  if (!layer || layer.type !== "particles") return [];
  // ParticleLayerData has emitters array with id and name
  const data = layer.data as { emitters?: Array<{ id: string; name: string }> };
  return data?.emitters || [];
}

function onTargetLayerChange(mapping: AudioMapping): void {
  // Clear targetEmitterId when layer changes (emitter may not exist in new layer)
  mapping.targetEmitterId = undefined;
}

// Methods
function toggleSection(section: string): void {
  if (expandedSections.value.has(section)) {
    expandedSections.value.delete(section);
  } else {
    expandedSections.value.add(section);
  }
}

function toggleMappingExpanded(id: string): void {
  if (expandedMappings.value.has(id)) {
    expandedMappings.value.delete(id);
  } else {
    expandedMappings.value.add(id);
  }
}

function detectPeaks(): void {
  if (!audioStore.audioAnalysis) return;

  const weights = audioStore.audioAnalysis.amplitudeEnvelope;
  peakData.value = detectAudioPeaks(weights, peakConfig.value);

  // Store in compositor store
  store.setPeakData(peakData.value);
}

function addMapping(): void {
  const mapping = createDefaultAudioMapping();
  mappings.value.push(mapping);
  expandedMappings.value.add(mapping.id);

  // Update store
  store.addAudioMapping(mapping);
}

function removeMapping(id: string): void {
  const index = mappings.value.findIndex((m) => m.id === id);
  if (index >= 0) {
    mappings.value.splice(index, 1);
    expandedMappings.value.delete(id);

    // Update store
    store.removeAudioMapping(id);
  }
}

function drawVisualizer(): void {
  const canvas = visualizerCanvas.value;
  if (!canvas || !audioStore.audioAnalysis) return;

  const ctx = canvas.getContext("2d");
  if (!ctx) return;

  const width = canvas.width;
  const height = canvas.height;

  // Clear
  ctx.fillStyle = "#1e1e1e";
  ctx.fillRect(0, 0, width, height);

  // Get feature data
  let featureData: number[] = [];
  const analysis = audioStore.audioAnalysis;

  switch (visualizerFeature.value) {
    case "amplitude":
      featureData = analysis.amplitudeEnvelope;
      break;
    case "rms":
      featureData = analysis.rmsEnergy;
      break;
    case "spectralCentroid":
      featureData = analysis.spectralCentroid;
      break;
    case "bass":
      featureData = analysis.frequencyBands.bass;
      break;
    case "mid":
      featureData = analysis.frequencyBands.mid;
      break;
    case "high":
      featureData = analysis.frequencyBands.high;
      break;
    case "sub":
      featureData = analysis.frequencyBands.sub;
      break;
    case "lowMid":
      featureData = analysis.frequencyBands.lowMid;
      break;
    case "highMid":
      featureData = analysis.frequencyBands.highMid;
      break;
    // New enhanced features
    case "spectralFlux":
      featureData = analysis.spectralFlux || [];
      break;
    case "zeroCrossingRate":
      featureData = analysis.zeroCrossingRate || [];
      break;
    case "spectralRolloff":
      featureData = analysis.spectralRolloff || [];
      break;
    case "spectralFlatness":
      featureData = analysis.spectralFlatness || [];
      break;
    case "chromaEnergy":
      featureData = analysis.chromaFeatures?.chromaEnergy || [];
      break;
    // Chroma pitch classes
    case "chromaC":
    case "chromaCs":
    case "chromaD":
    case "chromaDs":
    case "chromaE":
    case "chromaF":
    case "chromaFs":
    case "chromaG":
    case "chromaGs":
    case "chromaA":
    case "chromaAs":
    case "chromaB":
      if (analysis.chromaFeatures?.chroma) {
        const pitchIndex = [
          "chromaC",
          "chromaCs",
          "chromaD",
          "chromaDs",
          "chromaE",
          "chromaF",
          "chromaFs",
          "chromaG",
          "chromaGs",
          "chromaA",
          "chromaAs",
          "chromaB",
        ].indexOf(visualizerFeature.value);
        featureData = analysis.chromaFeatures.chroma.map(
          (frame) => frame[pitchIndex] || 0,
        );
      }
      break;
    case "onsets":
      // Create binary array for onsets
      featureData = new Array(analysis.frameCount).fill(0);
      for (const onset of analysis.onsets) {
        if (onset < featureData.length) featureData[onset] = 1;
      }
      break;
    case "peaks":
      if (peakData.value) {
        featureData = new Array(analysis.frameCount).fill(0);
        for (const peakIndex of peakData.value.indices) {
          if (peakIndex < featureData.length) featureData[peakIndex] = 1;
        }
      }
      break;
  }

  if (featureData.length === 0) return;

  // Draw feature curve
  ctx.strokeStyle = "#4a90d9";
  ctx.lineWidth = 1.5;
  ctx.beginPath();

  for (let i = 0; i < featureData.length; i++) {
    const x = (i / featureData.length) * width;
    const y = height - featureData[i] * height * 0.9 - 5;

    if (i === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  }
  ctx.stroke();

  // Draw peak markers if showing peaks
  if (peakData.value && visualizerFeature.value !== "peaks") {
    ctx.fillStyle = "#ff6b6b";
    for (const peakIndex of peakData.value.indices) {
      const x = (peakIndex / featureData.length) * width;
      ctx.beginPath();
      ctx.moveTo(x, 0);
      ctx.lineTo(x, height);
      ctx.strokeStyle = "rgba(255, 107, 107, 0.3)";
      ctx.stroke();
    }
  }
}

// Watch for changes
watch(
  () => [audioStore.audioAnalysis, visualizerFeature.value, peakData.value],
  () => {
    drawVisualizer();
  },
);

// Watch mappings for store sync
watch(
  mappings,
  (newMappings) => {
    for (const mapping of newMappings) {
      store.updateAudioMapping(mapping.id, mapping);
    }
  },
  { deep: true },
);

// Lifecycle
onMounted(() => {
  drawVisualizer();

  // Load existing mappings from store
  const existingMappings = store.getAudioMappings();
  if (existingMappings.length > 0) {
    mappings.value = [...existingMappings];
  }
});
</script>

<style scoped>
.audio-properties {
  padding: 8px 0;
}

.property-section {
  margin-bottom: 12px;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
  background: #2a2a2a;
  border-radius: 4px;
  cursor: pointer;
  font-size: 12px;
  font-weight: 500;
}

.section-header:hover {
  background: #333;
}

.section-header i {
  font-size: 12px;
  color: #888;
}

.section-content {
  padding: 8px;
  background: #252525;
  border-radius: 0 0 4px 4px;
  margin-top: 2px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.property-row label {
  flex-shrink: 0;
  font-size: 13px;
  color: #888;
  min-width: 80px;
}

.property-row input[type="range"] {
  flex: 1;
  height: 4px;
  -webkit-appearance: none;
  background: #3a3a3a;
  border-radius: 2px;
}

.property-row input[type="range"]::-webkit-slider-thumb {
  -webkit-appearance: none;
  width: 12px;
  height: 12px;
  background: #4a90d9;
  border-radius: 50%;
  cursor: pointer;
}

.property-row input[type="number"],
.property-row select {
  flex: 1;
  padding: 4px 8px;
  background: #1e1e1e;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
}

.small-input {
  max-width: 60px !important;
}

.separator {
  color: #666;
}

.value-display {
  font-size: 12px;
  color: #666;
  min-width: 50px;
  text-align: right;
}

.action-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 12px;
  background: #4a90d9;
  border: none;
  border-radius: 4px;
  color: #fff;
  font-size: 13px;
  cursor: pointer;
  transition: background 0.1s;
}

.action-btn:hover {
  background: #5aa0e9;
}

.add-mapping-btn {
  width: 100%;
  justify-content: center;
  margin-bottom: 8px;
}

.peak-count {
  font-size: 13px;
  color: #4a90d9;
  margin-left: auto;
}

.mapping-count {
  margin-left: auto;
  font-size: 12px;
  padding: 2px 6px;
  background: #4a90d9;
  border-radius: 10px;
  color: #fff;
}

.mapping-item {
  background: #1e1e1e;
  border-radius: 4px;
  margin-bottom: 6px;
  overflow: hidden;
}

.mapping-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px;
  cursor: pointer;
}

.mapping-enabled input {
  margin: 0;
}

.mapping-name {
  flex: 1;
  font-size: 13px;
  color: #aaa;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.delete-btn {
  padding: 4px;
  background: transparent;
  border: none;
  color: #666;
  cursor: pointer;
}

.delete-btn:hover {
  color: #ff6b6b;
}

.mapping-details {
  padding: 8px;
  border-top: 1px solid #2a2a2a;
}

.expand-btn {
  width: 100%;
  padding: 4px;
  background: #252525;
  border: none;
  color: #666;
  cursor: pointer;
}

.expand-btn:hover {
  background: #333;
  color: #aaa;
}

.visualizer-canvas-container {
  position: relative;
  margin: 8px 0;
}

.visualizer-canvas {
  width: 100%;
  height: 60px;
  background: #1e1e1e;
  border-radius: 4px;
}

.visualizer-playhead {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 2px;
  background: #ff6b6b;
  pointer-events: none;
}

.visualizer-value {
  font-size: 12px;
  color: #666;
  text-align: center;
}

/* Subsection headers for organizing mapping controls */
.subsection-header {
  font-size: 12px;
  color: #4a90d9;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin: 12px 0 6px 0;
  padding-bottom: 4px;
  border-bottom: 1px solid #333;
}

.curve-select,
.beat-select {
  flex: 1;
  min-width: 120px;
}

.checkbox-row {
  margin-top: 8px;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  min-width: auto;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
}

/* Optgroup styling for categorized dropdowns */
select optgroup {
  font-weight: 600;
  font-style: normal;
  color: #4a90d9;
  background: #252525;
}

select option {
  font-weight: normal;
  color: #e0e0e0;
  padding: 4px 8px;
}
</style>
