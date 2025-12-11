<template>
  <div class="audio-panel">
    <div class="panel-header">
      <span class="panel-title">Audio</span>
      <div class="header-actions">
        <button @click="loadAudioFile" title="Load Audio">
          <span class="icon">📁</span>
        </button>
      </div>
    </div>

    <div class="panel-content" v-if="hasAudio">
      <!-- Audio Info -->
      <div class="audio-info">
        <div class="file-info">
          <span class="file-icon">🎵</span>
          <div class="file-details">
            <span class="file-name">{{ audioFileName }}</span>
            <span class="file-meta">{{ audioDuration }} • {{ audioSampleRate }}</span>
          </div>
          <button class="remove-btn" @click="removeAudio" title="Remove Audio">×</button>
        </div>
      </div>

      <!-- Volume Control -->
      <div class="control-section">
        <div class="control-row">
          <label>Master Volume</label>
          <SliderInput
            v-model="masterVolume"
            :min="0"
            :max="100"
            :precision="0"
            unit="%"
          />
          <button class="mute-btn" :class="{ active: isMuted }" @click="toggleMute" title="Mute">
            {{ isMuted ? '🔇' : '🔊' }}
          </button>
        </div>
      </div>

      <!-- Waveform Display -->
      <div class="waveform-section">
        <div class="section-header">
          <span class="section-title">Waveform</span>
          <div class="waveform-controls">
            <button
              :class="{ active: waveformMode === 'waveform' }"
              @click="waveformMode = 'waveform'"
            >
              Wave
            </button>
            <button
              :class="{ active: waveformMode === 'spectrum' }"
              @click="waveformMode = 'spectrum'"
            >
              Spectrum
            </button>
          </div>
        </div>
        <div class="waveform-display">
          <canvas ref="waveformCanvas" class="waveform-canvas"></canvas>
        </div>
      </div>

      <!-- Beat Detection -->
      <div class="control-section">
        <div class="section-header" @click="toggleSection('beats')">
          <span class="expand-icon">{{ expandedSections.includes('beats') ? '▼' : '►' }}</span>
          <span class="section-title">Beat Detection</span>
        </div>

        <div v-if="expandedSections.includes('beats')" class="section-content">
          <div class="control-row">
            <label>Sensitivity</label>
            <SliderInput
              v-model="beatSensitivity"
              :min="0"
              :max="100"
              :precision="0"
              unit="%"
            />
          </div>
          <div class="control-row">
            <label>Threshold</label>
            <SliderInput
              v-model="beatThreshold"
              :min="0"
              :max="100"
              :precision="0"
              unit="%"
            />
          </div>
          <div class="beat-indicator">
            <span class="beat-label">BPM:</span>
            <span class="beat-value">{{ detectedBPM }}</span>
            <span class="beat-pulse" :class="{ active: beatPulse }"></span>
          </div>
        </div>
      </div>

      <!-- Frequency Bands -->
      <div class="control-section">
        <div class="section-header" @click="toggleSection('bands')">
          <span class="expand-icon">{{ expandedSections.includes('bands') ? '▼' : '►' }}</span>
          <span class="section-title">Frequency Bands</span>
        </div>

        <div v-if="expandedSections.includes('bands')" class="section-content">
          <div class="frequency-bands">
            <div
              v-for="(band, index) in frequencyBands"
              :key="band.name"
              class="band-item"
            >
              <span class="band-name">{{ band.name }}</span>
              <div class="band-meter">
                <div class="band-fill" :style="{ height: `${band.level}%` }"></div>
              </div>
              <span class="band-value">{{ Math.round(band.level) }}</span>
            </div>
          </div>
        </div>
      </div>

      <!-- Audio Reactivity -->
      <div class="control-section">
        <div class="section-header" @click="toggleSection('reactivity')">
          <span class="expand-icon">{{ expandedSections.includes('reactivity') ? '▼' : '►' }}</span>
          <span class="section-title">Audio Reactivity</span>
        </div>

        <div v-if="expandedSections.includes('reactivity')" class="section-content">
          <div class="control-row">
            <label>Link to Layer</label>
            <select v-model="linkedLayer" class="layer-select">
              <option value="">None</option>
              <option v-for="layer in availableLayers" :key="layer.id" :value="layer.id">
                {{ layer.name }}
              </option>
            </select>
          </div>

          <div v-if="linkedLayer" class="reactivity-options">
            <div class="control-row">
              <label>Property</label>
              <select v-model="reactiveProperty" class="property-select">
                <option value="opacity">Opacity</option>
                <option value="scale">Scale</option>
                <option value="rotation">Rotation</option>
                <option value="position.x">Position X</option>
                <option value="position.y">Position Y</option>
              </select>
            </div>

            <div class="control-row">
              <label>Band</label>
              <select v-model="reactiveBand" class="band-select">
                <option value="bass">Bass</option>
                <option value="lowMid">Low Mid</option>
                <option value="mid">Mid</option>
                <option value="highMid">High Mid</option>
                <option value="treble">Treble</option>
                <option value="overall">Overall</option>
              </select>
            </div>

            <div class="control-row">
              <label>Intensity</label>
              <SliderInput
                v-model="reactiveIntensity"
                :min="0"
                :max="200"
                :precision="0"
                unit="%"
              />
            </div>

            <div class="control-row">
              <label>Smoothing</label>
              <SliderInput
                v-model="reactiveSmoothing"
                :min="0"
                :max="100"
                :precision="0"
                unit="%"
              />
            </div>
          </div>
        </div>
      </div>
    </div>

    <!-- No Audio State -->
    <div v-else class="empty-state">
      <div class="empty-icon">🎵</div>
      <p>No audio loaded</p>
      <button class="load-btn" @click="loadAudioFile">
        Load Audio File
      </button>
      <p class="hint">Supports MP3, WAV, OGG, AAC</p>
    </div>

    <!-- Hidden file input -->
    <input
      ref="audioFileInput"
      type="file"
      accept="audio/*"
      style="display: none"
      @change="handleAudioFileSelected"
    />
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { SliderInput } from '@/components/controls';

const store = useCompositorStore();

// Refs
const audioFileInput = ref<HTMLInputElement | null>(null);
const waveformCanvas = ref<HTMLCanvasElement | null>(null);

// State
const expandedSections = ref<string[]>(['beats', 'bands']);
const waveformMode = ref<'waveform' | 'spectrum'>('waveform');

const masterVolume = ref(80);
const isMuted = ref(false);

const beatSensitivity = ref(70);
const beatThreshold = ref(50);
const detectedBPM = ref(120);
const beatPulse = ref(false);

const frequencyBands = ref([
  { name: 'Bass', level: 45 },
  { name: 'Low', level: 60 },
  { name: 'Mid', level: 75 },
  { name: 'High', level: 55 },
  { name: 'Treble', level: 40 }
]);

const linkedLayer = ref('');
const reactiveProperty = ref('opacity');
const reactiveBand = ref('bass');
const reactiveIntensity = ref(100);
const reactiveSmoothing = ref(50);

// Computed
const hasAudio = computed(() => !!store.audioBuffer);

const audioFileName = computed(() => {
  return store.audioFile?.name || 'Unknown';
});

const audioDuration = computed(() => {
  if (!store.audioBuffer) return '0:00';
  const duration = store.audioBuffer.duration;
  const minutes = Math.floor(duration / 60);
  const seconds = Math.floor(duration % 60);
  return `${minutes}:${String(seconds).padStart(2, '0')}`;
});

const audioSampleRate = computed(() => {
  if (!store.audioBuffer) return '0 Hz';
  return `${(store.audioBuffer.sampleRate / 1000).toFixed(1)} kHz`;
});

const availableLayers = computed(() => {
  return store.project?.composition?.layers || [];
});

// Methods
function loadAudioFile() {
  audioFileInput.value?.click();
}

async function handleAudioFileSelected(event: Event) {
  const input = event.target as HTMLInputElement;
  if (!input.files?.length) return;

  const file = input.files[0];
  await store.loadAudio(file);

  // Reset input
  input.value = '';
}

function removeAudio() {
  store.clearAudio();
}

function toggleMute() {
  isMuted.value = !isMuted.value;
}

function toggleSection(section: string) {
  const index = expandedSections.value.indexOf(section);
  if (index >= 0) {
    expandedSections.value.splice(index, 1);
  } else {
    expandedSections.value.push(section);
  }
}

// Waveform visualization
let animationFrame: number;
let analyser: AnalyserNode | null = null;

function initWaveformVisualization() {
  if (!waveformCanvas.value || !store.audioBuffer) return;

  const canvas = waveformCanvas.value;
  const ctx = canvas.getContext('2d');
  if (!ctx) return;

  // Set canvas size
  const rect = canvas.getBoundingClientRect();
  canvas.width = rect.width * window.devicePixelRatio;
  canvas.height = rect.height * window.devicePixelRatio;
  ctx.scale(window.devicePixelRatio, window.devicePixelRatio);

  // Draw static waveform from audio buffer
  drawStaticWaveform(ctx, rect.width, rect.height);
}

function drawStaticWaveform(ctx: CanvasRenderingContext2D, width: number, height: number) {
  if (!store.audioBuffer) return;

  const data = store.audioBuffer.getChannelData(0);
  const step = Math.ceil(data.length / width);
  const amp = height / 2;

  ctx.fillStyle = '#1a1a1a';
  ctx.fillRect(0, 0, width, height);

  ctx.beginPath();
  ctx.strokeStyle = '#4a90d9';
  ctx.lineWidth = 1;

  for (let i = 0; i < width; i++) {
    let min = 1.0;
    let max = -1.0;

    for (let j = 0; j < step; j++) {
      const sample = data[i * step + j];
      if (sample < min) min = sample;
      if (sample > max) max = sample;
    }

    const y1 = (1 + min) * amp;
    const y2 = (1 + max) * amp;

    ctx.moveTo(i, y1);
    ctx.lineTo(i, y2);
  }

  ctx.stroke();

  // Draw playhead
  const playheadX = (store.currentFrame / store.frameCount) * width;
  ctx.beginPath();
  ctx.strokeStyle = '#fff';
  ctx.lineWidth = 1;
  ctx.moveTo(playheadX, 0);
  ctx.lineTo(playheadX, height);
  ctx.stroke();
}

// Simulate beat detection
let beatInterval: number;

function startBeatSimulation() {
  const bpm = detectedBPM.value;
  const beatMs = 60000 / bpm;

  beatInterval = window.setInterval(() => {
    beatPulse.value = true;
    setTimeout(() => {
      beatPulse.value = false;
    }, 100);

    // Simulate frequency band changes
    frequencyBands.value = frequencyBands.value.map(band => ({
      ...band,
      level: Math.min(100, Math.max(10, band.level + (Math.random() - 0.5) * 30))
    }));
  }, beatMs);
}

function stopBeatSimulation() {
  clearInterval(beatInterval);
}

// Lifecycle
onMounted(() => {
  if (hasAudio.value) {
    initWaveformVisualization();
    startBeatSimulation();
  }
});

onUnmounted(() => {
  if (animationFrame) {
    cancelAnimationFrame(animationFrame);
  }
  stopBeatSimulation();
});

// Watch audio changes
watch(hasAudio, (hasAudio) => {
  if (hasAudio) {
    setTimeout(() => {
      initWaveformVisualization();
      startBeatSimulation();
    }, 100);
  } else {
    stopBeatSimulation();
  }
});

watch(() => store.currentFrame, () => {
  if (hasAudio.value && waveformCanvas.value) {
    const ctx = waveformCanvas.value.getContext('2d');
    if (ctx) {
      const rect = waveformCanvas.value.getBoundingClientRect();
      drawStaticWaveform(ctx, rect.width, rect.height);
    }
  }
});
</script>

<style scoped>
.audio-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 11px;
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 10px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.panel-title {
  font-weight: 600;
  font-size: 12px;
}

.header-actions button {
  width: 24px;
  height: 24px;
  padding: 0;
  border: none;
  background: transparent;
  color: #888;
  border-radius: 3px;
  cursor: pointer;
}

.header-actions button:hover {
  background: #3a3a3a;
  color: #e0e0e0;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
}

.audio-info {
  padding: 10px;
  border-bottom: 1px solid #2a2a2a;
}

.file-info {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 8px;
  background: #252525;
  border-radius: 4px;
}

.file-icon {
  font-size: 20px;
}

.file-details {
  flex: 1;
  display: flex;
  flex-direction: column;
}

.file-name {
  font-weight: 500;
  font-size: 12px;
}

.file-meta {
  font-size: 10px;
  color: #888;
}

.remove-btn {
  width: 24px;
  height: 24px;
  padding: 0;
  border: none;
  background: transparent;
  color: #666;
  border-radius: 3px;
  cursor: pointer;
  font-size: 16px;
}

.remove-btn:hover {
  background: #3a3a3a;
  color: #ff6b6b;
}

.control-section {
  border-bottom: 1px solid #2a2a2a;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 10px;
  cursor: pointer;
  user-select: none;
}

.section-header:hover {
  background: #252525;
}

.expand-icon {
  width: 10px;
  font-size: 8px;
  color: #666;
}

.section-title {
  flex: 1;
  font-weight: 500;
}

.section-content {
  padding: 4px 10px 10px;
}

.control-row {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px 10px;
  min-height: 26px;
}

.control-row label {
  width: 80px;
  color: #888;
  font-size: 10px;
  flex-shrink: 0;
}

.control-row > :last-child:not(label) {
  flex: 1;
}

.mute-btn {
  flex: 0 0 auto;
  width: 28px;
  height: 28px;
  padding: 0;
  border: none;
  background: transparent;
  color: #888;
  border-radius: 3px;
  cursor: pointer;
  font-size: 14px;
}

.mute-btn:hover {
  background: #3a3a3a;
}

.mute-btn.active {
  color: #ff6b6b;
}

/* Waveform */
.waveform-section {
  padding: 10px;
  border-bottom: 1px solid #2a2a2a;
}

.waveform-controls {
  display: flex;
  gap: 2px;
}

.waveform-controls button {
  padding: 3px 8px;
  border: none;
  background: transparent;
  color: #888;
  font-size: 10px;
  border-radius: 3px;
  cursor: pointer;
}

.waveform-controls button:hover {
  color: #e0e0e0;
}

.waveform-controls button.active {
  background: #3a3a3a;
  color: #e0e0e0;
}

.waveform-display {
  margin-top: 8px;
  height: 60px;
  background: #1a1a1a;
  border-radius: 4px;
  overflow: hidden;
}

.waveform-canvas {
  width: 100%;
  height: 100%;
}

/* Beat Detection */
.beat-indicator {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px;
  background: #252525;
  border-radius: 4px;
  margin-top: 8px;
}

.beat-label {
  color: #888;
}

.beat-value {
  font-family: 'SF Mono', Monaco, monospace;
  font-size: 14px;
  font-weight: 600;
  color: #4a90d9;
}

.beat-pulse {
  width: 12px;
  height: 12px;
  background: #333;
  border-radius: 50%;
  margin-left: auto;
  transition: background 0.1s;
}

.beat-pulse.active {
  background: #4a90d9;
  box-shadow: 0 0 8px #4a90d9;
}

/* Frequency Bands */
.frequency-bands {
  display: flex;
  gap: 8px;
  padding: 8px;
  background: #1a1a1a;
  border-radius: 4px;
}

.band-item {
  flex: 1;
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 4px;
}

.band-name {
  font-size: 9px;
  color: #888;
}

.band-meter {
  width: 100%;
  height: 60px;
  background: #252525;
  border-radius: 3px;
  position: relative;
  overflow: hidden;
}

.band-fill {
  position: absolute;
  bottom: 0;
  left: 0;
  right: 0;
  background: linear-gradient(to top, #4a90d9, #7c9cff);
  border-radius: 3px;
  transition: height 0.1s;
}

.band-value {
  font-size: 9px;
  color: #666;
  font-family: 'SF Mono', Monaco, monospace;
}

/* Selects */
.layer-select,
.property-select,
.band-select {
  flex: 1;
  padding: 4px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 11px;
}

.reactivity-options {
  margin-top: 8px;
  padding: 8px;
  background: #252525;
  border-radius: 4px;
}

/* Empty State */
.empty-state {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  height: 100%;
  padding: 24px;
  text-align: center;
  color: #555;
}

.empty-icon {
  font-size: 48px;
  margin-bottom: 12px;
  opacity: 0.5;
}

.load-btn {
  margin-top: 12px;
  padding: 8px 16px;
  background: #4a90d9;
  border: none;
  color: #fff;
  border-radius: 4px;
  cursor: pointer;
  font-size: 12px;
}

.load-btn:hover {
  background: #5aa0e9;
}

.hint {
  font-size: 10px;
  margin-top: 8px;
  color: #555;
}

.icon {
  font-size: 14px;
}
</style>
