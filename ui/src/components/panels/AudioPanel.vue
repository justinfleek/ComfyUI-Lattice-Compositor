<template>
  <div class="audio-panel">
    <div class="panel-header">
      <span class="panel-title">Audio Source</span>
      <div class="header-actions">
        <button @click="loadAudioFile" title="Load Audio">
          <PhFolder class="icon" />
        </button>
      </div>
    </div>

    <div class="panel-content" v-if="hasAudio">
      <div class="audio-info">
        <div class="file-info">
          <PhMusicNote class="file-icon" />
          <div class="file-details">
            <span class="file-name">{{ audioFileName }}</span>
            <span class="file-meta">{{ audioDuration }} • {{ audioSampleRate }}</span>
          </div>
          <button class="remove-btn" @click="removeAudio" title="Remove Audio">×</button>
        </div>
      </div>

      <div class="control-section">
        <div class="control-row">
          <label>Master Vol</label>
          <SliderInput v-model="masterVolume" :min="0" :max="100" unit="%" />
          <button class="mute-btn" :class="{ active: isMuted }" @click="toggleMute" title="Mute">
            <PhSpeakerSlash v-if="isMuted" />
            <PhSpeakerHigh v-else />
          </button>
        </div>
      </div>

      <div class="waveform-section">
        <div class="section-header">
          <span class="section-title">Waveform</span>
        </div>
        <div class="waveform-display">
          <canvas ref="waveformCanvas" class="waveform-canvas"></canvas>
        </div>
      </div>

      <!-- Real-time Audio Values Preview -->
      <div class="audio-values-section">
        <AudioValuePreview />
      </div>

      <div class="linker-section">
        <div class="linker-header">Audio Linker</div>
        <AudioProperties />
      </div>

      <!-- Convert Audio to Keyframes Section -->
      <div class="convert-section">
        <div class="section-header clickable" @click="convertSectionExpanded = !convertSectionExpanded">
          <span class="expand-icon">{{ convertSectionExpanded ? '▼' : '►' }}</span>
          <span class="section-title">Convert to Keyframes</span>
        </div>

        <div v-if="convertSectionExpanded" class="section-content">
          <p class="section-description">
            Creates a null layer with amplitude keyframes for expression linking.
          </p>

          <div class="control-row">
            <label>Layer Name</label>
            <input
              type="text"
              v-model="convertLayerName"
              placeholder="Audio Amplitude"
              class="text-input"
            />
          </div>

          <div class="control-row">
            <label>Amplitude Scale</label>
            <input
              type="range"
              min="10"
              max="200"
              v-model.number="convertAmplitudeScale"
              class="scale-slider"
            />
            <span class="value">{{ convertAmplitudeScale }}%</span>
          </div>

          <div class="control-row">
            <label>Smoothing</label>
            <input
              type="range"
              min="0"
              max="20"
              v-model.number="convertSmoothing"
              class="smoothing-slider"
            />
            <span class="value">{{ convertSmoothing }} frames</span>
          </div>

          <button
            class="convert-btn"
            @click="convertAudioToKeyframes"
            :disabled="isConverting"
          >
            {{ isConverting ? 'Converting...' : '🎹 Convert Audio to Keyframes' }}
          </button>

          <div v-if="convertResult" class="convert-result">
            <span class="result-icon">✅</span>
            <span>Created "{{ convertResult.layerName }}" with {{ convertResult.keyframeCount }} keyframes</span>
          </div>

          <div v-if="convertError" class="error-message">
            {{ convertError }}
          </div>
        </div>
      </div>

      <!-- Stem Separation Section -->
      <div class="stem-section">
        <div class="section-header clickable" @click="stemSectionExpanded = !stemSectionExpanded">
          <span class="expand-icon">{{ stemSectionExpanded ? '▼' : '►' }}</span>
          <span class="section-title">Stem Separation</span>
          <span class="badge" v-if="separatedStems">{{ Object.keys(separatedStems).length }} stems</span>
        </div>

        <div v-if="stemSectionExpanded" class="section-content">
          <div class="control-row">
            <label>Model</label>
            <select v-model="selectedModel" class="model-select">
              <option value="htdemucs">HT-Demucs (Recommended)</option>
              <option value="htdemucs_ft">HT-Demucs Fine-tuned</option>
              <option value="mdx_extra">MDX Extra (Fast)</option>
            </select>
          </div>

          <div class="preset-buttons">
            <button
              class="preset-btn"
              @click="separateStem('vocals')"
              :disabled="isSeparating"
              title="Extract vocals only"
            >
              🎤 Vocals
            </button>
            <button
              class="preset-btn"
              @click="separateStem('drums')"
              :disabled="isSeparating"
              title="Extract drums only"
            >
              🥁 Drums
            </button>
            <button
              class="preset-btn"
              @click="separateStem('bass')"
              :disabled="isSeparating"
              title="Extract bass only"
            >
              🎸 Bass
            </button>
            <button
              class="preset-btn karaoke"
              @click="makeKaraoke"
              :disabled="isSeparating"
              title="Remove vocals (instrumental)"
            >
              🎶 Karaoke
            </button>
            <button
              class="preset-btn all"
              @click="separateAll"
              :disabled="isSeparating"
              title="Separate all stems"
            >
              ✨ All Stems
            </button>
          </div>

          <div v-if="isSeparating" class="progress-row">
            <div class="progress-bar">
              <div class="progress-fill" :style="{ width: separationProgress + '%' }"></div>
            </div>
            <span class="progress-text">{{ separationMessage }}</span>
          </div>

          <div v-if="separatedStems" class="stems-list">
            <div class="stems-header">Separated Stems</div>
            <div
              v-for="(data, stemName) in separatedStems"
              :key="stemName"
              class="stem-item"
            >
              <span class="stem-icon">{{ getStemIcon(stemName as string) }}</span>
              <span class="stem-name">{{ stemName }}</span>
              <button class="stem-btn play" @click="playStem(stemName as string)" title="Play">▶</button>
              <button class="stem-btn download" @click="downloadStemFile(stemName as string)" title="Download">⬇</button>
              <button class="stem-btn use" @click="useStemForReactivity(stemName as string)" title="Use for Audio Reactivity">🔗</button>
            </div>
          </div>

          <div v-if="separationError" class="error-message">
            {{ separationError }}
          </div>
        </div>
      </div>

      <!-- Enhanced Beat Detection Section -->
      <div class="beat-section">
        <div class="section-header clickable" @click="beatSectionExpanded = !beatSectionExpanded">
          <span class="expand-icon">{{ beatSectionExpanded ? '▼' : '►' }}</span>
          <span class="section-title">Beat Detection</span>
          <span class="badge" v-if="beatGrid">{{ Math.round(beatGrid.bpm) }} BPM</span>
        </div>

        <div v-if="beatSectionExpanded" class="section-content">
          <!-- Genre Preset -->
          <div class="control-row">
            <label>Genre Preset</label>
            <select v-model="beatPreset" @change="applyBeatPreset" class="preset-select">
              <option value="">Custom</option>
              <option value="electronic">Electronic/EDM</option>
              <option value="rock">Rock/Pop</option>
              <option value="hiphop">Hip-Hop</option>
              <option value="jazz">Jazz</option>
              <option value="classical">Classical</option>
              <option value="waltz">Waltz (3/4)</option>
            </select>
          </div>

          <!-- Time Signature -->
          <div class="control-row">
            <label>Time Signature</label>
            <select v-model.number="beatConfig.timeSignature" @change="updateBeatConfig">
              <option :value="4">4/4</option>
              <option :value="3">3/4</option>
              <option :value="6">6/8</option>
              <option :value="2">2/4</option>
            </select>
          </div>

          <!-- Options -->
          <div class="checkbox-row">
            <label>
              <input type="checkbox" v-model="beatConfig.fillGaps" @change="updateBeatConfig" />
              <span>Fill Missing Beats</span>
            </label>
          </div>
          <div class="checkbox-row">
            <label>
              <input type="checkbox" v-model="beatConfig.interpolate" @change="updateBeatConfig" />
              <span>Snap to Grid</span>
            </label>
          </div>

          <!-- Sensitivity -->
          <div class="control-row">
            <label>Tolerance</label>
            <input
              type="range"
              min="1"
              max="10"
              v-model.number="beatConfig.positionTolerance"
              @input="updateBeatConfig"
              class="tolerance-slider"
            />
            <span class="value">{{ beatConfig.positionTolerance }}f</span>
          </div>

          <!-- Analyze Button -->
          <button
            class="analyze-btn"
            @click="analyzeBeats"
            :disabled="isAnalyzingBeats"
          >
            {{ isAnalyzingBeats ? 'Analyzing...' : '🎵 Analyze Beats' }}
          </button>

          <!-- Results -->
          <div v-if="beatGrid" class="beat-results">
            <div class="result-row">
              <span class="result-label">Detected BPM:</span>
              <span class="result-value">{{ Math.round(beatGrid.bpm) }}</span>
              <span class="confidence" :class="confidenceClass">
                {{ Math.round(beatGrid.bpmConfidence * 100) }}% confidence
              </span>
            </div>
            <div class="result-row">
              <span class="result-label">Beats Found:</span>
              <span class="result-value">{{ beatGrid.beats.length }}</span>
            </div>
            <div class="result-row">
              <span class="result-label">Downbeats:</span>
              <span class="result-value">{{ beatGrid.downbeats.length }}</span>
            </div>
            <div class="beat-actions">
              <button class="beat-btn" @click="snapToBeats" title="Snap keyframes to beats">
                ⏱️ Snap to Beats
              </button>
              <button class="beat-btn" @click="markBeatsAsMarkers" title="Add markers at beats">
                📍 Add Markers
              </button>
            </div>
          </div>
        </div>
      </div>

      <!-- MIDI Configuration Section -->
      <div class="midi-section">
        <div class="section-header clickable" @click="midiSectionExpanded = !midiSectionExpanded">
          <span class="expand-icon">{{ midiSectionExpanded ? '▼' : '►' }}</span>
          <span class="section-title">MIDI Input</span>
          <span class="badge" v-if="midiDevices.length > 0">{{ midiDevices.length }} device{{ midiDevices.length !== 1 ? 's' : '' }}</span>
          <span class="badge unavailable" v-else-if="!midiAvailable">Unavailable</span>
        </div>

        <div v-if="midiSectionExpanded" class="section-content">
          <div v-if="!midiAvailable" class="midi-unavailable">
            <p>Web MIDI API is not available in this browser.</p>
            <p class="hint">Try Chrome or Edge for MIDI support.</p>
          </div>

          <template v-else>
            <div class="control-row">
              <button class="refresh-btn" @click="refreshMIDIDevices" :disabled="isRefreshingMIDI">
                {{ isRefreshingMIDI ? 'Scanning...' : '🔄 Scan Devices' }}
              </button>
            </div>

            <div v-if="midiDevices.length === 0" class="no-devices">
              <p>No MIDI devices found.</p>
              <p class="hint">Connect a MIDI controller and click "Scan Devices".</p>
            </div>

            <div v-else class="device-list">
              <div v-for="device in midiDevices" :key="device.id" class="device-item">
                <span class="device-icon">🎹</span>
                <div class="device-info">
                  <span class="device-name">{{ device.name }}</span>
                  <span class="device-meta">{{ device.manufacturer }} • {{ device.type }}</span>
                </div>
                <span class="device-status" :class="device.state">{{ device.state }}</span>
              </div>
            </div>

            <div v-if="midiDevices.length > 0" class="midi-monitor">
              <div class="monitor-header">
                <span>MIDI Monitor</span>
                <label class="monitor-toggle">
                  <input type="checkbox" v-model="midiMonitorEnabled" />
                  <span>{{ midiMonitorEnabled ? 'On' : 'Off' }}</span>
                </label>
              </div>
              <div v-if="midiMonitorEnabled" class="monitor-messages">
                <div
                  v-for="(msg, idx) in recentMIDIMessages"
                  :key="idx"
                  class="midi-message"
                  :class="msg.type"
                >
                  <span class="msg-type">{{ msg.type }}</span>
                  <span class="msg-channel">Ch{{ msg.channel }}</span>
                  <span v-if="msg.note !== undefined" class="msg-note">{{ midiNoteToName(msg.note) }}</span>
                  <span v-if="msg.value !== undefined" class="msg-value">{{ msg.value }}</span>
                  <span v-if="msg.velocity !== undefined" class="msg-velocity">vel {{ msg.velocity }}</span>
                </div>
                <div v-if="recentMIDIMessages.length === 0" class="no-messages">
                  No MIDI messages yet. Move a fader or press a key.
                </div>
              </div>
            </div>
          </template>
        </div>
      </div>

      <!-- MIDI File to Keyframes Section -->
      <div class="midi-file-section">
        <div class="section-header clickable" @click="midiFileSectionExpanded = !midiFileSectionExpanded">
          <span class="expand-icon">{{ midiFileSectionExpanded ? '▼' : '►' }}</span>
          <span class="section-title">MIDI File to Keyframes</span>
          <span class="badge" v-if="loadedMIDIFile">{{ midiFileInfo?.totalNotes }} notes</span>
        </div>

        <div v-if="midiFileSectionExpanded" class="section-content">
          <!-- Load MIDI File -->
          <div v-if="!loadedMIDIFile" class="midi-load-area">
            <button class="load-midi-btn" @click="loadMIDIFile" :disabled="isLoadingMIDI">
              {{ isLoadingMIDI ? 'Loading...' : '🎹 Load MIDI File (.mid)' }}
            </button>
          </div>

          <!-- MIDI File Info -->
          <div v-else class="midi-file-info">
            <div class="file-row">
              <span class="file-icon">🎹</span>
              <div class="file-details">
                <span class="file-name">{{ midiFileName }}</span>
                <span class="file-meta">{{ midiFileInfo?.trackCount }} tracks • {{ midiFileInfo?.totalNotes }} notes • {{ midiFileInfo?.bpm }} BPM</span>
              </div>
              <button class="remove-btn" @click="removeMIDIFile" title="Remove">×</button>
            </div>

            <!-- Track Selection -->
            <div class="control-row">
              <label>Track</label>
              <select v-model="midiTrackIndex" class="track-select">
                <option :value="undefined">All Tracks</option>
                <option v-for="track in midiTracks" :key="track.index" :value="track.index">
                  {{ track.name }} ({{ track.noteCount }} notes)
                </option>
              </select>
            </div>

            <!-- Channel Selection -->
            <div class="control-row">
              <label>Channel</label>
              <select v-model="midiChannel" class="channel-select">
                <option :value="undefined">All Channels</option>
                <option v-for="ch in 16" :key="ch" :value="ch - 1">Channel {{ ch }}</option>
              </select>
            </div>

            <!-- Mapping Type -->
            <div class="control-row">
              <label>Map</label>
              <select v-model="midiMappingType" class="mapping-select">
                <option value="noteOnOff">Note On/Off</option>
                <option value="noteVelocity">Note Velocity</option>
                <option value="notePitch">Note Pitch</option>
                <option value="controlChange">Control Change (CC)</option>
              </select>
            </div>

            <!-- CC Number (only for controlChange) -->
            <div v-if="midiMappingType === 'controlChange'" class="control-row">
              <label>CC #</label>
              <select v-model="midiCCNumber" class="cc-select">
                <option :value="1">1 - Modulation</option>
                <option :value="7">7 - Volume</option>
                <option :value="10">10 - Pan</option>
                <option :value="11">11 - Expression</option>
                <option :value="64">64 - Sustain</option>
                <option :value="74">74 - Cutoff</option>
              </select>
            </div>

            <!-- Value Range -->
            <div class="control-row">
              <label>Min</label>
              <input type="number" v-model.number="midiValueMin" class="value-input" />
              <label>Max</label>
              <input type="number" v-model.number="midiValueMax" class="value-input" />
            </div>

            <!-- Interpolation -->
            <div class="control-row">
              <label>Easing</label>
              <select v-model="midiInterpolation" class="interp-select">
                <option value="hold">Hold (Step)</option>
                <option value="linear">Linear</option>
                <option value="bezier">Bezier</option>
              </select>
            </div>

            <!-- Layer Name -->
            <div class="control-row">
              <label>Layer</label>
              <input type="text" v-model="midiLayerName" placeholder="MIDI Animation" class="text-input" />
            </div>

            <!-- Convert Button -->
            <button
              class="convert-midi-btn"
              @click="convertMIDIToKeyframes"
              :disabled="isConvertingMIDI"
            >
              {{ isConvertingMIDI ? 'Converting...' : '✨ Create Keyframes' }}
            </button>

            <!-- Result -->
            <div v-if="midiConvertResult" class="convert-result">
              <span class="result-icon">✅</span>
              <span>Created "{{ midiConvertResult.layerName }}" with {{ midiConvertResult.keyframeCount }} keyframes</span>
            </div>

            <!-- Error -->
            <div v-if="midiConvertError" class="error-message">
              {{ midiConvertError }}
            </div>
          </div>
        </div>
      </div>

    </div>

    <div v-else class="empty-state">
      <div class="empty-icon">🎵</div>
      <p>No audio loaded</p>
      <button class="load-btn" @click="loadAudioFile">Load Audio File</button>
      <p class="hint">Supports MP3, WAV, OGG, AAC</p>
    </div>

    <input ref="audioFileInput" type="file" accept="audio/*" style="display: none" @change="handleAudioFileSelected" />
    <input ref="midiFileInput" type="file" accept=".mid,.midi" style="display: none" @change="handleMIDIFileSelected" />
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { SliderInput } from '@/components/controls';
import AudioProperties from '@/components/properties/AudioProperties.vue';
import AudioValuePreview from '@/components/panels/AudioValuePreview.vue';
import {
  PhFolder, PhMusicNote, PhSpeakerHigh, PhSpeakerSlash, PhMicrophone,
  PhGuitar, PhPiano, PhSparkle, PhLink, PhArrowsClockwise, PhMapPin, PhTimer
} from '@phosphor-icons/vue';
import {
  separateStems as separateStemsService,
  isolateStem,
  downloadStem,
  createAudioElement,
  type StemType,
  type DemucsModel,
} from '@/services/audio/stemSeparation';
import {
  createEnhancedBeatGrid,
  BEAT_DETECTION_PRESETS,
  DEFAULT_BEAT_CONFIG,
  type BeatGrid,
  type EnhancedBeatConfig,
} from '@/services/audio/enhancedBeatDetection';
import {
  getMIDIService,
  midiNoteToName,
  type MIDIDeviceInfo,
  type MIDIMessage,
} from '@/services/midi';
import {
  parseMIDIFile,
  midiNotesToKeyframes,
  midiCCToKeyframes,
  type MIDIParsedFile,
  type MIDIToKeyframeConfig,
} from '@/services/midiToKeyframes';

const store = useCompositorStore();

// Stem separation state
const stemSectionExpanded = ref(false);
const selectedModel = ref<DemucsModel>('htdemucs');
const isSeparating = ref(false);
const separationProgress = ref(0);
const separationMessage = ref('');
const separatedStems = ref<Record<string, string> | null>(null);
const separationError = ref<string | null>(null);
const currentStemAudio = ref<HTMLAudioElement | null>(null);
const audioFileInput = ref<HTMLInputElement | null>(null);
const waveformCanvas = ref<HTMLCanvasElement | null>(null);

// Enhanced beat detection state
const beatSectionExpanded = ref(false);
const beatPreset = ref('');
const beatConfig = ref<EnhancedBeatConfig>({ ...DEFAULT_BEAT_CONFIG });
const beatGrid = ref<BeatGrid | null>(null);
const isAnalyzingBeats = ref(false);

// Convert Audio to Keyframes state
const convertSectionExpanded = ref(false);
const convertLayerName = ref('Audio Amplitude');
const convertAmplitudeScale = ref(100);
const convertSmoothing = ref(3);
const isConverting = ref(false);
const convertResult = ref<{ layerName: string; keyframeCount: number } | null>(null);
const convertError = ref<string | null>(null);

const confidenceClass = computed(() => {
  if (!beatGrid.value) return '';
  const c = beatGrid.value.bpmConfidence;
  if (c >= 0.8) return 'high';
  if (c >= 0.5) return 'medium';
  return 'low';
});

// MIDI state
const midiSectionExpanded = ref(false);
const midiAvailable = ref(false);
const midiDevices = ref<MIDIDeviceInfo[]>([]);
const isRefreshingMIDI = ref(false);
const midiMonitorEnabled = ref(false);
const recentMIDIMessages = ref<MIDIMessage[]>([]);
let midiListenerRemove: (() => void) | null = null;

// MIDI File to Keyframes state
const midiFileSectionExpanded = ref(false);
const midiFileInput = ref<HTMLInputElement | null>(null);
const loadedMIDIFile = ref<MIDIParsedFile | null>(null);
const midiFileName = ref('');
const isLoadingMIDI = ref(false);
const midiTrackIndex = ref<number | undefined>(undefined);
const midiChannel = ref<number | undefined>(undefined);
const midiMappingType = ref<'noteOnOff' | 'noteVelocity' | 'notePitch' | 'controlChange'>('noteVelocity');
const midiCCNumber = ref(1); // Modulation by default
const midiValueMin = ref(0);
const midiValueMax = ref(100);
const midiInterpolation = ref<'linear' | 'hold' | 'bezier'>('linear');
const midiLayerName = ref('MIDI Animation');
const isConvertingMIDI = ref(false);
const midiConvertResult = ref<{ layerName: string; keyframeCount: number } | null>(null);
const midiConvertError = ref<string | null>(null);

// Audio volume/mute now uses store state
const masterVolume = computed({
  get: () => store.audioVolume,
  set: (val: number) => store.setAudioVolume(val)
});
const isMuted = computed({
  get: () => store.audioMuted,
  set: (val: boolean) => store.setAudioMuted(val)
});

const hasAudio = computed(() => !!store.audioBuffer);
const audioFileName = computed(() => store.audioFile?.name || 'Unknown');
const audioSampleRate = computed(() => store.audioBuffer ? `${(store.audioBuffer.sampleRate / 1000).toFixed(1)} kHz` : '');
const audioDuration = computed(() => {
  if (!store.audioBuffer) return '0:00';
  const m = Math.floor(store.audioBuffer.duration / 60);
  const s = Math.floor(store.audioBuffer.duration % 60);
  return `${m}:${s.toString().padStart(2, '0')}`;
});

function loadAudioFile() { audioFileInput.value?.click(); }

async function handleAudioFileSelected(e: Event) {
  const input = e.target as HTMLInputElement;
  if (input.files?.length) await store.loadAudio(input.files[0]);
  input.value = '';
}

function removeAudio() { store.clearAudio(); }

function toggleMute() { store.toggleAudioMute(); }

async function convertAudioToKeyframes() {
  if (!store.audioBuffer) {
    convertError.value = 'No audio loaded';
    return;
  }

  isConverting.value = true;
  convertError.value = null;
  convertResult.value = null;

  try {
    const result = store.convertAudioToKeyframes({
      name: convertLayerName.value || 'Audio Amplitude',
      amplitudeScale: convertAmplitudeScale.value / 100,
      smoothing: convertSmoothing.value
    });

    if (result) {
      convertResult.value = {
        layerName: result.layerName,
        keyframeCount: result.keyframeCount
      };
      console.log(`[Weyl] Created Audio Amplitude layer "${result.layerName}" with ${result.keyframeCount} keyframes per channel`);
    } else {
      convertError.value = 'Failed to create audio amplitude layer';
    }
  } catch (err) {
    convertError.value = err instanceof Error ? err.message : 'Unknown error';
  } finally {
    isConverting.value = false;
  }
}

function drawWaveform() {
  if (!waveformCanvas.value || !store.audioBuffer) return;
  const canvas = waveformCanvas.value;
  const ctx = canvas.getContext('2d');
  if (!ctx) return;

  const rect = canvas.getBoundingClientRect();
  const w = canvas.width = rect.width * window.devicePixelRatio;
  const h = canvas.height = 60 * window.devicePixelRatio;
  ctx.scale(window.devicePixelRatio, window.devicePixelRatio);

  const data = store.audioBuffer.getChannelData(0);
  const step = Math.ceil(data.length / rect.width);
  const amp = 30;

  ctx.fillStyle = '#1a1a1a';
  ctx.fillRect(0, 0, rect.width, 60);

  ctx.beginPath();
  ctx.strokeStyle = '#4a90d9';
  ctx.lineWidth = 1;
  for(let i = 0; i < rect.width; i++) {
    let min = 1.0; let max = -1.0;
    for (let j = 0; j < step; j++) {
      const datum = data[i * step + j];
      if (datum < min) min = datum;
      if (datum > max) max = datum;
    }
    ctx.moveTo(i, (1 + min) * amp);
    ctx.lineTo(i, (1 + max) * amp);
  }
  ctx.stroke();

  // Playhead
  const px = (store.currentFrame / store.frameCount) * rect.width;
  ctx.fillStyle = '#fff';
  ctx.fillRect(px, 0, 1, 60);
}

watch(() => [store.audioBuffer, store.currentFrame], drawWaveform);

onMounted(() => {
  if (hasAudio.value) {
    setTimeout(drawWaveform, 100);
  }
});

// ============================================================================
// Stem Separation Functions
// ============================================================================

function getStemIcon(stemName: string): string {
  const icons: Record<string, string> = {
    vocals: '🎤',
    drums: '🥁',
    bass: '🎸',
    other: '🎹',
    guitar: '🎸',
    piano: '🎹',
  };
  return icons[stemName] || '🎵';
}

async function separateStem(stem: StemType) {
  if (!store.audioFile) return;

  isSeparating.value = true;
  separationError.value = null;
  separationProgress.value = 10;
  separationMessage.value = `Isolating ${stem}...`;

  try {
    const arrayBuffer = await store.audioFile.arrayBuffer();
    separationProgress.value = 30;

    const result = await isolateStem(arrayBuffer, stem, selectedModel.value);

    if (result.status === 'success' && result.isolated) {
      separatedStems.value = {
        [stem]: result.isolated,
        [`no_${stem}`]: result.removed || '',
      };
      separationProgress.value = 100;
      separationMessage.value = 'Complete!';
    } else {
      separationError.value = result.message || 'Separation failed';
    }
  } catch (err) {
    separationError.value = err instanceof Error ? err.message : 'Unknown error';
  } finally {
    isSeparating.value = false;
  }
}

async function makeKaraoke() {
  if (!store.audioFile) return;

  isSeparating.value = true;
  separationError.value = null;
  separationProgress.value = 10;
  separationMessage.value = 'Creating karaoke track...';

  try {
    const arrayBuffer = await store.audioFile.arrayBuffer();
    separationProgress.value = 30;

    const result = await isolateStem(arrayBuffer, 'vocals', selectedModel.value);

    if (result.status === 'success' && result.removed) {
      separatedStems.value = {
        karaoke: result.removed,
        vocals: result.isolated || '',
      };
      separationProgress.value = 100;
      separationMessage.value = 'Karaoke track ready!';
    } else {
      separationError.value = result.message || 'Karaoke creation failed';
    }
  } catch (err) {
    separationError.value = err instanceof Error ? err.message : 'Unknown error';
  } finally {
    isSeparating.value = false;
  }
}

async function separateAll() {
  if (!store.audioFile) return;

  isSeparating.value = true;
  separationError.value = null;
  separationProgress.value = 10;
  separationMessage.value = 'Separating all stems...';

  try {
    const arrayBuffer = await store.audioFile.arrayBuffer();
    separationProgress.value = 30;

    const result = await separateStemsService(arrayBuffer, { model: selectedModel.value });

    if (result.status === 'success' && result.stems) {
      separatedStems.value = result.stems as Record<string, string>;
      separationProgress.value = 100;
      separationMessage.value = `Separated ${Object.keys(result.stems).length} stems!`;
    } else {
      separationError.value = result.message || 'Separation failed';
    }
  } catch (err) {
    separationError.value = err instanceof Error ? err.message : 'Unknown error';
  } finally {
    isSeparating.value = false;
  }
}

function playStem(stemName: string) {
  if (!separatedStems.value?.[stemName]) return;

  // Stop current playback
  if (currentStemAudio.value) {
    currentStemAudio.value.pause();
    currentStemAudio.value = null;
  }

  // Create and play new audio
  const audio = createAudioElement(separatedStems.value[stemName]);
  audio.volume = store.audioVolume / 100;
  audio.play();
  currentStemAudio.value = audio;
}

function downloadStemFile(stemName: string) {
  if (!separatedStems.value?.[stemName]) return;

  const fileName = `${store.audioFile?.name?.replace(/\.[^.]+$/, '') || 'audio'}_${stemName}.wav`;
  downloadStem(separatedStems.value[stemName], fileName);
}

function useStemForReactivity(stemName: string) {
  if (!separatedStems.value?.[stemName]) return;

  // TODO: Integrate with audio store to use this stem for audio reactivity
  // For now, show a message
  console.log(`[Weyl] Using ${stemName} stem for audio reactivity`);
  alert(`${stemName} stem selected for audio reactivity.\nThis feature will be fully integrated in a future update.`);
}

// ============================================================================
// Enhanced Beat Detection Functions
// ============================================================================

function applyBeatPreset() {
  if (beatPreset.value && BEAT_DETECTION_PRESETS[beatPreset.value]) {
    const preset = BEAT_DETECTION_PRESETS[beatPreset.value];
    beatConfig.value = { ...DEFAULT_BEAT_CONFIG, ...preset };
    // Re-analyze if we already have audio
    if (store.audioAnalysis) {
      analyzeBeats();
    }
  }
}

function updateBeatConfig() {
  // Clear preset when manually editing
  beatPreset.value = '';
  // Re-analyze if we already have results
  if (store.audioAnalysis && beatGrid.value) {
    analyzeBeats();
  }
}

async function analyzeBeats() {
  if (!store.audioAnalysis) {
    console.warn('[Weyl] No audio analysis available for beat detection');
    return;
  }

  isAnalyzingBeats.value = true;

  try {
    // Use store's fps or default to 16
    const fps = store.fps || 16;

    beatGrid.value = createEnhancedBeatGrid(
      store.audioAnalysis,
      fps,
      beatConfig.value
    );

    console.log(`[Weyl] Beat detection complete: ${beatGrid.value.bpm} BPM, ${beatGrid.value.beats.length} beats`);
  } catch (error) {
    console.error('[Weyl] Beat detection failed:', error);
    beatGrid.value = null;
  } finally {
    isAnalyzingBeats.value = false;
  }
}

function snapToBeats() {
  if (!beatGrid.value) return;

  // Get all beat frames
  const beatFrames = beatGrid.value.beats.map(b => b.frame);

  // Snap selected keyframes to nearest beat
  const selectedLayers = store.selectedLayerIds;
  let snappedCount = 0;

  for (const layerId of selectedLayers) {
    const layer = store.getLayer(layerId);
    if (!layer) continue;

    // Check each animated property for keyframes
    const transform = layer.transform;
    const animProps = [
      transform.position,
      transform.rotation,
      transform.scale,
      transform.opacity
    ];

    for (const prop of animProps) {
      if (!prop?.keyframes) continue;

      for (const kf of prop.keyframes) {
        // Find nearest beat
        let nearestBeat = beatFrames[0];
        let minDist = Math.abs(kf.frame - nearestBeat);

        for (const beat of beatFrames) {
          const dist = Math.abs(kf.frame - beat);
          if (dist < minDist) {
            minDist = dist;
            nearestBeat = beat;
          }
        }

        // Only snap if within reasonable distance (10 frames)
        if (minDist <= 10 && kf.frame !== nearestBeat) {
          kf.frame = nearestBeat;
          snappedCount++;
        }
      }
    }
  }

  if (snappedCount > 0) {
    console.log(`[Weyl] Snapped ${snappedCount} keyframes to beats`);
  } else {
    console.log('[Weyl] No keyframes were close enough to beats to snap');
  }
}

function markBeatsAsMarkers() {
  if (!beatGrid.value) return;

  // Add markers at downbeats (first beat of each measure)
  for (let i = 0; i < beatGrid.value.downbeats.length; i++) {
    const frame = beatGrid.value.downbeats[i];
    store.addMarker({
      frame,
      label: `Bar ${i + 1}`,
      color: '#8B5CF6'
    });
  }

  console.log(`[Weyl] Added ${beatGrid.value.downbeats.length} beat markers`);
}

// ============================================================================
// MIDI Functions
// ============================================================================

async function initMIDI() {
  const midiService = getMIDIService();
  midiAvailable.value = midiService.isAvailable();

  if (midiAvailable.value) {
    const success = await midiService.initialize();
    if (success) {
      midiDevices.value = midiService.getInputDevices();
    }
  }
}

async function refreshMIDIDevices() {
  isRefreshingMIDI.value = true;

  try {
    const midiService = getMIDIService();
    await midiService.initialize();
    midiDevices.value = midiService.getInputDevices();
    console.log(`[Weyl] Found ${midiDevices.value.length} MIDI devices`);
  } catch (error) {
    console.error('[Weyl] Failed to refresh MIDI devices:', error);
  } finally {
    isRefreshingMIDI.value = false;
  }
}

function handleMIDIMessage(message: MIDIMessage) {
  // Add to recent messages (keep last 10)
  recentMIDIMessages.value.unshift(message);
  if (recentMIDIMessages.value.length > 10) {
    recentMIDIMessages.value.pop();
  }
}

// Watch for monitor toggle
watch(midiMonitorEnabled, (enabled) => {
  const midiService = getMIDIService();

  if (enabled) {
    // Start listening
    midiService.addGlobalListener(handleMIDIMessage);
    midiListenerRemove = () => midiService.removeGlobalListener(handleMIDIMessage);
  } else {
    // Stop listening
    if (midiListenerRemove) {
      midiListenerRemove();
      midiListenerRemove = null;
    }
    recentMIDIMessages.value = [];
  }
});

// ============================================================================
// MIDI File to Keyframes Functions
// ============================================================================

function loadMIDIFile() {
  midiFileInput.value?.click();
}

async function handleMIDIFileSelected(e: Event) {
  const input = e.target as HTMLInputElement;
  if (!input.files?.length) return;

  const file = input.files[0];
  isLoadingMIDI.value = true;
  midiConvertError.value = null;
  midiConvertResult.value = null;

  try {
    const arrayBuffer = await file.arrayBuffer();
    loadedMIDIFile.value = await parseMIDIFile(arrayBuffer);
    midiFileName.value = file.name;
    console.log(`[Weyl] Loaded MIDI file: ${file.name}, ${loadedMIDIFile.value.tracks.length} tracks, ${loadedMIDIFile.value.duration.toFixed(2)}s`);
  } catch (err) {
    midiConvertError.value = err instanceof Error ? err.message : 'Failed to parse MIDI file';
    loadedMIDIFile.value = null;
  } finally {
    isLoadingMIDI.value = false;
    input.value = '';
  }
}

function removeMIDIFile() {
  loadedMIDIFile.value = null;
  midiFileName.value = '';
  midiConvertResult.value = null;
  midiConvertError.value = null;
}

const midiTracks = computed(() => {
  if (!loadedMIDIFile.value) return [];
  return loadedMIDIFile.value.tracks.map((t, i) => ({
    index: i,
    name: t.name || `Track ${i + 1}`,
    noteCount: t.notes.length,
    ccCount: t.controlChanges.length
  }));
});

const midiFileInfo = computed(() => {
  if (!loadedMIDIFile.value) return null;
  const totalNotes = loadedMIDIFile.value.tracks.reduce((sum, t) => sum + t.notes.length, 0);
  const totalCC = loadedMIDIFile.value.tracks.reduce((sum, t) => sum + t.controlChanges.length, 0);
  return {
    duration: loadedMIDIFile.value.duration.toFixed(2),
    trackCount: loadedMIDIFile.value.tracks.length,
    totalNotes,
    totalCC,
    bpm: loadedMIDIFile.value.tempos[loadedMIDIFile.value.tempos.length - 1]?.bpm?.toFixed(1) || '120'
  };
});

async function convertMIDIToKeyframes() {
  if (!loadedMIDIFile.value) {
    midiConvertError.value = 'No MIDI file loaded';
    return;
  }

  isConvertingMIDI.value = true;
  midiConvertError.value = null;
  midiConvertResult.value = null;

  try {
    const fps = store.fps || 16;
    const config: MIDIToKeyframeConfig = {
      trackIndex: midiTrackIndex.value,
      channel: midiChannel.value,
      mappingType: midiMappingType.value,
      ccNumber: midiMappingType.value === 'controlChange' ? midiCCNumber.value : undefined,
      valueMin: midiValueMin.value,
      valueMax: midiValueMax.value,
      fps,
      interpolation: midiInterpolation.value
    };

    const keyframes = midiMappingType.value === 'controlChange'
      ? midiCCToKeyframes(loadedMIDIFile.value, config)
      : midiNotesToKeyframes(loadedMIDIFile.value, config);

    if (keyframes.length === 0) {
      midiConvertError.value = 'No keyframes generated. Check track/channel selection.';
      return;
    }

    // Create a null layer with the keyframes
    const layer = store.addLayer('null', {
      name: midiLayerName.value || 'MIDI Animation'
    });

    if (layer) {
      // Apply keyframes to scale.x as a driver property
      layer.transform.scale = {
        id: `midi_scale_${Date.now()}`,
        name: 'Scale',
        defaultValue: { x: midiValueMin.value, y: midiValueMin.value, z: 1 },
        animated: true,
        keyframes: keyframes.map(kf => ({
          ...kf,
          value: { x: kf.value, y: kf.value, z: 1 }
        }))
      };

      midiConvertResult.value = {
        layerName: layer.name,
        keyframeCount: keyframes.length
      };

      console.log(`[Weyl] Created MIDI layer "${layer.name}" with ${keyframes.length} keyframes`);
    } else {
      midiConvertError.value = 'Failed to create layer';
    }
  } catch (err) {
    midiConvertError.value = err instanceof Error ? err.message : 'Unknown error';
  } finally {
    isConvertingMIDI.value = false;
  }
}

// Initialize MIDI on mount
onMounted(() => {
  initMIDI();
});

// Cleanup MIDI on unmount
onUnmounted(() => {
  if (midiListenerRemove) {
    midiListenerRemove();
  }
});
</script>

<style scoped>
.audio-panel { display: flex; flex-direction: column; height: 100%; background: #1e1e1e; color: #ccc; font-size: 13px; }
.panel-header { display: flex; justify-content: space-between; align-items: center; padding: 8px; background: #252525; border-bottom: 1px solid #111; font-weight: 600; }
.header-actions button { background: none; border: none; cursor: pointer; color: #aaa; padding: 4px; border-radius: 3px; }
.header-actions button:hover { background: #333; color: #fff; }
.panel-content { flex: 1; overflow-y: auto; }

.audio-info { padding: 10px; background: #222; border-bottom: 1px solid #333; }
.file-info { display: flex; align-items: center; gap: 8px; }
.file-icon { font-size: 20px; }
.file-details { flex: 1; display: flex; flex-direction: column; }
.file-name { font-weight: 500; color: #eee; }
.file-meta { color: #888; font-size: 12px; }
.remove-btn { background: none; border: none; color: #666; cursor: pointer; font-size: 16px; padding: 4px; }
.remove-btn:hover { color: #f44; }

.control-section { padding: 10px; border-bottom: 1px solid #333; }
.control-row { display: flex; align-items: center; gap: 8px; }
.control-row label { width: 70px; color: #888; flex-shrink: 0; }

.mute-btn {
  width: 28px; height: 28px; padding: 0;
  border: none; background: transparent;
  color: #888; border-radius: 3px; cursor: pointer;
  font-size: 14px; flex-shrink: 0;
}
.mute-btn:hover { background: #333; }
.mute-btn.active { color: #ff6b6b; }

.waveform-section { padding: 10px; border-bottom: 1px solid #333; background: #1a1a1a; }
.section-header { display: flex; align-items: center; margin-bottom: 8px; }
.section-title { font-weight: 500; color: #888; }
.waveform-display { height: 60px; background: #1a1a1a; border-radius: 4px; overflow: hidden; }
.waveform-canvas { width: 100%; height: 100%; display: block; }

.audio-values-section { padding: 10px; border-bottom: 1px solid #333; }

.linker-section { padding: 0; }
.linker-header { padding: 8px 10px; background: #2a2a2a; color: #4a90d9; font-weight: 600; border-bottom: 1px solid #333; }

/* Convert Audio to Keyframes Styles */
.convert-section { border-top: 1px solid #333; }
.convert-section .section-header.clickable { display: flex; align-items: center; gap: 8px; padding: 10px; background: #252525; cursor: pointer; user-select: none; }
.convert-section .section-header.clickable:hover { background: #2a2a2a; }
.convert-section .expand-icon { width: 12px; font-size: 10px; color: #666; }
.convert-section .section-title { flex: 1; font-weight: 600; color: #888; }

.convert-section .section-content { padding: 10px; background: #1a1a1a; display: flex; flex-direction: column; gap: 10px; }
.convert-section .section-description { margin: 0; font-size: 11px; color: #666; line-height: 1.4; }

.convert-section .text-input { flex: 1; padding: 6px 8px; background: #222; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; }
.convert-section .text-input:focus { outline: none; border-color: #4a90d9; }
.convert-section .text-input::placeholder { color: #555; }

.scale-slider, .smoothing-slider { flex: 1; height: 4px; accent-color: #4a90d9; }
.convert-section .value { width: 50px; text-align: right; font-size: 11px; color: #666; font-variant-numeric: tabular-nums; }

.convert-btn { padding: 8px 16px; background: #4a90d9; border: none; color: white; border-radius: 4px; cursor: pointer; font-size: 12px; font-weight: 500; transition: all 0.15s; }
.convert-btn:hover:not(:disabled) { background: #5aa0e9; }
.convert-btn:disabled { opacity: 0.5; cursor: not-allowed; }

.convert-result { display: flex; align-items: center; gap: 8px; padding: 8px; background: #10B98120; border: 1px solid #10B98140; border-radius: 4px; font-size: 12px; color: #10B981; }
.convert-result .result-icon { font-size: 14px; }

.empty-state { display: flex; flex-direction: column; align-items: center; justify-content: center; height: 100%; padding: 40px; text-align: center; color: #666; }
.empty-icon { font-size: 48px; margin-bottom: 12px; opacity: 0.5; }
.load-btn { padding: 8px 16px; background: #4a90d9; border: none; color: white; border-radius: 4px; cursor: pointer; margin-top: 12px; font-size: 12px; }
.load-btn:hover { background: #5aa0e9; }
.hint { font-size: 12px; margin-top: 8px; color: #555; }

/* Stem Separation Styles */
.stem-section { border-top: 1px solid #333; }
.stem-section .section-header.clickable { display: flex; align-items: center; gap: 8px; padding: 10px; background: #252525; cursor: pointer; user-select: none; }
.stem-section .section-header.clickable:hover { background: #2a2a2a; }
.stem-section .expand-icon { width: 12px; font-size: 10px; color: #666; }
.stem-section .section-title { flex: 1; font-weight: 600; color: #888; }
.stem-section .badge { background: #4a90d9; color: #fff; padding: 2px 6px; border-radius: 10px; font-size: 11px; }

.stem-section .section-content { padding: 10px; background: #1a1a1a; display: flex; flex-direction: column; gap: 10px; }

.model-select { flex: 1; padding: 6px 8px; background: #222; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; }
.model-select:focus { outline: none; border-color: #4a90d9; }

.preset-buttons { display: flex; flex-wrap: wrap; gap: 6px; }
.preset-btn { padding: 6px 10px; background: #2a2a2a; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; cursor: pointer; transition: all 0.15s; }
.preset-btn:hover:not(:disabled) { background: #3a3a3a; border-color: #4a90d9; color: #fff; }
.preset-btn:disabled { opacity: 0.5; cursor: not-allowed; }
.preset-btn.karaoke { border-color: #8B5CF6; }
.preset-btn.karaoke:hover:not(:disabled) { background: #8B5CF640; border-color: #8B5CF6; }
.preset-btn.all { border-color: #10B981; }
.preset-btn.all:hover:not(:disabled) { background: #10B98140; border-color: #10B981; }

.progress-row { display: flex; flex-direction: column; gap: 4px; }
.progress-bar { height: 4px; background: #333; border-radius: 2px; overflow: hidden; }
.progress-fill { height: 100%; background: linear-gradient(90deg, #4a90d9, #8B5CF6); transition: width 0.3s ease; }
.progress-text { font-size: 11px; color: #888; text-align: center; }

.stems-list { display: flex; flex-direction: column; gap: 4px; }
.stems-header { font-size: 11px; color: #666; text-transform: uppercase; letter-spacing: 0.5px; margin-bottom: 4px; }
.stem-item { display: flex; align-items: center; gap: 8px; padding: 6px 8px; background: #222; border-radius: 4px; }
.stem-icon { font-size: 14px; }
.stem-name { flex: 1; font-size: 12px; color: #ccc; text-transform: capitalize; }
.stem-btn { width: 24px; height: 24px; padding: 0; border: none; background: #333; color: #888; border-radius: 3px; cursor: pointer; font-size: 10px; display: flex; align-items: center; justify-content: center; }
.stem-btn:hover { background: #444; color: #fff; }
.stem-btn.play:hover { background: #4a90d9; }
.stem-btn.download:hover { background: #10B981; }
.stem-btn.use:hover { background: #8B5CF6; }

.error-message { padding: 8px; background: #ff4444; color: #fff; border-radius: 4px; font-size: 12px; }

/* Beat Detection Styles */
.beat-section { border-top: 1px solid #333; }
.beat-section .section-header.clickable { display: flex; align-items: center; gap: 8px; padding: 10px; background: #252525; cursor: pointer; user-select: none; }
.beat-section .section-header.clickable:hover { background: #2a2a2a; }
.beat-section .expand-icon { width: 12px; font-size: 10px; color: #666; }
.beat-section .section-title { flex: 1; font-weight: 600; color: #888; }
.beat-section .badge { background: #8B5CF6; color: #fff; padding: 2px 6px; border-radius: 10px; font-size: 11px; }

.beat-section .section-content { padding: 10px; background: #1a1a1a; display: flex; flex-direction: column; gap: 10px; }

.preset-select { flex: 1; padding: 6px 8px; background: #222; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; }
.preset-select:focus { outline: none; border-color: #8B5CF6; }

.beat-section .checkbox-row { display: flex; align-items: center; }
.beat-section .checkbox-row label { display: flex; align-items: center; gap: 8px; cursor: pointer; color: #aaa; font-size: 12px; }
.beat-section .checkbox-row input[type="checkbox"] { width: 14px; height: 14px; accent-color: #8B5CF6; }

.tolerance-slider { flex: 1; height: 4px; accent-color: #8B5CF6; }
.beat-section .value { width: 30px; text-align: right; font-size: 11px; color: #666; font-variant-numeric: tabular-nums; }

.analyze-btn { padding: 8px 16px; background: #8B5CF6; border: none; color: white; border-radius: 4px; cursor: pointer; font-size: 12px; font-weight: 500; transition: all 0.15s; }
.analyze-btn:hover:not(:disabled) { background: #9D6FF8; }
.analyze-btn:disabled { opacity: 0.5; cursor: not-allowed; }

.beat-results { padding: 10px; background: #222; border-radius: 4px; display: flex; flex-direction: column; gap: 8px; }
.result-row { display: flex; align-items: center; gap: 8px; font-size: 12px; }
.result-label { color: #888; }
.result-value { color: #fff; font-weight: 600; font-variant-numeric: tabular-nums; }
.confidence { font-size: 11px; padding: 2px 6px; border-radius: 10px; }
.confidence.high { background: #10B98140; color: #10B981; }
.confidence.medium { background: #F59E0B40; color: #F59E0B; }
.confidence.low { background: #EF444440; color: #EF4444; }

.beat-actions { display: flex; gap: 8px; margin-top: 4px; }
.beat-btn { padding: 6px 10px; background: #333; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 11px; cursor: pointer; transition: all 0.15s; }
.beat-btn:hover { background: #444; border-color: #8B5CF6; color: #fff; }

/* MIDI Section Styles */
.midi-section { border-top: 1px solid #333; }
.midi-section .section-header.clickable { display: flex; align-items: center; gap: 8px; padding: 10px; background: #252525; cursor: pointer; user-select: none; }
.midi-section .section-header.clickable:hover { background: #2a2a2a; }
.midi-section .expand-icon { width: 12px; font-size: 10px; color: #666; }
.midi-section .section-title { flex: 1; font-weight: 600; color: #888; }
.midi-section .badge { background: #10B981; color: #fff; padding: 2px 6px; border-radius: 10px; font-size: 11px; }
.midi-section .badge.unavailable { background: #666; }

.midi-section .section-content { padding: 10px; background: #1a1a1a; display: flex; flex-direction: column; gap: 10px; }

.midi-unavailable { text-align: center; color: #888; padding: 12px; }
.midi-unavailable p { margin: 4px 0; }

.refresh-btn { padding: 6px 12px; background: #333; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; cursor: pointer; transition: all 0.15s; }
.refresh-btn:hover:not(:disabled) { background: #444; border-color: #10B981; }
.refresh-btn:disabled { opacity: 0.5; cursor: not-allowed; }

.no-devices { text-align: center; color: #666; padding: 12px; }
.no-devices p { margin: 4px 0; }

.device-list { display: flex; flex-direction: column; gap: 6px; }
.device-item { display: flex; align-items: center; gap: 8px; padding: 8px; background: #222; border-radius: 4px; }
.device-icon { font-size: 16px; }
.device-info { flex: 1; display: flex; flex-direction: column; gap: 2px; }
.device-name { font-size: 12px; color: #ddd; }
.device-meta { font-size: 10px; color: #666; }
.device-status { font-size: 10px; padding: 2px 6px; border-radius: 10px; text-transform: uppercase; }
.device-status.connected { background: #10B98140; color: #10B981; }
.device-status.disconnected { background: #EF444440; color: #EF4444; }

.midi-monitor { background: #222; border-radius: 4px; overflow: hidden; }
.monitor-header { display: flex; justify-content: space-between; align-items: center; padding: 8px; background: #2a2a2a; }
.monitor-header span { font-size: 11px; color: #888; text-transform: uppercase; letter-spacing: 0.5px; }
.monitor-toggle { display: flex; align-items: center; gap: 6px; cursor: pointer; font-size: 11px; color: #888; }
.monitor-toggle input { width: 14px; height: 14px; accent-color: #10B981; }

.monitor-messages { max-height: 150px; overflow-y: auto; }
.midi-message { display: flex; gap: 6px; padding: 4px 8px; font-size: 10px; font-family: monospace; border-bottom: 1px solid #333; }
.midi-message.note-on { background: #10B98110; }
.midi-message.note-off { background: #EF444410; }
.midi-message.control-change { background: #8B5CF610; }
.msg-type { color: #888; width: 80px; }
.msg-channel { color: #4a90d9; }
.msg-note { color: #10B981; }
.msg-value { color: #8B5CF6; }
.msg-velocity { color: #F59E0B; }

.no-messages { padding: 16px; text-align: center; color: #555; font-size: 11px; }

/* MIDI File to Keyframes Styles */
.midi-file-section { border-top: 1px solid #333; }
.midi-file-section .section-header.clickable { display: flex; align-items: center; gap: 8px; padding: 10px; background: #252525; cursor: pointer; user-select: none; }
.midi-file-section .section-header.clickable:hover { background: #2a2a2a; }
.midi-file-section .expand-icon { width: 12px; font-size: 10px; color: #666; }
.midi-file-section .section-title { flex: 1; font-weight: 600; color: #888; }
.midi-file-section .badge { background: #8B5CF6; color: #fff; padding: 2px 6px; border-radius: 10px; font-size: 11px; }

.midi-file-section .section-content { padding: 10px; background: #1a1a1a; display: flex; flex-direction: column; gap: 10px; }

.midi-load-area { display: flex; justify-content: center; padding: 12px; }
.load-midi-btn { padding: 10px 20px; background: #8B5CF6; border: none; color: white; border-radius: 4px; cursor: pointer; font-size: 12px; font-weight: 500; transition: all 0.15s; }
.load-midi-btn:hover:not(:disabled) { background: #9D6FF8; }
.load-midi-btn:disabled { opacity: 0.5; cursor: not-allowed; }

.midi-file-info { display: flex; flex-direction: column; gap: 10px; }
.midi-file-info .file-row { display: flex; align-items: center; gap: 8px; padding: 8px; background: #222; border-radius: 4px; }
.midi-file-info .file-icon { font-size: 20px; }
.midi-file-info .file-details { flex: 1; display: flex; flex-direction: column; gap: 2px; }
.midi-file-info .file-name { font-size: 12px; color: #ddd; font-weight: 500; }
.midi-file-info .file-meta { font-size: 10px; color: #888; }

.midi-file-info .track-select,
.midi-file-info .channel-select,
.midi-file-info .mapping-select,
.midi-file-info .cc-select,
.midi-file-info .interp-select { flex: 1; padding: 6px 8px; background: #222; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; }
.midi-file-info select:focus { outline: none; border-color: #8B5CF6; }

.midi-file-info .value-input { width: 60px; padding: 6px 8px; background: #222; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; text-align: center; }
.midi-file-info .value-input:focus { outline: none; border-color: #8B5CF6; }

.midi-file-info .text-input { flex: 1; padding: 6px 8px; background: #222; border: 1px solid #444; color: #ccc; border-radius: 4px; font-size: 12px; }
.midi-file-info .text-input:focus { outline: none; border-color: #8B5CF6; }

.convert-midi-btn { padding: 10px 16px; background: #8B5CF6; border: none; color: white; border-radius: 4px; cursor: pointer; font-size: 12px; font-weight: 500; transition: all 0.15s; }
.convert-midi-btn:hover:not(:disabled) { background: #9D6FF8; }
.convert-midi-btn:disabled { opacity: 0.5; cursor: not-allowed; }
</style>
