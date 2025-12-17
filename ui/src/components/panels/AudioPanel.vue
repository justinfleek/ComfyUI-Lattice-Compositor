<template>
  <div class="audio-panel">
    <div class="panel-header">
      <span class="panel-title">Audio Source</span>
      <div class="header-actions">
        <button @click="loadAudioFile" title="Load Audio">
          <span class="icon">📁</span>
        </button>
      </div>
    </div>

    <div class="panel-content" v-if="hasAudio">
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

      <div class="control-section">
        <div class="control-row">
          <label>Master Vol</label>
          <SliderInput v-model="masterVolume" :min="0" :max="100" unit="%" />
          <button class="mute-btn" :class="{ active: isMuted }" @click="toggleMute" title="Mute">
            {{ isMuted ? '🔇' : '🔊' }}
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

      <div class="linker-section">
        <div class="linker-header">Audio Linker</div>
        <AudioProperties />
      </div>

    </div>

    <div v-else class="empty-state">
      <div class="empty-icon">🎵</div>
      <p>No audio loaded</p>
      <button class="load-btn" @click="loadAudioFile">Load Audio File</button>
      <p class="hint">Supports MP3, WAV, OGG, AAC</p>
    </div>

    <input ref="audioFileInput" type="file" accept="audio/*" style="display: none" @change="handleAudioFileSelected" />
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { SliderInput } from '@/components/controls';
import AudioProperties from '@/components/properties/AudioProperties.vue';

const store = useCompositorStore();
const audioFileInput = ref<HTMLInputElement | null>(null);
const waveformCanvas = ref<HTMLCanvasElement | null>(null);

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
</script>

<style scoped>
.audio-panel { display: flex; flex-direction: column; height: 100%; background: #1e1e1e; color: #ccc; font-size: 11px; }
.panel-header { display: flex; justify-content: space-between; align-items: center; padding: 8px; background: #252525; border-bottom: 1px solid #111; font-weight: 600; }
.header-actions button { background: none; border: none; cursor: pointer; color: #aaa; padding: 4px; border-radius: 3px; }
.header-actions button:hover { background: #333; color: #fff; }
.panel-content { flex: 1; overflow-y: auto; }

.audio-info { padding: 10px; background: #222; border-bottom: 1px solid #333; }
.file-info { display: flex; align-items: center; gap: 8px; }
.file-icon { font-size: 20px; }
.file-details { flex: 1; display: flex; flex-direction: column; }
.file-name { font-weight: 500; color: #eee; }
.file-meta { color: #888; font-size: 10px; }
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

.linker-section { padding: 0; }
.linker-header { padding: 8px 10px; background: #2a2a2a; color: #4a90d9; font-weight: 600; border-bottom: 1px solid #333; }

.empty-state { display: flex; flex-direction: column; align-items: center; justify-content: center; height: 100%; padding: 40px; text-align: center; color: #666; }
.empty-icon { font-size: 48px; margin-bottom: 12px; opacity: 0.5; }
.load-btn { padding: 8px 16px; background: #4a90d9; border: none; color: white; border-radius: 4px; cursor: pointer; margin-top: 12px; font-size: 12px; }
.load-btn:hover { background: #5aa0e9; }
.hint { font-size: 10px; margin-top: 8px; color: #555; }
</style>
