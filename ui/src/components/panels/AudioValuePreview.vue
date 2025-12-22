<script setup lang="ts">
/**
 * Audio Value Preview Panel
 *
 * Shows real-time audio feature values at the current frame.
 * Updates as the user scrubs through the timeline.
 *
 * Features displayed:
 * - Amplitude (with bar visualization)
 * - Frequency bands (bass, mid, high)
 * - HPSS (harmonic/percussive)
 * - Beat indicator
 * - Spectral features
 */

import { computed, ref, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { getFeatureAtFrame, isBeatAtFrame } from '@/services/audioFeatures';

const store = useCompositorStore();

// Whether to show expanded view
const expanded = ref(false);

// Get current frame
const currentFrame = computed(() => store.currentFrame);

// Check if audio is loaded
const hasAudio = computed(() => !!store.audioAnalysis);

// Audio analysis data
const audioAnalysis = computed(() => store.audioAnalysis);

// Feature values at current frame
const amplitude = computed(() => {
  if (!audioAnalysis.value) return 0;
  return getFeatureAtFrame(audioAnalysis.value, 'amplitude', currentFrame.value);
});

const bass = computed(() => {
  if (!audioAnalysis.value) return 0;
  return getFeatureAtFrame(audioAnalysis.value, 'bass', currentFrame.value);
});

const mid = computed(() => {
  if (!audioAnalysis.value) return 0;
  return getFeatureAtFrame(audioAnalysis.value, 'mid', currentFrame.value);
});

const high = computed(() => {
  if (!audioAnalysis.value) return 0;
  return getFeatureAtFrame(audioAnalysis.value, 'high', currentFrame.value);
});

const isBeat = computed(() => {
  if (!audioAnalysis.value) return false;
  return isBeatAtFrame(audioAnalysis.value, currentFrame.value);
});

// HPSS values
const harmonic = computed(() => {
  if (!audioAnalysis.value?.harmonicEnergy) return 0;
  return audioAnalysis.value.harmonicEnergy[currentFrame.value] ?? 0;
});

const percussive = computed(() => {
  if (!audioAnalysis.value?.percussiveEnergy) return 0;
  return audioAnalysis.value.percussiveEnergy[currentFrame.value] ?? 0;
});

// Spectral features
const spectralCentroid = computed(() => {
  if (!audioAnalysis.value) return 0;
  return getFeatureAtFrame(audioAnalysis.value, 'spectralCentroid', currentFrame.value);
});

const spectralFlux = computed(() => {
  if (!audioAnalysis.value) return 0;
  return getFeatureAtFrame(audioAnalysis.value, 'spectralFlux', currentFrame.value);
});

// Format percentage
const formatPercent = (value: number) => `${Math.round(value * 100)}%`;

// Toggle expanded view
const toggleExpanded = () => {
  expanded.value = !expanded.value;
};
</script>

<template>
  <div class="audio-value-preview" v-if="hasAudio">
    <!-- Header -->
    <div class="preview-header" @click="toggleExpanded">
      <span class="header-title">Audio Values</span>
      <span class="beat-indicator" :class="{ active: isBeat }">BEAT</span>
      <span class="expand-icon">{{ expanded ? '▼' : '▶' }}</span>
    </div>

    <!-- Main values (always visible) -->
    <div class="main-values">
      <div class="value-row">
        <span class="value-label">Amplitude</span>
        <div class="value-bar-container">
          <div class="value-bar amplitude" :style="{ width: formatPercent(amplitude) }"></div>
        </div>
        <span class="value-text">{{ formatPercent(amplitude) }}</span>
      </div>

      <div class="frequency-bands">
        <div class="band">
          <div class="band-bar bass" :style="{ height: formatPercent(bass) }"></div>
          <span class="band-label">Bass</span>
        </div>
        <div class="band">
          <div class="band-bar mid" :style="{ height: formatPercent(mid) }"></div>
          <span class="band-label">Mid</span>
        </div>
        <div class="band">
          <div class="band-bar high" :style="{ height: formatPercent(high) }"></div>
          <span class="band-label">High</span>
        </div>
      </div>
    </div>

    <!-- Expanded values -->
    <div class="expanded-values" v-if="expanded">
      <div class="section-title">HPSS (Harmonic/Percussive)</div>
      <div class="value-row">
        <span class="value-label">Harmonic</span>
        <div class="value-bar-container">
          <div class="value-bar harmonic" :style="{ width: formatPercent(harmonic) }"></div>
        </div>
        <span class="value-text">{{ formatPercent(harmonic) }}</span>
      </div>
      <div class="value-row">
        <span class="value-label">Percussive</span>
        <div class="value-bar-container">
          <div class="value-bar percussive" :style="{ width: formatPercent(percussive) }"></div>
        </div>
        <span class="value-text">{{ formatPercent(percussive) }}</span>
      </div>

      <div class="section-title">Spectral</div>
      <div class="value-row">
        <span class="value-label">Centroid</span>
        <div class="value-bar-container">
          <div class="value-bar spectral" :style="{ width: formatPercent(spectralCentroid) }"></div>
        </div>
        <span class="value-text">{{ formatPercent(spectralCentroid) }}</span>
      </div>
      <div class="value-row">
        <span class="value-label">Flux</span>
        <div class="value-bar-container">
          <div class="value-bar spectral" :style="{ width: formatPercent(spectralFlux) }"></div>
        </div>
        <span class="value-text">{{ formatPercent(spectralFlux) }}</span>
      </div>

      <div class="section-title">Info</div>
      <div class="info-row">
        <span>BPM:</span>
        <span class="info-value">{{ audioAnalysis?.bpm?.toFixed(1) ?? 'N/A' }}</span>
      </div>
      <div class="info-row">
        <span>Frame:</span>
        <span class="info-value">{{ currentFrame }} / {{ audioAnalysis?.frameCount ?? 0 }}</span>
      </div>
    </div>
  </div>

  <!-- No audio message -->
  <div class="no-audio" v-else>
    <span>Load audio to see values</span>
  </div>
</template>

<style scoped>
.audio-value-preview {
  background: var(--weyl-surface-1, #121212);
  border-radius: var(--weyl-radius-md, 4px);
  padding: 8px;
  font-size: 11px;
}

.preview-header {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  padding-bottom: 8px;
  border-bottom: 1px solid var(--weyl-border-subtle, #2a2a2a);
  margin-bottom: 8px;
}

.header-title {
  font-weight: 600;
  color: var(--weyl-text-primary, #e5e5e5);
  flex: 1;
}

.beat-indicator {
  padding: 2px 6px;
  border-radius: 3px;
  font-size: 9px;
  font-weight: 700;
  background: var(--weyl-surface-2, #1a1a1a);
  color: var(--weyl-text-muted, #6b7280);
  transition: all 0.1s ease;
}

.beat-indicator.active {
  background: var(--weyl-accent, #8b5cf6);
  color: white;
  box-shadow: 0 0 8px var(--weyl-accent, #8b5cf6);
}

.expand-icon {
  color: var(--weyl-text-muted, #6b7280);
  font-size: 10px;
}

.main-values {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.value-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.value-label {
  width: 70px;
  color: var(--weyl-text-secondary, #9ca3af);
  flex-shrink: 0;
}

.value-bar-container {
  flex: 1;
  height: 8px;
  background: var(--weyl-surface-0, #0a0a0a);
  border-radius: 4px;
  overflow: hidden;
}

.value-bar {
  height: 100%;
  border-radius: 4px;
  transition: width 0.05s ease;
}

.value-bar.amplitude {
  background: linear-gradient(90deg, var(--weyl-accent, #8b5cf6), var(--weyl-accent-secondary, #ec4899));
}

.value-bar.harmonic {
  background: #10b981;
}

.value-bar.percussive {
  background: #f59e0b;
}

.value-bar.spectral {
  background: #06b6d4;
}

.value-text {
  width: 40px;
  text-align: right;
  color: var(--weyl-text-primary, #e5e5e5);
  font-family: monospace;
}

.frequency-bands {
  display: flex;
  justify-content: space-around;
  height: 50px;
  padding: 8px 0;
  gap: 4px;
}

.band {
  display: flex;
  flex-direction: column;
  align-items: center;
  flex: 1;
}

.band-bar {
  width: 100%;
  max-width: 30px;
  border-radius: 3px;
  transition: height 0.05s ease;
}

.band-bar.bass {
  background: #ef4444;
}

.band-bar.mid {
  background: #f59e0b;
}

.band-bar.high {
  background: #10b981;
}

.band-label {
  margin-top: 4px;
  font-size: 9px;
  color: var(--weyl-text-muted, #6b7280);
}

.expanded-values {
  margin-top: 12px;
  padding-top: 12px;
  border-top: 1px solid var(--weyl-border-subtle, #2a2a2a);
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.section-title {
  font-size: 9px;
  font-weight: 600;
  color: var(--weyl-text-muted, #6b7280);
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-top: 8px;
  margin-bottom: 4px;
}

.section-title:first-child {
  margin-top: 0;
}

.info-row {
  display: flex;
  justify-content: space-between;
  color: var(--weyl-text-secondary, #9ca3af);
}

.info-value {
  color: var(--weyl-text-primary, #e5e5e5);
  font-family: monospace;
}

.no-audio {
  padding: 16px;
  text-align: center;
  color: var(--weyl-text-muted, #6b7280);
  font-size: 11px;
}
</style>
