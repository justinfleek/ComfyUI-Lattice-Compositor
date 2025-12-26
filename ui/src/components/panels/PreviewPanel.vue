<template>
  <div class="preview-panel">
    <div class="panel-header">
      <span class="panel-title">Preview</span>
    </div>

    <div class="panel-content">
      <!-- Playback Controls -->
      <div class="playback-section">
        <div class="control-row">
          <button
            class="transport-btn"
            @click="goToStart"
            title="Go to Start (Home)"
          >
            ⏮
          </button>
          <button
            class="transport-btn"
            @click="stepBackward"
            title="Step Backward (,)"
          >
            ◀
          </button>
          <button
            class="transport-btn play-btn"
            :class="{ playing: isPlaying }"
            @click="togglePlayback"
            title="Play/Pause (Space)"
          >
            {{ isPlaying ? '⏸' : '▶' }}
          </button>
          <button
            class="transport-btn"
            @click="stepForward"
            title="Step Forward (.)"
          >
            ▶
          </button>
          <button
            class="transport-btn"
            @click="goToEnd"
            title="Go to End (End)"
          >
            ⏭
          </button>
        </div>

        <div class="control-row">
          <label>
            <input type="checkbox" v-model="loopPlayback" />
            Loop
          </label>
          <select v-model="playbackSpeed" class="speed-select">
            <option :value="0.25">0.25x</option>
            <option :value="0.5">0.5x</option>
            <option :value="1">1x</option>
            <option :value="2">2x</option>
            <option :value="4">4x</option>
          </select>
        </div>
      </div>

      <!-- Frame Range -->
      <div class="range-section">
        <div class="range-row">
          <label>
            Render Range:
            <input
              type="number"
              v-model.number="renderRangeStart"
              :min="0"
              :max="frameCount - 1"
              class="frame-input"
            />
            -
            <input
              type="number"
              v-model.number="renderRangeEnd"
              :min="renderRangeStart"
              :max="frameCount"
              class="frame-input"
            />
          </label>
        </div>
        <div class="frame-info">
          Frame {{ currentFrame }} / {{ frameCount }}
          ({{ formattedTime }})
        </div>
      </div>

      <!-- Cache Controls -->
      <div class="cache-section">
        <div class="section-header">Particle Cache</div>

        <div v-if="particleLayers.length === 0" class="no-particles">
          No particle layers in composition
        </div>

        <div v-else>
          <div class="cache-controls">
            <button
              class="cache-btn"
              @click="cacheRenderRange"
              :disabled="isCaching"
              title="Pre-cache particle frames for smooth playback"
            >
              {{ isCaching ? 'Caching...' : 'Cache Render Range' }}
            </button>
            <button
              class="cache-btn secondary"
              @click="clearAllCaches"
              :disabled="isCaching"
              title="Clear all cached particle frames"
            >
              Clear Cache
            </button>
          </div>

          <div v-if="isCaching" class="progress-container">
            <div class="progress-bar">
              <div
                class="progress-fill"
                :style="{ width: `${cacheProgress}%` }"
              ></div>
            </div>
            <span class="progress-text">{{ cacheProgressText }}</span>
          </div>

          <div class="cache-stats">
            <div v-for="layer in particleLayers" :key="layer.id" class="layer-cache-info">
              <span class="layer-name">{{ layer.name }}</span>
              <span class="cache-count">{{ getCacheCount(layer.id) }} frames cached</span>
            </div>
          </div>
        </div>
      </div>

      <!-- Render Quality -->
      <div class="quality-section">
        <div class="section-header">Preview Quality</div>
        <div class="quality-row">
          <label>Resolution:</label>
          <select v-model="previewResolution" class="quality-select">
            <option :value="1">Full (100%)</option>
            <option :value="0.5">Half (50%)</option>
            <option :value="0.25">Quarter (25%)</option>
            <option :value="0.125">Eighth (12.5%)</option>
          </select>
        </div>
        <div class="quality-row">
          <label>
            <input type="checkbox" v-model="adaptiveQuality" />
            Adaptive (reduce during playback)
          </label>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { storeToRefs } from 'pinia';
import type { ParticleLayer } from '@/engine/layers/ParticleLayer';
import type { LatticeEngine } from '@/engine/LatticeEngine';

const props = defineProps<{
  engine?: LatticeEngine | null;
}>();

const store = useCompositorStore();
const {
  currentFrame,
  fps,
  frameCount,
  layers,
  isPlaying,
} = storeToRefs(store);

// Playback state
const loopPlayback = ref(true);
const playbackSpeed = ref(1);
const renderRangeStart = ref(0);
const renderRangeEnd = ref(81); // Default 81 frames

// Cache state
const isCaching = ref(false);
const cacheProgress = ref(0);
const currentCachingFrame = ref(0);
const totalFramesToCache = ref(0);

// Quality settings
const previewResolution = ref(1);
const adaptiveQuality = ref(true);

// Cache stats per layer
const cacheStats = ref<Map<string, { cachedFrames: number }>>(new Map());

// Computed
const formattedTime = computed(() => {
  const seconds = currentFrame.value / fps.value;
  const minutes = Math.floor(seconds / 60);
  const secs = (seconds % 60).toFixed(2);
  return `${minutes}:${secs.padStart(5, '0')}`;
});

const cacheProgressText = computed(() => {
  if (!isCaching.value) return '';
  return `${currentCachingFrame.value} / ${totalFramesToCache.value}`;
});

const particleLayers = computed(() => {
  return layers.value.filter(l => l.type === 'particles');
});

// Methods
function togglePlayback() {
  store.togglePlayback();
}

function goToStart() {
  store.setCurrentFrame(renderRangeStart.value);
}

function goToEnd() {
  store.setCurrentFrame(renderRangeEnd.value - 1);
}

function stepForward() {
  const next = Math.min(currentFrame.value + 1, frameCount.value - 1);
  store.setCurrentFrame(next);
}

function stepBackward() {
  const prev = Math.max(currentFrame.value - 1, 0);
  store.setCurrentFrame(prev);
}

function getCacheCount(layerId: string): number {
  return cacheStats.value.get(layerId)?.cachedFrames ?? 0;
}

async function cacheRenderRange() {
  if (isCaching.value) return;

  const particleLayerObjects = getParticleLayerObjects();
  if (particleLayerObjects.length === 0) return;

  isCaching.value = true;
  cacheProgress.value = 0;
  totalFramesToCache.value = renderRangeEnd.value - renderRangeStart.value;
  currentCachingFrame.value = 0;

  try {
    // Cache each particle layer
    for (const layer of particleLayerObjects) {
      await layer.preCacheFrames(
        renderRangeStart.value,
        renderRangeEnd.value - 1,
        (current, total) => {
          currentCachingFrame.value = current;
          cacheProgress.value = (current / total) * 100;
        }
      );

      // Update cache stats for this layer
      const stats = layer.getCacheStats();
      cacheStats.value.set(layer.id, { cachedFrames: stats.cachedFrames });
    }
  } catch (error) {
    console.error('Error caching particle frames:', error);
  } finally {
    isCaching.value = false;
    cacheProgress.value = 100;
  }
}

function clearAllCaches() {
  const particleLayerObjects = getParticleLayerObjects();
  for (const layer of particleLayerObjects) {
    layer.clearCache();
    cacheStats.value.set(layer.id, { cachedFrames: 0 });
  }
}

function getParticleLayerObjects(): ParticleLayer[] {
  // Get the actual layer objects from the engine
  if (!props.engine) return [];

  const result: ParticleLayer[] = [];
  for (const layerData of particleLayers.value) {
    const layer = props.engine.getLayerById(layerData.id);
    if (layer && 'preCacheFrames' in layer) {
      result.push(layer as ParticleLayer);
    }
  }
  return result;
}

function updateCacheStats() {
  const particleLayerObjects = getParticleLayerObjects();
  for (const layer of particleLayerObjects) {
    const stats = layer.getCacheStats();
    cacheStats.value.set(layer.id, { cachedFrames: stats.cachedFrames });
  }
}

// Initialize render range from composition
watch(frameCount, (newCount) => {
  if (renderRangeEnd.value > newCount) {
    renderRangeEnd.value = newCount;
  }
}, { immediate: true });

// Update cache stats periodically
let statsInterval: number | null = null;

onMounted(() => {
  updateCacheStats();
  statsInterval = window.setInterval(updateCacheStats, 2000);
});

onUnmounted(() => {
  if (statsInterval !== null) {
    clearInterval(statsInterval);
  }
});

// Expose playback speed and loop to parent if needed
defineExpose({
  playbackSpeed,
  loopPlayback,
  previewResolution,
  adaptiveQuality,
});
</script>

<style scoped>
.preview-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--surface-ground);
  color: var(--text-color);
}

.panel-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 8px 12px;
  background: var(--surface-section);
  border-bottom: 1px solid var(--surface-border);
}

.panel-title {
  font-weight: 600;
  font-size: 13px;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
  padding: 12px;
  display: flex;
  flex-direction: column;
  gap: 16px;
}

/* Playback Section */
.playback-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.control-row {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
}

.transport-btn {
  width: 32px;
  height: 32px;
  border: 1px solid var(--surface-border);
  background: var(--surface-card);
  border-radius: 4px;
  cursor: pointer;
  font-size: 14px;
  display: flex;
  align-items: center;
  justify-content: center;
  transition: all 0.15s;
}

.transport-btn:hover {
  background: var(--surface-hover);
}

.transport-btn:active {
  background: var(--primary-color);
  color: white;
}

.play-btn {
  width: 40px;
  height: 40px;
  font-size: 18px;
}

.play-btn.playing {
  background: var(--primary-color);
  color: white;
  border-color: var(--primary-color);
}

.speed-select {
  padding: 4px 8px;
  border: 1px solid var(--surface-border);
  background: var(--surface-card);
  border-radius: 4px;
  color: var(--text-color);
  font-size: 12px;
}

/* Range Section */
.range-section {
  display: flex;
  flex-direction: column;
  gap: 6px;
  padding: 8px;
  background: var(--surface-card);
  border-radius: 4px;
}

.range-row {
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 12px;
}

.frame-input {
  width: 60px;
  padding: 4px 6px;
  border: 1px solid var(--surface-border);
  background: var(--surface-ground);
  border-radius: 3px;
  color: var(--text-color);
  font-size: 12px;
}

.frame-info {
  font-size: 11px;
  color: var(--text-color-secondary);
  text-align: center;
}

/* Cache Section */
.cache-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
  padding: 8px;
  background: var(--surface-card);
  border-radius: 4px;
}

.section-header {
  font-weight: 600;
  font-size: 12px;
  color: var(--text-color-secondary);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.no-particles {
  font-size: 12px;
  color: var(--text-color-secondary);
  font-style: italic;
  text-align: center;
  padding: 8px;
}

.cache-controls {
  display: flex;
  gap: 8px;
}

.cache-btn {
  flex: 1;
  padding: 8px 12px;
  border: 1px solid var(--surface-border);
  background: var(--primary-color);
  color: white;
  border-radius: 4px;
  cursor: pointer;
  font-size: 12px;
  font-weight: 500;
  transition: all 0.15s;
}

.cache-btn:hover:not(:disabled) {
  filter: brightness(1.1);
}

.cache-btn:disabled {
  opacity: 0.6;
  cursor: not-allowed;
}

.cache-btn.secondary {
  background: var(--surface-ground);
  color: var(--text-color);
}

.cache-btn.secondary:hover:not(:disabled) {
  background: var(--surface-hover);
}

.progress-container {
  display: flex;
  align-items: center;
  gap: 8px;
}

.progress-bar {
  flex: 1;
  height: 6px;
  background: var(--surface-ground);
  border-radius: 3px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: var(--primary-color);
  transition: width 0.1s linear;
}

.progress-text {
  font-size: 11px;
  color: var(--text-color-secondary);
  min-width: 60px;
  text-align: right;
}

.cache-stats {
  display: flex;
  flex-direction: column;
  gap: 4px;
  margin-top: 4px;
}

.layer-cache-info {
  display: flex;
  justify-content: space-between;
  font-size: 11px;
  color: var(--text-color-secondary);
}

.layer-name {
  font-weight: 500;
}

.cache-count {
  color: var(--primary-color);
}

/* Quality Section */
.quality-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
  padding: 8px;
  background: var(--surface-card);
  border-radius: 4px;
}

.quality-row {
  display: flex;
  align-items: center;
  gap: 8px;
  font-size: 12px;
}

.quality-select {
  flex: 1;
  padding: 4px 8px;
  border: 1px solid var(--surface-border);
  background: var(--surface-ground);
  border-radius: 4px;
  color: var(--text-color);
  font-size: 12px;
}

/* Dark theme adjustments */
:deep(.p-checkbox) {
  width: 16px;
  height: 16px;
}

label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
}

input[type="checkbox"] {
  cursor: pointer;
}
</style>
