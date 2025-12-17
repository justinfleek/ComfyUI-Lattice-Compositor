/**
 * Audio Actions
 *
 * Audio loading, analysis, reactive mappings, and path animation.
 * Extracted from compositorStore for better maintainability.
 */

import { storeLogger } from '@/utils/logger';
import type { AudioAnalysis, PeakData, PeakDetectionConfig } from '@/services/audioFeatures';
import { getFeatureAtFrame, detectPeaks, isBeatAtFrame } from '@/services/audioFeatures';
import { loadAndAnalyzeAudio, cancelAnalysis } from '@/services/audioWorkerClient';
import type { AudioMapping, TargetParameter } from '@/services/audioReactiveMapping';
import { AudioReactiveMapper } from '@/services/audioReactiveMapping';
import { AudioPathAnimator, type PathAnimatorConfig } from '@/services/audioPathAnimator';
import type { AudioParticleMapping } from '@/types/project';

export interface AudioStore {
  // State
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;
  audioVolume: number;
  audioMuted: boolean;
  audioLoadingState: 'idle' | 'decoding' | 'analyzing' | 'complete' | 'error';
  audioLoadingProgress: number;
  audioLoadingPhase: string;
  audioLoadingError: string | null;
  audioMappings: Map<string, AudioParticleMapping[]>;
  peakData: PeakData | null;
  audioReactiveMappings: AudioMapping[];
  audioReactiveMapper: AudioReactiveMapper | null;
  pathAnimators: Map<string, AudioPathAnimator>;
  propertyDriverSystem: { setAudioAnalysis(analysis: AudioAnalysis): void } | null;

  // Methods the store must provide
  getActiveComp(): { currentFrame: number } | null;
  project: { composition: { fps: number } };
}

/**
 * Load audio file using Web Worker (non-blocking)
 */
export async function loadAudio(store: AudioStore, file: File): Promise<void> {
  store.audioFile = file;
  store.audioBuffer = null;
  store.audioAnalysis = null;
  store.audioLoadingState = 'decoding';
  store.audioLoadingProgress = 0;
  store.audioLoadingPhase = 'Preparing...';
  store.audioLoadingError = null;

  try {
    const result = await loadAndAnalyzeAudio(
      file,
      store.project.composition.fps,
      {
        onProgress: (progress) => {
          if (progress.phase === 'decoding') {
            store.audioLoadingState = 'decoding';
          } else {
            store.audioLoadingState = 'analyzing';
          }
          store.audioLoadingProgress = progress.progress;
          store.audioLoadingPhase = progress.message;
        }
      }
    );

    store.audioBuffer = result.buffer;
    store.audioAnalysis = result.analysis;
    store.audioLoadingState = 'complete';
    store.audioLoadingProgress = 1;
    store.audioLoadingPhase = 'Complete';

    // Initialize the audio reactive mapper
    initializeAudioReactiveMapper(store);

    // Update property driver system with new audio data
    if (store.propertyDriverSystem && store.audioAnalysis) {
      store.propertyDriverSystem.setAudioAnalysis(store.audioAnalysis);
    }

    storeLogger.debug('Audio loaded:', {
      duration: store.audioBuffer.duration,
      bpm: store.audioAnalysis.bpm,
      frameCount: store.audioAnalysis.frameCount
    });
  } catch (error) {
    storeLogger.error('Failed to load audio:', error);
    store.audioFile = null;
    store.audioBuffer = null;
    store.audioAnalysis = null;
    store.audioReactiveMapper = null;
    store.audioLoadingState = 'error';
    store.audioLoadingError = (error as Error).message;
  }
}

/**
 * Cancel ongoing audio analysis
 */
export function cancelAudioLoad(store: AudioStore): void {
  cancelAnalysis();
  store.audioLoadingState = 'idle';
  store.audioLoadingProgress = 0;
  store.audioLoadingPhase = '';
  store.audioLoadingError = null;
}

/**
 * Clear loaded audio
 */
export function clearAudio(store: AudioStore): void {
  cancelAudioLoad(store);
  store.audioFile = null;
  store.audioBuffer = null;
  store.audioAnalysis = null;
  store.audioMappings.clear();
}

/**
 * Get audio feature value at frame
 */
export function getAudioFeatureAtFrame(
  store: AudioStore,
  feature: string,
  frame?: number
): number {
  if (!store.audioAnalysis) return 0;
  return getFeatureAtFrame(store.audioAnalysis, feature, frame ?? (store.getActiveComp()?.currentFrame ?? 0));
}

/**
 * Set peak data
 */
export function setPeakData(store: AudioStore, peakData: PeakData): void {
  store.peakData = peakData;
  if (store.audioReactiveMapper) {
    store.audioReactiveMapper.setPeakData(peakData);
  }
}

/**
 * Detect peaks with config
 */
export function detectAudioPeaks(
  store: AudioStore,
  config: PeakDetectionConfig
): PeakData | null {
  if (!store.audioAnalysis) return null;

  const weights = store.audioAnalysis.amplitudeEnvelope;
  const peakData = detectPeaks(weights, config);
  store.peakData = peakData;

  if (store.audioReactiveMapper) {
    store.audioReactiveMapper.setPeakData(peakData);
  }

  return peakData;
}

/**
 * Add new audio mapping
 */
export function addAudioMapping(store: AudioStore, mapping: AudioMapping): void {
  store.audioReactiveMappings.push(mapping);

  if (store.audioReactiveMapper) {
    store.audioReactiveMapper.addMapping(mapping);
  }
}

/**
 * Remove audio mapping by ID
 */
export function removeAudioMapping(store: AudioStore, mappingId: string): void {
  const index = store.audioReactiveMappings.findIndex(m => m.id === mappingId);
  if (index >= 0) {
    store.audioReactiveMappings.splice(index, 1);
  }

  if (store.audioReactiveMapper) {
    store.audioReactiveMapper.removeMapping(mappingId);
  }
}

/**
 * Update audio mapping
 */
export function updateAudioMapping(
  store: AudioStore,
  mappingId: string,
  updates: Partial<AudioMapping>
): void {
  const mapping = store.audioReactiveMappings.find(m => m.id === mappingId);
  if (mapping) {
    Object.assign(mapping, updates);
  }

  if (store.audioReactiveMapper) {
    store.audioReactiveMapper.updateMapping(mappingId, updates);
  }
}

/**
 * Get mapped value at frame
 */
export function getMappedValueAtFrame(
  store: AudioStore,
  mappingId: string,
  frame: number
): number {
  if (!store.audioReactiveMapper) return 0;
  return store.audioReactiveMapper.getValueAtFrame(mappingId, frame);
}

/**
 * Get all mapped values at frame
 */
export function getAllMappedValuesAtFrame(
  store: AudioStore,
  frame?: number
): Map<TargetParameter, number> {
  if (!store.audioReactiveMapper) return new Map();
  return store.audioReactiveMapper.getAllValuesAtFrame(frame ?? (store.getActiveComp()?.currentFrame ?? 0));
}

/**
 * Get active mappings for a specific layer
 */
export function getActiveMappingsForLayer(
  store: AudioStore,
  layerId: string
): AudioMapping[] {
  return store.audioReactiveMappings.filter(
    m => m.enabled && (m.targetLayerId === layerId || m.targetLayerId === undefined)
  );
}

/**
 * Get audio reactive values for a specific layer at a specific frame
 */
export function getAudioReactiveValuesForLayer(
  store: AudioStore,
  layerId: string,
  frame: number
): Map<TargetParameter, number> {
  if (!store.audioReactiveMapper) return new Map();
  return store.audioReactiveMapper.getValuesForLayerAtFrame(layerId, frame);
}

/**
 * Check if current frame is a beat
 */
export function isBeatAtCurrentFrame(store: AudioStore): boolean {
  if (!store.audioAnalysis) return false;
  return isBeatAtFrame(store.audioAnalysis, store.getActiveComp()?.currentFrame ?? 0);
}

/**
 * Initialize audio reactive mapper when audio is loaded
 */
export function initializeAudioReactiveMapper(store: AudioStore): void {
  if (!store.audioAnalysis) return;

  store.audioReactiveMapper = new AudioReactiveMapper(store.audioAnalysis);

  // Add existing mappings
  for (const mapping of store.audioReactiveMappings) {
    store.audioReactiveMapper.addMapping(mapping);
  }

  // Set peak data if available
  if (store.peakData) {
    store.audioReactiveMapper.setPeakData(store.peakData);
  }
}

// ============================================================
// PATH ANIMATOR FUNCTIONS
// ============================================================

/**
 * Create path animator for a layer
 */
export function createPathAnimator(
  store: AudioStore,
  layerId: string,
  config: Partial<PathAnimatorConfig> = {}
): void {
  const animator = new AudioPathAnimator(config);
  store.pathAnimators.set(layerId, animator);
}

/**
 * Set path for an animator
 */
export function setPathAnimatorPath(
  store: AudioStore,
  layerId: string,
  pathData: string
): void {
  const animator = store.pathAnimators.get(layerId);
  if (animator) {
    animator.setPath(pathData);
  }
}

/**
 * Update path animator config
 */
export function updatePathAnimatorConfig(
  store: AudioStore,
  layerId: string,
  config: Partial<PathAnimatorConfig>
): void {
  const animator = store.pathAnimators.get(layerId);
  if (animator) {
    animator.setConfig(config);
  }
}

/**
 * Remove path animator
 */
export function removePathAnimator(store: AudioStore, layerId: string): void {
  store.pathAnimators.delete(layerId);
}

/**
 * Get path animator for layer
 */
export function getPathAnimator(
  store: AudioStore,
  layerId: string
): AudioPathAnimator | undefined {
  return store.pathAnimators.get(layerId) as AudioPathAnimator | undefined;
}

/**
 * Update all path animators for current frame
 */
export function updatePathAnimators(store: AudioStore): void {
  if (!store.audioAnalysis) return;

  const frame = store.getActiveComp()?.currentFrame ?? 0;
  const amplitude = getFeatureAtFrame(store.audioAnalysis, 'amplitude', frame);
  const isBeat = isBeatAtFrame(store.audioAnalysis, frame);

  for (const [_layerId, animator] of store.pathAnimators) {
    animator.update(amplitude, isBeat);
  }
}

/**
 * Reset all path animators
 */
export function resetPathAnimators(store: AudioStore): void {
  for (const animator of store.pathAnimators.values()) {
    animator.reset();
  }
}

// ============================================================
// LEGACY AUDIO MAPPINGS
// ============================================================

/**
 * Apply audio reactivity mapping to particle layer (legacy)
 */
export function applyAudioToParticles(
  store: AudioStore,
  layerId: string,
  mapping: AudioParticleMapping
): void {
  const existing = store.audioMappings.get(layerId) || [];
  existing.push(mapping);
  store.audioMappings.set(layerId, existing);
}

/**
 * Remove legacy audio mapping
 */
export function removeLegacyAudioMapping(
  store: AudioStore,
  layerId: string,
  index: number
): void {
  const mappings = store.audioMappings.get(layerId);
  if (mappings) {
    mappings.splice(index, 1);
    if (mappings.length === 0) {
      store.audioMappings.delete(layerId);
    }
  }
}

/**
 * Get legacy audio mappings for a layer
 */
export function getAudioMappingsForLayer(
  store: AudioStore,
  layerId: string
): AudioParticleMapping[] {
  return store.audioMappings.get(layerId) || [];
}
