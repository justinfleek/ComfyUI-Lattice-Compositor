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

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AudioReactiveMapperType = AudioReactiveMapper | any;

/**
 * Safely get a frame number, defaulting to 0 for NaN/undefined/null
 */
function safeFrame(frame: number | undefined | null, fallback = 0): number {
  return Number.isFinite(frame) ? frame! : fallback;
}

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
  // Using union with any to avoid Pinia proxy type incompatibilities
  audioReactiveMapper: AudioReactiveMapperType | null;
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  pathAnimators: Map<string, AudioPathAnimator | any>;
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
 * Clear loaded audio and release resources
 */
export function clearAudio(store: AudioStore): void {
  cancelAudioLoad(store);
  store.audioFile = null;
  store.audioBuffer = null;
  store.audioAnalysis = null;
  store.audioMappings.clear();

  // Dispose audio reactive mapper if it has a dispose method
  if (store.audioReactiveMapper?.dispose) {
    store.audioReactiveMapper.dispose();
  }
  store.audioReactiveMapper = null;

  // Dispose all path animators
  for (const animator of store.pathAnimators.values()) {
    if (animator?.dispose) {
      animator.dispose();
    }
  }
  store.pathAnimators.clear();
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
  const targetFrame = safeFrame(frame ?? store.getActiveComp()?.currentFrame);
  return getFeatureAtFrame(store.audioAnalysis, feature, targetFrame);
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
  const targetFrame = safeFrame(frame ?? store.getActiveComp()?.currentFrame);
  return store.audioReactiveMapper.getAllValuesAtFrame(targetFrame);
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
  return isBeatAtFrame(store.audioAnalysis, safeFrame(store.getActiveComp()?.currentFrame));
}

/**
 * Initialize audio reactive mapper when audio is loaded
 */
export function initializeAudioReactiveMapper(store: AudioStore): void {
  if (!store.audioAnalysis) return;

  // Dispose existing mapper before creating new one
  if (store.audioReactiveMapper?.dispose) {
    store.audioReactiveMapper.dispose();
  }

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
  // Dispose existing animator before creating new one
  const existing = store.pathAnimators.get(layerId);
  if (existing?.dispose) {
    existing.dispose();
  }

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
 * Remove path animator and release its resources
 */
export function removePathAnimator(store: AudioStore, layerId: string): void {
  const animator = store.pathAnimators.get(layerId);
  if (animator?.dispose) {
    animator.dispose();
  }
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

  const frame = safeFrame(store.getActiveComp()?.currentFrame);
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
  if (!mappings) return;

  // Validate index is a valid integer within bounds
  if (!Number.isInteger(index) || index < 0 || index >= mappings.length) {
    storeLogger.warn('[Audio] Invalid mapping index:', index);
    return;
  }

  mappings.splice(index, 1);
  if (mappings.length === 0) {
    store.audioMappings.delete(layerId);
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

// ============================================================
// CONVERT AUDIO TO KEYFRAMES
// ============================================================

import type { Layer, AnimatableProperty, Keyframe } from '@/types/project';
import { createAnimatableProperty } from '@/types/project';

export interface ConvertAudioToKeyframesStore extends AudioStore {
  createLayer(type: string, name: string): Layer;
  getActiveCompLayers(): Layer[];
  pushHistory(): void;
}

export interface AudioAmplitudeResult {
  layerId: string;
  layerName: string;
  bothChannelsPropertyId: string;
  leftChannelPropertyId: string;
  rightChannelPropertyId: string;
}

/**
 * Convert Audio to Keyframes
 *
 * Creates an "Audio Amplitude" control layer with slider properties
 * that have keyframes at every frame representing audio amplitude.
 * This converts audio waveform data into animatable keyframe data.
 *
 * The created layer has three properties:
 * - Both Channels: Combined stereo amplitude (0-100)
 * - Left Channel: Left channel amplitude (0-100)
 * - Right Channel: Right channel amplitude (0-100)
 *
 * @param store - The compositor store
 * @param options - Optional configuration
 * @returns The created layer info with property IDs for expression linking
 */
export function convertAudioToKeyframes(
  store: ConvertAudioToKeyframesStore,
  options: {
    name?: string;
    amplitudeScale?: number;  // Multiplier for amplitude values (default: 100)
    smoothing?: number;       // Smoothing factor 0-1 (default: 0)
  } = {}
): AudioAmplitudeResult | null {
  if (!store.audioAnalysis || !store.audioBuffer) {
    storeLogger.error('convertAudioToKeyframes: No audio loaded');
    return null;
  }

  const {
    name = 'Audio Amplitude',
    amplitudeScale: rawScale = 100,
    smoothing: rawSmoothing = 0
  } = options;

  // Validate numeric options (destructuring defaults don't catch NaN)
  const amplitudeScale = Number.isFinite(rawScale) ? rawScale : 100;
  const smoothing = Number.isFinite(rawSmoothing) ? Math.max(0, Math.min(1, rawSmoothing)) : 0;

  store.pushHistory();

  // Create the null layer
  const layer = store.createLayer('null', name);

  // Get audio data
  const analysis = store.audioAnalysis;
  const buffer = store.audioBuffer;
  const frameCount = analysis.frameCount;
  const fps = store.project.composition.fps;

  // Extract channel data
  const channelData = extractChannelAmplitudes(buffer, frameCount, fps, smoothing);

  // Create properties with keyframes
  const bothChannelsProperty = createAmplitudeProperty(
    'Both Channels',
    channelData.both,
    amplitudeScale
  );

  const leftChannelProperty = createAmplitudeProperty(
    'Left Channel',
    channelData.left,
    amplitudeScale
  );

  const rightChannelProperty = createAmplitudeProperty(
    'Right Channel',
    channelData.right,
    amplitudeScale
  );

  // Add properties to layer
  layer.properties.push(bothChannelsProperty);
  layer.properties.push(leftChannelProperty);
  layer.properties.push(rightChannelProperty);

  storeLogger.info(`convertAudioToKeyframes: Created "${name}" with ${frameCount} keyframes per channel`);

  return {
    layerId: layer.id,
    layerName: layer.name,
    bothChannelsPropertyId: bothChannelsProperty.id,
    leftChannelPropertyId: leftChannelProperty.id,
    rightChannelPropertyId: rightChannelProperty.id
  };
}

/**
 * Extract amplitude data from audio buffer for each channel
 */
function extractChannelAmplitudes(
  buffer: AudioBuffer,
  frameCount: number,
  fps: number,
  smoothing: number
): { both: number[]; left: number[]; right: number[] } {
  // Validate numeric parameters
  if (!Number.isFinite(fps) || fps <= 0) {
    storeLogger.warn('[Audio] Invalid fps:', fps, '- using default 30');
    fps = 30;
  }

  if (!Number.isFinite(frameCount) || frameCount <= 0) {
    return { both: [], left: [], right: [] };
  }

  const sampleRate = buffer.sampleRate;
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const numChannels = buffer.numberOfChannels;

  // Get raw channel data
  const leftData = buffer.getChannelData(0);
  const rightData = numChannels > 1 ? buffer.getChannelData(1) : leftData;

  const leftAmplitudes: number[] = [];
  const rightAmplitudes: number[] = [];
  const bothAmplitudes: number[] = [];

  // Calculate amplitude for each frame
  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(startSample + samplesPerFrame, leftData.length);

    // Calculate RMS amplitude for each channel
    let leftSum = 0;
    let rightSum = 0;
    let count = 0;

    for (let i = startSample; i < endSample; i++) {
      leftSum += leftData[i] * leftData[i];
      rightSum += rightData[i] * rightData[i];
      count++;
    }

    const leftRms = count > 0 ? Math.sqrt(leftSum / count) : 0;
    const rightRms = count > 0 ? Math.sqrt(rightSum / count) : 0;
    const bothRms = (leftRms + rightRms) / 2;

    // Normalize to 0-1 range (typical RMS values are 0-0.5)
    leftAmplitudes.push(Math.min(1, leftRms * 2));
    rightAmplitudes.push(Math.min(1, rightRms * 2));
    bothAmplitudes.push(Math.min(1, bothRms * 2));
  }

  // Apply smoothing if requested
  if (smoothing > 0) {
    return {
      left: applySmoothing(leftAmplitudes, smoothing),
      right: applySmoothing(rightAmplitudes, smoothing),
      both: applySmoothing(bothAmplitudes, smoothing)
    };
  }

  return { left: leftAmplitudes, right: rightAmplitudes, both: bothAmplitudes };
}

/**
 * Apply exponential smoothing to amplitude values
 */
function applySmoothing(values: number[], factor: number): number[] {
  if (values.length === 0) return values;

  const smoothed: number[] = [values[0]];
  for (let i = 1; i < values.length; i++) {
    smoothed[i] = factor * smoothed[i - 1] + (1 - factor) * values[i];
  }
  return smoothed;
}

/**
 * Create an animatable property with keyframes at every frame
 */
function createAmplitudeProperty(
  name: string,
  amplitudes: number[],
  scale: number
): AnimatableProperty<number> {
  const id = `prop_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

  // Ensure scale is valid
  const safeScale = Number.isFinite(scale) ? scale : 100;

  const keyframes: Keyframe<number>[] = amplitudes.map((amp, frame) => ({
    id: `kf_${id}_${frame}`,
    frame,
    value: Number.isFinite(amp) ? amp * safeScale : 0,
    interpolation: 'linear' as const,
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: 'smooth' as const
  }));

  return {
    id,
    name,
    type: 'number' as const,
    value: 0,
    animated: true,
    keyframes
  };
}

/**
 * Get the Audio Amplitude layer if it exists
 */
export function getAudioAmplitudeLayer(
  store: ConvertAudioToKeyframesStore
): Layer | undefined {
  return store.getActiveCompLayers().find(l =>
    l.type === 'null' && l.name === 'Audio Amplitude'
  );
}

/**
 * Get amplitude value from Audio Amplitude layer at a specific frame
 * This is used by expressions to reference audio data
 *
 * @param store - The compositor store
 * @param channel - 'both' | 'left' | 'right'
 * @param frame - The frame number
 * @returns The amplitude value (0-100) or 0 if not found
 */
export function getAudioAmplitudeAtFrame(
  store: ConvertAudioToKeyframesStore,
  channel: 'both' | 'left' | 'right',
  frame: number
): number {
  const layer = getAudioAmplitudeLayer(store);
  if (!layer) return 0;

  const propertyName = channel === 'both' ? 'Both Channels' :
                       channel === 'left' ? 'Left Channel' : 'Right Channel';

  const property = layer.properties.find(p => p.name === propertyName);
  if (!property || !property.animated || property.keyframes.length === 0) return 0;

  // Find the keyframe at this frame
  const keyframe = property.keyframes.find(k => k.frame === frame);
  if (keyframe) return keyframe.value as number;

  // If no exact keyframe, interpolate (though we have keyframes at every frame)
  // Find surrounding keyframes
  const prevKf = [...property.keyframes]
    .filter(k => k.frame <= frame)
    .sort((a, b) => b.frame - a.frame)[0];
  const nextKf = [...property.keyframes]
    .filter(k => k.frame > frame)
    .sort((a, b) => a.frame - b.frame)[0];

  if (!prevKf && !nextKf) return property.value as number;
  if (!prevKf) return nextKf.value as number;
  if (!nextKf) return prevKf.value as number;

  // Guard against division by zero (duplicate keyframes)
  const frameDiff = nextKf.frame - prevKf.frame;
  if (frameDiff === 0) {
    return prevKf.value as number;
  }

  // Linear interpolation
  const t = (frame - prevKf.frame) / frameDiff;
  return (prevKf.value as number) + t * ((nextKf.value as number) - (prevKf.value as number));
}

// ============================================================
// CONVERT FREQUENCY BANDS TO KEYFRAMES
// ============================================================

/**
 * Frequency band names for keyframe conversion
 */
export type FrequencyBandName = 'sub' | 'bass' | 'lowMid' | 'mid' | 'highMid' | 'high';

export interface FrequencyBandResult {
  layerId: string;
  layerName: string;
  propertyIds: Record<FrequencyBandName, string>;
}

/**
 * Convert Frequency Bands to Keyframes
 *
 * Creates an "Audio Spectrum" control layer with slider properties
 * for each frequency band (sub, bass, lowMid, mid, highMid, high).
 * Each property has keyframes at every frame representing the energy
 * in that frequency band.
 *
 * Frequency Ranges:
 * - Sub: 20-60 Hz (sub-bass rumble)
 * - Bass: 60-250 Hz (kick, bass)
 * - Low Mid: 250-500 Hz (warmth)
 * - Mid: 500-2000 Hz (presence, vocals)
 * - High Mid: 2000-4000 Hz (clarity, brightness)
 * - High: 4000-20000 Hz (air, cymbals)
 *
 * @param store - The compositor store
 * @param options - Optional configuration
 * @returns The created layer info with property IDs for expression linking
 */
export function convertFrequencyBandsToKeyframes(
  store: ConvertAudioToKeyframesStore,
  options: {
    name?: string;
    scale?: number;       // Multiplier for values (default: 100)
    smoothing?: number;   // Smoothing factor 0-1 (default: 0)
    bands?: FrequencyBandName[];  // Which bands to include (default: all)
  } = {}
): FrequencyBandResult | null {
  if (!store.audioAnalysis) {
    storeLogger.error('convertFrequencyBandsToKeyframes: No audio loaded');
    return null;
  }

  const {
    name = 'Audio Spectrum',
    scale = 100,
    smoothing = 0,
    bands = ['sub', 'bass', 'lowMid', 'mid', 'highMid', 'high']
  } = options;

  store.pushHistory();

  // Create the null layer
  const layer = store.createLayer('null', name);

  // Get frequency band data from analysis
  const analysis = store.audioAnalysis;
  const bandData = analysis.frequencyBands;

  const propertyIds: Record<FrequencyBandName, string> = {
    sub: '',
    bass: '',
    lowMid: '',
    mid: '',
    highMid: '',
    high: ''
  };

  // Band display names
  const bandNames: Record<FrequencyBandName, string> = {
    sub: 'Sub (20-60 Hz)',
    bass: 'Bass (60-250 Hz)',
    lowMid: 'Low Mid (250-500 Hz)',
    mid: 'Mid (500-2000 Hz)',
    highMid: 'High Mid (2-4 kHz)',
    high: 'High (4-20 kHz)'
  };

  // Create property for each requested band
  for (const bandKey of bands) {
    const rawData = bandData[bandKey];
    if (!rawData || rawData.length === 0) continue;

    // Apply smoothing if requested
    const data = smoothing > 0 ? applySmoothing(rawData, smoothing) : rawData;

    // Create property with keyframes
    const property = createAmplitudeProperty(
      bandNames[bandKey],
      data,
      scale
    );

    layer.properties.push(property);
    propertyIds[bandKey] = property.id;
  }

  const frameCount = analysis.frameCount;
  storeLogger.info(`convertFrequencyBandsToKeyframes: Created "${name}" with ${bands.length} bands, ${frameCount} keyframes each`);

  return {
    layerId: layer.id,
    layerName: layer.name,
    propertyIds
  };
}

/**
 * Convert All Audio Features to Keyframes
 *
 * Creates a comprehensive "Audio Features" control layer with:
 * - Amplitude (both/left/right channels)
 * - All frequency bands
 * - Spectral features (centroid, flux, rolloff, flatness)
 * - Beat/onset markers
 *
 * @param store - The compositor store
 * @param options - Optional configuration
 * @returns Object containing all created property IDs
 */
export interface AudioFeaturesResult {
  layerId: string;
  layerName: string;
  amplitude: {
    both: string;
    left: string;
    right: string;
  };
  bands: Record<FrequencyBandName, string>;
  spectral: {
    centroid: string;
    flux: string;
    rolloff: string;
    flatness: string;
  };
  dynamics: {
    rms: string;
    zeroCrossing: string;
  };
}

export function convertAllAudioFeaturesToKeyframes(
  store: ConvertAudioToKeyframesStore,
  options: {
    name?: string;
    scale?: number;
    smoothing?: number;
  } = {}
): AudioFeaturesResult | null {
  if (!store.audioAnalysis || !store.audioBuffer) {
    storeLogger.error('convertAllAudioFeaturesToKeyframes: No audio loaded');
    return null;
  }

  const {
    name = 'Audio Features',
    scale = 100,
    smoothing = 0
  } = options;

  store.pushHistory();

  // Create the null layer
  const layer = store.createLayer('null', name);

  const analysis = store.audioAnalysis;
  const buffer = store.audioBuffer;
  const frameCount = analysis.frameCount;
  const fps = store.project.composition.fps;

  // Extract channel amplitudes
  const channelData = extractChannelAmplitudes(buffer, frameCount, fps, smoothing);

  // Initialize result
  const result: AudioFeaturesResult = {
    layerId: layer.id,
    layerName: layer.name,
    amplitude: { both: '', left: '', right: '' },
    bands: { sub: '', bass: '', lowMid: '', mid: '', highMid: '', high: '' },
    spectral: { centroid: '', flux: '', rolloff: '', flatness: '' },
    dynamics: { rms: '', zeroCrossing: '' }
  };

  // ----- AMPLITUDE SECTION -----
  const bothProp = createAmplitudeProperty('Amplitude - Both', channelData.both, scale);
  const leftProp = createAmplitudeProperty('Amplitude - Left', channelData.left, scale);
  const rightProp = createAmplitudeProperty('Amplitude - Right', channelData.right, scale);

  layer.properties.push(bothProp);
  layer.properties.push(leftProp);
  layer.properties.push(rightProp);

  result.amplitude.both = bothProp.id;
  result.amplitude.left = leftProp.id;
  result.amplitude.right = rightProp.id;

  // ----- FREQUENCY BANDS SECTION -----
  const bandNames: Record<FrequencyBandName, string> = {
    sub: 'Band - Sub (20-60 Hz)',
    bass: 'Band - Bass (60-250 Hz)',
    lowMid: 'Band - Low Mid (250-500 Hz)',
    mid: 'Band - Mid (500-2000 Hz)',
    highMid: 'Band - High Mid (2-4 kHz)',
    high: 'Band - High (4-20 kHz)'
  };

  const allBands: FrequencyBandName[] = ['sub', 'bass', 'lowMid', 'mid', 'highMid', 'high'];
  for (const bandKey of allBands) {
    const rawData = analysis.frequencyBands[bandKey];
    if (!rawData || rawData.length === 0) continue;

    const data = smoothing > 0 ? applySmoothing(rawData, smoothing) : rawData;
    const prop = createAmplitudeProperty(bandNames[bandKey], data, scale);
    layer.properties.push(prop);
    result.bands[bandKey] = prop.id;
  }

  // ----- SPECTRAL FEATURES SECTION -----
  if (analysis.spectralCentroid && analysis.spectralCentroid.length > 0) {
    // Normalize spectral centroid to 0-1 range (typical values 0-10000 Hz)
    const normalizedCentroid = analysis.spectralCentroid.map(v => Math.min(1, v / 10000));
    const centroidProp = createAmplitudeProperty(
      'Spectral - Centroid',
      smoothing > 0 ? applySmoothing(normalizedCentroid, smoothing) : normalizedCentroid,
      scale
    );
    layer.properties.push(centroidProp);
    result.spectral.centroid = centroidProp.id;
  }

  if (analysis.spectralFlux && analysis.spectralFlux.length > 0) {
    const fluxProp = createAmplitudeProperty(
      'Spectral - Flux',
      smoothing > 0 ? applySmoothing(analysis.spectralFlux, smoothing) : analysis.spectralFlux,
      scale
    );
    layer.properties.push(fluxProp);
    result.spectral.flux = fluxProp.id;
  }

  if (analysis.spectralRolloff && analysis.spectralRolloff.length > 0) {
    // Normalize rolloff to 0-1 range
    const normalizedRolloff = analysis.spectralRolloff.map(v => Math.min(1, v / 10000));
    const rolloffProp = createAmplitudeProperty(
      'Spectral - Rolloff',
      smoothing > 0 ? applySmoothing(normalizedRolloff, smoothing) : normalizedRolloff,
      scale
    );
    layer.properties.push(rolloffProp);
    result.spectral.rolloff = rolloffProp.id;
  }

  if (analysis.spectralFlatness && analysis.spectralFlatness.length > 0) {
    const flatnessProp = createAmplitudeProperty(
      'Spectral - Flatness',
      smoothing > 0 ? applySmoothing(analysis.spectralFlatness, smoothing) : analysis.spectralFlatness,
      scale
    );
    layer.properties.push(flatnessProp);
    result.spectral.flatness = flatnessProp.id;
  }

  // ----- DYNAMICS SECTION -----
  if (analysis.rmsEnergy && analysis.rmsEnergy.length > 0) {
    const rmsProp = createAmplitudeProperty(
      'Dynamics - RMS Energy',
      smoothing > 0 ? applySmoothing(analysis.rmsEnergy, smoothing) : analysis.rmsEnergy,
      scale
    );
    layer.properties.push(rmsProp);
    result.dynamics.rms = rmsProp.id;
  }

  if (analysis.zeroCrossingRate && analysis.zeroCrossingRate.length > 0) {
    const zcrProp = createAmplitudeProperty(
      'Dynamics - Zero Crossing Rate',
      smoothing > 0 ? applySmoothing(analysis.zeroCrossingRate, smoothing) : analysis.zeroCrossingRate,
      scale
    );
    layer.properties.push(zcrProp);
    result.dynamics.zeroCrossing = zcrProp.id;
  }

  const propCount = layer.properties.length;
  storeLogger.info(`convertAllAudioFeaturesToKeyframes: Created "${name}" with ${propCount} properties, ${frameCount} keyframes each`);

  return result;
}

/**
 * Get frequency band value from Audio Spectrum layer at a specific frame
 *
 * @param store - The compositor store
 * @param band - The frequency band name
 * @param frame - The frame number
 * @returns The band value (0-100) or 0 if not found
 */
export function getFrequencyBandAtFrame(
  store: ConvertAudioToKeyframesStore,
  band: FrequencyBandName,
  frame: number
): number {
  const layer = store.getActiveCompLayers().find(l =>
    l.type === 'null' && (l.name === 'Audio Spectrum' || l.name === 'Audio Features')
  );
  if (!layer) return 0;

  // Find property containing the band name
  const bandLabels: Record<FrequencyBandName, string[]> = {
    sub: ['Sub', '20-60'],
    bass: ['Bass', '60-250'],
    lowMid: ['Low Mid', '250-500'],
    mid: ['Mid (500', '500-2000'],
    highMid: ['High Mid', '2-4 kHz', '2000-4000'],
    high: ['High (4', '4-20 kHz', '4000-20000']
  };

  const property = layer.properties.find(p =>
    bandLabels[band].some(label => p.name.includes(label))
  );

  if (!property || !property.animated || property.keyframes.length === 0) return 0;

  // Find the keyframe at this frame
  const keyframe = property.keyframes.find(k => k.frame === frame);
  if (keyframe) return keyframe.value as number;

  return property.value as number;
}
