/**
 * Audio Actions
 *
 * Contains audio-related actions that need access to compositorStore.
 * For pure audio state, use audioStore directly.
 *
 * This module handles:
 * - Convert audio to keyframes (needs createLayer, pushHistory)
 * - Path animators (managed on compositorStore)
 */

import {
  AudioPathAnimator,
  type PathAnimatorConfig,
  type PathAnimatorState,
} from "@/services/audioPathAnimator";
import type { AnimatableProperty, Keyframe, Layer } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useAudioStore } from "@/stores/audioStore";

// ============================================================
// STORE INTERFACE
// ============================================================

/**
 * Structural interface for AudioPathAnimator methods actually used.
 * This avoids Pinia reactive proxy issues by only declaring the methods we call,
 * not the full class implementation with private properties.
 */
export interface PathAnimatorAccess {
  setPath(pathData: string): void;
  setConfig(updates: Partial<PathAnimatorConfig>): void;
  update(audioValue: number, isBeat: boolean): PathAnimatorState;
  reset(): void;
}

/** Map of layer IDs to their PathAnimator instances (structural access) */
type PathAnimatorMap = Map<string, PathAnimatorAccess>;

/**
 * Interface for stores that can use audio-to-keyframe conversion
 */
export interface AudioKeyframeStore {
  project: { composition: { fps: number } };
  pathAnimators: PathAnimatorMap;
  createLayer(type: string, name: string): Layer;
  getActiveCompLayers(): Layer[];
  getActiveComp(): { currentFrame: number } | null;
  pushHistory(): void;
}

// ============================================================
// PATH ANIMATOR FUNCTIONS
// ============================================================

/**
 * Create path animator for a layer
 */
export function createPathAnimator(
  store: AudioKeyframeStore,
  layerId: string,
  config: Partial<PathAnimatorConfig> = {},
): void {
  const animator = new AudioPathAnimator(config);
  store.pathAnimators.set(layerId, animator);
}

/**
 * Set path for an animator
 */
export function setPathAnimatorPath(
  store: AudioKeyframeStore,
  layerId: string,
  pathData: string,
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
  store: AudioKeyframeStore,
  layerId: string,
  config: Partial<PathAnimatorConfig>,
): void {
  const animator = store.pathAnimators.get(layerId);
  if (animator) {
    animator.setConfig(config);
  }
}

/**
 * Remove path animator
 */
export function removePathAnimator(
  store: AudioKeyframeStore,
  layerId: string,
): void {
  store.pathAnimators.delete(layerId);
}

/**
 * Get path animator for layer
 */
export function getPathAnimator(
  store: AudioKeyframeStore,
  layerId: string,
): PathAnimatorAccess | undefined {
  return store.pathAnimators.get(layerId);
}

/**
 * Update all path animators for current frame
 */
export function updatePathAnimators(store: AudioKeyframeStore): void {
  const audioStore = useAudioStore();
  if (!audioStore.audioAnalysis) return;

  const frame = store.getActiveComp()?.currentFrame ?? 0;
  const amplitude = audioStore.getFeatureAtFrame("amplitude", frame);
  const isBeat = audioStore.isBeatAtFrame(frame);

  for (const [_layerId, animator] of store.pathAnimators) {
    animator.update(amplitude, isBeat);
  }
}

/**
 * Reset all path animators
 */
export function resetPathAnimators(store: AudioKeyframeStore): void {
  for (const animator of store.pathAnimators.values()) {
    animator.reset();
  }
}

// ============================================================
// CONVERT AUDIO TO KEYFRAMES
// ============================================================

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
 *
 * @param store - The compositor store
 * @param options - Optional configuration
 * @returns The created layer info with property IDs for expression linking
 */
export function convertAudioToKeyframes(
  store: AudioKeyframeStore,
  options: {
    name?: string;
    amplitudeScale?: number;
    smoothing?: number;
  } = {},
): AudioAmplitudeResult | null {
  const audioStore = useAudioStore();

  if (!audioStore.audioAnalysis || !audioStore.audioBuffer) {
    storeLogger.error("convertAudioToKeyframes: No audio loaded");
    return null;
  }

  const {
    name = "Audio Amplitude",
    amplitudeScale: rawScale = 100,
    smoothing: rawSmoothing = 0,
  } = options;

  const amplitudeScale = Number.isFinite(rawScale) ? rawScale : 100;
  const smoothing = Number.isFinite(rawSmoothing)
    ? Math.max(0, Math.min(1, rawSmoothing))
    : 0;

  store.pushHistory();

  // Create the null layer
  const layer = store.createLayer("null", name);

  const frameCount = audioStore.audioAnalysis.frameCount;
  const fps = store.project.composition.fps;

  // Extract channel data
  const channelData = extractChannelAmplitudes(
    audioStore.audioBuffer,
    frameCount,
    fps,
    smoothing,
  );

  // Create properties with keyframes
  const bothChannelsProperty = createAmplitudeProperty(
    "Both Channels",
    channelData.both,
    amplitudeScale,
  );

  const leftChannelProperty = createAmplitudeProperty(
    "Left Channel",
    channelData.left,
    amplitudeScale,
  );

  const rightChannelProperty = createAmplitudeProperty(
    "Right Channel",
    channelData.right,
    amplitudeScale,
  );

  layer.properties.push(bothChannelsProperty);
  layer.properties.push(leftChannelProperty);
  layer.properties.push(rightChannelProperty);

  storeLogger.info(
    `convertAudioToKeyframes: Created "${name}" with ${frameCount} keyframes per channel`,
  );

  return {
    layerId: layer.id,
    layerName: layer.name,
    bothChannelsPropertyId: bothChannelsProperty.id,
    leftChannelPropertyId: leftChannelProperty.id,
    rightChannelPropertyId: rightChannelProperty.id,
  };
}

/**
 * Get the Audio Amplitude layer if it exists
 */
export function getAudioAmplitudeLayer(
  store: AudioKeyframeStore,
): Layer | undefined {
  return store
    .getActiveCompLayers()
    .find((l) => l.type === "null" && l.name === "Audio Amplitude");
}

/**
 * Get amplitude value from Audio Amplitude layer at a specific frame
 */
export function getAudioAmplitudeAtFrame(
  store: AudioKeyframeStore,
  channel: "both" | "left" | "right",
  frame: number,
): number {
  const layer = getAudioAmplitudeLayer(store);
  if (!layer) return 0;

  const propertyName =
    channel === "both"
      ? "Both Channels"
      : channel === "left"
        ? "Left Channel"
        : "Right Channel";

  const property = layer.properties.find((p) => p.name === propertyName);
  if (!property || !property.animated || property.keyframes.length === 0)
    return 0;

  const keyframe = property.keyframes.find((k) => k.frame === frame);
  if (keyframe) return keyframe.value as number;

  // Interpolation fallback
  const prevKf = [...property.keyframes]
    .filter((k) => k.frame <= frame)
    .sort((a, b) => b.frame - a.frame)[0];
  const nextKf = [...property.keyframes]
    .filter((k) => k.frame > frame)
    .sort((a, b) => a.frame - b.frame)[0];

  if (!prevKf && !nextKf) return property.value as number;
  if (!prevKf) return nextKf.value as number;
  if (!nextKf) return prevKf.value as number;

  const frameDiff = nextKf.frame - prevKf.frame;
  if (frameDiff === 0) return prevKf.value as number;

  const t = (frame - prevKf.frame) / frameDiff;
  return (
    (prevKf.value as number) +
    t * ((nextKf.value as number) - (prevKf.value as number))
  );
}

// ============================================================
// CONVERT FREQUENCY BANDS TO KEYFRAMES
// ============================================================

export type FrequencyBandName =
  | "sub"
  | "bass"
  | "lowMid"
  | "mid"
  | "highMid"
  | "high";

export interface FrequencyBandResult {
  layerId: string;
  layerName: string;
  propertyIds: Record<FrequencyBandName, string>;
}

/**
 * Convert Frequency Bands to Keyframes
 */
export function convertFrequencyBandsToKeyframes(
  store: AudioKeyframeStore,
  options: {
    name?: string;
    scale?: number;
    smoothing?: number;
    bands?: FrequencyBandName[];
  } = {},
): FrequencyBandResult | null {
  const audioStore = useAudioStore();

  if (!audioStore.audioAnalysis) {
    storeLogger.error("convertFrequencyBandsToKeyframes: No audio loaded");
    return null;
  }

  const {
    name = "Audio Spectrum",
    scale = 100,
    smoothing = 0,
    bands = ["sub", "bass", "lowMid", "mid", "highMid", "high"],
  } = options;

  store.pushHistory();

  const layer = store.createLayer("null", name);
  const bandData = audioStore.audioAnalysis.frequencyBands;

  const propertyIds: Record<FrequencyBandName, string> = {
    sub: "",
    bass: "",
    lowMid: "",
    mid: "",
    highMid: "",
    high: "",
  };

  const bandNames: Record<FrequencyBandName, string> = {
    sub: "Sub (20-60 Hz)",
    bass: "Bass (60-250 Hz)",
    lowMid: "Low Mid (250-500 Hz)",
    mid: "Mid (500-2000 Hz)",
    highMid: "High Mid (2-4 kHz)",
    high: "High (4-20 kHz)",
  };

  for (const bandKey of bands) {
    const rawData = bandData[bandKey];
    if (!rawData || rawData.length === 0) continue;

    const data = smoothing > 0 ? applySmoothing(rawData, smoothing) : rawData;
    const property = createAmplitudeProperty(bandNames[bandKey], data, scale);

    layer.properties.push(property);
    propertyIds[bandKey] = property.id;
  }

  const frameCount = audioStore.audioAnalysis.frameCount;
  storeLogger.info(
    `convertFrequencyBandsToKeyframes: Created "${name}" with ${bands.length} bands, ${frameCount} keyframes each`,
  );

  return {
    layerId: layer.id,
    layerName: layer.name,
    propertyIds,
  };
}

// ============================================================
// CONVERT ALL AUDIO FEATURES TO KEYFRAMES
// ============================================================

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
  store: AudioKeyframeStore,
  options: {
    name?: string;
    scale?: number;
    smoothing?: number;
  } = {},
): AudioFeaturesResult | null {
  const audioStore = useAudioStore();

  if (!audioStore.audioAnalysis || !audioStore.audioBuffer) {
    storeLogger.error("convertAllAudioFeaturesToKeyframes: No audio loaded");
    return null;
  }

  const { name = "Audio Features", scale = 100, smoothing = 0 } = options;

  store.pushHistory();

  const layer = store.createLayer("null", name);
  const analysis = audioStore.audioAnalysis;
  const buffer = audioStore.audioBuffer;
  const frameCount = analysis.frameCount;
  const fps = store.project.composition.fps;

  // Extract channel amplitudes
  const channelData = extractChannelAmplitudes(
    buffer,
    frameCount,
    fps,
    smoothing,
  );

  const result: AudioFeaturesResult = {
    layerId: layer.id,
    layerName: layer.name,
    amplitude: { both: "", left: "", right: "" },
    bands: { sub: "", bass: "", lowMid: "", mid: "", highMid: "", high: "" },
    spectral: { centroid: "", flux: "", rolloff: "", flatness: "" },
    dynamics: { rms: "", zeroCrossing: "" },
  };

  // Amplitude section
  const bothProp = createAmplitudeProperty(
    "Amplitude - Both",
    channelData.both,
    scale,
  );
  const leftProp = createAmplitudeProperty(
    "Amplitude - Left",
    channelData.left,
    scale,
  );
  const rightProp = createAmplitudeProperty(
    "Amplitude - Right",
    channelData.right,
    scale,
  );

  layer.properties.push(bothProp, leftProp, rightProp);
  result.amplitude.both = bothProp.id;
  result.amplitude.left = leftProp.id;
  result.amplitude.right = rightProp.id;

  // Frequency bands section
  const bandNames: Record<FrequencyBandName, string> = {
    sub: "Band - Sub (20-60 Hz)",
    bass: "Band - Bass (60-250 Hz)",
    lowMid: "Band - Low Mid (250-500 Hz)",
    mid: "Band - Mid (500-2000 Hz)",
    highMid: "Band - High Mid (2-4 kHz)",
    high: "Band - High (4-20 kHz)",
  };

  const allBands: FrequencyBandName[] = [
    "sub",
    "bass",
    "lowMid",
    "mid",
    "highMid",
    "high",
  ];

  for (const bandKey of allBands) {
    const rawData = analysis.frequencyBands[bandKey];
    if (!rawData || rawData.length === 0) continue;

    const data = smoothing > 0 ? applySmoothing(rawData, smoothing) : rawData;
    const prop = createAmplitudeProperty(bandNames[bandKey], data, scale);
    layer.properties.push(prop);
    result.bands[bandKey] = prop.id;
  }

  // Spectral features section
  if (analysis.spectralCentroid?.length > 0) {
    const normalizedCentroid = analysis.spectralCentroid.map((v) =>
      Math.min(1, v / 10000),
    );
    const centroidProp = createAmplitudeProperty(
      "Spectral - Centroid",
      smoothing > 0
        ? applySmoothing(normalizedCentroid, smoothing)
        : normalizedCentroid,
      scale,
    );
    layer.properties.push(centroidProp);
    result.spectral.centroid = centroidProp.id;
  }

  if (analysis.spectralFlux?.length > 0) {
    const fluxProp = createAmplitudeProperty(
      "Spectral - Flux",
      smoothing > 0
        ? applySmoothing(analysis.spectralFlux, smoothing)
        : analysis.spectralFlux,
      scale,
    );
    layer.properties.push(fluxProp);
    result.spectral.flux = fluxProp.id;
  }

  if (analysis.spectralRolloff?.length > 0) {
    const normalizedRolloff = analysis.spectralRolloff.map((v) =>
      Math.min(1, v / 10000),
    );
    const rolloffProp = createAmplitudeProperty(
      "Spectral - Rolloff",
      smoothing > 0
        ? applySmoothing(normalizedRolloff, smoothing)
        : normalizedRolloff,
      scale,
    );
    layer.properties.push(rolloffProp);
    result.spectral.rolloff = rolloffProp.id;
  }

  if (analysis.spectralFlatness?.length > 0) {
    const flatnessProp = createAmplitudeProperty(
      "Spectral - Flatness",
      smoothing > 0
        ? applySmoothing(analysis.spectralFlatness, smoothing)
        : analysis.spectralFlatness,
      scale,
    );
    layer.properties.push(flatnessProp);
    result.spectral.flatness = flatnessProp.id;
  }

  // Dynamics section
  if (analysis.rmsEnergy?.length > 0) {
    const rmsProp = createAmplitudeProperty(
      "Dynamics - RMS Energy",
      smoothing > 0
        ? applySmoothing(analysis.rmsEnergy, smoothing)
        : analysis.rmsEnergy,
      scale,
    );
    layer.properties.push(rmsProp);
    result.dynamics.rms = rmsProp.id;
  }

  if (analysis.zeroCrossingRate?.length > 0) {
    const zcrProp = createAmplitudeProperty(
      "Dynamics - Zero Crossing Rate",
      smoothing > 0
        ? applySmoothing(analysis.zeroCrossingRate, smoothing)
        : analysis.zeroCrossingRate,
      scale,
    );
    layer.properties.push(zcrProp);
    result.dynamics.zeroCrossing = zcrProp.id;
  }

  storeLogger.info(
    `convertAllAudioFeaturesToKeyframes: Created "${name}" with ${layer.properties.length} properties`,
  );

  return result;
}

/**
 * Get frequency band value from Audio Spectrum layer at a specific frame
 */
export function getFrequencyBandAtFrame(
  store: AudioKeyframeStore,
  band: FrequencyBandName,
  frame: number,
): number {
  const layer = store
    .getActiveCompLayers()
    .find(
      (l) =>
        l.type === "null" &&
        (l.name === "Audio Spectrum" || l.name === "Audio Features"),
    );
  if (!layer) return 0;

  const bandLabels: Record<FrequencyBandName, string[]> = {
    sub: ["Sub", "20-60"],
    bass: ["Bass", "60-250"],
    lowMid: ["Low Mid", "250-500"],
    mid: ["Mid (500", "500-2000"],
    highMid: ["High Mid", "2-4 kHz", "2000-4000"],
    high: ["High (4", "4-20 kHz", "4000-20000"],
  };

  const property = layer.properties.find((p) =>
    bandLabels[band].some((label) => p.name.includes(label)),
  );

  if (!property || !property.animated || property.keyframes.length === 0)
    return 0;

  const keyframe = property.keyframes.find((k) => k.frame === frame);
  if (keyframe) return keyframe.value as number;

  return property.value as number;
}

// ============================================================
// HELPER FUNCTIONS
// ============================================================

/**
 * Extract amplitude data from audio buffer for each channel
 */
function extractChannelAmplitudes(
  buffer: AudioBuffer,
  frameCount: number,
  fps: number,
  smoothing: number,
): { both: number[]; left: number[]; right: number[] } {
  if (!Number.isFinite(fps) || fps <= 0) {
    fps = 30;
  }

  if (!Number.isFinite(frameCount) || frameCount <= 0) {
    return { both: [], left: [], right: [] };
  }

  const sampleRate = buffer.sampleRate;
  const samplesPerFrame = Math.floor(sampleRate / fps);
  const numChannels = buffer.numberOfChannels;

  const leftData = buffer.getChannelData(0);
  const rightData = numChannels > 1 ? buffer.getChannelData(1) : leftData;

  const leftAmplitudes: number[] = [];
  const rightAmplitudes: number[] = [];
  const bothAmplitudes: number[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const startSample = frame * samplesPerFrame;
    const endSample = Math.min(startSample + samplesPerFrame, leftData.length);

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

    leftAmplitudes.push(Math.min(1, leftRms * 2));
    rightAmplitudes.push(Math.min(1, rightRms * 2));
    bothAmplitudes.push(Math.min(1, bothRms * 2));
  }

  if (smoothing > 0) {
    return {
      left: applySmoothing(leftAmplitudes, smoothing),
      right: applySmoothing(rightAmplitudes, smoothing),
      both: applySmoothing(bothAmplitudes, smoothing),
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
  scale: number,
): AnimatableProperty<number> {
  const id = `prop_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
  const safeScale = Number.isFinite(scale) ? scale : 100;

  const keyframes: Keyframe<number>[] = amplitudes.map((amp, frame) => ({
    id: `kf_${id}_${frame}`,
    frame,
    value: Number.isFinite(amp) ? amp * safeScale : 0,
    interpolation: "linear" as const,
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: "smooth" as const,
  }));

  return {
    id,
    name,
    type: "number" as const,
    value: 0,
    animated: true,
    keyframes,
  };
}
