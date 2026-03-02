/**
 * Timeline Snap Service
 *
 * Provides snapping functionality for the timeline, including:
 * - Grid snapping (frame intervals)
 * - Keyframe snapping
 * - Audio beat/onset snapping
 * - Audio peak snapping
 * - Layer boundary snapping (in/out points)
 */

import type { AnimatableProperty, Layer } from "@/types/project";
import type { AudioAnalysis, PeakData } from "./audioFeatures";
import { isFiniteNumber } from "@/utils/typeGuards";

/** Snap target types */
export type SnapType =
  | "frame"
  | "keyframe"
  | "beat"
  | "peak"
  | "layer-in"
  | "layer-out"
  | "playhead";

/** Snap result */
export interface SnapResult {
  frame: number;
  type: SnapType;
  distance: number; // Distance from original frame in pixels
}

/** Snap configuration */
export interface SnapConfig {
  enabled: boolean;
  snapToGrid: boolean;
  snapToKeyframes: boolean;
  snapToBeats: boolean;
  snapToPeaks: boolean;
  snapToLayerBounds: boolean;
  snapToPlayhead: boolean;
  threshold: number; // Snap threshold in pixels
  gridInterval: number; // Grid interval in frames
}

/** Default snap configuration */
export const DEFAULT_SNAP_CONFIG: SnapConfig = {
  enabled: true,
  snapToGrid: true,
  snapToKeyframes: true,
  snapToBeats: true,
  snapToPeaks: true,
  snapToLayerBounds: true,
  snapToPlayhead: true,
  threshold: 8, // 8 pixels snap threshold
  gridInterval: 5, // Snap to every 5 frames by default
};

/**
 * Find the nearest snap point to a given frame
 */
export function findNearestSnap(
  frame: number,
  config: SnapConfig,
  pixelsPerFrame: number,
  context: {
    layers?: Layer[];
    selectedLayerId?: string | null;
    currentFrame?: number;
    audioAnalysis?: AudioAnalysis | null;
    peakData?: PeakData | null;
  },
): SnapResult {
  // System F/Omega proof: Explicit validation of snap configuration
  // Type proof: config.enabled ∈ boolean
  // Mathematical proof: Snap must be enabled to find targets
  if (!config.enabled) {
    throw new Error(
      `[TimelineSnap] Cannot find snap target: Snap is disabled in configuration. ` +
      `Frame: ${frame}, pixelsPerFrame: ${pixelsPerFrame}. ` +
      `Enable snap in timeline configuration to use snap functionality.`
    );
  }

  const snapTargets: SnapResult[] = [];
  const thresholdFrames = config.threshold / pixelsPerFrame;

  // Grid snapping
  if (config.snapToGrid) {
    const nearestGridFrame =
      Math.round(frame / config.gridInterval) * config.gridInterval;
    const gridDistance = Math.abs(frame - nearestGridFrame);
    if (gridDistance <= thresholdFrames) {
      snapTargets.push({
        frame: nearestGridFrame,
        type: "frame",
        distance: gridDistance * pixelsPerFrame,
      });
    }
  }

  // Keyframe snapping
  if (config.snapToKeyframes && context.layers) {
    for (const layer of context.layers) {
      // Don't snap to selected layer's own keyframes when dragging
      if (layer.id === context.selectedLayerId) continue;

      collectKeyframeSnapTargets(
        layer,
        frame,
        thresholdFrames,
        pixelsPerFrame,
        snapTargets,
      );
    }
  }

  // Audio beat snapping
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const audioAnalysis = (context != null && typeof context === "object" && "audioAnalysis" in context && context.audioAnalysis != null && typeof context.audioAnalysis === "object") ? context.audioAnalysis : undefined;
  const audioAnalysisOnsets = (audioAnalysis != null && typeof audioAnalysis === "object" && "onsets" in audioAnalysis && audioAnalysis.onsets != null && Array.isArray(audioAnalysis.onsets)) ? audioAnalysis.onsets : undefined;
  if (config.snapToBeats && audioAnalysisOnsets != null) {
    for (const onset of audioAnalysisOnsets) {
      const distance = Math.abs(frame - onset);
      if (distance <= thresholdFrames) {
        snapTargets.push({
          frame: onset,
          type: "beat",
          distance: distance * pixelsPerFrame,
        });
      }
    }
  }

  // Audio peak snapping
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const peakData = (context != null && typeof context === "object" && "peakData" in context && context.peakData != null && typeof context.peakData === "object") ? context.peakData : undefined;
  const peakDataIndices = (peakData != null && typeof peakData === "object" && "indices" in peakData && peakData.indices != null && Array.isArray(peakData.indices)) ? peakData.indices : undefined;
  if (config.snapToPeaks && peakDataIndices != null) {
    for (const peakFrame of peakDataIndices) {
      const distance = Math.abs(frame - peakFrame);
      if (distance <= thresholdFrames) {
        snapTargets.push({
          frame: peakFrame,
          type: "peak",
          distance: distance * pixelsPerFrame,
        });
      }
    }
  }

  // Layer bounds snapping
  if (config.snapToLayerBounds && context.layers) {
    for (const layer of context.layers) {
      if (layer.id === context.selectedLayerId) continue;

      // Type proof: layerStart ∈ number | undefined → number
      const layerStart = isFiniteNumber(layer.startFrame)
        ? layer.startFrame
        : isFiniteNumber(layer.inPoint)
          ? layer.inPoint
          : 0;
      // Type proof: layerEnd ∈ number | undefined → number
      const layerEnd = isFiniteNumber(layer.endFrame)
        ? layer.endFrame
        : isFiniteNumber(layer.outPoint)
          ? layer.outPoint
          : 80;
      const inDistance = Math.abs(frame - layerStart);
      const outDistance = Math.abs(frame - layerEnd);

      if (inDistance <= thresholdFrames) {
        snapTargets.push({
          frame: layerStart,
          type: "layer-in",
          distance: inDistance * pixelsPerFrame,
        });
      }

      if (outDistance <= thresholdFrames) {
        snapTargets.push({
          frame: layerEnd,
          type: "layer-out",
          distance: outDistance * pixelsPerFrame,
        });
      }
    }
  }

  // Playhead snapping
  if (config.snapToPlayhead && context.currentFrame !== undefined) {
    const distance = Math.abs(frame - context.currentFrame);
    if (distance <= thresholdFrames && distance > 0) {
      snapTargets.push({
        frame: context.currentFrame,
        type: "playhead",
        distance: distance * pixelsPerFrame,
      });
    }
  }

  // System F/Omega proof: Explicit validation of snap target existence
  // Type proof: snapTargets ∈ Array<SnapResult> → SnapResult (non-nullable)
  // Mathematical proof: Snap targets must exist to return result
  // Pattern proof: No snap targets is an explicit failure condition, not a lazy null return
  if (snapTargets.length === 0) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
    const layersLength = (context.layers !== null && context.layers !== undefined && Array.isArray(context.layers)) ? context.layers.length : 0;
    throw new Error(
      `[TimelineSnap] Cannot find snap target: No snap targets found within threshold. ` +
      `Frame: ${frame}, threshold: ${config.threshold}px (${thresholdFrames.toFixed(2)} frames), pixelsPerFrame: ${pixelsPerFrame}. ` +
      `Snap configuration: grid=${config.snapToGrid}, keyframes=${config.snapToKeyframes}, beats=${config.snapToBeats}, ` +
      `peaks=${config.snapToPeaks}, layerBounds=${config.snapToLayerBounds}, playhead=${config.snapToPlayhead}. ` +
      `Context: layers=${layersLength}, audioAnalysis=${context.audioAnalysis ? "present" : "null"}, ` +
      `peakData=${context.peakData ? "present" : "null"}. ` +
      `No snap targets match the current frame within the configured threshold. Wrap in try/catch if "no snap" is an expected state.`
    );
  }

  // Prioritize by type: playhead > beat/peak > keyframe > layer > grid
  const priority: Record<SnapType, number> = {
    playhead: 5,
    beat: 4,
    peak: 4,
    keyframe: 3,
    "layer-in": 2,
    "layer-out": 2,
    frame: 1,
  };

  // Sort by distance first, then by priority (higher priority wins for same distance)
  snapTargets.sort((a, b) => {
    const distDiff = a.distance - b.distance;
    if (Math.abs(distDiff) < 0.5) {
      // Very close - use priority
      return priority[b.type] - priority[a.type];
    }
    return distDiff;
  });

  return snapTargets[0];
}

/**
 * Collect keyframe snap targets from a layer's animatable properties
 */
function collectKeyframeSnapTargets(
  layer: Layer,
  frame: number,
  thresholdFrames: number,
  pixelsPerFrame: number,
  targets: SnapResult[],
): void {
  const properties: AnimatableProperty<any>[] = [
    layer.transform.position,
    layer.transform.scale,
    layer.transform.rotation,
    layer.opacity,
    ...layer.properties,
  ];

  for (const prop of properties) {
    if (!prop.animated || !prop.keyframes) continue;

    for (const kf of prop.keyframes) {
      const distance = Math.abs(frame - kf.frame);
      if (distance <= thresholdFrames) {
        // Avoid duplicates at same frame
        if (
          !targets.some((t) => t.frame === kf.frame && t.type === "keyframe")
        ) {
          targets.push({
            frame: kf.frame,
            type: "keyframe",
            distance: distance * pixelsPerFrame,
          });
        }
      }
    }
  }
}

/**
 * Get all beat frames from audio analysis
 */
export function getBeatFrames(audioAnalysis: AudioAnalysis | null): number[] {
  // Type proof: onsets ∈ number[] | undefined → number[]
  if (audioAnalysis && Array.isArray(audioAnalysis.onsets)) {
    return audioAnalysis.onsets;
  }
  return [];
}

/**
 * Get all peak frames from peak data
 */
export function getPeakFrames(peakData: PeakData | null): number[] {
  // Type proof: indices ∈ number[] | undefined → number[]
  if (peakData && Array.isArray(peakData.indices)) {
    return peakData.indices;
  }
  return [];
}

/**
 * Check if a frame is near a beat (within threshold)
 */
export function isNearBeat(
  frame: number,
  audioAnalysis: AudioAnalysis | null,
  thresholdFrames: number = 2,
): boolean {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const audioAnalysisOnsets = (audioAnalysis != null && typeof audioAnalysis === "object" && "onsets" in audioAnalysis && audioAnalysis.onsets != null && Array.isArray(audioAnalysis.onsets)) ? audioAnalysis.onsets : undefined;
  if (audioAnalysisOnsets == null) return false;

  return audioAnalysisOnsets.some(
    (onset) => Math.abs(frame - onset) <= thresholdFrames,
  );
}

/**
 * Get the nearest beat frame to a given frame
 * 
 * System F/Omega proof: Explicit validation of audio analysis and beats
 * Type proof: audioAnalysis ∈ AudioAnalysis | null, frame ∈ number → number (non-nullable)
 * Mathematical proof: Beat frames must exist to find nearest beat
 * Pattern proof: No beats is an explicit failure condition, not a lazy null return
 */
export function getNearestBeatFrame(
  frame: number,
  audioAnalysis: AudioAnalysis | null,
): number {
  // System F/Omega proof: Explicit validation of audio analysis existence
  // Type proof: audioAnalysis ∈ AudioAnalysis | null → onsets ∈ number[] | undefined
  // Mathematical proof: Audio analysis must exist and contain beats to find nearest beat
  if (!audioAnalysis) {
    throw new Error(
      `[TimelineSnap] Cannot find nearest beat frame: Audio analysis is null. ` +
      `Frame: ${frame}. ` +
      `Audio analysis must be provided and contain beat onset data. ` +
      `Ensure audio has been analyzed before calling getNearestBeatFrame().`
    );
  }

  // System F/Omega proof: Explicit validation of beat onsets existence
  // Type proof: onsets ∈ number[] | undefined → length ∈ number
  // Mathematical proof: Beat onsets array must exist and be non-empty
  if (!Array.isArray(audioAnalysis.onsets) || audioAnalysis.onsets.length === 0) {
    throw new Error(
      `[TimelineSnap] Cannot find nearest beat frame: No beat onsets available. ` +
      `Frame: ${frame}, audioAnalysis: ${audioAnalysis ? "present" : "null"}, ` +
      `onsets length: ${Array.isArray(audioAnalysis.onsets) ? audioAnalysis.onsets.length : "invalid"}. ` +
      `Audio analysis must contain beat onset data. Ensure audio has been analyzed and beats detected. ` +
      `Wrap in try/catch if "no beats" is an expected state.`
    );
  }

  let nearestFrame = audioAnalysis.onsets[0];
  let nearestDistance = Math.abs(frame - nearestFrame);

  for (const onset of audioAnalysis.onsets) {
    const distance = Math.abs(frame - onset);
    if (distance < nearestDistance) {
      nearestFrame = onset;
      nearestDistance = distance;
    }
  }

  return nearestFrame;
}

/**
 * Snap indicator data for visual feedback
 */
export interface SnapIndicator {
  frame: number;
  type: SnapType;
  color: string;
}

/**
 * Get color for snap type
 */
export function getSnapColor(type: SnapType): string {
  const colors: Record<SnapType, string> = {
    frame: "#666",
    keyframe: "#7c9cff",
    beat: "#ffc107",
    peak: "#ff6b6b",
    "layer-in": "#4ecdc4",
    "layer-out": "#4ecdc4",
    playhead: "#ff4444",
  };
  return colors[type];
}

export default {
  findNearestSnap,
  getBeatFrames,
  getPeakFrames,
  isNearBeat,
  getNearestBeatFrame,
  getSnapColor,
  DEFAULT_SNAP_CONFIG,
};
