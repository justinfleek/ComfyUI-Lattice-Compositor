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
): SnapResult | null {
  if (!config.enabled) {
    return null;
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
  if (config.snapToBeats && context.audioAnalysis?.onsets) {
    for (const onset of context.audioAnalysis.onsets) {
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
  if (config.snapToPeaks && context.peakData?.indices) {
    for (const peakFrame of context.peakData.indices) {
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

      const layerStart = layer.startFrame ?? layer.inPoint ?? 0;
      const layerEnd = layer.endFrame ?? layer.outPoint ?? 80;
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

  // Find the closest snap target
  if (snapTargets.length === 0) {
    return null;
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
  return audioAnalysis?.onsets ?? [];
}

/**
 * Get all peak frames from peak data
 */
export function getPeakFrames(peakData: PeakData | null): number[] {
  return peakData?.indices ?? [];
}

/**
 * Check if a frame is near a beat (within threshold)
 */
export function isNearBeat(
  frame: number,
  audioAnalysis: AudioAnalysis | null,
  thresholdFrames: number = 2,
): boolean {
  if (!audioAnalysis?.onsets) return false;

  return audioAnalysis.onsets.some(
    (onset) => Math.abs(frame - onset) <= thresholdFrames,
  );
}

/**
 * Get the nearest beat frame to a given frame
 */
export function getNearestBeatFrame(
  frame: number,
  audioAnalysis: AudioAnalysis | null,
): number | null {
  if (!audioAnalysis?.onsets || audioAnalysis.onsets.length === 0) {
    return null;
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
