/**
 * Wan-Move Export Service
 *
 * Exports trajectory and visibility data in Wan-Move compatible format
 * for motion-controllable video generation.
 *
 * Wan-Move Format:
 * - Trajectory: NumPy array shape (N, T, 2) - N points, T frames, x/y coords
 * - Visibility: NumPy array shape (N, T) - boolean visibility per point/frame
 *
 * @see https://github.com/ali-vilab/Wan-Move
 */

import type { ControlPoint } from "@/types/spline";

// Import flow generators and utilities from extracted module
import {
  generateDataRiverFlow,
  generateExplosionFlow,
  generateMorphFlow,
  generateSpiralFlow,
  generateSwarmFlow,
  generateVortexFlow,
  generateWaveFlow,
  SeededRandom,
} from "./wanMoveFlowGenerators";

// Re-export for backwards compatibility
export {
  generateDataRiverFlow,
  generateExplosionFlow,
  generateMorphFlow,
  generateSpiralFlow,
  generateSwarmFlow,
  generateVortexFlow,
  generateWaveFlow,
  SeededRandom,
  simplexNoise2D,
} from "./wanMoveFlowGenerators";

// Type alias for backwards compatibility
type SplinePoint = ControlPoint;

// ============================================================================
// TYPES
// ============================================================================

export interface WanMoveTrajectory {
  /** Trajectory coordinates: [N][T][2] where N=points, T=frames, 2=x,y */
  tracks: number[][][];
  /** Visibility mask: [N][T] where true = visible */
  visibility: boolean[][];
  /** Metadata */
  metadata: {
    numPoints: number;
    numFrames: number;
    width: number;
    height: number;
    fps: number;
  };
}

export interface GenerativeFlowConfig {
  /** Flow pattern type */
  pattern:
    | "spiral"
    | "wave"
    | "explosion"
    | "vortex"
    | "data-river"
    | "morph"
    | "swarm";
  /** Number of trajectory points */
  numPoints: number;
  /** Number of frames */
  numFrames: number;
  /** Canvas dimensions */
  width: number;
  height: number;
  /** Pattern-specific parameters */
  params: GenerativeFlowParams;
}

export interface GenerativeFlowParams {
  // Spiral
  spiralTurns?: number;
  spiralExpansion?: number;
  spiralSpeed?: number;

  // Wave
  waveAmplitude?: number;
  waveFrequency?: number;
  waveSpeed?: number;
  waveLayers?: number;

  // Explosion
  explosionSpeed?: number;
  explosionDecay?: number;
  explosionCenter?: { x: number; y: number };

  // Vortex
  vortexStrength?: number;
  vortexRadius?: number;
  vortexCenter?: { x: number; y: number };

  // Data River
  riverWidth?: number;
  riverCurve?: number;
  riverTurbulence?: number;

  // Morph
  morphSource?: "circle" | "grid" | "text" | "custom";
  morphTarget?: "circle" | "grid" | "text" | "custom";
  morphEasing?: "linear" | "ease-in" | "ease-out" | "ease-in-out";

  // Swarm
  swarmCohesion?: number;
  swarmSeparation?: number;
  swarmAlignment?: number;
  swarmSpeed?: number;

  // Common
  noiseStrength?: number;
  noiseScale?: number;
  seed?: number;
}

export interface DataDrivenFlowConfig {
  /** Data source - array of values per point */
  data: number[];
  /** How data maps to motion */
  mapping: "speed" | "direction" | "amplitude" | "phase" | "size";
  /** Base flow pattern */
  basePattern: GenerativeFlowConfig["pattern"];
  /** Number of frames */
  numFrames: number;
  /** Canvas dimensions */
  width: number;
  height: number;
  /** Spline path for flow direction */
  splinePath?: SplinePoint[];
}

// ============================================================================
// DATA-DRIVEN FLOW (from CSV/JSON data)
// ============================================================================

/**
 * Generate flow from imported data values
 */
export function generateDataDrivenFlow(
  config: DataDrivenFlowConfig,
): WanMoveTrajectory {
  const { data, mapping, basePattern, numFrames, width, height, splinePath } =
    config;
  const numPoints = data.length;

  // Generate base pattern
  const baseConfig: GenerativeFlowConfig = {
    pattern: basePattern,
    numPoints,
    numFrames,
    width,
    height,
    params: { seed: 42 },
  };

  let baseFlow: WanMoveTrajectory;
  switch (basePattern) {
    case "spiral":
      baseFlow = generateSpiralFlow(baseConfig);
      break;
    case "wave":
      baseFlow = generateWaveFlow(baseConfig);
      break;
    case "explosion":
      baseFlow = generateExplosionFlow(baseConfig);
      break;
    case "vortex":
      baseFlow = generateVortexFlow(baseConfig);
      break;
    case "data-river":
      baseFlow = generateDataRiverFlow(baseConfig);
      break;
    case "morph":
      baseFlow = generateMorphFlow(baseConfig);
      break;
    case "swarm":
      baseFlow = generateSwarmFlow(baseConfig);
      break;
    default:
      baseFlow = generateSpiralFlow(baseConfig);
  }

  // Normalize data to 0-1
  const minVal = Math.min(...data);
  const maxVal = Math.max(...data);
  const range = maxVal - minVal || 1;
  const normalizedData = data.map((v) => (v - minVal) / range);

  // Modify trajectories based on data mapping
  const modifiedTracks = baseFlow.tracks.map((track, i) => {
    const dataVal = normalizedData[i] ?? 0.5;

    return track.map((point, f) => {
      const [x, y] = point;

      switch (mapping) {
        case "speed": {
          // Data controls speed: higher values = faster progression
          const speedMult = 0.5 + dataVal * 1.5;
          const adjustedF = Math.min(
            track.length - 1,
            Math.floor(f * speedMult),
          );
          return track[adjustedF];
        }

        case "amplitude": {
          // Data controls distance from center
          const cx = width / 2;
          const cy = height / 2;
          const dx = x - cx;
          const dy = y - cy;
          const ampMult = 0.3 + dataVal * 1.4;
          return [cx + dx * ampMult, cy + dy * ampMult];
        }

        case "phase": {
          // Data controls phase offset (circular motion)
          const cx = width / 2;
          const cy = height / 2;
          const dx = x - cx;
          const dy = y - cy;
          const angle = Math.atan2(dy, dx) + dataVal * Math.PI * 2;
          const dist = Math.sqrt(dx * dx + dy * dy);
          return [cx + Math.cos(angle) * dist, cy + Math.sin(angle) * dist];
        }

        default:
          return point;
      }
    });
  });

  return {
    tracks: modifiedTracks,
    visibility: baseFlow.visibility,
    metadata: baseFlow.metadata,
  };
}

/**
 * Generate flow along a spline path (for path-based data visualization)
 */
export function generateSplineFlow(
  splinePoints: SplinePoint[],
  numPoints: number,
  numFrames: number,
  width: number,
  height: number,
  options: {
    spread?: number;
    stagger?: number;
    looping?: boolean;
    seed?: number;
  } = {},
): WanMoveTrajectory {
  const { spread = 20, stagger = 0.3, looping = false, seed = 42 } = options;
  const rng = new SeededRandom(seed);

  if (splinePoints.length < 2) {
    throw new Error("Spline must have at least 2 points");
  }

  // Sample spline at many points
  const splineSamples: { x: number; y: number }[] = [];
  const numSamples = 200;

  for (let i = 0; i < numSamples; i++) {
    const t = i / (numSamples - 1);
    const point = sampleSplineAt(splinePoints, t);
    splineSamples.push(point);
  }

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    // Staggered start
    const startOffset = rng.next() * stagger;
    // Lateral offset (spread perpendicular to path)
    const lateralOffset = rng.gaussian(0, spread);

    for (let f = 0; f < numFrames; f++) {
      let t = f / numFrames + startOffset;

      if (looping) {
        t = t % 1;
      } else {
        t = Math.min(1, t);
      }

      const sampleIdx = Math.floor(t * (numSamples - 1));
      const point = splineSamples[sampleIdx];

      // Get tangent for perpendicular offset
      const nextIdx = Math.min(numSamples - 1, sampleIdx + 1);
      const prevIdx = Math.max(0, sampleIdx - 1);
      const tangent = {
        x: splineSamples[nextIdx].x - splineSamples[prevIdx].x,
        y: splineSamples[nextIdx].y - splineSamples[prevIdx].y,
      };
      const tangentLen =
        Math.sqrt(tangent.x * tangent.x + tangent.y * tangent.y) || 1;
      const perpendicular = {
        x: -tangent.y / tangentLen,
        y: tangent.x / tangentLen,
      };

      const x = point.x + perpendicular.x * lateralOffset;
      const y = point.y + perpendicular.y * lateralOffset;

      track.push([
        Math.max(0, Math.min(width, x)),
        Math.max(0, Math.min(height, y)),
      ]);

      vis.push(t <= 1);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

// Helper: sample spline at parameter t
function sampleSplineAt(
  points: SplinePoint[],
  t: number,
): { x: number; y: number } {
  const numSegments = points.length - 1;
  const segmentT = t * numSegments;
  const segmentIdx = Math.min(numSegments - 1, Math.floor(segmentT));
  const localT = segmentT - segmentIdx;

  const p0 = points[segmentIdx];
  const p1 = points[segmentIdx + 1];

  // Cubic Bezier interpolation
  const h0 = p0.handleOut || { x: 0, y: 0 };
  const h1 = p1.handleIn || { x: 0, y: 0 };

  const cp0 = { x: p0.x, y: p0.y };
  const cp1 = { x: p0.x + h0.x, y: p0.y + h0.y };
  const cp2 = { x: p1.x + h1.x, y: p1.y + h1.y };
  const cp3 = { x: p1.x, y: p1.y };

  const t2 = localT * localT;
  const t3 = t2 * localT;
  const mt = 1 - localT;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;

  return {
    x:
      mt3 * cp0.x + 3 * mt2 * localT * cp1.x + 3 * mt * t2 * cp2.x + t3 * cp3.x,
    y:
      mt3 * cp0.y + 3 * mt2 * localT * cp1.y + 3 * mt * t2 * cp2.y + t3 * cp3.y,
  };
}

// ============================================================================
// EXPORT FUNCTIONS
// ============================================================================

/**
 * Export trajectory data as JSON (for JavaScript/ComfyUI consumption)
 */
export function exportAsJSON(trajectory: WanMoveTrajectory): string {
  return JSON.stringify(
    {
      tracks: trajectory.tracks,
      visibility: trajectory.visibility,
      metadata: trajectory.metadata,
    },
    null,
    2,
  );
}

// ============================================================================
// KIJAI WANVIDEOWRAPPER COMPATIBLE EXPORTS
// ============================================================================

/**
 * Track point as expected by Kijai's WanVideoWrapper
 */
export interface KijaiTrackPoint {
  x: number;
  y: number;
}

/**
 * Export trajectory as Kijai WanMove compatible JSON string
 *
 * Kijai's WanVideoWrapper expects:
 * - JSON string input to `track_coords` parameter
 * - Format: `[[{x, y}, {x, y}, ...], [{x, y}, ...], ...]`
 * - Each inner array is one track with per-frame {x, y} objects
 * - Coordinates are PIXEL VALUES (not normalized)
 *
 * @see https://github.com/kijai/ComfyUI-WanVideoWrapper/blob/main/WanMove/nodes.py
 */
export function exportAsKijaiWanMoveJSON(trajectory: WanMoveTrajectory): string {
  const { tracks } = trajectory;

  // Convert from number[][][] to {x, y}[][]
  // Lattice format: tracks[pointIdx][frameIdx][0=x, 1=y]
  // Kijai format: tracks[trackIdx][frameIdx] = {x, y}
  const kijaiTracks: KijaiTrackPoint[][] = tracks.map((track) =>
    track.map(([x, y]) => ({ x, y })),
  );

  return JSON.stringify(kijaiTracks);
}

/**
 * Export visibility as Kijai WanMove compatible JSON string
 *
 * Kijai's WanVideoWrapper creates visibility tensor from mask or defaults to all-visible.
 * When providing explicit visibility, it should be a boolean tensor matching track shape.
 *
 * Note: Most WanMove workflows don't require explicit visibility input -
 * the node creates all-visible mask by default. This is provided for completeness.
 */
export function exportAsKijaiWanMoveVisibility(
  trajectory: WanMoveTrajectory,
): string {
  // Kijai expects visibility shape (frames, num_tracks) after processing
  // but the JSON input is just used to create tracks, not visibility directly.
  // Visibility is typically derived from a mask input or defaulted to all-visible.
  //
  // If explicit visibility is needed, transpose from [N][T] to [T][N]
  const { visibility, metadata } = trajectory;
  const { numPoints, numFrames } = metadata;

  const transposedVis: boolean[][] = [];
  for (let f = 0; f < numFrames; f++) {
    transposedVis[f] = [];
    for (let n = 0; n < numPoints; n++) {
      transposedVis[f][n] = visibility[n]?.[f] ?? true;
    }
  }

  return JSON.stringify(transposedVis);
}

/**
 * Export complete WanMove package for Kijai's WanVideoWrapper
 *
 * Returns the track_coords JSON string ready for the WanVideoAddWanMoveTracks node.
 */
export function exportForKijaiWanMove(trajectory: WanMoveTrajectory): {
  trackCoords: string;
  metadata: WanMoveTrajectory["metadata"];
} {
  return {
    trackCoords: exportAsKijaiWanMoveJSON(trajectory),
    metadata: trajectory.metadata,
  };
}

/**
 * Export trajectory data as NPY-compatible format
 * Returns a structure that can be converted to NumPy arrays
 */
export function exportAsNPYData(trajectory: WanMoveTrajectory): {
  tracks: Float32Array;
  visibility: Uint8Array;
  shape: { tracks: [number, number, number]; visibility: [number, number] };
} {
  const { tracks, visibility, metadata } = trajectory;
  const { numPoints, numFrames } = metadata;

  // Flatten tracks to [N * T * 2] Float32Array
  const tracksFlat = new Float32Array(numPoints * numFrames * 2);
  for (let i = 0; i < numPoints; i++) {
    for (let f = 0; f < numFrames; f++) {
      const idx = (i * numFrames + f) * 2;
      tracksFlat[idx] = tracks[i][f][0];
      tracksFlat[idx + 1] = tracks[i][f][1];
    }
  }

  // Flatten visibility to [N * T] Uint8Array
  const visFlat = new Uint8Array(numPoints * numFrames);
  for (let i = 0; i < numPoints; i++) {
    for (let f = 0; f < numFrames; f++) {
      visFlat[i * numFrames + f] = visibility[i][f] ? 1 : 0;
    }
  }

  return {
    tracks: tracksFlat,
    visibility: visFlat,
    shape: {
      tracks: [numPoints, numFrames, 2],
      visibility: [numPoints, numFrames],
    },
  };
}

/**
 * Generate Wan-Move compatible output with conditioning image
 */
export async function exportWanMovePackage(
  trajectory: WanMoveTrajectory,
  sourceImage?: HTMLImageElement | ImageBitmap,
): Promise<{
  trajectoryJSON: string;
  trajectoryNPY: ReturnType<typeof exportAsNPYData>;
  conditioningImage?: Blob;
}> {
  const trajectoryJSON = exportAsJSON(trajectory);
  const trajectoryNPY = exportAsNPYData(trajectory);

  let conditioningImage: Blob | undefined;

  if (sourceImage) {
    // Render trajectory visualization on source image
    const canvas = new OffscreenCanvas(
      trajectory.metadata.width,
      trajectory.metadata.height,
    );
    const ctx = canvas.getContext("2d")!;

    // Draw source image
    ctx.drawImage(sourceImage, 0, 0, canvas.width, canvas.height);

    // Draw trajectory lines (for visualization/debugging)
    ctx.strokeStyle = "rgba(255, 100, 100, 0.5)";
    ctx.lineWidth = 1;

    for (const track of trajectory.tracks) {
      if (track.length < 2) continue;
      ctx.beginPath();
      ctx.moveTo(track[0][0], track[0][1]);
      for (let i = 1; i < track.length; i++) {
        ctx.lineTo(track[i][0], track[i][1]);
      }
      ctx.stroke();
    }

    conditioningImage = await canvas.convertToBlob({ type: "image/png" });
  }

  return {
    trajectoryJSON,
    trajectoryNPY,
    conditioningImage,
  };
}

// ============================================================================
// ENHANCED TRAJECTORY WITH COLOR DATA
// ============================================================================

export interface ColoredTrajectory extends WanMoveTrajectory {
  /** RGB color per point per frame: [N][T][3] values 0-255 */
  colors?: number[][][];
  /** Data values per point (for visualization): [N] */
  dataValues?: number[];
  /** Trail history length per point */
  trailLength?: number;
}

export interface ColorGradient {
  stops: Array<{ position: number; color: [number, number, number] }>;
}

/** Built-in color gradients for data visualization */
export const COLOR_GRADIENTS: Record<string, ColorGradient> = {
  viridis: {
    stops: [
      { position: 0, color: [68, 1, 84] },
      { position: 0.25, color: [59, 82, 139] },
      { position: 0.5, color: [33, 145, 140] },
      { position: 0.75, color: [94, 201, 98] },
      { position: 1, color: [253, 231, 37] },
    ],
  },
  plasma: {
    stops: [
      { position: 0, color: [13, 8, 135] },
      { position: 0.25, color: [126, 3, 168] },
      { position: 0.5, color: [204, 71, 120] },
      { position: 0.75, color: [248, 149, 64] },
      { position: 1, color: [240, 249, 33] },
    ],
  },
  inferno: {
    stops: [
      { position: 0, color: [0, 0, 4] },
      { position: 0.25, color: [87, 16, 110] },
      { position: 0.5, color: [188, 55, 84] },
      { position: 0.75, color: [249, 142, 9] },
      { position: 1, color: [252, 255, 164] },
    ],
  },
  "cool-warm": {
    stops: [
      { position: 0, color: [59, 76, 192] },
      { position: 0.5, color: [221, 221, 221] },
      { position: 1, color: [180, 4, 38] },
    ],
  },
  rainbow: {
    stops: [
      { position: 0, color: [255, 0, 0] },
      { position: 0.2, color: [255, 165, 0] },
      { position: 0.4, color: [255, 255, 0] },
      { position: 0.6, color: [0, 255, 0] },
      { position: 0.8, color: [0, 0, 255] },
      { position: 1, color: [128, 0, 128] },
    ],
  },
  depth: {
    stops: [
      { position: 0, color: [0, 0, 0] },
      { position: 1, color: [255, 255, 255] },
    ],
  },
};

/**
 * Sample color from gradient at position t (0-1)
 */
export function sampleGradient(
  gradient: ColorGradient,
  t: number,
): [number, number, number] {
  t = Math.max(0, Math.min(1, t));

  const stops = gradient.stops;
  if (stops.length === 0) return [128, 128, 128];
  if (stops.length === 1) return stops[0].color;

  // Find surrounding stops
  let lower = stops[0];
  let upper = stops[stops.length - 1];

  for (let i = 0; i < stops.length - 1; i++) {
    if (t >= stops[i].position && t <= stops[i + 1].position) {
      lower = stops[i];
      upper = stops[i + 1];
      break;
    }
  }

  const range = upper.position - lower.position;
  const localT = range > 0 ? (t - lower.position) / range : 0;

  return [
    Math.round(lower.color[0] + (upper.color[0] - lower.color[0]) * localT),
    Math.round(lower.color[1] + (upper.color[1] - lower.color[1]) * localT),
    Math.round(lower.color[2] + (upper.color[2] - lower.color[2]) * localT),
  ];
}

/**
 * Add color data to trajectory based on data values
 */
export function addColorToTrajectory(
  trajectory: WanMoveTrajectory,
  dataValues: number[],
  gradientName: keyof typeof COLOR_GRADIENTS = "viridis",
): ColoredTrajectory {
  const gradient = COLOR_GRADIENTS[gradientName];
  const minVal = Math.min(...dataValues);
  const maxVal = Math.max(...dataValues);
  const range = maxVal - minVal || 1;

  const colors: number[][][] = [];

  for (let i = 0; i < trajectory.tracks.length; i++) {
    const normalizedValue =
      (dataValues[i % dataValues.length] - minVal) / range;
    const color = sampleGradient(gradient, normalizedValue);

    // Same color for all frames of this trajectory
    colors.push(trajectory.tracks[i].map(() => color));
  }

  return {
    ...trajectory,
    colors,
    dataValues,
  };
}

/**
 * Add time-based color (earlier = one color, later = another)
 */
export function addTimeColorToTrajectory(
  trajectory: WanMoveTrajectory,
  gradientName: keyof typeof COLOR_GRADIENTS = "plasma",
): ColoredTrajectory {
  const gradient = COLOR_GRADIENTS[gradientName];
  const colors: number[][][] = [];
  const numFrames = trajectory.metadata.numFrames;

  for (let i = 0; i < trajectory.tracks.length; i++) {
    const trackColors: number[][] = [];
    for (let f = 0; f < trajectory.tracks[i].length; f++) {
      const t = f / (numFrames - 1);
      trackColors.push(sampleGradient(gradient, t));
    }
    colors.push(trackColors);
  }

  return { ...trajectory, colors };
}

// ============================================================================
// STRANGE ATTRACTORS (Chaotic systems for organic complexity)
// ============================================================================

export interface AttractorConfig {
  type: "lorenz" | "rossler" | "aizawa" | "thomas" | "halvorsen";
  numPoints: number;
  numFrames: number;
  width: number;
  height: number;
  /** Time step for integration */
  dt?: number;
  /** Scale factor to fit in canvas */
  scale?: number;
  /** Center offset */
  center?: { x: number; y: number };
  seed?: number;
}

/**
 * Generate Lorenz attractor trajectories
 * Creates the famous "butterfly" chaotic pattern
 */
export function generateLorenzAttractor(
  config: AttractorConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, seed = 42 } = config;
  const dt = config.dt ?? 0.005;
  const scale = config.scale ?? 8;
  const center = config.center ?? { x: width / 2, y: height / 2 };

  const rng = new SeededRandom(seed);

  // Lorenz parameters
  const sigma = 10;
  const rho = 28;
  const beta = 8 / 3;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    // Start near the attractor with small variations
    let x = rng.range(-0.1, 0.1);
    let y = rng.range(-0.1, 0.1);
    let z = rng.range(20, 30);

    const track: number[][] = [];
    const vis: boolean[] = [];

    // Let it settle into the attractor
    for (let s = 0; s < 500; s++) {
      const dx = sigma * (y - x);
      const dy = x * (rho - z) - y;
      const dz = x * y - beta * z;
      x += dx * dt;
      y += dy * dt;
      z += dz * dt;
    }

    // Record trajectory
    for (let f = 0; f < numFrames; f++) {
      // Multiple integration steps per frame for smoothness
      for (let s = 0; s < 10; s++) {
        const dx = sigma * (y - x);
        const dy = x * (rho - z) - y;
        const dz = x * y - beta * z;
        x += dx * dt;
        y += dy * dt;
        z += dz * dt;
      }

      // Project to 2D (XZ plane looks best for Lorenz)
      const px = center.x + x * scale;
      const py = center.y + (z - 25) * scale; // Center around z=25

      track.push([
        Math.max(0, Math.min(width, px)),
        Math.max(0, Math.min(height, py)),
      ]);
      vis.push(true);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate Rössler attractor trajectories
 * Creates a simpler spiral-like chaotic pattern
 */
export function generateRosslerAttractor(
  config: AttractorConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, seed = 42 } = config;
  const dt = config.dt ?? 0.02;
  const scale = config.scale ?? 15;
  const center = config.center ?? { x: width / 2, y: height / 2 };

  const rng = new SeededRandom(seed);

  // Rössler parameters
  const a = 0.2;
  const b = 0.2;
  const c = 5.7;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    let x = rng.range(-1, 1);
    let y = rng.range(-1, 1);
    let z = rng.range(0, 1);

    const track: number[][] = [];
    const vis: boolean[] = [];

    // Settle
    for (let s = 0; s < 300; s++) {
      const dx = -y - z;
      const dy = x + a * y;
      const dz = b + z * (x - c);
      x += dx * dt;
      y += dy * dt;
      z += dz * dt;
    }

    for (let f = 0; f < numFrames; f++) {
      for (let s = 0; s < 5; s++) {
        const dx = -y - z;
        const dy = x + a * y;
        const dz = b + z * (x - c);
        x += dx * dt;
        y += dy * dt;
        z += dz * dt;
      }

      const px = center.x + x * scale;
      const py = center.y + y * scale;

      track.push([
        Math.max(0, Math.min(width, px)),
        Math.max(0, Math.min(height, py)),
      ]);
      vis.push(true);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate Aizawa attractor (beautiful 3D torus-like chaos)
 */
export function generateAizawaAttractor(
  config: AttractorConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, seed = 42 } = config;
  const dt = config.dt ?? 0.01;
  const scale = config.scale ?? 80;
  const center = config.center ?? { x: width / 2, y: height / 2 };

  const rng = new SeededRandom(seed);

  // Aizawa parameters
  const a = 0.95,
    b = 0.7,
    c = 0.6,
    d = 3.5,
    e = 0.25,
    f = 0.1;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    let x = rng.range(0.1, 0.2);
    let y = rng.range(0, 0.1);
    let z = rng.range(0, 0.1);

    const track: number[][] = [];
    const vis: boolean[] = [];

    // Settle
    for (let s = 0; s < 500; s++) {
      const dx = (z - b) * x - d * y;
      const dy = d * x + (z - b) * y;
      const dz =
        c +
        a * z -
        (z * z * z) / 3 -
        (x * x + y * y) * (1 + e * z) +
        f * z * x * x * x;
      x += dx * dt;
      y += dy * dt;
      z += dz * dt;
    }

    for (let fr = 0; fr < numFrames; fr++) {
      for (let s = 0; s < 8; s++) {
        const dx = (z - b) * x - d * y;
        const dy = d * x + (z - b) * y;
        const dz =
          c +
          a * z -
          (z * z * z) / 3 -
          (x * x + y * y) * (1 + e * z) +
          f * z * x * x * x;
        x += dx * dt;
        y += dy * dt;
        z += dz * dt;
      }

      const px = center.x + x * scale;
      const py = center.y + y * scale;

      track.push([
        Math.max(0, Math.min(width, px)),
        Math.max(0, Math.min(height, py)),
      ]);
      vis.push(true);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

// ============================================================================
// SHAPE TARGET MORPHING
// ============================================================================

export interface ShapeTargetConfig {
  numPoints: number;
  numFrames: number;
  width: number;
  height: number;
  /** Source shape */
  source: ShapeDefinition;
  /** Target shape */
  target: ShapeDefinition;
  /** Easing function */
  easing?:
    | "linear"
    | "ease-in"
    | "ease-out"
    | "ease-in-out"
    | "elastic"
    | "bounce";
  /** Add organic noise during morph */
  morphNoise?: number;
  seed?: number;
}

export type ShapeDefinition =
  | { type: "circle"; radius?: number; center?: { x: number; y: number } }
  | { type: "grid"; columns?: number; rows?: number; padding?: number }
  | { type: "text"; text: string; fontSize?: number }
  | { type: "heart" }
  | {
      type: "star";
      points?: number;
      innerRadius?: number;
      outerRadius?: number;
    }
  | { type: "spiral"; turns?: number }
  | { type: "random" }
  | { type: "custom"; points: Array<{ x: number; y: number }> };

/**
 * Generate points for a shape
 */
function generateShapePoints(
  shape: ShapeDefinition,
  numPoints: number,
  width: number,
  height: number,
  rng: SeededRandom,
): Array<{ x: number; y: number }> {
  const cx = width / 2;
  const cy = height / 2;
  const size = Math.min(width, height) * 0.4;

  switch (shape.type) {
    case "circle": {
      const radius = shape.radius ?? size;
      const center = shape.center ?? { x: cx, y: cy };
      return Array.from({ length: numPoints }, (_, i) => {
        const angle = (i / numPoints) * Math.PI * 2;
        return {
          x: center.x + Math.cos(angle) * radius,
          y: center.y + Math.sin(angle) * radius,
        };
      });
    }

    case "grid": {
      const cols = shape.columns ?? Math.ceil(Math.sqrt(numPoints));
      const rows = shape.rows ?? Math.ceil(numPoints / cols);
      const padding = shape.padding ?? 0.1;
      const points: Array<{ x: number; y: number }> = [];

      for (let i = 0; i < numPoints; i++) {
        const col = i % cols;
        const row = Math.floor(i / cols);
        points.push({
          x:
            width * padding +
            (col / (cols - 1 || 1)) * width * (1 - 2 * padding),
          y:
            height * padding +
            (row / (rows - 1 || 1)) * height * (1 - 2 * padding),
        });
      }
      return points;
    }

    case "text": {
      // Generate points along text path (simplified - creates rough outline)
      const text = shape.text;
      const fontSize = shape.fontSize ?? 100;
      const points: Array<{ x: number; y: number }> = [];
      const textWidth = text.length * fontSize * 0.6;
      const startX = cx - textWidth / 2;

      for (let i = 0; i < numPoints; i++) {
        const charIndex = Math.floor((i / numPoints) * text.length);
        const localT = (i / numPoints) * text.length - charIndex;

        // Simple character outline approximation
        const charX = startX + charIndex * fontSize * 0.6;
        const angle = localT * Math.PI * 2;
        const charRadius = fontSize * 0.3;

        points.push({
          x: charX + Math.cos(angle) * charRadius + fontSize * 0.3,
          y: cy + Math.sin(angle) * charRadius,
        });
      }
      return points;
    }

    case "heart": {
      return Array.from({ length: numPoints }, (_, i) => {
        const t = (i / numPoints) * Math.PI * 2;
        // Heart parametric equation
        const x = 16 * Math.sin(t) ** 3;
        const y =
          13 * Math.cos(t) -
          5 * Math.cos(2 * t) -
          2 * Math.cos(3 * t) -
          Math.cos(4 * t);
        return {
          x: cx + (x * size) / 20,
          y: cy - (y * size) / 20, // Flip y for screen coords
        };
      });
    }

    case "star": {
      const outerRadius = shape.outerRadius ?? size;
      const innerRadius = shape.innerRadius ?? size * 0.4;
      const starPoints = shape.points ?? 5;

      return Array.from({ length: numPoints }, (_, i) => {
        const t = (i / numPoints) * Math.PI * 2;
        const pointIndex = Math.floor((i / numPoints) * starPoints * 2);
        const isOuter = pointIndex % 2 === 0;
        const radius = isOuter ? outerRadius : innerRadius;
        const angle = t - Math.PI / 2; // Start from top

        return {
          x: cx + Math.cos(angle) * radius,
          y: cy + Math.sin(angle) * radius,
        };
      });
    }

    case "spiral": {
      const turns = shape.turns ?? 3;
      return Array.from({ length: numPoints }, (_, i) => {
        const t = i / numPoints;
        const angle = t * Math.PI * 2 * turns;
        const radius = t * size;
        return {
          x: cx + Math.cos(angle) * radius,
          y: cy + Math.sin(angle) * radius,
        };
      });
    }

    case "random": {
      return Array.from({ length: numPoints }, () => ({
        x: rng.range(width * 0.1, width * 0.9),
        y: rng.range(height * 0.1, height * 0.9),
      }));
    }

    case "custom": {
      // Distribute points along custom shape
      if (shape.points.length === 0) return [];
      return Array.from({ length: numPoints }, (_, i) => {
        const idx = (i / numPoints) * shape.points.length;
        const lower = Math.floor(idx);
        const upper = Math.ceil(idx) % shape.points.length;
        const t = idx - lower;
        return {
          x:
            shape.points[lower].x +
            (shape.points[upper].x - shape.points[lower].x) * t,
          y:
            shape.points[lower].y +
            (shape.points[upper].y - shape.points[lower].y) * t,
        };
      });
    }
  }
}

/**
 * Generate shape-to-shape morph trajectories
 */
export function generateShapeMorph(
  config: ShapeTargetConfig,
): WanMoveTrajectory {
  const {
    numPoints,
    numFrames,
    width,
    height,
    source,
    target,
    seed = 42,
  } = config;
  const morphNoise = config.morphNoise ?? 0.1;
  const easing = config.easing ?? "ease-in-out";

  const rng = new SeededRandom(seed);

  const sourcePoints = generateShapePoints(
    source,
    numPoints,
    width,
    height,
    rng,
  );
  const targetPoints = generateShapePoints(
    target,
    numPoints,
    width,
    height,
    rng,
  );

  // Easing functions
  const easingFn = (t: number): number => {
    switch (easing) {
      case "ease-in":
        return t * t * t;
      case "ease-out":
        return 1 - (1 - t) ** 3;
      case "ease-in-out":
        return t < 0.5 ? 4 * t * t * t : 1 - (-2 * t + 2) ** 3 / 2;
      case "elastic": {
        const c4 = (2 * Math.PI) / 3;
        return t === 0
          ? 0
          : t === 1
            ? 1
            : 2 ** (-10 * t) * Math.sin((t * 10 - 0.75) * c4) + 1;
      }
      case "bounce": {
        const n1 = 7.5625,
          d1 = 2.75;
        if (t < 1 / d1) return n1 * t * t;
        if (t < 2 / d1) return n1 * (t -= 1.5 / d1) * t + 0.75;
        if (t < 2.5 / d1) return n1 * (t -= 2.25 / d1) * t + 0.9375;
        return n1 * (t -= 2.625 / d1) * t + 0.984375;
      }
      default:
        return t;
    }
  };

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    const src = sourcePoints[i];
    const tgt = targetPoints[i];

    for (let f = 0; f < numFrames; f++) {
      const t = f / (numFrames - 1);
      const easedT = easingFn(t);

      // Add noise that peaks in the middle of the morph
      const noiseMult = Math.sin(t * Math.PI) * morphNoise;
      const noiseX = (rng.next() - 0.5) * width * noiseMult;
      const noiseY = (rng.next() - 0.5) * height * noiseMult;

      const x = src.x + (tgt.x - src.x) * easedT + noiseX;
      const y = src.y + (tgt.y - src.y) * easedT + noiseY;

      track.push([
        Math.max(0, Math.min(width, x)),
        Math.max(0, Math.min(height, y)),
      ]);
      vis.push(true);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

// ============================================================================
// FORCE FIELD SYSTEM (Attractors & Repulsors)
// ============================================================================

export interface ForcePoint {
  x: number;
  y: number;
  /** Positive = attractor, Negative = repulsor */
  strength: number;
  /** Influence radius */
  radius: number;
  /** Falloff type */
  falloff?: "linear" | "quadratic" | "none";
}

export interface ForceFieldConfig {
  numPoints: number;
  numFrames: number;
  width: number;
  height: number;
  /** Force points (attractors/repulsors) */
  forces: ForcePoint[];
  /** Initial distribution */
  initialDistribution?: "random" | "grid" | "edge" | "center";
  /** Global damping */
  damping?: number;
  /** Maximum speed */
  maxSpeed?: number;
  seed?: number;
}

/**
 * Generate trajectories influenced by force fields
 */
export function generateForceFieldFlow(
  config: ForceFieldConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, forces, seed = 42 } = config;
  const damping = config.damping ?? 0.98;
  const maxSpeed = config.maxSpeed ?? 15;
  const distribution = config.initialDistribution ?? "random";

  const rng = new SeededRandom(seed);

  // Initialize particles
  const particles: Array<{ x: number; y: number; vx: number; vy: number }> = [];

  for (let i = 0; i < numPoints; i++) {
    let x: number, y: number;

    switch (distribution) {
      case "grid": {
        const cols = Math.ceil(Math.sqrt(numPoints));
        const col = i % cols;
        const row = Math.floor(i / cols);
        x = ((col + 0.5) / cols) * width;
        y = ((row + 0.5) / cols) * height;
        break;
      }
      case "edge": {
        const side = i % 4;
        const t = rng.next();
        switch (side) {
          case 0:
            x = t * width;
            y = 0;
            break;
          case 1:
            x = width;
            y = t * height;
            break;
          case 2:
            x = t * width;
            y = height;
            break;
          default:
            x = 0;
            y = t * height;
        }
        break;
      }
      case "center": {
        const angle = rng.next() * Math.PI * 2;
        const radius = rng.next() * Math.min(width, height) * 0.1;
        x = width / 2 + Math.cos(angle) * radius;
        y = height / 2 + Math.sin(angle) * radius;
        break;
      }
      default: // random
        x = rng.range(0, width);
        y = rng.range(0, height);
    }

    particles.push({ x, y, vx: 0, vy: 0 });
  }

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  // Pre-allocate
  for (let i = 0; i < numPoints; i++) {
    tracks.push([]);
    visibility.push([]);
  }

  // Simulate
  for (let f = 0; f < numFrames; f++) {
    for (let i = 0; i < numPoints; i++) {
      const p = particles[i];

      // Calculate force from all force points
      let fx = 0,
        fy = 0;

      for (const force of forces) {
        const dx = force.x - p.x;
        const dy = force.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < force.radius && dist > 0) {
          let falloffMult = 1;
          switch (force.falloff ?? "quadratic") {
            case "linear":
              falloffMult = 1 - dist / force.radius;
              break;
            case "quadratic":
              falloffMult = (1 - dist / force.radius) ** 2;
              break;
            case "none":
              falloffMult = 1;
              break;
          }

          const strength = force.strength * falloffMult;
          fx += (dx / dist) * strength;
          fy += (dy / dist) * strength;
        }
      }

      // Update velocity
      p.vx += fx;
      p.vy += fy;

      // Damping
      p.vx *= damping;
      p.vy *= damping;

      // Speed limit
      const speed = Math.sqrt(p.vx * p.vx + p.vy * p.vy);
      if (speed > maxSpeed) {
        p.vx = (p.vx / speed) * maxSpeed;
        p.vy = (p.vy / speed) * maxSpeed;
      }

      // Update position
      p.x += p.vx;
      p.y += p.vy;

      // Record
      tracks[i].push([
        Math.max(0, Math.min(width, p.x)),
        Math.max(0, Math.min(height, p.y)),
      ]);
      visibility[i].push(p.x >= 0 && p.x <= width && p.y >= 0 && p.y <= height);
    }
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

// ============================================================================
// MULTI-LAYER COMPOSITION
// ============================================================================

export interface FlowLayer {
  trajectory: WanMoveTrajectory;
  /** Layer name for identification */
  name?: string;
  /** Blend weight when compositing */
  weight?: number;
  /** Color override for this layer */
  color?: [number, number, number];
}

/**
 * Composite multiple flow layers into one trajectory
 */
export function compositeFlowLayers(layers: FlowLayer[]): WanMoveTrajectory {
  if (layers.length === 0) {
    throw new Error("At least one layer required");
  }

  // Use first layer's metadata as base
  const firstMeta = layers[0].trajectory.metadata;

  // Concatenate all tracks
  const allTracks: number[][][] = [];
  const allVisibility: boolean[][] = [];

  for (const layer of layers) {
    allTracks.push(...layer.trajectory.tracks);
    allVisibility.push(...layer.trajectory.visibility);
  }

  return {
    tracks: allTracks,
    visibility: allVisibility,
    metadata: {
      numPoints: allTracks.length,
      numFrames: firstMeta.numFrames,
      width: firstMeta.width,
      height: firstMeta.height,
      fps: firstMeta.fps,
    },
  };
}

/**
 * Composite with color data preserved per layer
 */
export function compositeColoredLayers(layers: FlowLayer[]): ColoredTrajectory {
  const base = compositeFlowLayers(layers);
  const colors: number[][][] = [];

  for (const layer of layers) {
    const layerColor = layer.color ?? [255, 255, 255];

    for (const track of layer.trajectory.tracks) {
      colors.push(track.map(() => layerColor));
    }
  }

  return { ...base, colors };
}

// ============================================================================
// VISUALIZATION / PREVIEW RENDERING
// ============================================================================

export interface RenderOptions {
  /** Background color */
  background?: string;
  /** Draw trails */
  showTrails?: boolean;
  /** Trail length (frames) */
  trailLength?: number;
  /** Trail fade */
  trailFade?: boolean;
  /** Point size */
  pointSize?: number;
  /** Use colors from trajectory */
  useTrajectoryColors?: boolean;
  /** Default color if no trajectory colors */
  defaultColor?: string;
  /** Show velocity vectors */
  showVelocity?: boolean;
}

/**
 * Render trajectory frame to canvas
 */
export function renderTrajectoryFrame(
  ctx: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D,
  trajectory: WanMoveTrajectory | ColoredTrajectory,
  frame: number,
  options: RenderOptions = {},
): void {
  const {
    background = "#0a0a0a",
    showTrails = true,
    trailLength = 10,
    trailFade = true,
    pointSize = 2,
    useTrajectoryColors = true,
    defaultColor = "#8b5cf6",
    showVelocity = false,
  } = options;

  const { tracks, metadata } = trajectory;
  const colors = "colors" in trajectory ? trajectory.colors : undefined;
  const { width, height } = metadata;

  // Clear
  ctx.fillStyle = background;
  ctx.fillRect(0, 0, width, height);

  // Draw each trajectory
  for (let i = 0; i < tracks.length; i++) {
    const track = tracks[i];
    if (frame >= track.length) continue;

    // Determine color
    let color = defaultColor;
    if (useTrajectoryColors && colors && colors[i] && colors[i][frame]) {
      const [r, g, b] = colors[i][frame];
      color = `rgb(${r},${g},${b})`;
    }

    // Draw trail
    if (showTrails && frame > 0) {
      const startFrame = Math.max(0, frame - trailLength);

      ctx.beginPath();
      ctx.moveTo(track[startFrame][0], track[startFrame][1]);

      for (let f = startFrame + 1; f <= frame; f++) {
        ctx.lineTo(track[f][0], track[f][1]);
      }

      if (trailFade) {
        const gradient = ctx.createLinearGradient(
          track[startFrame][0],
          track[startFrame][1],
          track[frame][0],
          track[frame][1],
        );
        gradient.addColorStop(0, "transparent");
        gradient.addColorStop(1, color);
        ctx.strokeStyle = gradient;
      } else {
        ctx.strokeStyle = color;
      }

      ctx.lineWidth = 1;
      ctx.stroke();
    }

    // Draw point
    ctx.fillStyle = color;
    ctx.beginPath();
    ctx.arc(track[frame][0], track[frame][1], pointSize, 0, Math.PI * 2);
    ctx.fill();

    // Draw velocity vector
    if (showVelocity && frame > 0) {
      const vx = track[frame][0] - track[frame - 1][0];
      const vy = track[frame][1] - track[frame - 1][1];

      ctx.strokeStyle = "rgba(255,255,255,0.3)";
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(track[frame][0], track[frame][1]);
      ctx.lineTo(track[frame][0] + vx * 3, track[frame][1] + vy * 3);
      ctx.stroke();
    }
  }
}

/**
 * Render all frames to image sequence
 */
export async function renderTrajectorySequence(
  trajectory: WanMoveTrajectory | ColoredTrajectory,
  options: RenderOptions = {},
): Promise<Blob[]> {
  const { width, height, numFrames } = trajectory.metadata;
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext("2d")!;

  const frames: Blob[] = [];

  for (let f = 0; f < numFrames; f++) {
    renderTrajectoryFrame(ctx, trajectory, f, options);
    const blob = await canvas.convertToBlob({ type: "image/png" });
    frames.push(blob);
  }

  return frames;
}

// ============================================================================
// GENERATIVE FLOW PRESETS (Ready-to-use configurations)
// ============================================================================

export const FLOW_PRESETS = {
  /** Data flowing through neural pathways */
  "neural-flow": {
    pattern: "data-river" as const,
    params: {
      riverWidth: 0.4,
      riverCurve: 2,
      riverTurbulence: 0.15,
      noiseStrength: 0.08,
    },
  },

  /** Particles spiraling into a black hole */
  singularity: {
    pattern: "vortex" as const,
    params: {
      vortexStrength: 0.8,
      vortexRadius: 0.4,
      noiseStrength: 0.05,
    },
  },

  /** Big bang style data explosion */
  "data-genesis": {
    pattern: "explosion" as const,
    params: {
      explosionSpeed: 1.2,
      explosionDecay: 0.92,
      noiseStrength: 0.15,
    },
  },

  /** Gentle wave of information */
  "information-tide": {
    pattern: "wave" as const,
    params: {
      waveAmplitude: 0.12,
      waveFrequency: 2,
      waveLayers: 8,
      noiseStrength: 0.05,
    },
  },

  /** Spiral galaxy formation */
  "cosmic-spiral": {
    pattern: "spiral" as const,
    params: {
      spiralTurns: 4,
      spiralExpansion: 1.2,
      noiseStrength: 0.1,
    },
  },

  /** Data morphing between shapes */
  metamorphosis: {
    pattern: "morph" as const,
    params: {
      morphSource: "grid" as const,
      morphTarget: "circle" as const,
      morphEasing: "ease-in-out" as const,
      noiseStrength: 0.08,
    },
  },

  /** Collective intelligence swarm */
  hivemind: {
    pattern: "swarm" as const,
    params: {
      swarmCohesion: 0.015,
      swarmSeparation: 25,
      swarmAlignment: 0.08,
      swarmSpeed: 4,
    },
  },
};

/**
 * Generate flow from preset name
 */
export function generateFromPreset(
  presetName: keyof typeof FLOW_PRESETS,
  numPoints: number,
  numFrames: number,
  width: number,
  height: number,
  seed?: number,
): WanMoveTrajectory {
  const preset = FLOW_PRESETS[presetName];
  const config: GenerativeFlowConfig = {
    pattern: preset.pattern,
    numPoints,
    numFrames,
    width,
    height,
    params: { ...preset.params, seed: seed ?? 42 },
  };

  switch (preset.pattern) {
    case "spiral":
      return generateSpiralFlow(config);
    case "wave":
      return generateWaveFlow(config);
    case "explosion":
      return generateExplosionFlow(config);
    case "vortex":
      return generateVortexFlow(config);
    case "data-river":
      return generateDataRiverFlow(config);
    case "morph":
      return generateMorphFlow(config);
    case "swarm":
      return generateSwarmFlow(config);
    default:
      return generateSpiralFlow(config);
  }
}

// ============================================================================
// ATTRACTOR PRESETS
// ============================================================================

export const ATTRACTOR_PRESETS = {
  "lorenz-butterfly": {
    type: "lorenz" as const,
    scale: 8,
    dt: 0.005,
  },
  "rossler-spiral": {
    type: "rossler" as const,
    scale: 15,
    dt: 0.02,
  },
  "aizawa-torus": {
    type: "aizawa" as const,
    scale: 80,
    dt: 0.01,
  },
};

// ============================================================================
// SHAPE MORPH PRESETS
// ============================================================================

export const SHAPE_PRESETS = {
  "grid-to-circle": {
    source: { type: "grid" as const },
    target: { type: "circle" as const },
    easing: "ease-in-out" as const,
  },
  "random-to-heart": {
    source: { type: "random" as const },
    target: { type: "heart" as const },
    easing: "elastic" as const,
  },
  "circle-to-star": {
    source: { type: "circle" as const },
    target: { type: "star" as const, points: 5 },
    easing: "bounce" as const,
  },
  "spiral-to-grid": {
    source: { type: "spiral" as const, turns: 3 },
    target: { type: "grid" as const },
    easing: "ease-out" as const,
  },
};

// ============================================================================
// DEFAULT EXPORT
// ============================================================================

export default {
  // Basic flow generators
  generateSpiralFlow,
  generateWaveFlow,
  generateExplosionFlow,
  generateVortexFlow,
  generateDataRiverFlow,
  generateMorphFlow,
  generateSwarmFlow,
  generateDataDrivenFlow,
  generateSplineFlow,

  // Strange attractors
  generateLorenzAttractor,
  generateRosslerAttractor,
  generateAizawaAttractor,

  // Shape morphing
  generateShapeMorph,

  // Force fields
  generateForceFieldFlow,

  // Multi-layer
  compositeFlowLayers,
  compositeColoredLayers,

  // Color mapping
  addColorToTrajectory,
  addTimeColorToTrajectory,
  sampleGradient,
  COLOR_GRADIENTS,

  // Rendering
  renderTrajectoryFrame,
  renderTrajectorySequence,

  // Export functions
  exportAsJSON,
  exportAsNPYData,
  exportWanMovePackage,

  // Presets
  FLOW_PRESETS,
  ATTRACTOR_PRESETS,
  SHAPE_PRESETS,
  generateFromPreset,
};
