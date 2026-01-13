/**
 * WanMove Export Schemas
 *
 * Zod schemas for validating WanMove trajectory export data.
 * WanMove format uses N points across T frames with [x,y] coordinates.
 * All numeric values use .finite() to reject NaN/Infinity.
 *
 * @see https://github.com/ali-vilab/Wan-Move
 */

import { z } from "zod";

// ============================================================================
// Constants
// ============================================================================

/** Maximum supported dimension */
export const WANMOVE_MAX_DIMENSION = 8192;

/** Maximum number of trajectory points */
export const WANMOVE_MAX_POINTS = 10000;

/** Maximum number of frames */
export const WANMOVE_MAX_FRAMES = 10000;

// ============================================================================
// Primitive Schemas
// ============================================================================

/** Finite number that rejects NaN and Infinity */
const finiteNumber = z.number().finite();

/** Positive finite number */
const positiveFinite = z.number().finite().positive();

/** Non-negative finite number */
const nonNegativeFinite = z.number().finite().nonnegative();

/** Normalized 0-1 value */
const normalized01 = z.number().finite().min(0).max(1);

/** Positive integer dimension */
const positiveDimension = z
  .number()
  .int()
  .positive()
  .max(WANMOVE_MAX_DIMENSION);

/** Positive integer count */
const positiveCount = z.number().int().positive();

/** Non-negative integer */
const nonNegativeInt = z.number().int().nonnegative();

/** RGB channel (0-255) */
const colorChannel = z.number().int().min(0).max(255);

// ============================================================================
// Point Schemas
// ============================================================================

/**
 * Simple 2D point with x,y coordinates.
 */
export const Point2DSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
});

export type Point2D = z.infer<typeof Point2DSchema>;

/**
 * Track point as [x, y] tuple for internal track representation.
 */
export const TrackPointTupleSchema = z.tuple([finiteNumber, finiteNumber]);

export type TrackPointTuple = z.infer<typeof TrackPointTupleSchema>;

/**
 * TrackPoint as object (for JSON export to ComfyUI).
 */
export const TrackPointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
});

export type TrackPoint = z.infer<typeof TrackPointSchema>;

/**
 * RGB color tuple [r, g, b] with values 0-255.
 */
export const RGBColorTupleSchema = z.tuple([
  colorChannel,
  colorChannel,
  colorChannel,
]);

export type RGBColorTuple = z.infer<typeof RGBColorTupleSchema>;

// ============================================================================
// Trajectory Metadata Schema
// ============================================================================

/**
 * Metadata for a WanMove trajectory export.
 */
export const WanMoveMetadataSchema = z.object({
  numPoints: positiveCount,
  numFrames: positiveCount,
  width: positiveDimension,
  height: positiveDimension,
  fps: positiveFinite,
});

export type WanMoveMetadata = z.infer<typeof WanMoveMetadataSchema>;

// ============================================================================
// Main Trajectory Schema
// ============================================================================

/**
 * A single track's trajectory: array of [x, y] points per frame.
 */
export const SingleTrackSchema = z.array(TrackPointTupleSchema);

export type SingleTrack = z.infer<typeof SingleTrackSchema>;

/**
 * All tracks: [N][T][2] format - N points, T frames, 2 coordinates.
 */
export const TracksArraySchema = z.array(SingleTrackSchema);

export type TracksArray = z.infer<typeof TracksArraySchema>;

/**
 * Visibility for a single track: boolean per frame.
 */
export const SingleVisibilitySchema = z.array(z.boolean());

export type SingleVisibility = z.infer<typeof SingleVisibilitySchema>;

/**
 * All visibility data: [N][T] format.
 */
export const VisibilityArraySchema = z.array(SingleVisibilitySchema);

export type VisibilityArray = z.infer<typeof VisibilityArraySchema>;

/**
 * Main WanMove trajectory structure.
 */
export const WanMoveTrajectorySchema = z.object({
  /** Trajectory coordinates: [N][T][2] */
  tracks: TracksArraySchema,
  /** Visibility mask: [N][T] */
  visibility: VisibilityArraySchema,
  /** Metadata */
  metadata: WanMoveMetadataSchema,
});

export type WanMoveTrajectory = z.infer<typeof WanMoveTrajectorySchema>;

// ============================================================================
// Color Gradient Schema
// ============================================================================

/**
 * A single color stop in a gradient.
 */
export const ColorStopSchema = z.object({
  position: normalized01,
  color: RGBColorTupleSchema,
});

export type ColorStop = z.infer<typeof ColorStopSchema>;

/**
 * A color gradient definition.
 */
export const ColorGradientSchema = z.object({
  stops: z.array(ColorStopSchema).min(1),
});

export type ColorGradient = z.infer<typeof ColorGradientSchema>;

// ============================================================================
// Colored Trajectory Schema
// ============================================================================

/**
 * Extended trajectory with color data.
 */
export const ColoredTrajectorySchema = WanMoveTrajectorySchema.extend({
  /** RGB color per point per frame: [N][T][3] values 0-255 */
  colors: z.array(z.array(RGBColorTupleSchema)).optional(),
  /** Data values per point (for visualization): [N] */
  dataValues: z.array(finiteNumber).optional(),
  /** Trail history length per point */
  trailLength: positiveCount.optional(),
});

export type ColoredTrajectory = z.infer<typeof ColoredTrajectorySchema>;

// ============================================================================
// Flow Pattern Schema
// ============================================================================

/**
 * Available flow pattern types.
 */
export const FlowPatternSchema = z.enum([
  "spiral",
  "wave",
  "explosion",
  "vortex",
  "data-river",
  "morph",
  "swarm",
]);

export type FlowPattern = z.infer<typeof FlowPatternSchema>;

/**
 * Morph source/target type.
 */
export const MorphShapeTypeSchema = z.enum([
  "circle",
  "grid",
  "text",
  "custom",
]);

export type MorphShapeType = z.infer<typeof MorphShapeTypeSchema>;

/**
 * Morph easing type.
 */
export const MorphEasingSchema = z.enum([
  "linear",
  "ease-in",
  "ease-out",
  "ease-in-out",
]);

export type MorphEasing = z.infer<typeof MorphEasingSchema>;

/**
 * Extended easing type for shape morphing.
 */
export const ShapeEasingSchema = z.enum([
  "linear",
  "ease-in",
  "ease-out",
  "ease-in-out",
  "elastic",
  "bounce",
]);

export type ShapeEasing = z.infer<typeof ShapeEasingSchema>;

// ============================================================================
// Generative Flow Params Schema
// ============================================================================

/**
 * Pattern-specific parameters for generative flows.
 */
export const GenerativeFlowParamsSchema = z.object({
  // Spiral
  spiralTurns: positiveFinite.optional(),
  spiralExpansion: finiteNumber.optional(),
  spiralSpeed: positiveFinite.optional(),

  // Wave
  waveAmplitude: positiveFinite.optional(),
  waveFrequency: positiveFinite.optional(),
  waveSpeed: positiveFinite.optional(),
  waveLayers: positiveCount.optional(),

  // Explosion
  explosionSpeed: positiveFinite.optional(),
  explosionDecay: nonNegativeFinite.optional(),
  explosionCenter: Point2DSchema.optional(),

  // Vortex
  vortexStrength: finiteNumber.optional(),
  vortexRadius: positiveFinite.optional(),
  vortexCenter: Point2DSchema.optional(),

  // Data River
  riverWidth: positiveFinite.optional(),
  riverCurve: finiteNumber.optional(),
  riverTurbulence: nonNegativeFinite.optional(),

  // Morph
  morphSource: MorphShapeTypeSchema.optional(),
  morphTarget: MorphShapeTypeSchema.optional(),
  morphEasing: MorphEasingSchema.optional(),

  // Swarm
  swarmCohesion: nonNegativeFinite.optional(),
  swarmSeparation: nonNegativeFinite.optional(),
  swarmAlignment: nonNegativeFinite.optional(),
  swarmSpeed: positiveFinite.optional(),

  // Common
  noiseStrength: nonNegativeFinite.optional(),
  noiseScale: positiveFinite.optional(),
  seed: z.number().int().optional(),
});

export type GenerativeFlowParams = z.infer<typeof GenerativeFlowParamsSchema>;

// ============================================================================
// Generative Flow Config Schema
// ============================================================================

/**
 * Configuration for generating flow patterns.
 */
export const GenerativeFlowConfigSchema = z.object({
  /** Flow pattern type */
  pattern: FlowPatternSchema,
  /** Number of trajectory points */
  numPoints: positiveCount.max(WANMOVE_MAX_POINTS),
  /** Number of frames */
  numFrames: positiveCount.max(WANMOVE_MAX_FRAMES),
  /** Canvas width */
  width: positiveDimension,
  /** Canvas height */
  height: positiveDimension,
  /** Pattern-specific parameters */
  params: GenerativeFlowParamsSchema,
});

export type GenerativeFlowConfig = z.infer<typeof GenerativeFlowConfigSchema>;

// ============================================================================
// Data Mapping Schema
// ============================================================================

/**
 * Data mapping type for data-driven flows.
 */
export const DataMappingSchema = z.enum([
  "speed",
  "direction",
  "amplitude",
  "phase",
  "size",
]);

export type DataMapping = z.infer<typeof DataMappingSchema>;

// ============================================================================
// Spline Point Schema (for spline-based flows)
// ============================================================================

/**
 * Control point for spline paths.
 */
export const SplinePointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  handleIn: Point2DSchema.optional(),
  handleOut: Point2DSchema.optional(),
});

export type SplinePoint = z.infer<typeof SplinePointSchema>;

// ============================================================================
// Data-Driven Flow Config Schema
// ============================================================================

/**
 * Configuration for data-driven flow generation.
 */
export const DataDrivenFlowConfigSchema = z.object({
  /** Data source - array of values per point */
  data: z.array(finiteNumber).min(1),
  /** How data maps to motion */
  mapping: DataMappingSchema,
  /** Base flow pattern */
  basePattern: FlowPatternSchema,
  /** Number of frames */
  numFrames: positiveCount.max(WANMOVE_MAX_FRAMES),
  /** Canvas width */
  width: positiveDimension,
  /** Canvas height */
  height: positiveDimension,
  /** Spline path for flow direction */
  splinePath: z.array(SplinePointSchema).optional(),
});

export type DataDrivenFlowConfig = z.infer<typeof DataDrivenFlowConfigSchema>;

// ============================================================================
// Attractor Config Schema
// ============================================================================

/**
 * Available strange attractor types.
 */
export const AttractorTypeSchema = z.enum([
  "lorenz",
  "rossler",
  "aizawa",
  "thomas",
  "halvorsen",
]);

export type AttractorType = z.infer<typeof AttractorTypeSchema>;

/**
 * Configuration for strange attractor generation.
 */
export const AttractorConfigSchema = z.object({
  type: AttractorTypeSchema,
  numPoints: positiveCount.max(WANMOVE_MAX_POINTS),
  numFrames: positiveCount.max(WANMOVE_MAX_FRAMES),
  width: positiveDimension,
  height: positiveDimension,
  /** Time step for integration */
  dt: positiveFinite.optional(),
  /** Scale factor to fit in canvas */
  scale: positiveFinite.optional(),
  /** Center offset */
  center: Point2DSchema.optional(),
  seed: z.number().int().optional(),
});

export type AttractorConfig = z.infer<typeof AttractorConfigSchema>;

// ============================================================================
// Shape Definition Schemas
// ============================================================================

/**
 * Circle shape definition.
 */
export const CircleShapeSchema = z.object({
  type: z.literal("circle"),
  radius: positiveFinite.optional(),
  center: Point2DSchema.optional(),
});

/**
 * Grid shape definition.
 */
export const GridShapeSchema = z.object({
  type: z.literal("grid"),
  columns: positiveCount.optional(),
  rows: positiveCount.optional(),
  padding: normalized01.optional(),
});

/**
 * Text shape definition.
 */
export const TextShapeSchema = z.object({
  type: z.literal("text"),
  text: z.string().min(1),
  fontSize: positiveFinite.optional(),
});

/**
 * Heart shape definition.
 */
export const HeartShapeSchema = z.object({
  type: z.literal("heart"),
});

/**
 * Star shape definition.
 */
export const StarShapeSchema = z.object({
  type: z.literal("star"),
  points: positiveCount.optional(),
  innerRadius: positiveFinite.optional(),
  outerRadius: positiveFinite.optional(),
});

/**
 * Spiral shape definition.
 */
export const SpiralShapeSchema = z.object({
  type: z.literal("spiral"),
  turns: positiveFinite.optional(),
});

/**
 * Random shape definition.
 */
export const RandomShapeSchema = z.object({
  type: z.literal("random"),
});

/**
 * Custom shape definition.
 */
export const CustomShapeSchema = z.object({
  type: z.literal("custom"),
  points: z.array(Point2DSchema).min(1),
});

/**
 * Discriminated union of all shape types.
 */
export const ShapeDefinitionSchema = z.discriminatedUnion("type", [
  CircleShapeSchema,
  GridShapeSchema,
  TextShapeSchema,
  HeartShapeSchema,
  StarShapeSchema,
  SpiralShapeSchema,
  RandomShapeSchema,
  CustomShapeSchema,
]);

export type ShapeDefinition = z.infer<typeof ShapeDefinitionSchema>;

// ============================================================================
// Shape Target Config Schema
// ============================================================================

/**
 * Configuration for shape morphing.
 */
export const ShapeTargetConfigSchema = z.object({
  numPoints: positiveCount.max(WANMOVE_MAX_POINTS),
  numFrames: positiveCount.max(WANMOVE_MAX_FRAMES),
  width: positiveDimension,
  height: positiveDimension,
  /** Source shape */
  source: ShapeDefinitionSchema,
  /** Target shape */
  target: ShapeDefinitionSchema,
  /** Easing function */
  easing: ShapeEasingSchema.optional(),
  /** Add organic noise during morph */
  morphNoise: nonNegativeFinite.optional(),
  seed: z.number().int().optional(),
});

export type ShapeTargetConfig = z.infer<typeof ShapeTargetConfigSchema>;

// ============================================================================
// Force Point Schema
// ============================================================================

/**
 * Falloff types for force points.
 */
export const ForceFalloffSchema = z.enum(["linear", "quadratic", "none"]);

export type ForceFalloff = z.infer<typeof ForceFalloffSchema>;

/**
 * A single force point (attractor or repulsor).
 */
export const ForcePointSchema = z.object({
  x: finiteNumber,
  y: finiteNumber,
  /** Positive = attractor, Negative = repulsor */
  strength: finiteNumber,
  /** Influence radius */
  radius: positiveFinite,
  /** Falloff type */
  falloff: ForceFalloffSchema.optional(),
});

export type ForcePoint = z.infer<typeof ForcePointSchema>;

// ============================================================================
// Force Field Config Schema
// ============================================================================

/**
 * Initial distribution types for force fields.
 */
export const InitialDistributionSchema = z.enum([
  "random",
  "grid",
  "edge",
  "center",
]);

export type InitialDistribution = z.infer<typeof InitialDistributionSchema>;

/**
 * Configuration for force field flow generation.
 */
export const ForceFieldConfigSchema = z.object({
  numPoints: positiveCount.max(WANMOVE_MAX_POINTS),
  numFrames: positiveCount.max(WANMOVE_MAX_FRAMES),
  width: positiveDimension,
  height: positiveDimension,
  /** Force points (attractors/repulsors) */
  forces: z.array(ForcePointSchema),
  /** Initial distribution */
  initialDistribution: InitialDistributionSchema.optional(),
  /** Global damping */
  damping: normalized01.optional(),
  /** Maximum speed */
  maxSpeed: positiveFinite.optional(),
  seed: z.number().int().optional(),
});

export type ForceFieldConfig = z.infer<typeof ForceFieldConfigSchema>;

// ============================================================================
// Flow Layer Schema
// ============================================================================

/**
 * A single layer in multi-layer composition.
 */
export const FlowLayerSchema = z.object({
  trajectory: WanMoveTrajectorySchema,
  /** Layer name for identification */
  name: z.string().optional(),
  /** Blend weight when compositing */
  weight: normalized01.optional(),
  /** Color override for this layer */
  color: RGBColorTupleSchema.optional(),
});

export type FlowLayer = z.infer<typeof FlowLayerSchema>;

// ============================================================================
// Render Options Schema
// ============================================================================

/**
 * Options for rendering trajectory previews.
 */
export const RenderOptionsSchema = z.object({
  /** Background color */
  background: z.string().optional(),
  /** Draw trails */
  showTrails: z.boolean().optional(),
  /** Trail length (frames) */
  trailLength: positiveCount.optional(),
  /** Trail fade */
  trailFade: z.boolean().optional(),
  /** Point size */
  pointSize: positiveFinite.optional(),
  /** Use colors from trajectory */
  useTrajectoryColors: z.boolean().optional(),
  /** Default color if no trajectory colors */
  defaultColor: z.string().optional(),
  /** Show velocity vectors */
  showVelocity: z.boolean().optional(),
});

export type RenderOptions = z.infer<typeof RenderOptionsSchema>;

// ============================================================================
// Export Package Schema
// ============================================================================

/**
 * Complete WanMove export package for ComfyUI.
 */
export const WanMoveExportPackageSchema = z.object({
  /** JSON-serialized track coordinates for WanVideoAddWanMoveTracks */
  trackCoords: z.string().min(1),
  /** Metadata about the export */
  metadata: WanMoveMetadataSchema,
  /** Optional visibility data */
  visibility: z.string().optional(),
});

export type WanMoveExportPackage = z.infer<typeof WanMoveExportPackageSchema>;

// ============================================================================
// Full Export Data Schema (for file import/export)
// ============================================================================

/**
 * Full WanMove data structure for import/export operations.
 */
export const WanMoveDataSchema = z.object({
  trajectory: WanMoveTrajectorySchema,
  /** Optional color data */
  colors: z.array(z.array(RGBColorTupleSchema)).optional(),
  /** Export metadata */
  exportMetadata: z.object({
    version: z.string().min(1),
    exportedAt: z.string().optional(),
    source: z.string().optional(),
  }).optional(),
});

export type WanMoveData = z.infer<typeof WanMoveDataSchema>;
