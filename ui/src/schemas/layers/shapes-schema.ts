/**
 * Shape Layer Schemas
 *
 * Zod schemas for shape layer system with generators, modifiers, operators, and groups.
 * All numeric values use .finite() to reject NaN/Infinity.
 *
 * This schema matches the structure in types/shapes.ts exactly.
 */

import { z } from "zod";
import {
  finiteNumber,
  positiveFinite,
  nonNegativeFinite,
  normalized01,
  Vec2Schema,
  EntityIdSchema,
} from "./primitives-schema";
import {
  AnimatableNumberSchema,
  AnimatablePositionSchema,
  AnimatablePropertySchema,
  createAnimatablePropertySchema,
} from "./animation-schema";

// ============================================================================
// BASE TYPES
// ============================================================================

/**
 * 2D Point (alias for Vec2Schema)
 */
export const Point2DSchema = Vec2Schema;

export type Point2D = z.infer<typeof Point2DSchema>;

/**
 * ShapeColor - RGBA with r,g,b in 0-255 range, a in 0-1 range
 */
export const ShapeColorSchema = z.object({
  r: z.number().int().min(0).max(255),
  g: z.number().int().min(0).max(255),
  b: z.number().int().min(0).max(255),
  a: normalized01,
});

export type ShapeColor = z.infer<typeof ShapeColorSchema>;

/**
 * Bezier vertex with handles
 */
export const BezierVertexSchema = z.object({
  point: Point2DSchema,
  inHandle: Point2DSchema, // Relative to point
  outHandle: Point2DSchema, // Relative to point
});

export type BezierVertex = z.infer<typeof BezierVertexSchema>;

/**
 * Bezier path (open or closed)
 */
export const BezierPathSchema = z.object({
  vertices: z.array(BezierVertexSchema),
  closed: z.boolean(),
});

export type BezierPath = z.infer<typeof BezierPathSchema>;

/**
 * Gradient stop
 */
export const GradientStopSchema = z.object({
  position: normalized01,
  color: ShapeColorSchema,
});

export type GradientStop = z.infer<typeof GradientStopSchema>;

/**
 * Gradient definition
 */
export const GradientDefSchema = z.object({
  type: z.enum(["linear", "radial"]),
  stops: z.array(GradientStopSchema),
  startPoint: Point2DSchema, // Normalized 0-1
  endPoint: Point2DSchema, // For linear: end point, for radial: edge point
  highlightLength: z.number().finite().min(0).max(100).optional(), // Radial only
  highlightAngle: finiteNumber.optional(), // Radial only: degrees
});

export type GradientDef = z.infer<typeof GradientDefSchema>;

// ============================================================================
// ANIMATABLE PROPERTY SCHEMAS FOR SHAPES
// ============================================================================

/**
 * Animatable Point2D property
 */
export const AnimatablePoint2DSchema = createAnimatablePropertySchema(Point2DSchema);

export type AnimatablePoint2D = z.infer<typeof AnimatablePoint2DSchema>;

/**
 * Animatable ShapeColor property
 */
export const AnimatableShapeColorSchema = createAnimatablePropertySchema(ShapeColorSchema);

export type AnimatableShapeColor = z.infer<typeof AnimatableShapeColorSchema>;

/**
 * Animatable BezierPath property
 */
export const AnimatableBezierPathSchema = createAnimatablePropertySchema(BezierPathSchema);

export type AnimatableBezierPath = z.infer<typeof AnimatableBezierPathSchema>;

/**
 * Animatable GradientDef property
 */
export const AnimatableGradientDefSchema = createAnimatablePropertySchema(GradientDefSchema);

export type AnimatableGradientDef = z.infer<typeof AnimatableGradientDefSchema>;

/**
 * Animatable number array property (for dash patterns)
 */
export const AnimatableNumberArraySchema = createAnimatablePropertySchema(
  z.array(nonNegativeFinite)
);

export type AnimatableNumberArray = z.infer<typeof AnimatableNumberArraySchema>;

// ============================================================================
// SHAPE GENERATORS
// ============================================================================

export const RectangleShapeSchema = z.object({
  type: z.literal("rectangle"),
  name: z.string(),
  position: AnimatablePoint2DSchema,
  size: AnimatablePoint2DSchema,
  roundness: AnimatableNumberSchema, // Corner radius in pixels
  direction: z.union([z.literal(1), z.literal(-1)]), // 1 = clockwise, -1 = counter-clockwise
});

export type RectangleShape = z.infer<typeof RectangleShapeSchema>;

export const EllipseShapeSchema = z.object({
  type: z.literal("ellipse"),
  name: z.string(),
  position: AnimatablePoint2DSchema,
  size: AnimatablePoint2DSchema,
  direction: z.union([z.literal(1), z.literal(-1)]),
});

export type EllipseShape = z.infer<typeof EllipseShapeSchema>;

export const PolygonShapeSchema = z.object({
  type: z.literal("polygon"),
  name: z.string(),
  position: AnimatablePoint2DSchema,
  points: AnimatableNumberSchema, // Number of sides (3+)
  outerRadius: AnimatableNumberSchema,
  outerRoundness: AnimatableNumberSchema, // 0-100%
  rotation: AnimatableNumberSchema, // Degrees
  direction: z.union([z.literal(1), z.literal(-1)]),
});

export type PolygonShape = z.infer<typeof PolygonShapeSchema>;

export const StarShapeSchema = z.object({
  type: z.literal("star"),
  name: z.string(),
  position: AnimatablePoint2DSchema,
  points: AnimatableNumberSchema, // Number of points (3+)
  outerRadius: AnimatableNumberSchema,
  innerRadius: AnimatableNumberSchema,
  outerRoundness: AnimatableNumberSchema, // 0-100%
  innerRoundness: AnimatableNumberSchema, // 0-100%
  rotation: AnimatableNumberSchema,
  direction: z.union([z.literal(1), z.literal(-1)]),
});

export type StarShape = z.infer<typeof StarShapeSchema>;

export const PathShapeSchema = z.object({
  type: z.literal("path"),
  name: z.string(),
  path: AnimatableBezierPathSchema,
  direction: z.union([z.literal(1), z.literal(-1)]),
});

export type PathShape = z.infer<typeof PathShapeSchema>;

export const ShapeGeneratorSchema = z.discriminatedUnion("type", [
  RectangleShapeSchema,
  EllipseShapeSchema,
  PolygonShapeSchema,
  StarShapeSchema,
  PathShapeSchema,
]);

export type ShapeGenerator = z.infer<typeof ShapeGeneratorSchema>;

// ============================================================================
// SHAPE MODIFIERS (Fill/Stroke)
// ============================================================================

export const FillRuleSchema = z.enum(["nonzero", "evenodd"]);
export const LineCapSchema = z.enum(["butt", "round", "square"]);
export const LineJoinSchema = z.enum(["miter", "round", "bevel"]);

export const FillShapeSchema = z.object({
  type: z.literal("fill"),
  name: z.string(),
  color: AnimatableShapeColorSchema,
  opacity: AnimatableNumberSchema, // 0-100
  fillRule: FillRuleSchema,
  blendMode: z.string(),
});

export type FillShape = z.infer<typeof FillShapeSchema>;

export const StrokeShapeSchema = z.object({
  type: z.literal("stroke"),
  name: z.string(),
  color: AnimatableShapeColorSchema,
  opacity: AnimatableNumberSchema, // 0-100
  width: AnimatableNumberSchema,
  lineCap: LineCapSchema,
  lineJoin: LineJoinSchema,
  miterLimit: finiteNumber,
  // Dashes
  dashPattern: AnimatableNumberArraySchema, // [dash, gap, dash, gap, ...]
  dashOffset: AnimatableNumberSchema,
  blendMode: z.string(),
  // Taper (stroke width variation)
  taperEnabled: z.boolean(),
  taperStartLength: AnimatableNumberSchema, // 0-100%
  taperEndLength: AnimatableNumberSchema,
  taperStartWidth: AnimatableNumberSchema, // 0-100%
  taperEndWidth: AnimatableNumberSchema,
  taperStartEase: AnimatableNumberSchema, // 0-100%
  taperEndEase: AnimatableNumberSchema,
});

export type StrokeShape = z.infer<typeof StrokeShapeSchema>;

export const GradientFillShapeSchema = z.object({
  type: z.literal("gradientFill"),
  name: z.string(),
  gradient: AnimatableGradientDefSchema,
  opacity: AnimatableNumberSchema,
  fillRule: FillRuleSchema,
  blendMode: z.string(),
});

export type GradientFillShape = z.infer<typeof GradientFillShapeSchema>;

export const GradientStrokeShapeSchema = z.object({
  type: z.literal("gradientStroke"),
  name: z.string(),
  gradient: AnimatableGradientDefSchema,
  opacity: AnimatableNumberSchema,
  width: AnimatableNumberSchema,
  lineCap: LineCapSchema,
  lineJoin: LineJoinSchema,
  miterLimit: finiteNumber,
  dashPattern: AnimatableNumberArraySchema,
  dashOffset: AnimatableNumberSchema,
  blendMode: z.string(),
});

export type GradientStrokeShape = z.infer<typeof GradientStrokeShapeSchema>;

export const ShapeModifierSchema = z.discriminatedUnion("type", [
  FillShapeSchema,
  StrokeShapeSchema,
  GradientFillShapeSchema,
  GradientStrokeShapeSchema,
]);

export type ShapeModifier = z.infer<typeof ShapeModifierSchema>;

// ============================================================================
// PATH OPERATORS
// ============================================================================

export const TrimModeSchema = z.enum(["simultaneously", "individually"]);

export const TrimPathsOperatorSchema = z.object({
  type: z.literal("trimPaths"),
  name: z.string(),
  start: AnimatableNumberSchema, // 0-100%
  end: AnimatableNumberSchema, // 0-100%
  offset: AnimatableNumberSchema, // Degrees (-360 to 360)
  mode: TrimModeSchema,
});

export type TrimPathsOperator = z.infer<typeof TrimPathsOperatorSchema>;

export const MergeModeSchema = z.enum([
  "add", // Union
  "subtract", // Minus Front
  "intersect", // Intersection
  "exclude", // Exclude Intersection
  "minusFront", // Same as subtract
  "minusBack", // Minus Back (Illustrator)
]);

export const MergePathsOperatorSchema = z.object({
  type: z.literal("mergePaths"),
  name: z.string(),
  mode: MergeModeSchema,
});

export type MergePathsOperator = z.infer<typeof MergePathsOperatorSchema>;

export const OffsetJoinSchema = z.enum(["miter", "round", "bevel"]);

export const OffsetPathsOperatorSchema = z.object({
  type: z.literal("offsetPaths"),
  name: z.string(),
  amount: AnimatableNumberSchema, // Positive = expand, negative = contract
  lineJoin: OffsetJoinSchema,
  miterLimit: AnimatableNumberSchema,
  copies: AnimatableNumberSchema, // AE: can create multiple offset copies
  copyOffset: AnimatableNumberSchema, // Distance between copies
});

export type OffsetPathsOperator = z.infer<typeof OffsetPathsOperatorSchema>;

export const PuckerBloatOperatorSchema = z.object({
  type: z.literal("puckerBloat"),
  name: z.string(),
  amount: AnimatableNumberSchema, // -100 (pucker) to 100 (bloat)
});

export type PuckerBloatOperator = z.infer<typeof PuckerBloatOperatorSchema>;

export const WigglePointTypeSchema = z.enum(["corner", "smooth"]);

export const WigglePathsOperatorSchema = z.object({
  type: z.literal("wigglePaths"),
  name: z.string(),
  size: AnimatableNumberSchema, // Wiggle magnitude
  detail: AnimatableNumberSchema, // Segments per curve (1-10)
  points: WigglePointTypeSchema,
  correlation: AnimatableNumberSchema, // 0-100% how linked adjacent points are
  temporalPhase: AnimatableNumberSchema, // Animation offset
  spatialPhase: AnimatableNumberSchema, // Spatial offset
  randomSeed: z.number().int(),
});

export type WigglePathsOperator = z.infer<typeof WigglePathsOperatorSchema>;

export const ZigZagPointTypeSchema = z.enum(["corner", "smooth"]);

export const ZigZagOperatorSchema = z.object({
  type: z.literal("zigZag"),
  name: z.string(),
  size: AnimatableNumberSchema, // Peak height
  ridgesPerSegment: AnimatableNumberSchema, // Zigzags per path segment
  points: ZigZagPointTypeSchema,
});

export type ZigZagOperator = z.infer<typeof ZigZagOperatorSchema>;

export const TwistOperatorSchema = z.object({
  type: z.literal("twist"),
  name: z.string(),
  angle: AnimatableNumberSchema, // Total twist in degrees
  center: AnimatablePoint2DSchema,
});

export type TwistOperator = z.infer<typeof TwistOperatorSchema>;

export const RoundedCornersOperatorSchema = z.object({
  type: z.literal("roundedCorners"),
  name: z.string(),
  radius: AnimatableNumberSchema,
});

export type RoundedCornersOperator = z.infer<typeof RoundedCornersOperatorSchema>;

export const PathOperatorSchema = z.discriminatedUnion("type", [
  TrimPathsOperatorSchema,
  MergePathsOperatorSchema,
  OffsetPathsOperatorSchema,
  PuckerBloatOperatorSchema,
  WigglePathsOperatorSchema,
  ZigZagOperatorSchema,
  TwistOperatorSchema,
  RoundedCornersOperatorSchema,
]);

export type PathOperator = z.infer<typeof PathOperatorSchema>;

// ============================================================================
// TRANSFORM & REPEATER
// ============================================================================

export const ShapeTransformSchema = z.object({
  type: z.literal("transform"),
  name: z.string(),
  anchorPoint: AnimatablePoint2DSchema,
  position: AnimatablePoint2DSchema,
  scale: AnimatablePoint2DSchema, // Percentage (100 = 100%)
  rotation: AnimatableNumberSchema, // Degrees
  skew: AnimatableNumberSchema, // Degrees
  skewAxis: AnimatableNumberSchema, // Degrees
  opacity: AnimatableNumberSchema, // 0-100%
});

export type ShapeTransform = z.infer<typeof ShapeTransformSchema>;

export const RepeaterCompositeSchema = z.enum(["above", "below"]);

export const RepeaterOperatorSchema = z.object({
  type: z.literal("repeater"),
  name: z.string(),
  copies: AnimatableNumberSchema,
  offset: AnimatableNumberSchema, // Offset from original (degrees for radial)
  composite: RepeaterCompositeSchema, // Stack order
  // Transform per copy
  transform: z.object({
    anchorPoint: AnimatablePoint2DSchema,
    position: AnimatablePoint2DSchema,
    scale: AnimatablePoint2DSchema, // End scale (100 = no change)
    rotation: AnimatableNumberSchema, // Rotation per copy
    startOpacity: AnimatableNumberSchema, // Opacity of first copy
    endOpacity: AnimatableNumberSchema, // Opacity of last copy
  }),
});

export type RepeaterOperator = z.infer<typeof RepeaterOperatorSchema>;

// ============================================================================
// ILLUSTRATOR-SPECIFIC OPERATORS
// ============================================================================

export const SimplifyPathOperatorSchema = z.object({
  type: z.literal("simplifyPath"),
  name: z.string(),
  tolerance: AnimatableNumberSchema, // Curve precision (0-100)
  angleTolerance: AnimatableNumberSchema, // Corner angle threshold
  straightLines: z.boolean(), // Convert to straight segments
});

export type SimplifyPathOperator = z.infer<typeof SimplifyPathOperatorSchema>;

export const SmoothPathOperatorSchema = z.object({
  type: z.literal("smoothPath"),
  name: z.string(),
  amount: AnimatableNumberSchema, // 0-100%
});

export type SmoothPathOperator = z.infer<typeof SmoothPathOperatorSchema>;

export const ExtrudeOperatorSchema = z.object({
  type: z.literal("extrude"),
  name: z.string(),
  depth: AnimatableNumberSchema, // Extrusion depth
  bevelDepth: AnimatableNumberSchema, // Bevel size
  bevelSegments: z.number().int().nonnegative(), // Smoothness of bevel
  capType: z.enum(["flat", "round", "bevel"]),
  material: z.object({
    frontColor: AnimatableShapeColorSchema,
    sideColor: AnimatableShapeColorSchema,
    bevelColor: AnimatableShapeColorSchema,
  }),
});

export type ExtrudeOperator = z.infer<typeof ExtrudeOperatorSchema>;

export const TraceOperatorSchema = z.object({
  type: z.literal("trace"),
  name: z.string(),
  mode: z.enum(["blackAndWhite", "grayscale", "color"]),
  threshold: AnimatableNumberSchema, // B&W threshold (0-255)
  colors: z.number().int().positive(), // Max colors for color mode
  cornerAngle: finiteNumber, // Corner detection threshold
  pathFitting: AnimatableNumberSchema, // Tolerance for path simplification
  noiseReduction: AnimatableNumberSchema, // Ignore small features
  // Source
  sourceLayerId: EntityIdSchema.optional(), // Layer to trace
  sourceFrame: z.number().int().nonnegative().optional(), // Frame to trace (for video)
});

export type TraceOperator = z.infer<typeof TraceOperatorSchema>;

export const IllustratorOperatorSchema = z.discriminatedUnion("type", [
  SimplifyPathOperatorSchema,
  SmoothPathOperatorSchema,
  ExtrudeOperatorSchema,
  TraceOperatorSchema,
]);

export type IllustratorOperator = z.infer<typeof IllustratorOperatorSchema>;

// ============================================================================
// NON-GROUP SHAPE CONTENT (for use inside ShapeGroup.contents)
// ============================================================================

// Non-recursive shape content (groups cannot contain other groups)
// This breaks the circular dependency while allowing groups at root level
export const NonGroupShapeContentSchema = z.discriminatedUnion("type", [
  // Generators
  RectangleShapeSchema,
  EllipseShapeSchema,
  PolygonShapeSchema,
  StarShapeSchema,
  PathShapeSchema,
  // Modifiers
  FillShapeSchema,
  StrokeShapeSchema,
  GradientFillShapeSchema,
  GradientStrokeShapeSchema,
  // Operators
  TrimPathsOperatorSchema,
  MergePathsOperatorSchema,
  OffsetPathsOperatorSchema,
  PuckerBloatOperatorSchema,
  WigglePathsOperatorSchema,
  ZigZagOperatorSchema,
  TwistOperatorSchema,
  RoundedCornersOperatorSchema,
  // Transform & Repeater
  ShapeTransformSchema,
  RepeaterOperatorSchema,
  // Illustrator operators
  SimplifyPathOperatorSchema,
  SmoothPathOperatorSchema,
  ExtrudeOperatorSchema,
  TraceOperatorSchema,
]);

export type NonGroupShapeContent = z.infer<typeof NonGroupShapeContentSchema>;

// ============================================================================
// SHAPE GROUP (non-recursive - groups cannot contain other groups)
// ============================================================================

export const ShapeGroupSchema = z.object({
  type: z.literal("group"),
  name: z.string(),
  // Non-recursive: groups cannot contain other groups (breaks circular dependency)
  contents: z.array(NonGroupShapeContentSchema),
  transform: ShapeTransformSchema,
  blendMode: z.string(),
});

export type ShapeGroup = z.infer<typeof ShapeGroupSchema>;

// ============================================================================
// FULL SHAPE CONTENT (includes groups for root-level ShapeLayerData.contents)
// ============================================================================

// Full shape content union (includes groups for root level)
export const ShapeContentSchema = z.union([
  NonGroupShapeContentSchema,
  ShapeGroupSchema,
]);

export type ShapeContent = z.infer<typeof ShapeContentSchema>;

// ============================================================================
// SHAPE LAYER DATA
// ============================================================================

export const ShapeLayerDataSchema = z.object({
  /** Root contents (groups, shapes, operators) */
  contents: z.array(ShapeContentSchema),
  /** Layer-level blend mode */
  blendMode: z.string(),
  /** Quality settings */
  quality: z.enum(["draft", "normal", "high"]),
  /** Enable GPU acceleration if available */
  gpuAccelerated: z.boolean(),
});

export type ShapeLayerData = z.infer<typeof ShapeLayerDataSchema>;
