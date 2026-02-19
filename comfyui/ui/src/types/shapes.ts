/**
 * Shape Layer Types & Interfaces
 *
 * Comprehensive shape layer system with industry-standard vector features.
 * Supports path operations, shape generators, modifiers, and advanced operators.
 */

import { createAnimatableProperty } from "./animation";
import type { AnimatableProperty } from "./project";

// ============================================================================
// BASE TYPES
// ============================================================================

/** 2D Point */
export interface Point2D {
  x: number;
  y: number;
}

/** Bezier control point with handles */
export interface BezierVertex {
  point: Point2D;
  inHandle: Point2D; // Relative to point
  outHandle: Point2D; // Relative to point
}

/** A bezier path (can be open or closed) */
export interface BezierPath {
  vertices: BezierVertex[];
  closed: boolean;
}

/** Color with alpha */
export interface ShapeColor {
  r: number; // 0-255
  g: number;
  b: number;
  a: number; // 0-1
}

/** Gradient stop */
export interface GradientStop {
  position: number; // 0-1
  color: ShapeColor;
}

/** Gradient definition */
export interface GradientDef {
  type: "linear" | "radial";
  stops: GradientStop[];
  startPoint: Point2D; // Normalized 0-1
  endPoint: Point2D; // For linear: end point, for radial: edge point
  highlightLength?: number; // Radial only: 0-100
  highlightAngle?: number; // Radial only: degrees
}

// ============================================================================
// SHAPE CONTENT TYPES (What goes inside a shape layer)
// ============================================================================

export type ShapeContentType =
  // Generators
  | "rectangle"
  | "ellipse"
  | "polygon"
  | "star"
  | "path"
  // Modifiers
  | "fill"
  | "stroke"
  | "gradientFill"
  | "gradientStroke"
  // Operators
  | "trimPaths"
  | "mergePaths"
  | "offsetPaths"
  | "puckerBloat"
  | "wigglePaths"
  | "zigZag"
  | "twist"
  | "roundedCorners"
  | "repeater"
  | "transform"
  // Group
  | "group";

// ============================================================================
// SHAPE GENERATORS
// ============================================================================

export interface RectangleShape {
  type: "rectangle";
  name: string;
  position: AnimatableProperty<Point2D>;
  size: AnimatableProperty<Point2D>;
  roundness: AnimatableProperty<number>; // Corner radius in pixels
  direction: 1 | -1; // 1 = clockwise, -1 = counter-clockwise
}

export interface EllipseShape {
  type: "ellipse";
  name: string;
  position: AnimatableProperty<Point2D>;
  size: AnimatableProperty<Point2D>;
  direction: 1 | -1;
}

export interface PolygonShape {
  type: "polygon";
  name: string;
  position: AnimatableProperty<Point2D>;
  points: AnimatableProperty<number>; // Number of sides (3+)
  outerRadius: AnimatableProperty<number>;
  outerRoundness: AnimatableProperty<number>; // 0-100%
  rotation: AnimatableProperty<number>; // Degrees
  direction: 1 | -1;
}

export interface StarShape {
  type: "star";
  name: string;
  position: AnimatableProperty<Point2D>;
  points: AnimatableProperty<number>; // Number of points (3+)
  outerRadius: AnimatableProperty<number>;
  innerRadius: AnimatableProperty<number>;
  outerRoundness: AnimatableProperty<number>; // 0-100%
  innerRoundness: AnimatableProperty<number>; // 0-100%
  rotation: AnimatableProperty<number>;
  direction: 1 | -1;
}

export interface PathShape {
  type: "path";
  name: string;
  path: AnimatableProperty<BezierPath>;
  direction: 1 | -1;
}

export type ShapeGenerator =
  | RectangleShape
  | EllipseShape
  | PolygonShape
  | StarShape
  | PathShape;

// ============================================================================
// SHAPE MODIFIERS (Fill/Stroke)
// ============================================================================

export type FillRule = "nonzero" | "evenodd";
export type LineCap = "butt" | "round" | "square";
export type LineJoin = "miter" | "round" | "bevel";

export interface FillShape {
  type: "fill";
  name: string;
  color: AnimatableProperty<ShapeColor>;
  opacity: AnimatableProperty<number>; // 0-100
  fillRule: FillRule;
  blendMode: string;
}

export interface StrokeShape {
  type: "stroke";
  name: string;
  color: AnimatableProperty<ShapeColor>;
  opacity: AnimatableProperty<number>; // 0-100
  width: AnimatableProperty<number>;
  lineCap: LineCap;
  lineJoin: LineJoin;
  miterLimit: number;
  // Dashes
  dashPattern: AnimatableProperty<number[]>; // [dash, gap, dash, gap, ...]
  dashOffset: AnimatableProperty<number>;
  blendMode: string;
  // Taper (stroke width variation)
  taperEnabled: boolean;
  taperStartLength: AnimatableProperty<number>; // 0-100%
  taperEndLength: AnimatableProperty<number>;
  taperStartWidth: AnimatableProperty<number>; // 0-100%
  taperEndWidth: AnimatableProperty<number>;
  taperStartEase: AnimatableProperty<number>; // 0-100%
  taperEndEase: AnimatableProperty<number>;
}

export interface GradientFillShape {
  type: "gradientFill";
  name: string;
  gradient: AnimatableProperty<GradientDef>;
  opacity: AnimatableProperty<number>;
  fillRule: FillRule;
  blendMode: string;
}

export interface GradientStrokeShape {
  type: "gradientStroke";
  name: string;
  gradient: AnimatableProperty<GradientDef>;
  opacity: AnimatableProperty<number>;
  width: AnimatableProperty<number>;
  lineCap: LineCap;
  lineJoin: LineJoin;
  miterLimit: number;
  dashPattern: AnimatableProperty<number[]>;
  dashOffset: AnimatableProperty<number>;
  blendMode: string;
}

export type ShapeModifier =
  | FillShape
  | StrokeShape
  | GradientFillShape
  | GradientStrokeShape;

// ============================================================================
// PATH OPERATORS
// ============================================================================

export type TrimMode = "simultaneously" | "individually";

export interface TrimPathsOperator {
  type: "trimPaths";
  name: string;
  start: AnimatableProperty<number>; // 0-100%
  end: AnimatableProperty<number>; // 0-100%
  offset: AnimatableProperty<number>; // Degrees (-360 to 360)
  mode: TrimMode;
}

export type MergeMode =
  | "add" // Union
  | "subtract" // Minus Front
  | "intersect" // Intersection
  | "exclude" // Exclude Intersection
  | "minusFront" // Same as subtract
  | "minusBack"; // Minus Back (Illustrator)

export interface MergePathsOperator {
  type: "mergePaths";
  name: string;
  mode: MergeMode;
}

export type OffsetJoin = "miter" | "round" | "bevel";

export interface OffsetPathsOperator {
  type: "offsetPaths";
  name: string;
  amount: AnimatableProperty<number>; // Positive = expand, negative = contract
  lineJoin: OffsetJoin;
  miterLimit: AnimatableProperty<number>;
  copies: AnimatableProperty<number>; // AE: can create multiple offset copies
  copyOffset: AnimatableProperty<number>; // Distance between copies
}

export interface PuckerBloatOperator {
  type: "puckerBloat";
  name: string;
  amount: AnimatableProperty<number>; // -100 (pucker) to 100 (bloat)
}

export type WigglePointType = "corner" | "smooth";

export interface WigglePathsOperator {
  type: "wigglePaths";
  name: string;
  size: AnimatableProperty<number>; // Wiggle magnitude
  detail: AnimatableProperty<number>; // Segments per curve (1-10)
  points: WigglePointType;
  correlation: AnimatableProperty<number>; // 0-100% how linked adjacent points are
  temporalPhase: AnimatableProperty<number>; // Animation offset
  spatialPhase: AnimatableProperty<number>; // Spatial offset
  randomSeed: number;
}

export type ZigZagPointType = "corner" | "smooth";

export interface ZigZagOperator {
  type: "zigZag";
  name: string;
  size: AnimatableProperty<number>; // Peak height
  ridgesPerSegment: AnimatableProperty<number>; // Zigzags per path segment
  points: ZigZagPointType;
}

export interface TwistOperator {
  type: "twist";
  name: string;
  angle: AnimatableProperty<number>; // Total twist in degrees
  center: AnimatableProperty<Point2D>;
}

export interface RoundedCornersOperator {
  type: "roundedCorners";
  name: string;
  radius: AnimatableProperty<number>;
}

export type PathOperator =
  | TrimPathsOperator
  | MergePathsOperator
  | OffsetPathsOperator
  | PuckerBloatOperator
  | WigglePathsOperator
  | ZigZagOperator
  | TwistOperator
  | RoundedCornersOperator;

// ============================================================================
// TRANSFORM & REPEATER
// ============================================================================

export interface ShapeTransform {
  type: "transform";
  name: string;
  anchorPoint: AnimatableProperty<Point2D>;
  position: AnimatableProperty<Point2D>;
  scale: AnimatableProperty<Point2D>; // Percentage (100 = 100%)
  rotation: AnimatableProperty<number>; // Degrees
  skew: AnimatableProperty<number>; // Degrees
  skewAxis: AnimatableProperty<number>; // Degrees
  opacity: AnimatableProperty<number>; // 0-100%
}

export type RepeaterComposite = "above" | "below";

export interface RepeaterOperator {
  type: "repeater";
  name: string;
  copies: AnimatableProperty<number>;
  offset: AnimatableProperty<number>; // Offset from original (degrees for radial)
  composite: RepeaterComposite; // Stack order
  // Transform per copy
  transform: {
    anchorPoint: AnimatableProperty<Point2D>;
    position: AnimatableProperty<Point2D>;
    scale: AnimatableProperty<Point2D>; // End scale (100 = no change)
    rotation: AnimatableProperty<number>; // Rotation per copy
    startOpacity: AnimatableProperty<number>; // Opacity of first copy
    endOpacity: AnimatableProperty<number>; // Opacity of last copy
  };
}

// ============================================================================
// SHAPE GROUP
// ============================================================================

export interface ShapeGroup {
  type: "group";
  name: string;
  // Non-recursive: groups cannot contain other groups (breaks circular dependency)
  contents: NonGroupShapeContent[];
  transform: ShapeTransform;
  blendMode: string;
}

// ============================================================================
// ILLUSTRATOR-SPECIFIC OPERATORS
// ============================================================================

export interface SimplifyPathOperator {
  type: "simplifyPath";
  name: string;
  tolerance: AnimatableProperty<number>; // Curve precision (0-100)
  angleTolerance: AnimatableProperty<number>; // Corner angle threshold
  straightLines: boolean; // Convert to straight segments
}

export interface SmoothPathOperator {
  type: "smoothPath";
  name: string;
  amount: AnimatableProperty<number>; // 0-100%
}

export interface ExtrudeOperator {
  type: "extrude";
  name: string;
  depth: AnimatableProperty<number>; // Extrusion depth
  bevelDepth: AnimatableProperty<number>; // Bevel size
  bevelSegments: number; // Smoothness of bevel
  capType: "flat" | "round" | "bevel";
  material: {
    frontColor: AnimatableProperty<ShapeColor>;
    sideColor: AnimatableProperty<ShapeColor>;
    bevelColor: AnimatableProperty<ShapeColor>;
  };
}

/** Image trace / vectorization settings */
export interface TraceOperator {
  type: "trace";
  name: string;
  mode: "blackAndWhite" | "grayscale" | "color";
  threshold: AnimatableProperty<number>; // B&W threshold (0-255)
  colors: number; // Max colors for color mode
  cornerAngle: number; // Corner detection threshold
  pathFitting: AnimatableProperty<number>; // Tolerance for path simplification
  noiseReduction: AnimatableProperty<number>; // Ignore small features
  // Source
  sourceLayerId?: string; // Layer to trace
  sourceFrame?: number; // Frame to trace (for video)
}

export type IllustratorOperator =
  | SimplifyPathOperator
  | SmoothPathOperator
  | ExtrudeOperator
  | TraceOperator;

// ============================================================================
// COMBINED SHAPE CONTENT TYPE
// ============================================================================

// Non-group shape content (used inside ShapeGroup.contents to avoid circular dependency)
export type NonGroupShapeContent =
  | ShapeGenerator
  | ShapeModifier
  | PathOperator
  | ShapeTransform
  | RepeaterOperator
  | IllustratorOperator;

// Full shape content (includes groups for root-level ShapeLayerData.contents)
export type ShapeContent = NonGroupShapeContent | ShapeGroup;

// ============================================================================
// SHAPE LAYER DATA
// ============================================================================

export interface ShapeLayerData {
  /** Root contents (groups, shapes, operators) */
  contents: ShapeContent[];
  /** Layer-level blend mode */
  blendMode: string;
  /** Quality settings */
  quality: "draft" | "normal" | "high";
  /** Enable GPU acceleration if available */
  gpuAccelerated: boolean;
}

// ============================================================================
// DEFAULT FACTORIES
// ============================================================================

let shapePropertyIdCounter = 0;

function generateShapePropertyId(): string {
  return `shape_prop_${++shapePropertyIdCounter}_${Math.random().toString(36).slice(2, 7)}`;
}

export function createDefaultAnimatablePoint(
  name: string = "Point",
): AnimatableProperty<Point2D> {
  return {
    id: generateShapePropertyId(),
    name,
    type: "position",
    value: { x: 0, y: 0 },
    animated: false,
    keyframes: [],
  };
}

export function createDefaultAnimatableNumber(
  value: number = 0,
  name: string = "Value",
): AnimatableProperty<number> {
  return {
    id: generateShapePropertyId(),
    name,
    type: "number",
    value,
    animated: false,
    keyframes: [],
  };
}

export function createDefaultAnimatableColor(
  r = 255,
  g = 255,
  b = 255,
  a = 1,
  name: string = "Color",
): AnimatableProperty<ShapeColor> {
  return {
    id: generateShapePropertyId(),
    name,
    type: "color",
    value: { r, g, b, a },
    animated: false,
    keyframes: [],
  };
}

export function createDefaultAnimatablePath(
  name: string = "Path",
): AnimatableProperty<BezierPath> {
  return {
    id: generateShapePropertyId(),
    name,
    type: "position", // Using 'position' as closest match for path type
    value: { vertices: [], closed: false },
    animated: false,
    keyframes: [],
  };
}

export function createDefaultAnimatableNumberArray(
  value: number[] = [],
  name: string = "Array",
): AnimatableProperty<number[]> {
  return {
    id: generateShapePropertyId(),
    name,
    type: "number", // Closest match
    value,
    animated: false,
    keyframes: [],
  };
}

export function createDefaultShapeTransform(): ShapeTransform {
  const scalePoint = createDefaultAnimatablePoint("Scale");
  scalePoint.value = { x: 100, y: 100 };
  return {
    type: "transform",
    name: "Transform",
    anchorPoint: createDefaultAnimatablePoint("Anchor Point"),
    position: createDefaultAnimatablePoint("Position"),
    scale: scalePoint,
    rotation: createDefaultAnimatableNumber(0, "Rotation"),
    skew: createDefaultAnimatableNumber(0, "Skew"),
    skewAxis: createDefaultAnimatableNumber(0, "Skew Axis"),
    opacity: createDefaultAnimatableNumber(100, "Opacity"),
  };
}

export function createDefaultRectangle(): RectangleShape {
  const size = createDefaultAnimatablePoint("Size");
  size.value = { x: 100, y: 100 };
  return {
    type: "rectangle",
    name: "Rectangle",
    position: createDefaultAnimatablePoint("Position"),
    size,
    roundness: createDefaultAnimatableNumber(0, "Roundness"),
    direction: 1,
  };
}

export function createDefaultEllipse(): EllipseShape {
  const size = createDefaultAnimatablePoint("Size");
  size.value = { x: 100, y: 100 };
  return {
    type: "ellipse",
    name: "Ellipse",
    position: createDefaultAnimatablePoint("Position"),
    size,
    direction: 1,
  };
}

export function createDefaultPolygon(): PolygonShape {
  return {
    type: "polygon",
    name: "Polygon",
    position: createDefaultAnimatablePoint("Position"),
    points: createDefaultAnimatableNumber(6, "Points"),
    outerRadius: createDefaultAnimatableNumber(50, "Outer Radius"),
    outerRoundness: createDefaultAnimatableNumber(0, "Outer Roundness"),
    rotation: createDefaultAnimatableNumber(0, "Rotation"),
    direction: 1,
  };
}

export function createDefaultStar(): StarShape {
  return {
    type: "star",
    name: "Star",
    position: createDefaultAnimatablePoint("Position"),
    points: createDefaultAnimatableNumber(5, "Points"),
    outerRadius: createDefaultAnimatableNumber(50, "Outer Radius"),
    innerRadius: createDefaultAnimatableNumber(25, "Inner Radius"),
    outerRoundness: createDefaultAnimatableNumber(0, "Outer Roundness"),
    innerRoundness: createDefaultAnimatableNumber(0, "Inner Roundness"),
    rotation: createDefaultAnimatableNumber(0, "Rotation"),
    direction: 1,
  };
}

export function createDefaultPath(): PathShape {
  return {
    type: "path",
    name: "Path",
    path: createDefaultAnimatablePath("Path"),
    direction: 1,
  };
}

export function createDefaultFill(): FillShape {
  return {
    type: "fill",
    name: "Fill",
    color: createDefaultAnimatableColor(255, 255, 255, 1, "Color"),
    opacity: createDefaultAnimatableNumber(100, "Opacity"),
    fillRule: "nonzero",
    blendMode: "normal",
  };
}

export function createDefaultStroke(): StrokeShape {
  return {
    type: "stroke",
    name: "Stroke",
    color: createDefaultAnimatableColor(255, 255, 255, 1, "Color"),
    opacity: createDefaultAnimatableNumber(100, "Opacity"),
    width: createDefaultAnimatableNumber(2, "Stroke Width"),
    lineCap: "round",
    lineJoin: "round",
    miterLimit: 4,
    dashPattern: createDefaultAnimatableNumberArray([], "Dash Pattern"),
    dashOffset: createDefaultAnimatableNumber(0, "Dash Offset"),
    blendMode: "normal",
    taperEnabled: false,
    taperStartLength: createDefaultAnimatableNumber(0, "Taper Start Length"),
    taperEndLength: createDefaultAnimatableNumber(0, "Taper End Length"),
    taperStartWidth: createDefaultAnimatableNumber(100, "Taper Start Width"),
    taperEndWidth: createDefaultAnimatableNumber(100, "Taper End Width"),
    taperStartEase: createDefaultAnimatableNumber(0, "Taper Start Ease"),
    taperEndEase: createDefaultAnimatableNumber(0, "Taper End Ease"),
  };
}

export function createDefaultTrimPaths(): TrimPathsOperator {
  return {
    type: "trimPaths",
    name: "Trim Paths",
    start: createDefaultAnimatableNumber(0),
    end: createDefaultAnimatableNumber(100),
    offset: createDefaultAnimatableNumber(0),
    mode: "simultaneously",
  };
}

export function createDefaultMergePaths(): MergePathsOperator {
  return {
    type: "mergePaths",
    name: "Merge Paths",
    mode: "add",
  };
}

export function createDefaultOffsetPaths(): OffsetPathsOperator {
  return {
    type: "offsetPaths",
    name: "Offset Paths",
    amount: createDefaultAnimatableNumber(0),
    lineJoin: "miter",
    miterLimit: createDefaultAnimatableNumber(4),
    copies: createDefaultAnimatableNumber(1),
    copyOffset: createDefaultAnimatableNumber(0),
  };
}

export function createDefaultPuckerBloat(): PuckerBloatOperator {
  return {
    type: "puckerBloat",
    name: "Pucker & Bloat",
    amount: createDefaultAnimatableNumber(0),
  };
}

export function createDefaultWigglePaths(): WigglePathsOperator {
  return {
    type: "wigglePaths",
    name: "Wiggle Paths",
    size: createDefaultAnimatableNumber(10),
    detail: createDefaultAnimatableNumber(3),
    points: "smooth",
    correlation: createDefaultAnimatableNumber(50),
    temporalPhase: createDefaultAnimatableNumber(0),
    spatialPhase: createDefaultAnimatableNumber(0),
    randomSeed: 12345,
  };
}

export function createDefaultZigZag(): ZigZagOperator {
  return {
    type: "zigZag",
    name: "Zig Zag",
    size: createDefaultAnimatableNumber(10),
    ridgesPerSegment: createDefaultAnimatableNumber(5),
    points: "smooth",
  };
}

export function createDefaultTwist(): TwistOperator {
  return {
    type: "twist",
    name: "Twist",
    angle: createDefaultAnimatableNumber(0, "Angle"),
    center: createDefaultAnimatablePoint("Center"),
  };
}

export function createDefaultRoundedCorners(): RoundedCornersOperator {
  return {
    type: "roundedCorners",
    name: "Rounded Corners",
    radius: createDefaultAnimatableNumber(10),
  };
}

export function createDefaultRepeater(): RepeaterOperator {
  const position = createDefaultAnimatablePoint("Position");
  position.value = { x: 100, y: 0 };
  const scale = createDefaultAnimatablePoint("Scale");
  scale.value = { x: 100, y: 100 };
  return {
    type: "repeater",
    name: "Repeater",
    copies: createDefaultAnimatableNumber(3, "Copies"),
    offset: createDefaultAnimatableNumber(0, "Offset"),
    composite: "below",
    transform: {
      anchorPoint: createDefaultAnimatablePoint("Anchor Point"),
      position,
      scale,
      rotation: createDefaultAnimatableNumber(0, "Rotation"),
      startOpacity: createDefaultAnimatableNumber(100, "Start Opacity"),
      endOpacity: createDefaultAnimatableNumber(100, "End Opacity"),
    },
  };
}

export function createDefaultGroup(): ShapeGroup {
  return {
    type: "group",
    name: "Group",
    contents: [],
    transform: createDefaultShapeTransform(),
    blendMode: "normal",
  };
}

export function createDefaultExtrude(): ExtrudeOperator {
  return {
    type: "extrude",
    name: "Extrude",
    depth: createDefaultAnimatableNumber(50),
    bevelDepth: createDefaultAnimatableNumber(5),
    bevelSegments: 3,
    capType: "flat",
    material: {
      frontColor: createDefaultAnimatableColor(255, 255, 255, 1),
      sideColor: createDefaultAnimatableColor(200, 200, 200, 1),
      bevelColor: createDefaultAnimatableColor(180, 180, 180, 1),
    },
  };
}

export function createDefaultTrace(): TraceOperator {
  return {
    type: "trace",
    name: "Image Trace",
    mode: "blackAndWhite",
    threshold: createDefaultAnimatableNumber(128),
    colors: 16,
    cornerAngle: 20,
    pathFitting: createDefaultAnimatableNumber(2),
    noiseReduction: createDefaultAnimatableNumber(25),
  };
}

export function createDefaultSimplifyPath(): SimplifyPathOperator {
  return {
    type: "simplifyPath",
    name: "Simplify Path",
    tolerance: createDefaultAnimatableNumber(50),
    angleTolerance: createDefaultAnimatableNumber(10),
    straightLines: false,
  };
}

export function createDefaultSmoothPath(): SmoothPathOperator {
  return {
    type: "smoothPath",
    name: "Smooth Path",
    amount: createDefaultAnimatableNumber(50),
  };
}

export function createDefaultGradientFill(): GradientFillShape {
  const gradientValue: GradientDef = {
    type: "linear",
    stops: [
      { position: 0, color: { r: 0, g: 0, b: 0, a: 1 } },
      { position: 1, color: { r: 255, g: 255, b: 255, a: 1 } },
    ],
    startPoint: { x: 0, y: 0.5 },
    endPoint: { x: 1, y: 0.5 },
  };

  return {
    type: "gradientFill",
    name: "Gradient Fill",
    gradient: createAnimatableProperty("Gradient", gradientValue, "enum"),
    opacity: createDefaultAnimatableNumber(100, "Opacity"),
    fillRule: "nonzero",
    blendMode: "normal",
  };
}

export function createDefaultGradientStroke(): GradientStrokeShape {
  const gradientValue: GradientDef = {
    type: "linear",
    stops: [
      { position: 0, color: { r: 255, g: 255, b: 255, a: 1 } },
      { position: 1, color: { r: 0, g: 0, b: 0, a: 1 } },
    ],
    startPoint: { x: 0, y: 0.5 },
    endPoint: { x: 1, y: 0.5 },
  };

  return {
    type: "gradientStroke",
    name: "Gradient Stroke",
    gradient: createAnimatableProperty("Gradient", gradientValue, "enum"),
    opacity: createDefaultAnimatableNumber(100, "Opacity"),
    width: createDefaultAnimatableNumber(2, "Width"),
    lineCap: "round",
    lineJoin: "round",
    miterLimit: 4,
    dashPattern: createDefaultAnimatableNumberArray([], "Dash Pattern"),
    dashOffset: createDefaultAnimatableNumber(0, "Dash Offset"),
    blendMode: "normal",
  };
}

export function createDefaultShapeLayerData(): ShapeLayerData {
  return {
    contents: [],
    blendMode: "normal",
    quality: "normal",
    gpuAccelerated: true,
  };
}
