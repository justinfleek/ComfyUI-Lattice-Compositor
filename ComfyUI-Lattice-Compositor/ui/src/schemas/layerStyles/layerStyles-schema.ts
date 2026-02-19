/**
 * Layer Styles Schemas
 *
 * Zod schemas for layer styles (drop shadow, glow, bevel, etc.).
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { finiteNumber, normalized01, BlendModeSchema } from "../layers/primitives-schema";
import { AnimatablePropertySchema } from "../layers/animation-schema";
import {
  boundedArray,
  MAX_NAME_LENGTH,
} from "../shared-validation";

// ============================================================================
// RGBA Color
// ============================================================================

export const RGBASchema = z.object({
  r: z.number().int().min(0).max(255),
  g: z.number().int().min(0).max(255),
  b: z.number().int().min(0).max(255),
  a: normalized01,
}).strict();

export type RGBA = z.infer<typeof RGBASchema>;

// ============================================================================
// Gradient
// ============================================================================

export const GradientStopSchema = z.object({
  position: normalized01,
  color: RGBASchema,
}).strict();

export type GradientStop = z.infer<typeof GradientStopSchema>;

export const GradientDefSchema = z.object({
  type: z.enum(["linear", "radial"]),
  stops: boundedArray(GradientStopSchema, 100).min(2), // Min 2 stops for gradient
  angle: finiteNumber.optional(),
}).strict().refine(
  (data) => {
    // Stops should be sorted by position
    const positions = data.stops.map((s) => s.position);
    for (let i = 1; i < positions.length; i++) {
      if (positions[i] < positions[i - 1]) {
        return false;
      }
    }
    return true;
  },
  { message: "Gradient stops must be sorted by position", path: ["stops"] }
);

export type GradientDef = z.infer<typeof GradientDefSchema>;

// ============================================================================
// Contour Curve
// ============================================================================

export const ContourCurveSchema = z.object({
  points: boundedArray(
    z.object({
      x: normalized01,
      y: normalized01,
    }).strict(),
    1000 // Max 1000 points
  ).min(2), // Min 2 points for curve
}).strict();

export type ContourCurve = z.infer<typeof ContourCurveSchema>;

// ============================================================================
// Base Layer Style
// ============================================================================

const BaseLayerStyleSchema = z.object({
  enabled: z.boolean(),
  blendMode: BlendModeSchema,
  opacity: AnimatablePropertySchema,
}).strict();

// ============================================================================
// Drop Shadow
// ============================================================================

export const DropShadowStyleSchema = BaseLayerStyleSchema.extend({
  color: AnimatablePropertySchema,
  angle: AnimatablePropertySchema,
  useGlobalLight: z.boolean(),
  distance: AnimatablePropertySchema,
  spread: AnimatablePropertySchema,
  size: AnimatablePropertySchema,
  noise: AnimatablePropertySchema,
  contour: ContourCurveSchema.optional(),
  antiAliased: z.boolean().optional(),
  layerKnocksOut: z.boolean().optional(),
}).strict();

export type DropShadowStyle = z.infer<typeof DropShadowStyleSchema>;

// ============================================================================
// Inner Shadow
// ============================================================================

export const InnerShadowStyleSchema = BaseLayerStyleSchema.extend({
  color: AnimatablePropertySchema,
  angle: AnimatablePropertySchema,
  useGlobalLight: z.boolean(),
  distance: AnimatablePropertySchema,
  choke: AnimatablePropertySchema,
  size: AnimatablePropertySchema,
  noise: AnimatablePropertySchema,
  contour: ContourCurveSchema.optional(),
  antiAliased: z.boolean().optional(),
}).strict();

export type InnerShadowStyle = z.infer<typeof InnerShadowStyleSchema>;

// ============================================================================
// Outer Glow
// ============================================================================

export const GlowTechniqueSchema = z.enum(["softer", "precise"]);

export type GlowTechnique = z.infer<typeof GlowTechniqueSchema>;

export const OuterGlowStyleSchema = BaseLayerStyleSchema.extend({
  color: AnimatablePropertySchema,
  gradient: GradientDefSchema.optional(),
  useGradient: z.boolean().optional(),
  technique: GlowTechniqueSchema,
  spread: AnimatablePropertySchema,
  size: AnimatablePropertySchema,
  range: AnimatablePropertySchema,
  jitter: AnimatablePropertySchema,
  noise: AnimatablePropertySchema,
  contour: ContourCurveSchema.optional(),
  antiAliased: z.boolean().optional(),
}).strict();

export type OuterGlowStyle = z.infer<typeof OuterGlowStyleSchema>;

// ============================================================================
// Inner Glow
// ============================================================================

export const InnerGlowSourceSchema = z.enum(["center", "edge"]);

export type InnerGlowSource = z.infer<typeof InnerGlowSourceSchema>;

export const InnerGlowStyleSchema = BaseLayerStyleSchema.extend({
  color: AnimatablePropertySchema,
  gradient: GradientDefSchema.optional(),
  useGradient: z.boolean().optional(),
  technique: GlowTechniqueSchema,
  source: InnerGlowSourceSchema,
  choke: AnimatablePropertySchema,
  size: AnimatablePropertySchema,
  range: AnimatablePropertySchema,
  jitter: AnimatablePropertySchema,
  noise: AnimatablePropertySchema,
  contour: ContourCurveSchema.optional(),
  antiAliased: z.boolean().optional(),
}).strict();

export type InnerGlowStyle = z.infer<typeof InnerGlowStyleSchema>;

// ============================================================================
// Bevel and Emboss
// ============================================================================

export const BevelStyleSchema = z.enum([
  "outer-bevel",
  "inner-bevel",
  "emboss",
  "pillow-emboss",
  "stroke-emboss",
]);

export type BevelStyle = z.infer<typeof BevelStyleSchema>;

export const BevelTechniqueSchema = z.enum([
  "smooth",
  "chisel-hard",
  "chisel-soft",
]);

export type BevelTechnique = z.infer<typeof BevelTechniqueSchema>;

export const BevelDirectionSchema = z.enum(["up", "down"]);

export type BevelDirection = z.infer<typeof BevelDirectionSchema>;

export const BevelEmbossStyleSchema = BaseLayerStyleSchema.extend({
  style: BevelStyleSchema,
  technique: BevelTechniqueSchema,
  depth: AnimatablePropertySchema,
  direction: BevelDirectionSchema,
  size: AnimatablePropertySchema,
  soften: AnimatablePropertySchema,
  angle: AnimatablePropertySchema,
  useGlobalLight: z.boolean(),
  altitude: AnimatablePropertySchema,
  glossContour: ContourCurveSchema.optional(),
  glossAntiAliased: z.boolean().optional(),
  highlightMode: BlendModeSchema,
  highlightColor: AnimatablePropertySchema,
  highlightOpacity: AnimatablePropertySchema,
  shadowMode: BlendModeSchema,
  shadowColor: AnimatablePropertySchema,
  shadowOpacity: AnimatablePropertySchema,
  contourEnabled: z.boolean().optional(),
  contour: ContourCurveSchema.optional(),
  contourAntiAliased: z.boolean().optional(),
  contourRange: AnimatablePropertySchema.optional(),
  textureEnabled: z.boolean().optional(),
  texturePattern: z.string().max(MAX_NAME_LENGTH).optional(),
  textureScale: AnimatablePropertySchema.optional(),
  textureDepth: AnimatablePropertySchema.optional(),
  textureInvert: z.boolean().optional(),
  textureLinkWithLayer: z.boolean().optional(),
}).strict();

export type BevelEmbossStyle = z.infer<typeof BevelEmbossStyleSchema>;

// ============================================================================
// Satin
// ============================================================================

export const SatinStyleSchema = BaseLayerStyleSchema.extend({
  color: AnimatablePropertySchema,
  angle: AnimatablePropertySchema,
  distance: AnimatablePropertySchema,
  size: AnimatablePropertySchema,
  contour: ContourCurveSchema.optional(),
  antiAliased: z.boolean().optional(),
  invert: z.boolean(),
}).strict();

export type SatinStyle = z.infer<typeof SatinStyleSchema>;

// ============================================================================
// Color Overlay
// ============================================================================

export const ColorOverlayStyleSchema = BaseLayerStyleSchema.extend({
  color: AnimatablePropertySchema,
}).strict();

export type ColorOverlayStyle = z.infer<typeof ColorOverlayStyleSchema>;

// ============================================================================
// Gradient Overlay
// ============================================================================

export const GradientOverlayTypeSchema = z.enum([
  "linear",
  "radial",
  "angle",
  "reflected",
  "diamond",
]);

export type GradientOverlayType = z.infer<typeof GradientOverlayTypeSchema>;

export const GradientOverlayStyleSchema = BaseLayerStyleSchema.extend({
  gradient: AnimatablePropertySchema,
  style: GradientOverlayTypeSchema,
  angle: AnimatablePropertySchema,
  scale: AnimatablePropertySchema,
  alignWithLayer: z.boolean(),
  reverse: z.boolean(),
  offset: AnimatablePropertySchema,
  dither: z.boolean().optional(),
}).strict();

export type GradientOverlayStyle = z.infer<typeof GradientOverlayStyleSchema>;

// ============================================================================
// Pattern Overlay
// ============================================================================

export const PatternOverlayStyleSchema = BaseLayerStyleSchema.extend({
  pattern: z.string().max(MAX_NAME_LENGTH).trim(),
  scale: AnimatablePropertySchema,
  angle: AnimatablePropertySchema,
  linkWithLayer: z.boolean(),
  snapToOrigin: z.boolean(),
  offset: AnimatablePropertySchema,
}).strict();

export type PatternOverlayStyle = z.infer<typeof PatternOverlayStyleSchema>;

// ============================================================================
// Stroke
// ============================================================================

export const StrokePositionSchema = z.enum(["outside", "inside", "center"]);

export type StrokePosition = z.infer<typeof StrokePositionSchema>;

export const StrokeFillTypeSchema = z.enum(["color", "gradient", "pattern"]);

export type StrokeFillType = z.infer<typeof StrokeFillTypeSchema>;

export const StrokeStyleSchema = BaseLayerStyleSchema.extend({
  color: AnimatablePropertySchema,
  gradient: GradientDefSchema.optional(),
  pattern: z.string().max(MAX_NAME_LENGTH).optional(),
  fillType: StrokeFillTypeSchema,
  size: AnimatablePropertySchema,
  position: StrokePositionSchema,
  gradientAngle: AnimatablePropertySchema.optional(),
  gradientScale: AnimatablePropertySchema.optional(),
  patternScale: AnimatablePropertySchema.optional(),
  patternLinkWithLayer: z.boolean().optional(),
}).strict().refine(
  (data) => {
    // If fillType is "gradient", gradient should be present
    if (data.fillType === "gradient" && !data.gradient) {
      return false;
    }
    // If fillType is "pattern", pattern should be present
    if (data.fillType === "pattern" && !data.pattern) {
      return false;
    }
    return true;
  },
  { message: "gradient/pattern required when fillType matches", path: ["fillType"] }
);

export type StrokeStyle = z.infer<typeof StrokeStyleSchema>;

// ============================================================================
// Style Blending Options
// ============================================================================

export const ChannelBlendRangeSchema = z.object({
  inputBlack: z.number().int().min(0).max(255),
  inputWhite: z.number().int().min(0).max(255),
  outputBlack: z.number().int().min(0).max(255),
  outputWhite: z.number().int().min(0).max(255),
}).strict().refine(
  (data) => data.inputBlack < data.inputWhite,
  { message: "inputBlack must be < inputWhite", path: ["inputBlack"] }
).refine(
  (data) => data.outputBlack < data.outputWhite,
  { message: "outputBlack must be < outputWhite", path: ["outputBlack"] }
);

export type ChannelBlendRange = z.infer<typeof ChannelBlendRangeSchema>;

export const StyleBlendingOptionsSchema = z.object({
  fillOpacity: AnimatablePropertySchema,
  blendInteriorStylesAsGroup: z.boolean(),
  blendClippedLayersAsGroup: z.boolean().optional(),
  transparencyShapesLayer: z.boolean().optional(),
  layerMaskHidesEffects: z.boolean().optional(),
  vectorMaskHidesEffects: z.boolean().optional(),
  blendIfEnabled: z.boolean().optional(),
  thisLayerRange: ChannelBlendRangeSchema.optional(),
  underlyingLayerRange: ChannelBlendRangeSchema.optional(),
}).strict();

export type StyleBlendingOptions = z.infer<typeof StyleBlendingOptionsSchema>;

// ============================================================================
// Layer Styles
// ============================================================================

export const LayerStylesSchema = z.object({
  enabled: z.boolean(),
  blendingOptions: StyleBlendingOptionsSchema.optional(),
  dropShadow: DropShadowStyleSchema.optional(),
  innerShadow: InnerShadowStyleSchema.optional(),
  outerGlow: OuterGlowStyleSchema.optional(),
  innerGlow: InnerGlowStyleSchema.optional(),
  bevelEmboss: BevelEmbossStyleSchema.optional(),
  satin: SatinStyleSchema.optional(),
  colorOverlay: ColorOverlayStyleSchema.optional(),
  gradientOverlay: GradientOverlayStyleSchema.optional(),
  stroke: StrokeStyleSchema.optional(),
}).strict();

export type LayerStyles = z.infer<typeof LayerStylesSchema>;

// ============================================================================
// Global Light Settings
// ============================================================================

export const GlobalLightSettingsSchema = z.object({
  angle: AnimatablePropertySchema,
  altitude: AnimatablePropertySchema,
}).strict();

export type GlobalLightSettings = z.infer<typeof GlobalLightSettingsSchema>;
