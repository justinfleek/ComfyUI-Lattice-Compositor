// ============================================================
// LAYER STYLES TYPE DEFINITIONS
// ============================================================
//
// Industry-standard layer styles for Lattice Compositor
// Each style renders in a fixed order (shadow → glow → bevel → overlay → stroke)
// Separate from effects[] - styles apply BEFORE effects
//
// ============================================================

import type { AnimatableProperty, BlendMode } from "./project";

// ============================================================
// CORE TYPES
// ============================================================

/** RGBA color with alpha */
export interface RGBA {
  r: number; // 0-255
  g: number; // 0-255
  b: number; // 0-255
  a: number; // 0-1
}

/** Gradient stop */
export interface GradientStop {
  position: number; // 0-1
  color: RGBA;
}

/** Gradient definition */
export interface GradientDef {
  type: "linear" | "radial";
  stops: GradientStop[];
  angle?: number; // For linear gradients (degrees)
}

/** Contour curve for advanced effects */
export interface ContourCurve {
  points: Array<{ x: number; y: number }>; // 0-1 normalized
}

// ============================================================
// BASE STYLE INTERFACE
// ============================================================

/** Base interface for all layer styles */
export interface BaseLayerStyle {
  /** Whether this style is enabled */
  enabled: boolean;
  /** Blend mode for this style */
  blendMode: BlendMode;
  /** Opacity of the style (0-100) */
  opacity: AnimatableProperty<number>;
}

// ============================================================
// DROP SHADOW
// ============================================================

export interface DropShadowStyle extends BaseLayerStyle {
  /** Shadow color */
  color: AnimatableProperty<RGBA>;
  /** Light angle (0-360 degrees) */
  angle: AnimatableProperty<number>;
  /** Use composition's global light angle */
  useGlobalLight: boolean;
  /** Distance from layer (pixels) */
  distance: AnimatableProperty<number>;
  /** Spread/expansion before blur (0-100%) */
  spread: AnimatableProperty<number>;
  /** Blur radius (pixels) */
  size: AnimatableProperty<number>;
  /** Noise amount (0-100%) */
  noise: AnimatableProperty<number>;
  /** Contour for falloff shape */
  contour?: ContourCurve;
  /** Anti-alias the shadow edge */
  antiAliased?: boolean;
  /** Layer knocks out shadow (shadow only visible outside layer) */
  layerKnocksOut?: boolean;
}

// ============================================================
// INNER SHADOW
// ============================================================

export interface InnerShadowStyle extends BaseLayerStyle {
  /** Shadow color */
  color: AnimatableProperty<RGBA>;
  /** Light angle (0-360 degrees) */
  angle: AnimatableProperty<number>;
  /** Use composition's global light angle */
  useGlobalLight: boolean;
  /** Distance from edge (pixels) */
  distance: AnimatableProperty<number>;
  /** Choke/expansion (0-100%) - how much shadow is solid before blur */
  choke: AnimatableProperty<number>;
  /** Blur radius (pixels) */
  size: AnimatableProperty<number>;
  /** Noise amount (0-100%) */
  noise: AnimatableProperty<number>;
  /** Contour for falloff shape */
  contour?: ContourCurve;
  /** Anti-alias the shadow edge */
  antiAliased?: boolean;
}

// ============================================================
// OUTER GLOW
// ============================================================

/** Glow rendering technique */
export type GlowTechnique = "softer" | "precise";

export interface OuterGlowStyle extends BaseLayerStyle {
  /** Glow color (if not using gradient) */
  color: AnimatableProperty<RGBA>;
  /** Optional gradient for glow */
  gradient?: GradientDef;
  /** Use gradient instead of solid color */
  useGradient?: boolean;
  /** Rendering technique */
  technique: GlowTechnique;
  /** Spread before blur (0-100%) */
  spread: AnimatableProperty<number>;
  /** Blur radius (pixels) */
  size: AnimatableProperty<number>;
  /** Range of glow effect (0-100%) */
  range: AnimatableProperty<number>;
  /** Jitter for noise variation (0-100%) */
  jitter: AnimatableProperty<number>;
  /** Noise amount (0-100%) */
  noise: AnimatableProperty<number>;
  /** Contour for falloff shape */
  contour?: ContourCurve;
  /** Anti-alias the glow edge */
  antiAliased?: boolean;
}

// ============================================================
// INNER GLOW
// ============================================================

/** Where inner glow originates from */
export type InnerGlowSource = "center" | "edge";

export interface InnerGlowStyle extends BaseLayerStyle {
  /** Glow color (if not using gradient) */
  color: AnimatableProperty<RGBA>;
  /** Optional gradient for glow */
  gradient?: GradientDef;
  /** Use gradient instead of solid color */
  useGradient?: boolean;
  /** Rendering technique */
  technique: GlowTechnique;
  /** Glow source: from center or from edge */
  source: InnerGlowSource;
  /** Choke amount (0-100%) */
  choke: AnimatableProperty<number>;
  /** Blur radius (pixels) */
  size: AnimatableProperty<number>;
  /** Range of glow effect (0-100%) */
  range: AnimatableProperty<number>;
  /** Jitter for noise variation (0-100%) */
  jitter: AnimatableProperty<number>;
  /** Noise amount (0-100%) */
  noise: AnimatableProperty<number>;
  /** Contour for falloff shape */
  contour?: ContourCurve;
  /** Anti-alias the glow edge */
  antiAliased?: boolean;
}

// ============================================================
// BEVEL AND EMBOSS
// ============================================================

/** Bevel style type */
export type BevelStyle =
  | "outer-bevel" // Bevel on outside edge
  | "inner-bevel" // Bevel on inside edge
  | "emboss" // Raised emboss
  | "pillow-emboss" // Sunken edges
  | "stroke-emboss"; // Bevel on stroke

/** Bevel rendering technique */
export type BevelTechnique = "smooth" | "chisel-hard" | "chisel-soft";

/** Bevel direction */
export type BevelDirection = "up" | "down";

export interface BevelEmbossStyle extends BaseLayerStyle {
  /** Bevel style type */
  style: BevelStyle;
  /** Rendering technique */
  technique: BevelTechnique;
  /** Depth intensity (1-1000%) */
  depth: AnimatableProperty<number>;
  /** Direction: raised or sunken */
  direction: BevelDirection;
  /** Size/thickness (pixels) */
  size: AnimatableProperty<number>;
  /** Soften edges (pixels) */
  soften: AnimatableProperty<number>;

  // Shading
  /** Light source angle (0-360 degrees) */
  angle: AnimatableProperty<number>;
  /** Use composition's global light angle */
  useGlobalLight: boolean;
  /** Light altitude/elevation (0-90 degrees) */
  altitude: AnimatableProperty<number>;

  // Gloss Contour
  /** Gloss contour curve */
  glossContour?: ContourCurve;
  /** Anti-alias gloss */
  glossAntiAliased?: boolean;

  // Highlight
  /** Blend mode for highlights */
  highlightMode: BlendMode;
  /** Highlight color */
  highlightColor: AnimatableProperty<RGBA>;
  /** Highlight opacity (0-100%) */
  highlightOpacity: AnimatableProperty<number>;

  // Shadow
  /** Blend mode for shadows */
  shadowMode: BlendMode;
  /** Shadow color */
  shadowColor: AnimatableProperty<RGBA>;
  /** Shadow opacity (0-100%) */
  shadowOpacity: AnimatableProperty<number>;

  // Contour (sub-effect)
  /** Enable contour sub-effect */
  contourEnabled?: boolean;
  /** Contour curve */
  contour?: ContourCurve;
  /** Anti-alias contour */
  contourAntiAliased?: boolean;
  /** Contour range (0-100%) */
  contourRange?: AnimatableProperty<number>;

  // Texture (sub-effect)
  /** Enable texture sub-effect */
  textureEnabled?: boolean;
  /** Texture pattern (pattern ID or asset ID) */
  texturePattern?: string;
  /** Texture scale (1-1000%) */
  textureScale?: AnimatableProperty<number>;
  /** Texture depth (-1000 to 1000%) */
  textureDepth?: AnimatableProperty<number>;
  /** Invert texture */
  textureInvert?: boolean;
  /** Link texture with layer transform */
  textureLinkWithLayer?: boolean;
}

// ============================================================
// SATIN
// ============================================================

export interface SatinStyle extends BaseLayerStyle {
  /** Satin color */
  color: AnimatableProperty<RGBA>;
  /** Light angle (0-360 degrees) */
  angle: AnimatableProperty<number>;
  /** Distance of effect (pixels) */
  distance: AnimatableProperty<number>;
  /** Size/blur (pixels) */
  size: AnimatableProperty<number>;
  /** Contour for sheen pattern */
  contour?: ContourCurve;
  /** Anti-alias the effect */
  antiAliased?: boolean;
  /** Invert the effect */
  invert: boolean;
}

// ============================================================
// COLOR OVERLAY
// ============================================================

export interface ColorOverlayStyle extends BaseLayerStyle {
  /** Overlay color */
  color: AnimatableProperty<RGBA>;
}

// ============================================================
// GRADIENT OVERLAY
// ============================================================

/** Gradient overlay style type */
export type GradientOverlayType =
  | "linear"
  | "radial"
  | "angle"
  | "reflected"
  | "diamond";

export interface GradientOverlayStyle extends BaseLayerStyle {
  /** Gradient definition */
  gradient: AnimatableProperty<GradientDef>;
  /** Gradient style/shape */
  style: GradientOverlayType;
  /** Angle for linear/angle gradients (degrees) */
  angle: AnimatableProperty<number>;
  /** Scale of gradient (10-150%) */
  scale: AnimatableProperty<number>;
  /** Align gradient with layer bounds */
  alignWithLayer: boolean;
  /** Reverse gradient direction */
  reverse: boolean;
  /** Gradient center offset from layer center */
  offset: AnimatableProperty<{ x: number; y: number }>;
  /** Dither to reduce banding */
  dither?: boolean;
}

// ============================================================
// PATTERN OVERLAY
// ============================================================

export interface PatternOverlayStyle extends BaseLayerStyle {
  /** Pattern asset ID or URL */
  pattern: string;
  /** Scale of pattern (1-1000%) */
  scale: AnimatableProperty<number>;
  /** Angle of pattern rotation (degrees) */
  angle: AnimatableProperty<number>;
  /** Link pattern with layer transforms */
  linkWithLayer: boolean;
  /** Snap pattern origin to layer origin */
  snapToOrigin: boolean;
  /** Pattern offset from origin */
  offset: AnimatableProperty<{ x: number; y: number }>;
}

// ============================================================
// STROKE
// ============================================================

/** Stroke position relative to edge */
export type StrokePosition = "outside" | "inside" | "center";

/** Stroke fill type */
export type StrokeFillType = "color" | "gradient" | "pattern";

export interface StrokeStyle extends BaseLayerStyle {
  /** Stroke color (if fillType is 'color') */
  color: AnimatableProperty<RGBA>;
  /** Stroke gradient (if fillType is 'gradient') */
  gradient?: GradientDef;
  /** Stroke pattern asset ID (if fillType is 'pattern') */
  pattern?: string;
  /** Fill type */
  fillType: StrokeFillType;
  /** Stroke width (pixels) */
  size: AnimatableProperty<number>;
  /** Position relative to edge */
  position: StrokePosition;
  /** Gradient angle (if using gradient) */
  gradientAngle?: AnimatableProperty<number>;
  /** Gradient scale (if using gradient) */
  gradientScale?: AnimatableProperty<number>;
  /** Pattern scale (if using pattern) */
  patternScale?: AnimatableProperty<number>;
  /** Link pattern with layer */
  patternLinkWithLayer?: boolean;
}

// ============================================================
// STYLE BLENDING OPTIONS
// ============================================================

/** Channel blend options */
export interface ChannelBlendRange {
  /** Black input level (0-255) */
  inputBlack: number;
  /** White input level (0-255) */
  inputWhite: number;
  /** Black output level (0-255) */
  outputBlack: number;
  /** White output level (0-255) */
  outputWhite: number;
}

export interface StyleBlendingOptions {
  /** Fill opacity - affects layer content but NOT styles (0-100%) */
  fillOpacity: AnimatableProperty<number>;
  /** Blend interior effects as a group */
  blendInteriorStylesAsGroup: boolean;
  /** Blend clipped layers as a group */
  blendClippedLayersAsGroup?: boolean;
  /** Transparency shapes layer (knockout) */
  transparencyShapesLayer?: boolean;
  /** Layer mask hides effects */
  layerMaskHidesEffects?: boolean;
  /** Vector mask hides effects */
  vectorMaskHidesEffects?: boolean;

  // Advanced blending (Blend If)
  /** Enable Blend If sliders */
  blendIfEnabled?: boolean;
  /** This layer's blend range */
  thisLayerRange?: ChannelBlendRange;
  /** Underlying layer's blend range */
  underlyingLayerRange?: ChannelBlendRange;
}

// ============================================================
// MAIN LAYER STYLES CONTAINER
// ============================================================

/**
 * Complete Layer Styles definition
 * Renders in fixed order (back to front):
 * 1. Drop Shadow (behind layer)
 * 2. Inner Shadow
 * 3. Outer Glow (behind layer)
 * 4. Inner Glow
 * 5. Bevel and Emboss
 * 6. Satin
 * 7. Color Overlay
 * 8. Gradient Overlay
 * 9. Stroke (on top)
 */
export interface LayerStyles {
  /** Master enable/disable for all layer styles */
  enabled: boolean;

  /** Advanced blending options (Fill Opacity, etc.) */
  blendingOptions?: StyleBlendingOptions;

  /** Drop shadow (renders behind layer) */
  dropShadow?: DropShadowStyle;

  /** Inner shadow (renders inside layer) */
  innerShadow?: InnerShadowStyle;

  /** Outer glow (renders behind layer) */
  outerGlow?: OuterGlowStyle;

  /** Inner glow (renders inside layer) */
  innerGlow?: InnerGlowStyle;

  /** Bevel and emboss (3D appearance) */
  bevelEmboss?: BevelEmbossStyle;

  /** Satin (internal shading effect) */
  satin?: SatinStyle;

  /** Color overlay (solid color fill) */
  colorOverlay?: ColorOverlayStyle;

  /** Gradient overlay (gradient fill) */
  gradientOverlay?: GradientOverlayStyle;

  /** Stroke (outline around layer) */
  stroke?: StrokeStyle;
}

// ============================================================
// GLOBAL LIGHT
// ============================================================

/**
 * Global Light settings for a composition
 * Styles with useGlobalLight=true share these values
 */
export interface GlobalLightSettings {
  /** Global light angle (0-360 degrees) */
  angle: AnimatableProperty<number>;
  /** Global light altitude (0-90 degrees) */
  altitude: AnimatableProperty<number>;
}

// ============================================================
// FACTORY FUNCTIONS
// ============================================================

/** Create a default animatable property for layer styles */
export function createStyleProperty<T>(
  name: string,
  value: T,
  type: "number" | "color" | "position" = "number",
): AnimatableProperty<T> {
  return {
    id: `style-${name}-${Date.now()}`,
    name,
    type,
    value,
    animated: false,
    keyframes: [],
  };
}

/** Create default RGBA color */
export function createRGBA(
  r: number,
  g: number,
  b: number,
  a: number = 1,
): RGBA {
  return { r, g, b, a };
}

/** Create default layer styles (all disabled) */
export function createDefaultLayerStyles(): LayerStyles {
  return {
    enabled: false,
  };
}

/** Create default drop shadow style */
export function createDefaultDropShadow(): DropShadowStyle {
  return {
    enabled: true,
    blendMode: "multiply",
    opacity: createStyleProperty("opacity", 75),
    color: createStyleProperty("color", createRGBA(0, 0, 0, 1), "color"),
    angle: createStyleProperty("angle", 120),
    useGlobalLight: true,
    distance: createStyleProperty("distance", 5),
    spread: createStyleProperty("spread", 0),
    size: createStyleProperty("size", 5),
    noise: createStyleProperty("noise", 0),
    layerKnocksOut: true,
  };
}

/** Create default inner shadow style */
export function createDefaultInnerShadow(): InnerShadowStyle {
  return {
    enabled: true,
    blendMode: "multiply",
    opacity: createStyleProperty("opacity", 75),
    color: createStyleProperty("color", createRGBA(0, 0, 0, 1), "color"),
    angle: createStyleProperty("angle", 120),
    useGlobalLight: true,
    distance: createStyleProperty("distance", 5),
    choke: createStyleProperty("choke", 0),
    size: createStyleProperty("size", 5),
    noise: createStyleProperty("noise", 0),
  };
}

/** Create default outer glow style */
export function createDefaultOuterGlow(): OuterGlowStyle {
  return {
    enabled: true,
    blendMode: "screen",
    opacity: createStyleProperty("opacity", 75),
    color: createStyleProperty("color", createRGBA(255, 255, 190, 1), "color"),
    technique: "softer",
    spread: createStyleProperty("spread", 0),
    size: createStyleProperty("size", 5),
    range: createStyleProperty("range", 50),
    jitter: createStyleProperty("jitter", 0),
    noise: createStyleProperty("noise", 0),
  };
}

/** Create default inner glow style */
export function createDefaultInnerGlow(): InnerGlowStyle {
  return {
    enabled: true,
    blendMode: "screen",
    opacity: createStyleProperty("opacity", 75),
    color: createStyleProperty("color", createRGBA(255, 255, 190, 1), "color"),
    technique: "softer",
    source: "edge",
    choke: createStyleProperty("choke", 0),
    size: createStyleProperty("size", 5),
    range: createStyleProperty("range", 50),
    jitter: createStyleProperty("jitter", 0),
    noise: createStyleProperty("noise", 0),
  };
}

/** Create default bevel and emboss style */
export function createDefaultBevelEmboss(): BevelEmbossStyle {
  return {
    enabled: true,
    blendMode: "normal",
    opacity: createStyleProperty("opacity", 100),
    style: "inner-bevel",
    technique: "smooth",
    depth: createStyleProperty("depth", 100),
    direction: "up",
    size: createStyleProperty("size", 5),
    soften: createStyleProperty("soften", 0),
    angle: createStyleProperty("angle", 120),
    useGlobalLight: true,
    altitude: createStyleProperty("altitude", 30),
    highlightMode: "screen",
    highlightColor: createStyleProperty(
      "highlightColor",
      createRGBA(255, 255, 255, 1),
      "color",
    ),
    highlightOpacity: createStyleProperty("highlightOpacity", 75),
    shadowMode: "multiply",
    shadowColor: createStyleProperty(
      "shadowColor",
      createRGBA(0, 0, 0, 1),
      "color",
    ),
    shadowOpacity: createStyleProperty("shadowOpacity", 75),
  };
}

/** Create default satin style */
export function createDefaultSatin(): SatinStyle {
  return {
    enabled: true,
    blendMode: "multiply",
    opacity: createStyleProperty("opacity", 50),
    color: createStyleProperty("color", createRGBA(0, 0, 0, 1), "color"),
    angle: createStyleProperty("angle", 19),
    distance: createStyleProperty("distance", 11),
    size: createStyleProperty("size", 14),
    invert: true,
  };
}

/** Create default color overlay style */
export function createDefaultColorOverlay(): ColorOverlayStyle {
  return {
    enabled: true,
    blendMode: "normal",
    opacity: createStyleProperty("opacity", 100),
    color: createStyleProperty("color", createRGBA(255, 0, 0, 1), "color"),
  };
}

/** Create default gradient overlay style */
export function createDefaultGradientOverlay(): GradientOverlayStyle {
  return {
    enabled: true,
    blendMode: "normal",
    opacity: createStyleProperty("opacity", 100),
    gradient: createStyleProperty("gradient", {
      type: "linear",
      stops: [
        { position: 0, color: createRGBA(0, 0, 0, 1) },
        { position: 1, color: createRGBA(255, 255, 255, 1) },
      ],
    }),
    style: "linear",
    angle: createStyleProperty("angle", 90),
    scale: createStyleProperty("scale", 100),
    alignWithLayer: true,
    reverse: false,
    offset: createStyleProperty("offset", { x: 0, y: 0 }, "position"),
  };
}

/** Create default stroke style */
export function createDefaultStroke(): StrokeStyle {
  return {
    enabled: true,
    blendMode: "normal",
    opacity: createStyleProperty("opacity", 100),
    color: createStyleProperty("color", createRGBA(255, 0, 0, 1), "color"),
    fillType: "color",
    size: createStyleProperty("size", 3),
    position: "outside",
  };
}

/** Create default blending options */
export function createDefaultBlendingOptions(): StyleBlendingOptions {
  return {
    fillOpacity: createStyleProperty("fillOpacity", 100),
    blendInteriorStylesAsGroup: false,
    blendClippedLayersAsGroup: true,
    transparencyShapesLayer: true,
    layerMaskHidesEffects: false,
    vectorMaskHidesEffects: false,
  };
}

/** Create default global light settings */
export function createDefaultGlobalLight(): GlobalLightSettings {
  return {
    angle: createStyleProperty("angle", 120),
    altitude: createStyleProperty("altitude", 30),
  };
}

// ============================================================
// UTILITY TYPES FOR STYLE UPDATES
// ============================================================

/**
 * Utility type for style update payloads.
 * Converts AnimatableProperty<T> fields to just T, allowing editors
 * to emit raw values that the parent component will merge.
 */
export type StyleUpdate<T> = {
  [K in keyof T]?: T[K] extends AnimatableProperty<infer V>
    ? V | AnimatableProperty<V>
    : T[K];
};

// Export specific update types for each style
export type DropShadowUpdate = StyleUpdate<DropShadowStyle>;
export type InnerShadowUpdate = StyleUpdate<InnerShadowStyle>;
export type OuterGlowUpdate = StyleUpdate<OuterGlowStyle>;
export type InnerGlowUpdate = StyleUpdate<InnerGlowStyle>;
export type BevelEmbossUpdate = StyleUpdate<BevelEmbossStyle>;
export type SatinUpdate = StyleUpdate<SatinStyle>;
export type ColorOverlayUpdate = StyleUpdate<ColorOverlayStyle>;
export type GradientOverlayUpdate = StyleUpdate<GradientOverlayStyle>;
export type PatternOverlayUpdate = StyleUpdate<PatternOverlayStyle>;
export type StrokeStyleUpdate = StyleUpdate<StrokeStyle>;
export type StyleBlendingOptionsUpdate = StyleUpdate<StyleBlendingOptions>;
