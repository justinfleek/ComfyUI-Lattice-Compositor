/-
  Lattice.LayerStyles.Core - Layer style structures

  Part of LayerStyles module. Max 500 lines.

  Source: ui/src/types/layerStyles.ts (lines 17-465)
-/

import Lattice.Primitives
import Lattice.Enums
import Lattice.LayerStyles.Enums

namespace Lattice.LayerStyles.Core

open Lattice.Primitives
open Lattice.Enums
open Lattice.LayerStyles.Enums

/-! ## Color Types -/

/-- RGBA color for layer styles -/
structure StyleRGBA where
  r : Nat  -- 0-255
  g : Nat  -- 0-255
  b : Nat  -- 0-255
  a : Float  -- 0-1
  r_le_255 : r ≤ 255
  g_le_255 : g ≤ 255
  b_le_255 : b ≤ 255
  a_ge_0 : a ≥ 0
  a_le_1 : a ≤ 1
  a_finite : a.isFinite
  deriving Repr

/-- Gradient stop for styles -/
structure StyleGradientStop where
  position : Float  -- 0-1
  color : StyleRGBA
  pos_ge_0 : position ≥ 0
  pos_le_1 : position ≤ 1
  pos_finite : position.isFinite
  deriving Repr

/-- Gradient type -/
inductive StyleGradientType where
  | linear
  | radial
  deriving Repr, BEq, DecidableEq

/-- Gradient definition -/
structure StyleGradientDef where
  gradientType : StyleGradientType
  stops : Array StyleGradientStop
  angle : Option Float  -- For linear gradients (degrees)
  h_min_stops : stops.size ≥ 2
  deriving Repr

/-- Contour curve point -/
structure ContourPoint where
  x : Float  -- 0-1 normalized
  y : Float  -- 0-1 normalized
  x_ge_0 : x ≥ 0
  x_le_1 : x ≤ 1
  y_ge_0 : y ≥ 0
  y_le_1 : y ≤ 1
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-- Contour curve for falloff -/
structure ContourCurve where
  points : Array ContourPoint
  deriving Repr

/-! ## Base Style -/

/-- Base layer style fields -/
structure BaseStyleFields where
  enabled : Bool
  blendMode : BlendMode
  opacityPropertyId : NonEmptyString  -- AnimatableProperty ID
  deriving Repr

/-! ## Drop Shadow -/

/-- Drop shadow style -/
structure DropShadowStyle extends BaseStyleFields where
  colorPropertyId : NonEmptyString
  anglePropertyId : NonEmptyString
  useGlobalLight : Bool
  distancePropertyId : NonEmptyString
  spreadPropertyId : NonEmptyString
  sizePropertyId : NonEmptyString
  noisePropertyId : NonEmptyString
  contour : Option ContourCurve
  antiAliased : Bool
  layerKnocksOut : Bool
  deriving Repr

/-! ## Inner Shadow -/

/-- Inner shadow style -/
structure InnerShadowStyle extends BaseStyleFields where
  colorPropertyId : NonEmptyString
  anglePropertyId : NonEmptyString
  useGlobalLight : Bool
  distancePropertyId : NonEmptyString
  chokePropertyId : NonEmptyString
  sizePropertyId : NonEmptyString
  noisePropertyId : NonEmptyString
  contour : Option ContourCurve
  antiAliased : Bool
  deriving Repr

/-! ## Outer Glow -/

/-- Outer glow style -/
structure OuterGlowStyle extends BaseStyleFields where
  colorPropertyId : NonEmptyString
  gradient : Option StyleGradientDef
  useGradient : Bool
  technique : GlowTechnique
  spreadPropertyId : NonEmptyString
  sizePropertyId : NonEmptyString
  rangePropertyId : NonEmptyString
  jitterPropertyId : NonEmptyString
  noisePropertyId : NonEmptyString
  contour : Option ContourCurve
  antiAliased : Bool
  deriving Repr

/-! ## Inner Glow -/

/-- Inner glow style -/
structure InnerGlowStyle extends BaseStyleFields where
  colorPropertyId : NonEmptyString
  gradient : Option StyleGradientDef
  useGradient : Bool
  technique : GlowTechnique
  source : InnerGlowSource
  chokePropertyId : NonEmptyString
  sizePropertyId : NonEmptyString
  rangePropertyId : NonEmptyString
  jitterPropertyId : NonEmptyString
  noisePropertyId : NonEmptyString
  contour : Option ContourCurve
  antiAliased : Bool
  deriving Repr

/-! ## Bevel and Emboss -/

/-- Bevel and emboss style -/
structure BevelEmbossStyle extends BaseStyleFields where
  style : BevelStyle
  technique : BevelTechnique
  depthPropertyId : NonEmptyString
  direction : BevelDirection
  sizePropertyId : NonEmptyString
  softenPropertyId : NonEmptyString
  anglePropertyId : NonEmptyString
  useGlobalLight : Bool
  altitudePropertyId : NonEmptyString
  glossContour : Option ContourCurve
  glossAntiAliased : Bool
  highlightMode : BlendMode
  highlightColorPropertyId : NonEmptyString
  highlightOpacityPropertyId : NonEmptyString
  shadowMode : BlendMode
  shadowColorPropertyId : NonEmptyString
  shadowOpacityPropertyId : NonEmptyString
  contourEnabled : Bool
  contour : Option ContourCurve
  contourAntiAliased : Bool
  contourRangePropertyId : Option NonEmptyString
  textureEnabled : Bool
  texturePattern : Option NonEmptyString
  textureScalePropertyId : Option NonEmptyString
  textureDepthPropertyId : Option NonEmptyString
  textureInvert : Bool
  textureLinkWithLayer : Bool
  deriving Repr

/-! ## Satin -/

/-- Satin style -/
structure SatinStyle extends BaseStyleFields where
  colorPropertyId : NonEmptyString
  anglePropertyId : NonEmptyString
  distancePropertyId : NonEmptyString
  sizePropertyId : NonEmptyString
  contour : Option ContourCurve
  antiAliased : Bool
  invert : Bool
  deriving Repr

/-! ## Color Overlay -/

/-- Color overlay style -/
structure ColorOverlayStyle extends BaseStyleFields where
  colorPropertyId : NonEmptyString
  deriving Repr

/-! ## Gradient Overlay -/

/-- Gradient overlay style -/
structure GradientOverlayStyle extends BaseStyleFields where
  gradientPropertyId : NonEmptyString
  style : GradientOverlayType
  anglePropertyId : NonEmptyString
  scalePropertyId : NonEmptyString
  alignWithLayer : Bool
  reverse : Bool
  offsetPropertyId : NonEmptyString
  dither : Bool
  deriving Repr

/-! ## Stroke -/

/-- Stroke style -/
structure StrokeStyleDef extends BaseStyleFields where
  colorPropertyId : NonEmptyString
  gradient : Option StyleGradientDef
  pattern : Option NonEmptyString
  fillType : StrokeFillType
  sizePropertyId : NonEmptyString
  position : StrokePosition
  gradientAnglePropertyId : Option NonEmptyString
  gradientScalePropertyId : Option NonEmptyString
  patternScalePropertyId : Option NonEmptyString
  patternLinkWithLayer : Bool
  deriving Repr

/-! ## Blending Options -/

/-- Channel blend range -/
structure ChannelBlendRange where
  inputBlack : Nat   -- 0-255
  inputWhite : Nat   -- 0-255
  outputBlack : Nat  -- 0-255
  outputWhite : Nat  -- 0-255
  inputBlack_le_255 : inputBlack ≤ 255
  inputWhite_le_255 : inputWhite ≤ 255
  outputBlack_le_255 : outputBlack ≤ 255
  outputWhite_le_255 : outputWhite ≤ 255
  deriving Repr

/-- Style blending options -/
structure StyleBlendingOptions where
  fillOpacityPropertyId : NonEmptyString
  blendInteriorStylesAsGroup : Bool
  blendClippedLayersAsGroup : Bool
  transparencyShapesLayer : Bool
  layerMaskHidesEffects : Bool
  vectorMaskHidesEffects : Bool
  blendIfEnabled : Bool
  thisLayerRange : Option ChannelBlendRange
  underlyingLayerRange : Option ChannelBlendRange
  deriving Repr

/-! ## Layer Styles Container -/

/-- Complete layer styles -/
structure LayerStyles where
  enabled : Bool
  blendingOptions : Option StyleBlendingOptions
  dropShadow : Option DropShadowStyle
  innerShadow : Option InnerShadowStyle
  outerGlow : Option OuterGlowStyle
  innerGlow : Option InnerGlowStyle
  bevelEmboss : Option BevelEmbossStyle
  satin : Option SatinStyle
  colorOverlay : Option ColorOverlayStyle
  gradientOverlay : Option GradientOverlayStyle
  stroke : Option StrokeStyleDef
  deriving Repr

/-! ## Global Light -/

/-- Global light settings -/
structure GlobalLightSettings where
  anglePropertyId : NonEmptyString
  altitudePropertyId : NonEmptyString
  deriving Repr

end Lattice.LayerStyles.Core
