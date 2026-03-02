-- |
-- Module      : Lattice.Types.LayerStyles.Core
-- Description : Core types for layer styles (drop shadow, glow, bevel, etc.)
-- 
-- Migrated from ui/src/types/layerStyles.ts
-- Industry-standard layer styles for Lattice Compositor
-- Each style renders in a fixed order (shadow → glow → bevel → overlay → stroke)
-- Separate from effects[] - styles apply BEFORE effects
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerStyles.Core
  ( -- Base types
    RGBAColor (..),
    GradientStop (..),
    GradientDef (..),
    GradientType (..),
    ContourCurve (..),
    ContourPoint (..),
    -- Base style interface
    BaseLayerStyle (..),
    -- Style types
    DropShadowStyle (..),
    InnerShadowStyle (..),
    OuterGlowStyle (..),
    InnerGlowStyle (..),
    GlowTechnique (..),
    InnerGlowSource (..),
    BevelEmbossStyle (..),
    BevelStyle (..),
    BevelTechnique (..),
    BevelDirection (..),
    SatinStyle (..),
    ColorOverlayStyle (..),
    GradientOverlayStyle (..),
    GradientOverlayType (..),
    PatternOverlayStyle (..),
    StrokeStyle (..),
    StrokePosition (..),
    StrokeFillType (..),
    -- Blending options
    StyleBlendingOptions (..),
    ChannelBlendRange (..),
    -- Main container
    LayerStyles (..),
    -- Global light
    GlobalLightSettings (..),
  )
where

import Data.Aeson
  ( ToJSON (..),
    FromJSON (..),
    withObject,
    withText,
    object,
    (.=),
    (.:),
    (.:?),
    Value (..),
  )
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
  )
import Lattice.Types.LayerDataShapes (Point2D (..))
import Lattice.Types.Primitives
  ( BlendMode (..),
    validateFinite,
    validateNonNegative,
    validateNormalized01,
  )
import Lattice.Schema.SharedValidation
  ( validateBoundedArray,
  )
import qualified Data.Text as T

-- ============================================================================
-- BASE TYPES
-- ============================================================================

-- | RGBA color with alpha
-- RGB values: 0-255, Alpha: 0-1
data RGBAColor = RGBAColor
  { rgbaR :: Double, -- 0-255
    rgbaG :: Double, -- 0-255
    rgbaB :: Double, -- 0-255
    rgbaA :: Double -- 0-1
  }
  deriving (Eq, Show, Generic)

instance ToJSON RGBAColor where
  toJSON (RGBAColor r g b a) =
    object ["r" .= r, "g" .= g, "b" .= b, "a" .= a]

instance FromJSON RGBAColor where
  parseJSON = withObject "RGBAColor" $ \o -> do
    r <- o .: "r"
    g <- o .: "g"
    b <- o .: "b"
    a <- o .: "a"
    if validateFinite r && validateFinite g && validateFinite b && validateFinite a &&
       validateNonNegative r && validateNonNegative g && validateNonNegative b &&
       validateNormalized01 a && r <= 255 && g <= 255 && b <= 255
      then return (RGBAColor r g b a)
      else fail "RGBAColor: r, g, b must be in [0,255], a must be in [0,1]"

-- | Gradient stop
data GradientStop = GradientStop
  { gradientStopPosition :: Double, -- 0-1
    gradientStopColor :: RGBAColor
  }
  deriving (Eq, Show, Generic)

instance ToJSON GradientStop where
  toJSON (GradientStop position color) =
    object ["position" .= position, "color" .= color]

instance FromJSON GradientStop where
  parseJSON = withObject "GradientStop" $ \o -> do
    position <- o .: "position"
    color <- o .: "color"
    if validateNormalized01 position
      then return (GradientStop position color)
      else fail "GradientStop: position must be in [0,1]"

-- | Gradient type
data GradientType
  = GradientTypeLinear
  | GradientTypeRadial
  deriving (Eq, Show, Generic)

instance ToJSON GradientType where
  toJSON GradientTypeLinear = "linear"
  toJSON GradientTypeRadial = "radial"

instance FromJSON GradientType where
  parseJSON = withText "GradientType" $ \s ->
    case s of
      _ | s == T.pack "linear" -> return GradientTypeLinear
      _ | s == T.pack "radial" -> return GradientTypeRadial
      _ -> fail "Invalid GradientType"

-- | Gradient definition (simpler than shapes - only type, stops, optional angle)
data GradientDef = GradientDef
  { gradientDefType :: GradientType,
    gradientDefStops :: [GradientStop],
    gradientDefAngle :: Maybe Double -- For linear gradients (degrees)
  }
  deriving (Eq, Show, Generic)

instance ToJSON GradientDef where
  toJSON (GradientDef gType stops mAngle) =
    object $
      [ "type" .= gType,
        "stops" .= stops
      ]
        ++ maybe [] (\a -> ["angle" .= a]) mAngle

instance FromJSON GradientDef where
  parseJSON = withObject "GradientDef" $ \o -> do
    gType <- o .: "type"
    stopsRaw <- o .: "stops"
    mAngle <- o .:? "angle"
    -- Validate max 100 stops per gradient
    stops <- case validateBoundedArray 100 stopsRaw of
      Left err -> fail (T.unpack err)
      Right sts ->
        -- Must have at least 2 stops
        if length sts < 2
          then fail "Gradient must have at least 2 stops"
          else return sts
    if maybe True (\a -> validateFinite a) mAngle
      then return (GradientDef gType stops mAngle)
      else fail "GradientDef: angle must be finite"

-- | Contour point (normalized 0-1)
data ContourPoint = ContourPoint
  { contourPointX :: Double,
    contourPointY :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON ContourPoint where
  toJSON (ContourPoint x y) =
    object ["x" .= x, "y" .= y]

instance FromJSON ContourPoint where
  parseJSON = withObject "ContourPoint" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    if validateNormalized01 x && validateNormalized01 y
      then return (ContourPoint x y)
      else fail "ContourPoint: x and y must be in [0,1]"

-- | Contour curve for advanced effects
data ContourCurve = ContourCurve
  { contourCurvePoints :: [ContourPoint] -- 0-1 normalized
  }
  deriving (Eq, Show, Generic)

instance ToJSON ContourCurve where
  toJSON (ContourCurve points) =
    object ["points" .= points]

instance FromJSON ContourCurve where
  parseJSON = withObject "ContourCurve" $ \o -> do
    pointsRaw <- o .: "points"
    -- Validate max 1000 points per contour
    points <- case validateBoundedArray 1000 pointsRaw of
      Left err -> fail (T.unpack err)
      Right ps -> return ps
    return (ContourCurve points)

-- ============================================================================
-- BASE STYLE INTERFACE
-- ============================================================================

-- | Base interface for all layer styles
data BaseLayerStyle = BaseLayerStyle
  { baseLayerStyleEnabled :: Bool, -- Whether this style is enabled
    baseLayerStyleBlendMode :: BlendMode, -- Blend mode for this style
    baseLayerStyleOpacity :: AnimatableProperty Double -- Opacity of the style (0-100)
  }
  deriving (Eq, Show, Generic)

instance ToJSON BaseLayerStyle where
  toJSON (BaseLayerStyle enabled blendMode opacity) =
    object
      [ "enabled" .= enabled,
        "blendMode" .= blendMode,
        "opacity" .= opacity
      ]

instance FromJSON BaseLayerStyle where
  parseJSON = withObject "BaseLayerStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    return (BaseLayerStyle enabled blendMode opacity)

-- ============================================================================
-- DROP SHADOW
-- ============================================================================

-- | Drop shadow style
data DropShadowStyle = DropShadowStyle
  { dropShadowStyleBase :: BaseLayerStyle,
    dropShadowStyleColor :: AnimatableProperty RGBAColor,
    dropShadowStyleAngle :: AnimatableProperty Double, -- Light angle (0-360 degrees)
    dropShadowStyleUseGlobalLight :: Bool, -- Use composition's global light angle
    dropShadowStyleDistance :: AnimatableProperty Double, -- Distance from layer (pixels)
    dropShadowStyleSpread :: AnimatableProperty Double, -- Spread/expansion before blur (0-100%)
    dropShadowStyleSize :: AnimatableProperty Double, -- Blur radius (pixels)
    dropShadowStyleNoise :: AnimatableProperty Double, -- Noise amount (0-100%)
    dropShadowStyleContour :: Maybe ContourCurve, -- Contour for falloff shape
    dropShadowStyleAntiAliased :: Maybe Bool, -- Anti-alias the shadow edge
    dropShadowStyleLayerKnocksOut :: Maybe Bool -- Layer knocks out shadow
  }
  deriving (Eq, Show, Generic)

instance ToJSON DropShadowStyle where
  toJSON (DropShadowStyle base color angle useGlobalLight distance spread size noise contour antiAliased layerKnocksOut) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "color" .= color,
            "angle" .= angle,
            "useGlobalLight" .= useGlobalLight,
            "distance" .= distance,
            "spread" .= spread,
            "size" .= size,
            "noise" .= noise
          ],
          maybe [] (\c -> ["contour" .= c]) contour,
          maybe [] (\aa -> ["antiAliased" .= aa]) antiAliased,
          maybe [] (\lko -> ["layerKnocksOut" .= lko]) layerKnocksOut
        ]

instance FromJSON DropShadowStyle where
  parseJSON = withObject "DropShadowStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    color <- o .: "color"
    angle <- o .: "angle"
    useGlobalLight <- o .: "useGlobalLight"
    distance <- o .: "distance"
    spread <- o .: "spread"
    size <- o .: "size"
    noise <- o .: "noise"
    contour <- o .:? "contour"
    antiAliased <- o .:? "antiAliased"
    layerKnocksOut <- o .:? "layerKnocksOut"
    let base = BaseLayerStyle enabled blendMode opacity
    return (DropShadowStyle base color angle useGlobalLight distance spread size noise contour antiAliased layerKnocksOut)

-- ============================================================================
-- INNER SHADOW
-- ============================================================================

-- | Inner shadow style
data InnerShadowStyle = InnerShadowStyle
  { innerShadowStyleBase :: BaseLayerStyle,
    innerShadowStyleColor :: AnimatableProperty RGBAColor,
    innerShadowStyleAngle :: AnimatableProperty Double, -- Light angle (0-360 degrees)
    innerShadowStyleUseGlobalLight :: Bool,
    innerShadowStyleDistance :: AnimatableProperty Double, -- Distance from edge (pixels)
    innerShadowStyleChoke :: AnimatableProperty Double, -- Choke/expansion (0-100%)
    innerShadowStyleSize :: AnimatableProperty Double, -- Blur radius (pixels)
    innerShadowStyleNoise :: AnimatableProperty Double, -- Noise amount (0-100%)
    innerShadowStyleContour :: Maybe ContourCurve,
    innerShadowStyleAntiAliased :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON InnerShadowStyle where
  toJSON (InnerShadowStyle base color angle useGlobalLight distance choke size noise contour antiAliased) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "color" .= color,
            "angle" .= angle,
            "useGlobalLight" .= useGlobalLight,
            "distance" .= distance,
            "choke" .= choke,
            "size" .= size,
            "noise" .= noise
          ],
          maybe [] (\c -> ["contour" .= c]) contour,
          maybe [] (\aa -> ["antiAliased" .= aa]) antiAliased
        ]

instance FromJSON InnerShadowStyle where
  parseJSON = withObject "InnerShadowStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    color <- o .: "color"
    angle <- o .: "angle"
    useGlobalLight <- o .: "useGlobalLight"
    distance <- o .: "distance"
    choke <- o .: "choke"
    size <- o .: "size"
    noise <- o .: "noise"
    contour <- o .:? "contour"
    antiAliased <- o .:? "antiAliased"
    let base = BaseLayerStyle enabled blendMode opacity
    return (InnerShadowStyle base color angle useGlobalLight distance choke size noise contour antiAliased)

-- ============================================================================
-- OUTER GLOW
-- ============================================================================

-- | Glow rendering technique
data GlowTechnique
  = GlowTechniqueSofter
  | GlowTechniquePrecise
  deriving (Eq, Show, Generic)

instance ToJSON GlowTechnique where
  toJSON GlowTechniqueSofter = "softer"
  toJSON GlowTechniquePrecise = "precise"

instance FromJSON GlowTechnique where
  parseJSON = withText "GlowTechnique" $ \s ->
    case s of
      _ | s == T.pack "softer" -> return GlowTechniqueSofter
      _ | s == T.pack "precise" -> return GlowTechniquePrecise
      _ -> fail "Invalid GlowTechnique"

-- | Outer glow style
data OuterGlowStyle = OuterGlowStyle
  { outerGlowStyleBase :: BaseLayerStyle,
    outerGlowStyleColor :: AnimatableProperty RGBAColor, -- Glow color (if not using gradient)
    outerGlowStyleGradient :: Maybe GradientDef, -- Optional gradient for glow
    outerGlowStyleUseGradient :: Maybe Bool, -- Use gradient instead of solid color
    outerGlowStyleTechnique :: GlowTechnique,
    outerGlowStyleSpread :: AnimatableProperty Double, -- Spread before blur (0-100%)
    outerGlowStyleSize :: AnimatableProperty Double, -- Blur radius (pixels)
    outerGlowStyleRange :: AnimatableProperty Double, -- Range of glow effect (0-100%)
    outerGlowStyleJitter :: AnimatableProperty Double, -- Jitter for noise variation (0-100%)
    outerGlowStyleNoise :: AnimatableProperty Double, -- Noise amount (0-100%)
    outerGlowStyleContour :: Maybe ContourCurve,
    outerGlowStyleAntiAliased :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON OuterGlowStyle where
  toJSON (OuterGlowStyle base color gradient useGradient technique spread size range jitter noise contour antiAliased) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "color" .= color,
            "technique" .= technique,
            "spread" .= spread,
            "size" .= size,
            "range" .= range,
            "jitter" .= jitter,
            "noise" .= noise
          ],
          maybe [] (\g -> ["gradient" .= g]) gradient,
          maybe [] (\ug -> ["useGradient" .= ug]) useGradient,
          maybe [] (\c -> ["contour" .= c]) contour,
          maybe [] (\aa -> ["antiAliased" .= aa]) antiAliased
        ]

instance FromJSON OuterGlowStyle where
  parseJSON = withObject "OuterGlowStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    color <- o .: "color"
    technique <- o .: "technique"
    spread <- o .: "spread"
    size <- o .: "size"
    range <- o .: "range"
    jitter <- o .: "jitter"
    noise <- o .: "noise"
    gradient <- o .:? "gradient"
    useGradient <- o .:? "useGradient"
    contour <- o .:? "contour"
    antiAliased <- o .:? "antiAliased"
    let base = BaseLayerStyle enabled blendMode opacity
    return (OuterGlowStyle base color gradient useGradient technique spread size range jitter noise contour antiAliased)

-- ============================================================================
-- INNER GLOW
-- ============================================================================

-- | Where inner glow originates from
data InnerGlowSource
  = InnerGlowSourceCenter
  | InnerGlowSourceEdge
  deriving (Eq, Show, Generic)

instance ToJSON InnerGlowSource where
  toJSON InnerGlowSourceCenter = "center"
  toJSON InnerGlowSourceEdge = "edge"

instance FromJSON InnerGlowSource where
  parseJSON = withText "InnerGlowSource" $ \s ->
    case s of
      _ | s == T.pack "center" -> return InnerGlowSourceCenter
      _ | s == T.pack "edge" -> return InnerGlowSourceEdge
      _ -> fail "Invalid InnerGlowSource"

-- | Inner glow style
data InnerGlowStyle = InnerGlowStyle
  { innerGlowStyleBase :: BaseLayerStyle,
    innerGlowStyleColor :: AnimatableProperty RGBAColor,
    innerGlowStyleGradient :: Maybe GradientDef,
    innerGlowStyleUseGradient :: Maybe Bool,
    innerGlowStyleTechnique :: GlowTechnique,
    innerGlowStyleSource :: InnerGlowSource, -- Glow source: from center or from edge
    innerGlowStyleChoke :: AnimatableProperty Double, -- Choke amount (0-100%)
    innerGlowStyleSize :: AnimatableProperty Double,
    innerGlowStyleRange :: AnimatableProperty Double,
    innerGlowStyleJitter :: AnimatableProperty Double,
    innerGlowStyleNoise :: AnimatableProperty Double,
    innerGlowStyleContour :: Maybe ContourCurve,
    innerGlowStyleAntiAliased :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON InnerGlowStyle where
  toJSON (InnerGlowStyle base color gradient useGradient technique source choke size range jitter noise contour antiAliased) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "color" .= color,
            "technique" .= technique,
            "source" .= source,
            "choke" .= choke,
            "size" .= size,
            "range" .= range,
            "jitter" .= jitter,
            "noise" .= noise
          ],
          maybe [] (\g -> ["gradient" .= g]) gradient,
          maybe [] (\ug -> ["useGradient" .= ug]) useGradient,
          maybe [] (\c -> ["contour" .= c]) contour,
          maybe [] (\aa -> ["antiAliased" .= aa]) antiAliased
        ]

instance FromJSON InnerGlowStyle where
  parseJSON = withObject "InnerGlowStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    color <- o .: "color"
    technique <- o .: "technique"
    source <- o .: "source"
    choke <- o .: "choke"
    size <- o .: "size"
    range <- o .: "range"
    jitter <- o .: "jitter"
    noise <- o .: "noise"
    gradient <- o .:? "gradient"
    useGradient <- o .:? "useGradient"
    contour <- o .:? "contour"
    antiAliased <- o .:? "antiAliased"
    let base = BaseLayerStyle enabled blendMode opacity
    return (InnerGlowStyle base color gradient useGradient technique source choke size range jitter noise contour antiAliased)

-- ============================================================================
-- BEVEL AND EMBOSS
-- ============================================================================

-- | Bevel style type
data BevelStyle
  = BevelStyleOuterBevel -- Bevel on outside edge
  | BevelStyleInnerBevel -- Bevel on inside edge
  | BevelStyleEmboss -- Raised emboss
  | BevelStylePillowEmboss -- Sunken edges
  | BevelStyleStrokeEmboss -- Bevel on stroke
  deriving (Eq, Show, Generic)

instance ToJSON BevelStyle where
  toJSON BevelStyleOuterBevel = "outer-bevel"
  toJSON BevelStyleInnerBevel = "inner-bevel"
  toJSON BevelStyleEmboss = "emboss"
  toJSON BevelStylePillowEmboss = "pillow-emboss"
  toJSON BevelStyleStrokeEmboss = "stroke-emboss"

instance FromJSON BevelStyle where
  parseJSON = withText "BevelStyle" $ \s ->
    case s of
      _ | s == T.pack "outer-bevel" -> return BevelStyleOuterBevel
      _ | s == T.pack "inner-bevel" -> return BevelStyleInnerBevel
      _ | s == T.pack "emboss" -> return BevelStyleEmboss
      _ | s == T.pack "pillow-emboss" -> return BevelStylePillowEmboss
      _ | s == T.pack "stroke-emboss" -> return BevelStyleStrokeEmboss
      _ -> fail "Invalid BevelStyle"

-- | Bevel rendering technique
data BevelTechnique
  = BevelTechniqueSmooth
  | BevelTechniqueChiselHard
  | BevelTechniqueChiselSoft
  deriving (Eq, Show, Generic)

instance ToJSON BevelTechnique where
  toJSON BevelTechniqueSmooth = "smooth"
  toJSON BevelTechniqueChiselHard = "chisel-hard"
  toJSON BevelTechniqueChiselSoft = "chisel-soft"

instance FromJSON BevelTechnique where
  parseJSON = withText "BevelTechnique" $ \s ->
    case s of
      _ | s == T.pack "smooth" -> return BevelTechniqueSmooth
      _ | s == T.pack "chisel-hard" -> return BevelTechniqueChiselHard
      _ | s == T.pack "chisel-soft" -> return BevelTechniqueChiselSoft
      _ -> fail "Invalid BevelTechnique"

-- | Bevel direction
data BevelDirection
  = BevelDirectionUp
  | BevelDirectionDown
  deriving (Eq, Show, Generic)

instance ToJSON BevelDirection where
  toJSON BevelDirectionUp = "up"
  toJSON BevelDirectionDown = "down"

instance FromJSON BevelDirection where
  parseJSON = withText "BevelDirection" $ \s ->
    case s of
      _ | s == T.pack "up" -> return BevelDirectionUp
      _ | s == T.pack "down" -> return BevelDirectionDown
      _ -> fail "Invalid BevelDirection"

-- | Bevel and emboss style
data BevelEmbossStyle = BevelEmbossStyle
  { bevelEmbossStyleBase :: BaseLayerStyle,
    bevelEmbossStyleStyle :: BevelStyle,
    bevelEmbossStyleTechnique :: BevelTechnique,
    bevelEmbossStyleDepth :: AnimatableProperty Double, -- Depth intensity (1-1000%)
    bevelEmbossStyleDirection :: BevelDirection,
    bevelEmbossStyleSize :: AnimatableProperty Double, -- Size/thickness (pixels)
    bevelEmbossStyleSoften :: AnimatableProperty Double, -- Soften edges (pixels)
    bevelEmbossStyleAngle :: AnimatableProperty Double, -- Light source angle (0-360 degrees)
    bevelEmbossStyleUseGlobalLight :: Bool,
    bevelEmbossStyleAltitude :: AnimatableProperty Double, -- Light altitude/elevation (0-90 degrees)
    bevelEmbossStyleGlossContour :: Maybe ContourCurve,
    bevelEmbossStyleGlossAntiAliased :: Maybe Bool,
    bevelEmbossStyleHighlightMode :: BlendMode,
    bevelEmbossStyleHighlightColor :: AnimatableProperty RGBAColor,
    bevelEmbossStyleHighlightOpacity :: AnimatableProperty Double, -- Highlight opacity (0-100%)
    bevelEmbossStyleShadowMode :: BlendMode,
    bevelEmbossStyleShadowColor :: AnimatableProperty RGBAColor,
    bevelEmbossStyleShadowOpacity :: AnimatableProperty Double, -- Shadow opacity (0-100%)
    bevelEmbossStyleContourEnabled :: Maybe Bool,
    bevelEmbossStyleContour :: Maybe ContourCurve,
    bevelEmbossStyleContourAntiAliased :: Maybe Bool,
    bevelEmbossStyleContourRange :: Maybe (AnimatableProperty Double), -- Contour range (0-100%)
    bevelEmbossStyleTextureEnabled :: Maybe Bool,
    bevelEmbossStyleTexturePattern :: Maybe Text, -- Texture pattern (pattern ID or asset ID)
    bevelEmbossStyleTextureScale :: Maybe (AnimatableProperty Double), -- Texture scale (1-1000%)
    bevelEmbossStyleTextureDepth :: Maybe (AnimatableProperty Double), -- Texture depth (-1000 to 1000%)
    bevelEmbossStyleTextureInvert :: Maybe Bool,
    bevelEmbossStyleTextureLinkWithLayer :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON BevelEmbossStyle where
  toJSON (BevelEmbossStyle base style technique depth direction size soften angle useGlobalLight altitude glossContour glossAntiAliased highlightMode highlightColor highlightOpacity shadowMode shadowColor shadowOpacity contourEnabled contour contourAntiAliased contourRange textureEnabled texturePattern textureScale textureDepth textureInvert textureLinkWithLayer) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "style" .= style,
            "technique" .= technique,
            "depth" .= depth,
            "direction" .= direction,
            "size" .= size,
            "soften" .= soften,
            "angle" .= angle,
            "useGlobalLight" .= useGlobalLight,
            "altitude" .= altitude,
            "highlightMode" .= highlightMode,
            "highlightColor" .= highlightColor,
            "highlightOpacity" .= highlightOpacity,
            "shadowMode" .= shadowMode,
            "shadowColor" .= shadowColor,
            "shadowOpacity" .= shadowOpacity
          ],
          maybe [] (\gc -> ["glossContour" .= gc]) glossContour,
          maybe [] (\gaa -> ["glossAntiAliased" .= gaa]) glossAntiAliased,
          maybe [] (\ce -> ["contourEnabled" .= ce]) contourEnabled,
          maybe [] (\c -> ["contour" .= c]) contour,
          maybe [] (\caa -> ["contourAntiAliased" .= caa]) contourAntiAliased,
          maybe [] (\cr -> ["contourRange" .= cr]) contourRange,
          maybe [] (\te -> ["textureEnabled" .= te]) textureEnabled,
          maybe [] (\tp -> ["texturePattern" .= tp]) texturePattern,
          maybe [] (\ts -> ["textureScale" .= ts]) textureScale,
          maybe [] (\td -> ["textureDepth" .= td]) textureDepth,
          maybe [] (\ti -> ["textureInvert" .= ti]) textureInvert,
          maybe [] (\tl -> ["textureLinkWithLayer" .= tl]) textureLinkWithLayer
        ]

instance FromJSON BevelEmbossStyle where
  parseJSON = withObject "BevelEmbossStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    style <- o .: "style"
    technique <- o .: "technique"
    depth <- o .: "depth"
    direction <- o .: "direction"
    size <- o .: "size"
    soften <- o .: "soften"
    angle <- o .: "angle"
    useGlobalLight <- o .: "useGlobalLight"
    altitude <- o .: "altitude"
    highlightMode <- o .: "highlightMode"
    highlightColor <- o .: "highlightColor"
    highlightOpacity <- o .: "highlightOpacity"
    shadowMode <- o .: "shadowMode"
    shadowColor <- o .: "shadowColor"
    shadowOpacity <- o .: "shadowOpacity"
    glossContour <- o .:? "glossContour"
    glossAntiAliased <- o .:? "glossAntiAliased"
    contourEnabled <- o .:? "contourEnabled"
    contour <- o .:? "contour"
    contourAntiAliased <- o .:? "contourAntiAliased"
    contourRange <- o .:? "contourRange"
    textureEnabled <- o .:? "textureEnabled"
    texturePattern <- o .:? "texturePattern"
    textureScale <- o .:? "textureScale"
    textureDepth <- o .:? "textureDepth"
    textureInvert <- o .:? "textureInvert"
    textureLinkWithLayer <- o .:? "textureLinkWithLayer"
    let base = BaseLayerStyle enabled blendMode opacity
    return (BevelEmbossStyle base style technique depth direction size soften angle useGlobalLight altitude glossContour glossAntiAliased highlightMode highlightColor highlightOpacity shadowMode shadowColor shadowOpacity contourEnabled contour contourAntiAliased contourRange textureEnabled texturePattern textureScale textureDepth textureInvert textureLinkWithLayer)

-- ============================================================================
-- SATIN
-- ============================================================================

-- | Satin style
data SatinStyle = SatinStyle
  { satinStyleBase :: BaseLayerStyle,
    satinStyleColor :: AnimatableProperty RGBAColor,
    satinStyleAngle :: AnimatableProperty Double, -- Light angle (0-360 degrees)
    satinStyleDistance :: AnimatableProperty Double, -- Distance of effect (pixels)
    satinStyleSize :: AnimatableProperty Double, -- Size/blur (pixels)
    satinStyleContour :: Maybe ContourCurve,
    satinStyleAntiAliased :: Maybe Bool,
    satinStyleInvert :: Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON SatinStyle where
  toJSON (SatinStyle base color angle distance size contour antiAliased invert) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "color" .= color,
            "angle" .= angle,
            "distance" .= distance,
            "size" .= size,
            "invert" .= invert
          ],
          maybe [] (\c -> ["contour" .= c]) contour,
          maybe [] (\aa -> ["antiAliased" .= aa]) antiAliased
        ]

instance FromJSON SatinStyle where
  parseJSON = withObject "SatinStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    color <- o .: "color"
    angle <- o .: "angle"
    distance <- o .: "distance"
    size <- o .: "size"
    invert <- o .: "invert"
    contour <- o .:? "contour"
    antiAliased <- o .:? "antiAliased"
    let base = BaseLayerStyle enabled blendMode opacity
    return (SatinStyle base color angle distance size contour antiAliased invert)

-- ============================================================================
-- COLOR OVERLAY
-- ============================================================================

-- | Color overlay style
data ColorOverlayStyle = ColorOverlayStyle
  { colorOverlayStyleBase :: BaseLayerStyle,
    colorOverlayStyleColor :: AnimatableProperty RGBAColor
  }
  deriving (Eq, Show, Generic)

instance ToJSON ColorOverlayStyle where
  toJSON (ColorOverlayStyle base color) =
    object
      [ "enabled" .= baseLayerStyleEnabled base,
        "blendMode" .= baseLayerStyleBlendMode base,
        "opacity" .= baseLayerStyleOpacity base,
        "color" .= color
      ]

instance FromJSON ColorOverlayStyle where
  parseJSON = withObject "ColorOverlayStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    color <- o .: "color"
    let base = BaseLayerStyle enabled blendMode opacity
    return (ColorOverlayStyle base color)

-- ============================================================================
-- GRADIENT OVERLAY
-- ============================================================================

-- | Gradient overlay style type
data GradientOverlayType
  = GradientOverlayTypeLinear
  | GradientOverlayTypeRadial
  | GradientOverlayTypeAngle
  | GradientOverlayTypeReflected
  | GradientOverlayTypeDiamond
  deriving (Eq, Show, Generic)

instance ToJSON GradientOverlayType where
  toJSON GradientOverlayTypeLinear = "linear"
  toJSON GradientOverlayTypeRadial = "radial"
  toJSON GradientOverlayTypeAngle = "angle"
  toJSON GradientOverlayTypeReflected = "reflected"
  toJSON GradientOverlayTypeDiamond = "diamond"

instance FromJSON GradientOverlayType where
  parseJSON = withText "GradientOverlayType" $ \s ->
    case s of
      _ | s == T.pack "linear" -> return GradientOverlayTypeLinear
      _ | s == T.pack "radial" -> return GradientOverlayTypeRadial
      _ | s == T.pack "angle" -> return GradientOverlayTypeAngle
      _ | s == T.pack "reflected" -> return GradientOverlayTypeReflected
      _ | s == T.pack "diamond" -> return GradientOverlayTypeDiamond
      _ -> fail "Invalid GradientOverlayType"

-- | Gradient overlay style
data GradientOverlayStyle = GradientOverlayStyle
  { gradientOverlayStyleBase :: BaseLayerStyle,
    gradientOverlayStyleGradient :: AnimatableProperty GradientDef,
    gradientOverlayStyleStyle :: GradientOverlayType,
    gradientOverlayStyleAngle :: AnimatableProperty Double, -- Angle for linear/angle gradients (degrees)
    gradientOverlayStyleScale :: AnimatableProperty Double, -- Scale of gradient (10-150%)
    gradientOverlayStyleAlignWithLayer :: Bool,
    gradientOverlayStyleReverse :: Bool,
    gradientOverlayStyleOffset :: AnimatableProperty Point2D, -- Gradient center offset from layer center
    gradientOverlayStyleDither :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON GradientOverlayStyle where
  toJSON (GradientOverlayStyle base gradient style angle scale alignWithLayer reverse offset dither) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "gradient" .= gradient,
            "style" .= style,
            "angle" .= angle,
            "scale" .= scale,
            "alignWithLayer" .= alignWithLayer,
            "reverse" .= reverse,
            "offset" .= offset
          ],
          maybe [] (\d -> ["dither" .= d]) dither
        ]

instance FromJSON GradientOverlayStyle where
  parseJSON = withObject "GradientOverlayStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    gradient <- o .: "gradient"
    style <- o .: "style"
    angle <- o .: "angle"
    scale <- o .: "scale"
    alignWithLayer <- o .: "alignWithLayer"
    reverse <- o .: "reverse"
    offset <- o .: "offset"
    dither <- o .:? "dither"
    let base = BaseLayerStyle enabled blendMode opacity
    return (GradientOverlayStyle base gradient style angle scale alignWithLayer reverse offset dither)

-- ============================================================================
-- PATTERN OVERLAY
-- ============================================================================

-- | Pattern overlay style
data PatternOverlayStyle = PatternOverlayStyle
  { patternOverlayStyleBase :: BaseLayerStyle,
    patternOverlayStylePattern :: Text, -- Pattern asset ID or URL
    patternOverlayStyleScale :: AnimatableProperty Double, -- Scale of pattern (1-1000%)
    patternOverlayStyleAngle :: AnimatableProperty Double, -- Angle of pattern rotation (degrees)
    patternOverlayStyleLinkWithLayer :: Bool,
    patternOverlayStyleSnapToOrigin :: Bool,
    patternOverlayStyleOffset :: AnimatableProperty Point2D -- Pattern offset from origin
  }
  deriving (Eq, Show, Generic)

instance ToJSON PatternOverlayStyle where
  toJSON (PatternOverlayStyle base pattern scale angle linkWithLayer snapToOrigin offset) =
    object
      [ "enabled" .= baseLayerStyleEnabled base,
        "blendMode" .= baseLayerStyleBlendMode base,
        "opacity" .= baseLayerStyleOpacity base,
        "pattern" .= pattern,
        "scale" .= scale,
        "angle" .= angle,
        "linkWithLayer" .= linkWithLayer,
        "snapToOrigin" .= snapToOrigin,
        "offset" .= offset
      ]

instance FromJSON PatternOverlayStyle where
  parseJSON = withObject "PatternOverlayStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    pattern <- o .: "pattern"
    scale <- o .: "scale"
    angle <- o .: "angle"
    linkWithLayer <- o .: "linkWithLayer"
    snapToOrigin <- o .: "snapToOrigin"
    offset <- o .: "offset"
    let base = BaseLayerStyle enabled blendMode opacity
    return (PatternOverlayStyle base pattern scale angle linkWithLayer snapToOrigin offset)

-- ============================================================================
-- STROKE
-- ============================================================================

-- | Stroke position relative to edge
data StrokePosition
  = StrokePositionOutside
  | StrokePositionInside
  | StrokePositionCenter
  deriving (Eq, Show, Generic)

instance ToJSON StrokePosition where
  toJSON StrokePositionOutside = "outside"
  toJSON StrokePositionInside = "inside"
  toJSON StrokePositionCenter = "center"

instance FromJSON StrokePosition where
  parseJSON = withText "StrokePosition" $ \s ->
    case s of
      _ | s == T.pack "outside" -> return StrokePositionOutside
      _ | s == T.pack "inside" -> return StrokePositionInside
      _ | s == T.pack "center" -> return StrokePositionCenter
      _ -> fail "Invalid StrokePosition"

-- | Stroke fill type
data StrokeFillType
  = StrokeFillTypeColor
  | StrokeFillTypeGradient
  | StrokeFillTypePattern
  deriving (Eq, Show, Generic)

instance ToJSON StrokeFillType where
  toJSON StrokeFillTypeColor = "color"
  toJSON StrokeFillTypeGradient = "gradient"
  toJSON StrokeFillTypePattern = "pattern"

instance FromJSON StrokeFillType where
  parseJSON = withText "StrokeFillType" $ \s ->
    case s of
      _ | s == T.pack "color" -> return StrokeFillTypeColor
      _ | s == T.pack "gradient" -> return StrokeFillTypeGradient
      _ | s == T.pack "pattern" -> return StrokeFillTypePattern
      _ -> fail "Invalid StrokeFillType"

-- | Stroke style
data StrokeStyle = StrokeStyle
  { strokeStyleBase :: BaseLayerStyle,
    strokeStyleColor :: AnimatableProperty RGBAColor, -- Stroke color (if fillType is 'color')
    strokeStyleGradient :: Maybe GradientDef, -- Stroke gradient (if fillType is 'gradient')
    strokeStylePattern :: Maybe Text, -- Stroke pattern asset ID (if fillType is 'pattern')
    strokeStyleFillType :: StrokeFillType,
    strokeStyleSize :: AnimatableProperty Double, -- Stroke width (pixels)
    strokeStylePosition :: StrokePosition,
    strokeStyleGradientAngle :: Maybe (AnimatableProperty Double), -- Gradient angle (if using gradient)
    strokeStyleGradientScale :: Maybe (AnimatableProperty Double), -- Gradient scale (if using gradient)
    strokeStylePatternScale :: Maybe (AnimatableProperty Double), -- Pattern scale (if using pattern)
    strokeStylePatternLinkWithLayer :: Maybe Bool
  }
  deriving (Eq, Show, Generic)

instance ToJSON StrokeStyle where
  toJSON (StrokeStyle base color gradient pattern fillType size position gradientAngle gradientScale patternScale patternLinkWithLayer) =
    object $
      concat
        [ [ "enabled" .= baseLayerStyleEnabled base,
            "blendMode" .= baseLayerStyleBlendMode base,
            "opacity" .= baseLayerStyleOpacity base,
            "color" .= color,
            "fillType" .= fillType,
            "size" .= size,
            "position" .= position
          ],
          maybe [] (\g -> ["gradient" .= g]) gradient,
          maybe [] (\p -> ["pattern" .= p]) pattern,
          maybe [] (\ga -> ["gradientAngle" .= ga]) gradientAngle,
          maybe [] (\gs -> ["gradientScale" .= gs]) gradientScale,
          maybe [] (\ps -> ["patternScale" .= ps]) patternScale,
          maybe [] (\pl -> ["patternLinkWithLayer" .= pl]) patternLinkWithLayer
        ]

instance FromJSON StrokeStyle where
  parseJSON = withObject "StrokeStyle" $ \o -> do
    enabled <- o .: "enabled"
    blendMode <- o .: "blendMode"
    opacity <- o .: "opacity"
    color <- o .: "color"
    fillType <- o .: "fillType"
    size <- o .: "size"
    position <- o .: "position"
    gradient <- o .:? "gradient"
    pattern <- o .:? "pattern"
    gradientAngle <- o .:? "gradientAngle"
    gradientScale <- o .:? "gradientScale"
    patternScale <- o .:? "patternScale"
    patternLinkWithLayer <- o .:? "patternLinkWithLayer"
    let base = BaseLayerStyle enabled blendMode opacity
    return (StrokeStyle base color gradient pattern fillType size position gradientAngle gradientScale patternScale patternLinkWithLayer)

-- ============================================================================
-- STYLE BLENDING OPTIONS
-- ============================================================================

-- | Channel blend options
data ChannelBlendRange = ChannelBlendRange
  { channelBlendRangeInputBlack :: Double, -- Black input level (0-255)
    channelBlendRangeInputWhite :: Double, -- White input level (0-255)
    channelBlendRangeOutputBlack :: Double, -- Black output level (0-255)
    channelBlendRangeOutputWhite :: Double -- White output level (0-255)
  }
  deriving (Eq, Show, Generic)

instance ToJSON ChannelBlendRange where
  toJSON (ChannelBlendRange inputBlack inputWhite outputBlack outputWhite) =
    object
      [ "inputBlack" .= inputBlack,
        "inputWhite" .= inputWhite,
        "outputBlack" .= outputBlack,
        "outputWhite" .= outputWhite
      ]

instance FromJSON ChannelBlendRange where
  parseJSON = withObject "ChannelBlendRange" $ \o -> do
    inputBlack <- o .: "inputBlack"
    inputWhite <- o .: "inputWhite"
    outputBlack <- o .: "outputBlack"
    outputWhite <- o .: "outputWhite"
    if validateFinite inputBlack && validateFinite inputWhite &&
       validateFinite outputBlack && validateFinite outputWhite &&
       validateNonNegative inputBlack && validateNonNegative inputWhite &&
       validateNonNegative outputBlack && validateNonNegative outputWhite &&
       inputBlack <= 255 && inputWhite <= 255 &&
       outputBlack <= 255 && outputWhite <= 255
      then return (ChannelBlendRange inputBlack inputWhite outputBlack outputWhite)
      else fail "ChannelBlendRange: all values must be in [0,255]"

-- | Style blending options
data StyleBlendingOptions = StyleBlendingOptions
  { styleBlendingOptionsFillOpacity :: AnimatableProperty Double, -- Fill opacity - affects layer content but NOT styles (0-100%)
    styleBlendingOptionsBlendInteriorStylesAsGroup :: Bool,
    styleBlendingOptionsBlendClippedLayersAsGroup :: Maybe Bool,
    styleBlendingOptionsTransparencyShapesLayer :: Maybe Bool, -- Transparency shapes layer (knockout)
    styleBlendingOptionsLayerMaskHidesEffects :: Maybe Bool,
    styleBlendingOptionsVectorMaskHidesEffects :: Maybe Bool,
    styleBlendingOptionsBlendIfEnabled :: Maybe Bool, -- Enable Blend If sliders
    styleBlendingOptionsThisLayerRange :: Maybe ChannelBlendRange, -- This layer's blend range
    styleBlendingOptionsUnderlyingLayerRange :: Maybe ChannelBlendRange -- Underlying layer's blend range
  }
  deriving (Eq, Show, Generic)

instance ToJSON StyleBlendingOptions where
  toJSON (StyleBlendingOptions fillOpacity blendInteriorStylesAsGroup blendClippedLayersAsGroup transparencyShapesLayer layerMaskHidesEffects vectorMaskHidesEffects blendIfEnabled thisLayerRange underlyingLayerRange) =
    object $
      concat
        [ [ "fillOpacity" .= fillOpacity,
            "blendInteriorStylesAsGroup" .= blendInteriorStylesAsGroup
          ],
          maybe [] (\b -> ["blendClippedLayersAsGroup" .= b]) blendClippedLayersAsGroup,
          maybe [] (\t -> ["transparencyShapesLayer" .= t]) transparencyShapesLayer,
          maybe [] (\l -> ["layerMaskHidesEffects" .= l]) layerMaskHidesEffects,
          maybe [] (\v -> ["vectorMaskHidesEffects" .= v]) vectorMaskHidesEffects,
          maybe [] (\b -> ["blendIfEnabled" .= b]) blendIfEnabled,
          maybe [] (\t -> ["thisLayerRange" .= t]) thisLayerRange,
          maybe [] (\u -> ["underlyingLayerRange" .= u]) underlyingLayerRange
        ]

instance FromJSON StyleBlendingOptions where
  parseJSON = withObject "StyleBlendingOptions" $ \o -> do
    fillOpacity <- o .: "fillOpacity"
    blendInteriorStylesAsGroup <- o .: "blendInteriorStylesAsGroup"
    blendClippedLayersAsGroup <- o .:? "blendClippedLayersAsGroup"
    transparencyShapesLayer <- o .:? "transparencyShapesLayer"
    layerMaskHidesEffects <- o .:? "layerMaskHidesEffects"
    vectorMaskHidesEffects <- o .:? "vectorMaskHidesEffects"
    blendIfEnabled <- o .:? "blendIfEnabled"
    thisLayerRange <- o .:? "thisLayerRange"
    underlyingLayerRange <- o .:? "underlyingLayerRange"
    return (StyleBlendingOptions fillOpacity blendInteriorStylesAsGroup blendClippedLayersAsGroup transparencyShapesLayer layerMaskHidesEffects vectorMaskHidesEffects blendIfEnabled thisLayerRange underlyingLayerRange)

-- ============================================================================
-- MAIN LAYER STYLES CONTAINER
-- ============================================================================

-- | Complete Layer Styles definition
-- Renders in fixed order (back to front):
-- 1. Drop Shadow (behind layer)
-- 2. Inner Shadow
-- 3. Outer Glow (behind layer)
-- 4. Inner Glow
-- 5. Bevel and Emboss
-- 6. Satin
-- 7. Color Overlay
-- 8. Gradient Overlay
-- 9. Stroke (on top)
data LayerStyles = LayerStyles
  { layerStylesEnabled :: Bool, -- Master enable/disable for all layer styles
    layerStylesBlendingOptions :: Maybe StyleBlendingOptions, -- Advanced blending options (Fill Opacity, etc.)
    layerStylesDropShadow :: Maybe DropShadowStyle,
    layerStylesInnerShadow :: Maybe InnerShadowStyle,
    layerStylesOuterGlow :: Maybe OuterGlowStyle,
    layerStylesInnerGlow :: Maybe InnerGlowStyle,
    layerStylesBevelEmboss :: Maybe BevelEmbossStyle,
    layerStylesSatin :: Maybe SatinStyle,
    layerStylesColorOverlay :: Maybe ColorOverlayStyle,
    layerStylesGradientOverlay :: Maybe GradientOverlayStyle,
    layerStylesPatternOverlay :: Maybe PatternOverlayStyle,
    layerStylesStroke :: Maybe StrokeStyle
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerStyles where
  toJSON (LayerStyles enabled blendingOptions dropShadow innerShadow outerGlow innerGlow bevelEmboss satin colorOverlay gradientOverlay patternOverlay stroke) =
    object $
      concat
        [ [ "enabled" .= enabled
          ],
          maybe [] (\bo -> ["blendingOptions" .= bo]) blendingOptions,
          maybe [] (\ds -> ["dropShadow" .= ds]) dropShadow,
          maybe [] (\is -> ["innerShadow" .= is]) innerShadow,
          maybe [] (\og -> ["outerGlow" .= og]) outerGlow,
          maybe [] (\ig -> ["innerGlow" .= ig]) innerGlow,
          maybe [] (\be -> ["bevelEmboss" .= be]) bevelEmboss,
          maybe [] (\s -> ["satin" .= s]) satin,
          maybe [] (\co -> ["colorOverlay" .= co]) colorOverlay,
          maybe [] (\go -> ["gradientOverlay" .= go]) gradientOverlay,
          maybe [] (\po -> ["patternOverlay" .= po]) patternOverlay,
          maybe [] (\st -> ["stroke" .= st]) stroke
        ]

instance FromJSON LayerStyles where
  parseJSON = withObject "LayerStyles" $ \o -> do
    enabled <- o .: "enabled"
    blendingOptions <- o .:? "blendingOptions"
    dropShadow <- o .:? "dropShadow"
    innerShadow <- o .:? "innerShadow"
    outerGlow <- o .:? "outerGlow"
    innerGlow <- o .:? "innerGlow"
    bevelEmboss <- o .:? "bevelEmboss"
    satin <- o .:? "satin"
    colorOverlay <- o .:? "colorOverlay"
    gradientOverlay <- o .:? "gradientOverlay"
    patternOverlay <- o .:? "patternOverlay"
    stroke <- o .:? "stroke"
    return (LayerStyles enabled blendingOptions dropShadow innerShadow outerGlow innerGlow bevelEmboss satin colorOverlay gradientOverlay patternOverlay stroke)

-- ============================================================================
-- GLOBAL LIGHT
-- ============================================================================

-- | Global Light settings for a composition
-- Styles with useGlobalLight=true share these values
data GlobalLightSettings = GlobalLightSettings
  { globalLightSettingsAngle :: AnimatableProperty Double, -- Global light angle (0-360 degrees)
    globalLightSettingsAltitude :: AnimatableProperty Double -- Global light altitude (0-90 degrees)
  }
  deriving (Eq, Show, Generic)

instance ToJSON GlobalLightSettings where
  toJSON (GlobalLightSettings angle altitude) =
    object
      [ "angle" .= angle,
        "altitude" .= altitude
      ]

instance FromJSON GlobalLightSettings where
  parseJSON = withObject "GlobalLightSettings" $ \o -> do
    angle <- o .: "angle"
    altitude <- o .: "altitude"
    return (GlobalLightSettings angle altitude)
