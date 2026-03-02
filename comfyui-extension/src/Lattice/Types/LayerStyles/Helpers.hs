-- |
-- Module      : Lattice.Types.LayerStyles.Helpers
-- Description : Helper functions for creating default layer style instances
-- 
-- Migrated from ui/src/types/layerStyles.ts factory functions
-- Pure functions for creating default layer style configurations
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.LayerStyles.Helpers
  ( -- Utility functions
    createStyleProperty,
    createRGBA,
    -- Style factories
    createDefaultLayerStyles,
    createDefaultDropShadow,
    createDefaultInnerShadow,
    createDefaultOuterGlow,
    createDefaultInnerGlow,
    createDefaultBevelEmboss,
    createDefaultSatin,
    createDefaultColorOverlay,
    createDefaultGradientOverlay,
    createDefaultStroke,
    -- Blending options factory
    createDefaultBlendingOptions,
    -- Global light factory
    createDefaultGlobalLight,
  )
where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
    createAnimatableProperty,
  )
import Lattice.Types.LayerDataShapes (Point2D (..))
import Lattice.Types.LayerStyles.Core
  ( BaseLayerStyle (..),
    BevelDirection (..),
    BevelEmbossStyle (..),
    BevelStyle (..),
    BevelTechnique (..),
    ChannelBlendRange (..),
    ColorOverlayStyle (..),
    ContourCurve (..),
    DropShadowStyle (..),
    GlobalLightSettings (..),
    GlowTechnique (..),
    GradientDef (..),
    GradientOverlayStyle (..),
    GradientOverlayType (..),
    GradientStop (..),
    GradientType (..),
    InnerGlowSource (..),
    InnerGlowStyle (..),
    InnerShadowStyle (..),
    LayerStyles (..),
    OuterGlowStyle (..),
    RGBAColor (..),
    SatinStyle (..),
    StrokeFillType (..),
    StrokePosition (..),
    StrokeStyle (..),
    StyleBlendingOptions (..),
  )
import Lattice.Types.Primitives (BlendMode (..))

-- ============================================================================
-- UTILITY FUNCTIONS
-- ============================================================================

-- | Create a default animatable property for layer styles
-- NOTE: ID generation should be handled by caller (no IO in pure functions)
createStyleProperty ::
  Text ->
  a ->
  PropertyType ->
  AnimatableProperty a
createStyleProperty name value propType =
  createAnimatableProperty
    ("style-" <> name <> "-prop")
    name
    value
    propType
    Nothing

-- | Create default RGBA color
createRGBA :: Double -> Double -> Double -> Double -> RGBAColor
createRGBA r g b a = RGBAColor r g b a

-- ============================================================================
-- STYLE FACTORIES
-- ============================================================================

-- | Create default layer styles (all disabled)
createDefaultLayerStyles :: LayerStyles
createDefaultLayerStyles =
  LayerStyles
    { layerStylesEnabled = False,
      layerStylesBlendingOptions = Nothing,
      layerStylesDropShadow = Nothing,
      layerStylesInnerShadow = Nothing,
      layerStylesOuterGlow = Nothing,
      layerStylesInnerGlow = Nothing,
      layerStylesBevelEmboss = Nothing,
      layerStylesSatin = Nothing,
      layerStylesColorOverlay = Nothing,
      layerStylesGradientOverlay = Nothing,
      layerStylesPatternOverlay = Nothing,
      layerStylesStroke = Nothing
    }

-- | Create default drop shadow style
createDefaultDropShadow :: DropShadowStyle
createDefaultDropShadow =
  DropShadowStyle
    { dropShadowStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendMultiply,
            baseLayerStyleOpacity = createStyleProperty "opacity" 75.0 PropertyTypeNumber
          },
      dropShadowStyleColor =
        createStyleProperty "color" (createRGBA 0.0 0.0 0.0 1.0) PropertyTypeColor,
      dropShadowStyleAngle = createStyleProperty "angle" 120.0 PropertyTypeNumber,
      dropShadowStyleUseGlobalLight = True,
      dropShadowStyleDistance = createStyleProperty "distance" 5.0 PropertyTypeNumber,
      dropShadowStyleSpread = createStyleProperty "spread" 0.0 PropertyTypeNumber,
      dropShadowStyleSize = createStyleProperty "size" 5.0 PropertyTypeNumber,
      dropShadowStyleNoise = createStyleProperty "noise" 0.0 PropertyTypeNumber,
      dropShadowStyleContour = Nothing,
      dropShadowStyleAntiAliased = Nothing,
      dropShadowStyleLayerKnocksOut = Just True
    }

-- | Create default inner shadow style
createDefaultInnerShadow :: InnerShadowStyle
createDefaultInnerShadow =
  InnerShadowStyle
    { innerShadowStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendMultiply,
            baseLayerStyleOpacity = createStyleProperty "opacity" 75.0 PropertyTypeNumber
          },
      innerShadowStyleColor =
        createStyleProperty "color" (createRGBA 0.0 0.0 0.0 1.0) PropertyTypeColor,
      innerShadowStyleAngle = createStyleProperty "angle" 120.0 PropertyTypeNumber,
      innerShadowStyleUseGlobalLight = True,
      innerShadowStyleDistance = createStyleProperty "distance" 5.0 PropertyTypeNumber,
      innerShadowStyleChoke = createStyleProperty "choke" 0.0 PropertyTypeNumber,
      innerShadowStyleSize = createStyleProperty "size" 5.0 PropertyTypeNumber,
      innerShadowStyleNoise = createStyleProperty "noise" 0.0 PropertyTypeNumber,
      innerShadowStyleContour = Nothing,
      innerShadowStyleAntiAliased = Nothing
    }

-- | Create default outer glow style
createDefaultOuterGlow :: OuterGlowStyle
createDefaultOuterGlow =
  OuterGlowStyle
    { outerGlowStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendScreen,
            baseLayerStyleOpacity = createStyleProperty "opacity" 75.0 PropertyTypeNumber
          },
      outerGlowStyleColor =
        createStyleProperty "color" (createRGBA 255.0 255.0 190.0 1.0) PropertyTypeColor,
      outerGlowStyleGradient = Nothing,
      outerGlowStyleUseGradient = Nothing,
      outerGlowStyleTechnique = GlowTechniqueSofter,
      outerGlowStyleSpread = createStyleProperty "spread" 0.0 PropertyTypeNumber,
      outerGlowStyleSize = createStyleProperty "size" 5.0 PropertyTypeNumber,
      outerGlowStyleRange = createStyleProperty "range" 50.0 PropertyTypeNumber,
      outerGlowStyleJitter = createStyleProperty "jitter" 0.0 PropertyTypeNumber,
      outerGlowStyleNoise = createStyleProperty "noise" 0.0 PropertyTypeNumber,
      outerGlowStyleContour = Nothing,
      outerGlowStyleAntiAliased = Nothing
    }

-- | Create default inner glow style
createDefaultInnerGlow :: InnerGlowStyle
createDefaultInnerGlow =
  InnerGlowStyle
    { innerGlowStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendScreen,
            baseLayerStyleOpacity = createStyleProperty "opacity" 75.0 PropertyTypeNumber
          },
      innerGlowStyleColor =
        createStyleProperty "color" (createRGBA 255.0 255.0 190.0 1.0) PropertyTypeColor,
      innerGlowStyleGradient = Nothing,
      innerGlowStyleUseGradient = Nothing,
      innerGlowStyleTechnique = GlowTechniqueSofter,
      innerGlowStyleSource = InnerGlowSourceEdge,
      innerGlowStyleChoke = createStyleProperty "choke" 0.0 PropertyTypeNumber,
      innerGlowStyleSize = createStyleProperty "size" 5.0 PropertyTypeNumber,
      innerGlowStyleRange = createStyleProperty "range" 50.0 PropertyTypeNumber,
      innerGlowStyleJitter = createStyleProperty "jitter" 0.0 PropertyTypeNumber,
      innerGlowStyleNoise = createStyleProperty "noise" 0.0 PropertyTypeNumber,
      innerGlowStyleContour = Nothing,
      innerGlowStyleAntiAliased = Nothing
    }

-- | Create default bevel and emboss style
createDefaultBevelEmboss :: BevelEmbossStyle
createDefaultBevelEmboss =
  BevelEmbossStyle
    { bevelEmbossStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendNormal,
            baseLayerStyleOpacity = createStyleProperty "opacity" 100.0 PropertyTypeNumber
          },
      bevelEmbossStyleStyle = BevelStyleInnerBevel,
      bevelEmbossStyleTechnique = BevelTechniqueSmooth,
      bevelEmbossStyleDepth = createStyleProperty "depth" 100.0 PropertyTypeNumber,
      bevelEmbossStyleDirection = BevelDirectionUp,
      bevelEmbossStyleSize = createStyleProperty "size" 5.0 PropertyTypeNumber,
      bevelEmbossStyleSoften = createStyleProperty "soften" 0.0 PropertyTypeNumber,
      bevelEmbossStyleAngle = createStyleProperty "angle" 120.0 PropertyTypeNumber,
      bevelEmbossStyleUseGlobalLight = True,
      bevelEmbossStyleAltitude = createStyleProperty "altitude" 30.0 PropertyTypeNumber,
      bevelEmbossStyleGlossContour = Nothing,
      bevelEmbossStyleGlossAntiAliased = Nothing,
      bevelEmbossStyleHighlightMode = BlendScreen,
      bevelEmbossStyleHighlightColor =
        createStyleProperty "highlightColor" (createRGBA 255.0 255.0 255.0 1.0) PropertyTypeColor,
      bevelEmbossStyleHighlightOpacity =
        createStyleProperty "highlightOpacity" 75.0 PropertyTypeNumber,
      bevelEmbossStyleShadowMode = BlendMultiply,
      bevelEmbossStyleShadowColor =
        createStyleProperty "shadowColor" (createRGBA 0.0 0.0 0.0 1.0) PropertyTypeColor,
      bevelEmbossStyleShadowOpacity =
        createStyleProperty "shadowOpacity" 75.0 PropertyTypeNumber,
      bevelEmbossStyleContourEnabled = Nothing,
      bevelEmbossStyleContour = Nothing,
      bevelEmbossStyleContourAntiAliased = Nothing,
      bevelEmbossStyleContourRange = Nothing,
      bevelEmbossStyleTextureEnabled = Nothing,
      bevelEmbossStyleTexturePattern = Nothing,
      bevelEmbossStyleTextureScale = Nothing,
      bevelEmbossStyleTextureDepth = Nothing,
      bevelEmbossStyleTextureInvert = Nothing,
      bevelEmbossStyleTextureLinkWithLayer = Nothing
    }

-- | Create default satin style
createDefaultSatin :: SatinStyle
createDefaultSatin =
  SatinStyle
    { satinStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendMultiply,
            baseLayerStyleOpacity = createStyleProperty "opacity" 50.0 PropertyTypeNumber
          },
      satinStyleColor =
        createStyleProperty "color" (createRGBA 0.0 0.0 0.0 1.0) PropertyTypeColor,
      satinStyleAngle = createStyleProperty "angle" 19.0 PropertyTypeNumber,
      satinStyleDistance = createStyleProperty "distance" 11.0 PropertyTypeNumber,
      satinStyleSize = createStyleProperty "size" 14.0 PropertyTypeNumber,
      satinStyleContour = Nothing,
      satinStyleAntiAliased = Nothing,
      satinStyleInvert = True
    }

-- | Create default color overlay style
createDefaultColorOverlay :: ColorOverlayStyle
createDefaultColorOverlay =
  ColorOverlayStyle
    { colorOverlayStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendNormal,
            baseLayerStyleOpacity = createStyleProperty "opacity" 100.0 PropertyTypeNumber
          },
      colorOverlayStyleColor =
        createStyleProperty "color" (createRGBA 255.0 0.0 0.0 1.0) PropertyTypeColor
    }

-- | Create default gradient overlay style
createDefaultGradientOverlay :: GradientOverlayStyle
createDefaultGradientOverlay =
  let gradientValue =
        GradientDef
          { gradientDefType = GradientTypeLinear,
            gradientDefStops =
              [ GradientStop 0.0 (createRGBA 0.0 0.0 0.0 1.0),
                GradientStop 1.0 (createRGBA 255.0 255.0 255.0 1.0)
              ],
            gradientDefAngle = Nothing
          }
   in GradientOverlayStyle
        { gradientOverlayStyleBase =
            BaseLayerStyle
              { baseLayerStyleEnabled = True,
                baseLayerStyleBlendMode = BlendNormal,
                baseLayerStyleOpacity = createStyleProperty "opacity" 100.0 PropertyTypeNumber
              },
          gradientOverlayStyleGradient =
            createStyleProperty "gradient" gradientValue PropertyTypeEnum,
          gradientOverlayStyleStyle = GradientOverlayTypeLinear,
          gradientOverlayStyleAngle = createStyleProperty "angle" 90.0 PropertyTypeNumber,
          gradientOverlayStyleScale = createStyleProperty "scale" 100.0 PropertyTypeNumber,
          gradientOverlayStyleAlignWithLayer = True,
          gradientOverlayStyleReverse = False,
          gradientOverlayStyleOffset =
            createStyleProperty "offset" (Point2D 0.0 0.0) PropertyTypePosition,
          gradientOverlayStyleDither = Nothing
        }

-- | Create default stroke style
createDefaultStroke :: StrokeStyle
createDefaultStroke =
  StrokeStyle
    { strokeStyleBase =
        BaseLayerStyle
          { baseLayerStyleEnabled = True,
            baseLayerStyleBlendMode = BlendNormal,
            baseLayerStyleOpacity = createStyleProperty "opacity" 100.0 PropertyTypeNumber
          },
      strokeStyleColor =
        createStyleProperty "color" (createRGBA 255.0 0.0 0.0 1.0) PropertyTypeColor,
      strokeStyleGradient = Nothing,
      strokeStylePattern = Nothing,
      strokeStyleFillType = StrokeFillTypeColor,
      strokeStyleSize = createStyleProperty "size" 3.0 PropertyTypeNumber,
      strokeStylePosition = StrokePositionOutside,
      strokeStyleGradientAngle = Nothing,
      strokeStyleGradientScale = Nothing,
      strokeStylePatternScale = Nothing,
      strokeStylePatternLinkWithLayer = Nothing
    }

-- ============================================================================
-- BLENDING OPTIONS FACTORY
-- ============================================================================

-- | Create default blending options
createDefaultBlendingOptions :: StyleBlendingOptions
createDefaultBlendingOptions =
  StyleBlendingOptions
    { styleBlendingOptionsFillOpacity =
        createStyleProperty "fillOpacity" 100.0 PropertyTypeNumber,
      styleBlendingOptionsBlendInteriorStylesAsGroup = False,
      styleBlendingOptionsBlendClippedLayersAsGroup = Just True,
      styleBlendingOptionsTransparencyShapesLayer = Just True,
      styleBlendingOptionsLayerMaskHidesEffects = Just False,
      styleBlendingOptionsVectorMaskHidesEffects = Just False,
      styleBlendingOptionsBlendIfEnabled = Nothing,
      styleBlendingOptionsThisLayerRange = Nothing,
      styleBlendingOptionsUnderlyingLayerRange = Nothing
    }

-- ============================================================================
-- GLOBAL LIGHT FACTORY
-- ============================================================================

-- | Create default global light settings
createDefaultGlobalLight :: GlobalLightSettings
createDefaultGlobalLight =
  GlobalLightSettings
    { globalLightSettingsAngle = createStyleProperty "angle" 120.0 PropertyTypeNumber,
      globalLightSettingsAltitude = createStyleProperty "altitude" 30.0 PropertyTypeNumber
    }
