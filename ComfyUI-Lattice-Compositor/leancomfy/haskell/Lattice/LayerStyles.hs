{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.LayerStyles
Description : Layer styles (shadows, glows, bevels, etc.)
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/LayerStyles.lean
Consolidated from LayerStyles/Enums.lean and LayerStyles/Core.lean
-}

module Lattice.LayerStyles
  ( -- * Enumerations
    GlowTechnique(..)
  , InnerGlowSource(..)
  , BevelStyle(..)
  , BevelTechnique(..)
  , BevelDirection(..)
  , GradientOverlayType(..)
  , StrokePosition(..)
  , StrokeFillType(..)
  , StyleOrder(..)
  , styleOrderIndex
    -- * Color Types
  , StyleRGBA(..)
  , StyleGradientStop(..)
  , StyleGradientType(..)
  , StyleGradientDef(..)
  , ContourPoint(..)
  , ContourCurve(..)
    -- * Base Style
  , BaseStyleFields(..)
    -- * Style Types
  , DropShadowStyle(..)
  , InnerShadowStyle(..)
  , OuterGlowStyle(..)
  , InnerGlowStyle(..)
  , BevelEmbossStyle(..)
  , SatinStyle(..)
  , ColorOverlayStyle(..)
  , GradientOverlayStyle(..)
  , StrokeStyleDef(..)
    -- * Blending Options
  , ChannelBlendRange(..)
  , StyleBlendingOptions(..)
    -- * Container
  , LayerStyles(..)
  , GlobalLightSettings(..)
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import Lattice.Primitives
import Lattice.BlendModes (BlendMode)

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data GlowTechnique = GTSofter | GTPrecise
  deriving stock (Eq, Show, Generic)

data InnerGlowSource = IGSCenter | IGSEdge
  deriving stock (Eq, Show, Generic)

data BevelStyle
  = BSOuterBevel | BSInnerBevel | BSEmboss | BSPillowEmboss | BSStrokeEmboss
  deriving stock (Eq, Show, Generic)

data BevelTechnique = BTSmooth | BTChiselHard | BTChiselSoft
  deriving stock (Eq, Show, Generic)

data BevelDirection = BDUp | BDDown
  deriving stock (Eq, Show, Generic)

data GradientOverlayType
  = GOTLinear | GOTRadial | GOTAngle | GOTReflected | GOTDiamond
  deriving stock (Eq, Show, Generic)

data StrokePosition = SPOutside | SPInside | SPCenter
  deriving stock (Eq, Show, Generic)

data StrokeFillType = SFTColor | SFTGradient | SFTPattern
  deriving stock (Eq, Show, Generic)

data StyleOrder
  = SODropShadow | SOInnerShadow | SOOuterGlow | SOInnerGlow
  | SOBevelEmboss | SOSatin | SOColorOverlay | SOGradientOverlay
  | SOPatternOverlay | SOStroke
  deriving stock (Eq, Show, Generic)

styleOrderIndex :: StyleOrder -> Int
styleOrderIndex SODropShadow      = 0
styleOrderIndex SOInnerShadow     = 1
styleOrderIndex SOOuterGlow       = 2
styleOrderIndex SOInnerGlow       = 3
styleOrderIndex SOBevelEmboss     = 4
styleOrderIndex SOSatin           = 5
styleOrderIndex SOColorOverlay    = 6
styleOrderIndex SOGradientOverlay = 7
styleOrderIndex SOPatternOverlay  = 8
styleOrderIndex SOStroke          = 9

--------------------------------------------------------------------------------
-- Color Types
--------------------------------------------------------------------------------

data StyleRGBA = StyleRGBA
  { srgbaR :: !Int        -- 0-255
  , srgbaG :: !Int        -- 0-255
  , srgbaB :: !Int        -- 0-255
  , srgbaA :: !UnitFloat  -- 0-1
  } deriving stock (Eq, Show, Generic)

data StyleGradientStop = StyleGradientStop
  { sgsPosition :: !UnitFloat
  , sgsColor    :: !StyleRGBA
  } deriving stock (Eq, Show, Generic)

data StyleGradientType = SGTLinear | SGTRadial
  deriving stock (Eq, Show, Generic)

data StyleGradientDef = StyleGradientDef
  { sgdGradientType :: !StyleGradientType
  , sgdStops        :: !(Vector StyleGradientStop)  -- min 2
  , sgdAngle        :: !(Maybe FiniteFloat)
  } deriving stock (Eq, Show, Generic)

data ContourPoint = ContourPoint
  { cpX :: !UnitFloat  -- 0-1 normalized
  , cpY :: !UnitFloat  -- 0-1 normalized
  } deriving stock (Eq, Show, Generic)

data ContourCurve = ContourCurve
  { ccPoints :: !(Vector ContourPoint)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Base Style
--------------------------------------------------------------------------------

data BaseStyleFields = BaseStyleFields
  { bsfEnabled           :: !Bool
  , bsfBlendMode         :: !BlendMode
  , bsfOpacityPropertyId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Drop Shadow
--------------------------------------------------------------------------------

data DropShadowStyle = DropShadowStyle
  { dssBase               :: !BaseStyleFields
  , dssColorPropertyId    :: !NonEmptyString
  , dssAnglePropertyId    :: !NonEmptyString
  , dssUseGlobalLight     :: !Bool
  , dssDistancePropertyId :: !NonEmptyString
  , dssSpreadPropertyId   :: !NonEmptyString
  , dssSizePropertyId     :: !NonEmptyString
  , dssNoisePropertyId    :: !NonEmptyString
  , dssContour            :: !(Maybe ContourCurve)
  , dssAntiAliased        :: !Bool
  , dssLayerKnocksOut     :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Inner Shadow
--------------------------------------------------------------------------------

data InnerShadowStyle = InnerShadowStyle
  { issBase               :: !BaseStyleFields
  , issColorPropertyId    :: !NonEmptyString
  , issAnglePropertyId    :: !NonEmptyString
  , issUseGlobalLight     :: !Bool
  , issDistancePropertyId :: !NonEmptyString
  , issChokePropertyId    :: !NonEmptyString
  , issSizePropertyId     :: !NonEmptyString
  , issNoisePropertyId    :: !NonEmptyString
  , issContour            :: !(Maybe ContourCurve)
  , issAntiAliased        :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Outer Glow
--------------------------------------------------------------------------------

data OuterGlowStyle = OuterGlowStyle
  { ogsBase              :: !BaseStyleFields
  , ogsColorPropertyId   :: !NonEmptyString
  , ogsGradient          :: !(Maybe StyleGradientDef)
  , ogsUseGradient       :: !Bool
  , ogsTechnique         :: !GlowTechnique
  , ogsSpreadPropertyId  :: !NonEmptyString
  , ogsSizePropertyId    :: !NonEmptyString
  , ogsRangePropertyId   :: !NonEmptyString
  , ogsJitterPropertyId  :: !NonEmptyString
  , ogsNoisePropertyId   :: !NonEmptyString
  , ogsContour           :: !(Maybe ContourCurve)
  , ogsAntiAliased       :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Inner Glow
--------------------------------------------------------------------------------

data InnerGlowStyle = InnerGlowStyle
  { igsBase              :: !BaseStyleFields
  , igsColorPropertyId   :: !NonEmptyString
  , igsGradient          :: !(Maybe StyleGradientDef)
  , igsUseGradient       :: !Bool
  , igsTechnique         :: !GlowTechnique
  , igsSource            :: !InnerGlowSource
  , igsChokePropertyId   :: !NonEmptyString
  , igsSizePropertyId    :: !NonEmptyString
  , igsRangePropertyId   :: !NonEmptyString
  , igsJitterPropertyId  :: !NonEmptyString
  , igsNoisePropertyId   :: !NonEmptyString
  , igsContour           :: !(Maybe ContourCurve)
  , igsAntiAliased       :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Bevel and Emboss
--------------------------------------------------------------------------------

data BevelEmbossStyle = BevelEmbossStyle
  { besBase                       :: !BaseStyleFields
  , besStyle                      :: !BevelStyle
  , besTechnique                  :: !BevelTechnique
  , besDepthPropertyId            :: !NonEmptyString
  , besDirection                  :: !BevelDirection
  , besSizePropertyId             :: !NonEmptyString
  , besSoftenPropertyId           :: !NonEmptyString
  , besAnglePropertyId            :: !NonEmptyString
  , besUseGlobalLight             :: !Bool
  , besAltitudePropertyId         :: !NonEmptyString
  , besGlossContour               :: !(Maybe ContourCurve)
  , besGlossAntiAliased           :: !Bool
  , besHighlightMode              :: !BlendMode
  , besHighlightColorPropertyId   :: !NonEmptyString
  , besHighlightOpacityPropertyId :: !NonEmptyString
  , besShadowMode                 :: !BlendMode
  , besShadowColorPropertyId      :: !NonEmptyString
  , besShadowOpacityPropertyId    :: !NonEmptyString
  , besContourEnabled             :: !Bool
  , besContour                    :: !(Maybe ContourCurve)
  , besContourAntiAliased         :: !Bool
  , besContourRangePropertyId     :: !(Maybe NonEmptyString)
  , besTextureEnabled             :: !Bool
  , besTexturePattern             :: !(Maybe NonEmptyString)
  , besTextureScalePropertyId     :: !(Maybe NonEmptyString)
  , besTextureDepthPropertyId     :: !(Maybe NonEmptyString)
  , besTextureInvert              :: !Bool
  , besTextureLinkWithLayer       :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Satin
--------------------------------------------------------------------------------

data SatinStyle = SatinStyle
  { ssBase               :: !BaseStyleFields
  , ssColorPropertyId    :: !NonEmptyString
  , ssAnglePropertyId    :: !NonEmptyString
  , ssDistancePropertyId :: !NonEmptyString
  , ssSizePropertyId     :: !NonEmptyString
  , ssContour            :: !(Maybe ContourCurve)
  , ssAntiAliased        :: !Bool
  , ssInvert             :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Color Overlay
--------------------------------------------------------------------------------

data ColorOverlayStyle = ColorOverlayStyle
  { cosBase            :: !BaseStyleFields
  , cosColorPropertyId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Gradient Overlay
--------------------------------------------------------------------------------

data GradientOverlayStyle = GradientOverlayStyle
  { gosBase               :: !BaseStyleFields
  , gosGradientPropertyId :: !NonEmptyString
  , gosStyle              :: !GradientOverlayType
  , gosAnglePropertyId    :: !NonEmptyString
  , gosScalePropertyId    :: !NonEmptyString
  , gosAlignWithLayer     :: !Bool
  , gosReverse            :: !Bool
  , gosOffsetPropertyId   :: !NonEmptyString
  , gosDither             :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Stroke
--------------------------------------------------------------------------------

data StrokeStyleDef = StrokeStyleDef
  { ssdBase                    :: !BaseStyleFields
  , ssdColorPropertyId         :: !NonEmptyString
  , ssdGradient                :: !(Maybe StyleGradientDef)
  , ssdPattern                 :: !(Maybe NonEmptyString)
  , ssdFillType                :: !StrokeFillType
  , ssdSizePropertyId          :: !NonEmptyString
  , ssdPosition                :: !StrokePosition
  , ssdGradientAnglePropertyId :: !(Maybe NonEmptyString)
  , ssdGradientScalePropertyId :: !(Maybe NonEmptyString)
  , ssdPatternScalePropertyId  :: !(Maybe NonEmptyString)
  , ssdPatternLinkWithLayer    :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Blending Options
--------------------------------------------------------------------------------

data ChannelBlendRange = ChannelBlendRange
  { cbrInputBlack  :: !Int  -- 0-255
  , cbrInputWhite  :: !Int  -- 0-255
  , cbrOutputBlack :: !Int  -- 0-255
  , cbrOutputWhite :: !Int  -- 0-255
  } deriving stock (Eq, Show, Generic)

data StyleBlendingOptions = StyleBlendingOptions
  { sboFillOpacityPropertyId       :: !NonEmptyString
  , sboBlendInteriorStylesAsGroup  :: !Bool
  , sboBlendClippedLayersAsGroup   :: !Bool
  , sboTransparencyShapesLayer     :: !Bool
  , sboLayerMaskHidesEffects       :: !Bool
  , sboVectorMaskHidesEffects      :: !Bool
  , sboBlendIfEnabled              :: !Bool
  , sboThisLayerRange              :: !(Maybe ChannelBlendRange)
  , sboUnderlyingLayerRange        :: !(Maybe ChannelBlendRange)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Layer Styles Container
--------------------------------------------------------------------------------

data LayerStyles = LayerStyles
  { lsEnabled         :: !Bool
  , lsBlendingOptions :: !(Maybe StyleBlendingOptions)
  , lsDropShadow      :: !(Maybe DropShadowStyle)
  , lsInnerShadow     :: !(Maybe InnerShadowStyle)
  , lsOuterGlow       :: !(Maybe OuterGlowStyle)
  , lsInnerGlow       :: !(Maybe InnerGlowStyle)
  , lsBevelEmboss     :: !(Maybe BevelEmbossStyle)
  , lsSatin           :: !(Maybe SatinStyle)
  , lsColorOverlay    :: !(Maybe ColorOverlayStyle)
  , lsGradientOverlay :: !(Maybe GradientOverlayStyle)
  , lsStroke          :: !(Maybe StrokeStyleDef)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Global Light
--------------------------------------------------------------------------------

data GlobalLightSettings = GlobalLightSettings
  { glsAnglePropertyId    :: !NonEmptyString
  , glsAltitudePropertyId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)
