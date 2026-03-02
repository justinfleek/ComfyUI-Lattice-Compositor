-- | Lattice.LayerStyles - Layer styles (shadows, glows, bevels, etc.)
-- |
-- | Source: leancomfy/lean/Lattice/LayerStyles.lean
-- | Consolidated from LayerStyles/Enums.lean and LayerStyles/Core.lean

module Lattice.LayerStyles
  ( GlowTechnique(..)
  , InnerGlowSource(..)
  , BevelStyle(..)
  , BevelTechnique(..)
  , BevelDirection(..)
  , GradientOverlayType(..)
  , StrokePosition(..)
  , StrokeFillType(..)
  , StyleOrder(..)
  , styleOrderIndex
  , StyleRGBA
  , StyleGradientStop
  , StyleGradientType(..)
  , StyleGradientDef
  , ContourPoint
  , ContourCurve
  , BaseStyleFields
  , DropShadowStyle
  , InnerShadowStyle
  , OuterGlowStyle
  , InnerGlowStyle
  , BevelEmbossStyle
  , SatinStyle
  , ColorOverlayStyle
  , GradientOverlayStyle
  , PatternOverlayStyle
  , StrokeStyleDef
  , ChannelBlendRange
  , StyleBlendingOptions
  , LayerStyles
  , GlobalLightSettings
  , createDefaultLayerStyles
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.BlendModes (BlendMode)

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data GlowTechnique = GTSofter | GTPrecise

derive instance Eq GlowTechnique
derive instance Generic GlowTechnique _
instance Show GlowTechnique where show = genericShow

data InnerGlowSource = IGSCenter | IGSEdge

derive instance Eq InnerGlowSource
derive instance Generic InnerGlowSource _
instance Show InnerGlowSource where show = genericShow

data BevelStyle
  = BSOuterBevel | BSInnerBevel | BSEmboss | BSPillowEmboss | BSStrokeEmboss

derive instance Eq BevelStyle
derive instance Generic BevelStyle _
instance Show BevelStyle where show = genericShow

data BevelTechnique = BTSmooth | BTChiselHard | BTChiselSoft

derive instance Eq BevelTechnique
derive instance Generic BevelTechnique _
instance Show BevelTechnique where show = genericShow

data BevelDirection = BDUp | BDDown

derive instance Eq BevelDirection
derive instance Generic BevelDirection _
instance Show BevelDirection where show = genericShow

data GradientOverlayType
  = GOTLinear | GOTRadial | GOTAngle | GOTReflected | GOTDiamond

derive instance Eq GradientOverlayType
derive instance Generic GradientOverlayType _
instance Show GradientOverlayType where show = genericShow

data StrokePosition = SPOutside | SPInside | SPCenter

derive instance Eq StrokePosition
derive instance Generic StrokePosition _
instance Show StrokePosition where show = genericShow

data StrokeFillType = SFTColor | SFTGradient | SFTPattern

derive instance Eq StrokeFillType
derive instance Generic StrokeFillType _
instance Show StrokeFillType where show = genericShow

data StyleOrder
  = SODropShadow | SOInnerShadow | SOOuterGlow | SOInnerGlow
  | SOBevelEmboss | SOSatin | SOColorOverlay | SOGradientOverlay
  | SOPatternOverlay | SOStroke

derive instance Eq StyleOrder
derive instance Generic StyleOrder _
instance Show StyleOrder where show = genericShow

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

type StyleRGBA =
  { r :: Int        -- 0-255
  , g :: Int        -- 0-255
  , b :: Int        -- 0-255
  , a :: UnitFloat  -- 0-1
  }

type StyleGradientStop =
  { position :: UnitFloat
  , color    :: StyleRGBA
  }

data StyleGradientType = SGTLinear | SGTRadial

derive instance Eq StyleGradientType
derive instance Generic StyleGradientType _
instance Show StyleGradientType where show = genericShow

type StyleGradientDef =
  { gradientType :: StyleGradientType
  , stops        :: Array StyleGradientStop  -- min 2
  , angle        :: Maybe FiniteFloat
  }

type ContourPoint =
  { x :: UnitFloat  -- 0-1 normalized
  , y :: UnitFloat  -- 0-1 normalized
  }

type ContourCurve =
  { points :: Array ContourPoint
  }

--------------------------------------------------------------------------------
-- Base Style
--------------------------------------------------------------------------------

type BaseStyleFields =
  { enabled           :: Boolean
  , blendMode         :: BlendMode
  , opacityPropertyId :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- Drop Shadow
--------------------------------------------------------------------------------

type DropShadowStyle =
  { base               :: BaseStyleFields
  , colorPropertyId    :: NonEmptyString
  , anglePropertyId    :: NonEmptyString
  , useGlobalLight     :: Boolean
  , distancePropertyId :: NonEmptyString
  , spreadPropertyId   :: NonEmptyString
  , sizePropertyId     :: NonEmptyString
  , noisePropertyId    :: NonEmptyString
  , contour            :: Maybe ContourCurve
  , antiAliased        :: Boolean
  , layerKnocksOut     :: Boolean
  }

--------------------------------------------------------------------------------
-- Inner Shadow
--------------------------------------------------------------------------------

type InnerShadowStyle =
  { base               :: BaseStyleFields
  , colorPropertyId    :: NonEmptyString
  , anglePropertyId    :: NonEmptyString
  , useGlobalLight     :: Boolean
  , distancePropertyId :: NonEmptyString
  , chokePropertyId    :: NonEmptyString
  , sizePropertyId     :: NonEmptyString
  , noisePropertyId    :: NonEmptyString
  , contour            :: Maybe ContourCurve
  , antiAliased        :: Boolean
  }

--------------------------------------------------------------------------------
-- Outer Glow
--------------------------------------------------------------------------------

type OuterGlowStyle =
  { base              :: BaseStyleFields
  , colorPropertyId   :: NonEmptyString
  , gradient          :: Maybe StyleGradientDef
  , useGradient       :: Boolean
  , technique         :: GlowTechnique
  , spreadPropertyId  :: NonEmptyString
  , sizePropertyId    :: NonEmptyString
  , rangePropertyId   :: NonEmptyString
  , jitterPropertyId  :: NonEmptyString
  , noisePropertyId   :: NonEmptyString
  , contour           :: Maybe ContourCurve
  , antiAliased       :: Boolean
  }

--------------------------------------------------------------------------------
-- Inner Glow
--------------------------------------------------------------------------------

type InnerGlowStyle =
  { base              :: BaseStyleFields
  , colorPropertyId   :: NonEmptyString
  , gradient          :: Maybe StyleGradientDef
  , useGradient       :: Boolean
  , technique         :: GlowTechnique
  , source            :: InnerGlowSource
  , chokePropertyId   :: NonEmptyString
  , sizePropertyId    :: NonEmptyString
  , rangePropertyId   :: NonEmptyString
  , jitterPropertyId  :: NonEmptyString
  , noisePropertyId   :: NonEmptyString
  , contour           :: Maybe ContourCurve
  , antiAliased       :: Boolean
  }

--------------------------------------------------------------------------------
-- Bevel and Emboss
--------------------------------------------------------------------------------

type BevelEmbossStyle =
  { base                       :: BaseStyleFields
  , style                      :: BevelStyle
  , technique                  :: BevelTechnique
  , depthPropertyId            :: NonEmptyString
  , direction                  :: BevelDirection
  , sizePropertyId             :: NonEmptyString
  , softenPropertyId           :: NonEmptyString
  , anglePropertyId            :: NonEmptyString
  , useGlobalLight             :: Boolean
  , altitudePropertyId         :: NonEmptyString
  , glossContour               :: Maybe ContourCurve
  , glossAntiAliased           :: Boolean
  , highlightMode              :: BlendMode
  , highlightColorPropertyId   :: NonEmptyString
  , highlightOpacityPropertyId :: NonEmptyString
  , shadowMode                 :: BlendMode
  , shadowColorPropertyId      :: NonEmptyString
  , shadowOpacityPropertyId    :: NonEmptyString
  , contourEnabled             :: Boolean
  , contour                    :: Maybe ContourCurve
  , contourAntiAliased         :: Boolean
  , contourRangePropertyId     :: Maybe NonEmptyString
  , textureEnabled             :: Boolean
  , texturePattern             :: Maybe NonEmptyString
  , textureScalePropertyId     :: Maybe NonEmptyString
  , textureDepthPropertyId     :: Maybe NonEmptyString
  , textureInvert              :: Boolean
  , textureLinkWithLayer       :: Boolean
  }

--------------------------------------------------------------------------------
-- Satin
--------------------------------------------------------------------------------

type SatinStyle =
  { base               :: BaseStyleFields
  , colorPropertyId    :: NonEmptyString
  , anglePropertyId    :: NonEmptyString
  , distancePropertyId :: NonEmptyString
  , sizePropertyId     :: NonEmptyString
  , contour            :: Maybe ContourCurve
  , antiAliased        :: Boolean
  , invert             :: Boolean
  }

--------------------------------------------------------------------------------
-- Color Overlay
--------------------------------------------------------------------------------

type ColorOverlayStyle =
  { base            :: BaseStyleFields
  , colorPropertyId :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- Gradient Overlay
--------------------------------------------------------------------------------

type GradientOverlayStyle =
  { base               :: BaseStyleFields
  , gradientPropertyId :: NonEmptyString
  , style              :: GradientOverlayType
  , anglePropertyId    :: NonEmptyString
  , scalePropertyId    :: NonEmptyString
  , alignWithLayer     :: Boolean
  , reverse            :: Boolean
  , offsetPropertyId   :: NonEmptyString
  , dither             :: Boolean
  }

--------------------------------------------------------------------------------
-- Pattern Overlay
--------------------------------------------------------------------------------

type PatternOverlayStyle =
  { base              :: BaseStyleFields
  , pattern           :: NonEmptyString    -- Pattern asset ID or URL
  , scalePropertyId   :: NonEmptyString    -- Scale (1-1000%)
  , anglePropertyId   :: NonEmptyString    -- Rotation angle (degrees)
  , linkWithLayer     :: Boolean
  , snapToOrigin      :: Boolean
  , offsetPropertyId  :: NonEmptyString    -- Pattern offset from origin
  }

--------------------------------------------------------------------------------
-- Stroke
--------------------------------------------------------------------------------

type StrokeStyleDef =
  { base                    :: BaseStyleFields
  , colorPropertyId         :: NonEmptyString
  , gradient                :: Maybe StyleGradientDef
  , pattern                 :: Maybe NonEmptyString
  , fillType                :: StrokeFillType
  , sizePropertyId          :: NonEmptyString
  , position                :: StrokePosition
  , gradientAnglePropertyId :: Maybe NonEmptyString
  , gradientScalePropertyId :: Maybe NonEmptyString
  , patternScalePropertyId  :: Maybe NonEmptyString
  , patternLinkWithLayer    :: Boolean
  }

--------------------------------------------------------------------------------
-- Blending Options
--------------------------------------------------------------------------------

type ChannelBlendRange =
  { inputBlack  :: Int  -- 0-255
  , inputWhite  :: Int  -- 0-255
  , outputBlack :: Int  -- 0-255
  , outputWhite :: Int  -- 0-255
  }

type StyleBlendingOptions =
  { fillOpacityPropertyId       :: NonEmptyString
  , blendInteriorStylesAsGroup  :: Boolean
  , blendClippedLayersAsGroup   :: Boolean
  , transparencyShapesLayer     :: Boolean
  , layerMaskHidesEffects       :: Boolean
  , vectorMaskHidesEffects      :: Boolean
  , blendIfEnabled              :: Boolean
  , thisLayerRange              :: Maybe ChannelBlendRange
  , underlyingLayerRange        :: Maybe ChannelBlendRange
  }

--------------------------------------------------------------------------------
-- Layer Styles Container
--------------------------------------------------------------------------------

type LayerStyles =
  { enabled         :: Boolean
  , blendingOptions :: Maybe StyleBlendingOptions
  , dropShadow      :: Maybe DropShadowStyle
  , innerShadow     :: Maybe InnerShadowStyle
  , outerGlow       :: Maybe OuterGlowStyle
  , innerGlow       :: Maybe InnerGlowStyle
  , bevelEmboss     :: Maybe BevelEmbossStyle
  , satin           :: Maybe SatinStyle
  , colorOverlay    :: Maybe ColorOverlayStyle
  , gradientOverlay :: Maybe GradientOverlayStyle
  , patternOverlay  :: Maybe PatternOverlayStyle
  , stroke          :: Maybe StrokeStyleDef
  }

--------------------------------------------------------------------------------
-- Global Light
--------------------------------------------------------------------------------

type GlobalLightSettings =
  { anglePropertyId    :: NonEmptyString
  , altitudePropertyId :: NonEmptyString
  }

--------------------------------------------------------------------------------
-- Factory Functions
--------------------------------------------------------------------------------

-- | Create default layer styles (disabled, no effects)
createDefaultLayerStyles :: LayerStyles
createDefaultLayerStyles =
  { enabled: false
  , blendingOptions: Nothing
  , dropShadow: Nothing
  , innerShadow: Nothing
  , outerGlow: Nothing
  , innerGlow: Nothing
  , bevelEmboss: Nothing
  , satin: Nothing
  , colorOverlay: Nothing
  , gradientOverlay: Nothing
  , patternOverlay: Nothing
  , stroke: Nothing
  }
