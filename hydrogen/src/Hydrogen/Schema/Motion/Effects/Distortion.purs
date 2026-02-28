-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // effects // distortion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distortion Effects — Spatial distortion and warping effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's Distortion effect category:
-- |
-- | - **Warp**: Photoshop-style warp with 15 presets
-- | - **Displacement Map**: Displace pixels using map image
-- | - **Bezier Warp**: 4-point bezier mesh deformation
-- | - **Bulge**: Spherical bulge distortion
-- | - **Corner Pin**: 4-corner perspective distortion
-- | - **Liquify**: Brush-based deformation
-- | - **Mirror**: Reflection/mirror effects
-- | - **Offset**: Tile/offset image
-- | - **Optics Compensation**: Lens distortion correction
-- | - **Polar Coordinates**: Rectangular to polar conversion
-- | - **Ripple**: Radial wave distortion
-- | - **Spherize**: Wrap around sphere
-- | - **Transform**: Basic spatial transform
-- | - **Turbulent Displace**: Fractal-based displacement
-- | - **Twirl**: Rotational distortion
-- | - **Wave Warp**: Sine wave distortion
-- | - **CC Bend It**: Bend layer around axis
-- | - **CC Blobbylize**: Organic blob distortion
-- | - **CC Flo Motion**: Flow-based motion blur
-- | - **CC Griddler**: Grid-based distortion
-- | - **CC Lens**: Lens distortion
-- | - **CC Page Turn**: Page turn effect
-- | - **CC Power Pin**: Advanced corner pin
-- | - **CC Ripple Pulse**: Expanding ripple
-- | - **CC Slant**: Perspective slant
-- | - **CC Smear**: Directional smear
-- | - **CC Split**: Split/duplicate effect
-- | - **CC Tiler**: Tiling effect
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Distortion
  ( -- * Ramp Shape
    RampShape(..)
  , allRampShapes
  , rampShapeToString
  , rampShapeFromString
  
    -- * Warp Style
  , WarpStyle(..)
  , allWarpStyles
  , warpStyleToString
  , warpStyleFromString
  
    -- * Displacement Map Type
  , DisplacementMapType(..)
  , allDisplacementMapTypes
  , displacementMapTypeToString
  , displacementMapTypeFromString
  
    -- * Displacement Channel
  , DisplacementChannel(..)
  , allDisplacementChannels
  , displacementChannelToString
  , displacementChannelFromString
  
    -- * Edge Behavior
  , EdgeBehavior(..)
  , allEdgeBehaviors
  , edgeBehaviorToString
  , edgeBehaviorFromString
  
  -- * Warp Effect
  , WarpEffect
  , defaultWarp
  , warpWithStyle
  , warpWithBend
  
  -- * Displacement Map Effect
  , DisplacementMapEffect
  , defaultDisplacementMap
  , displacementMapWithLayer
  
  -- * Bezier Warp Effect
  , BezierWarpEffect
  , defaultBezierWarp
  
  -- * Bulge Effect
  , BulgeEffect
  , defaultBulge
  , bulgeWithRadius
  
  -- * Corner Pin Effect
  , CornerPinEffect
  , defaultCornerPin
  
  -- * Liquify Effect
  , LiquifyEffect
  , LiquifyTool(..)
  , defaultLiquify
  
  -- * Mirror Effect
  , MirrorEffect
  , defaultMirror
  , mirrorWithAngle
  
  -- * Offset Effect
  , OffsetEffect
  , defaultOffset
  , offsetWithShift
  
  -- * Optics Compensation Effect
  , OpticsCompensationEffect
  , defaultOpticsCompensation
  
  -- * Polar Coordinates Effect
  , PolarCoordinatesEffect
  , PolarType(..)
  , defaultPolarCoordinates
  
  -- * Ripple Effect
  , RippleEffect
  , RippleConversion(..)
  , defaultRipple
  , rippleWithWaves
  
  -- * Spherize Effect
  , SpherizeEffect
  , defaultSpherize
  , spherizeWithRadius
  
  -- * Transform Effect
  , TransformEffect
  , defaultTransform
  , transformWithPosition
  
  -- * Turbulent Displace Effect
  , TurbulentDisplaceEffect
  , TurbulentDisplaceType(..)
  , defaultTurbulentDisplace
  , turbulentDisplaceWithAmount
  
  -- * Twirl Effect
  , TwirlEffect
  , defaultTwirl
  , twirlWithAngle
  
  -- * Wave Warp Effect
  , WaveWarpEffect
  , WaveType(..)
  , defaultWaveWarp
  , waveWarpWithHeight
  
  -- * CC Bend It Effect
  , CCBendItEffect
  , defaultCCBendIt
  
  -- * CC Blobbylize Effect
  , CCBlobbylizeEffect
  , defaultCCBlobbylize
  
  -- * CC Flo Motion Effect
  , CCFloMotionEffect
  , defaultCCFloMotion
  
  -- * CC Griddler Effect
  , CCGriddlerEffect
  , defaultCCGriddler
  
  -- * CC Lens Effect
  , CCLensEffect
  , defaultCCLens
  
  -- * CC Page Turn Effect
  , CCPageTurnEffect
  , defaultCCPageTurn
  
  -- * CC Power Pin Effect
  , CCPowerPinEffect
  , defaultCCPowerPin
  
  -- * CC Ripple Pulse Effect
  , CCRipplePulseEffect
  , defaultCCRipplePulse
  
  -- * CC Slant Effect
  , CCSlantEffect
  , defaultCCSlant
  
  -- * CC Smear Effect
  , CCSmearEffect
  , defaultCCSmear
  
  -- * CC Split Effect  
  , CCSplitEffect
  , CCSplitDirection(..)
  , defaultCCSplit
  
  -- * CC Tiler Effect
  , CCTilerEffect
  , defaultCCTiler
  
  -- * Effect Names
  , warpEffectName
  , displacementMapEffectName
  , bezierWarpEffectName
  , bulgeEffectName
  , cornerPinEffectName
  , liquifyEffectName
  , mirrorEffectName
  , offsetEffectName
  , opticsCompensationEffectName
  , polarCoordinatesEffectName
  , rippleEffectName
  , spherizeEffectName
  , transformEffectName
  , turbulentDisplaceEffectName
  , twirlEffectName
  , waveWarpEffectName
  , ccBendItEffectName
  , ccBlobbylizeEffectName
  , ccFloMotionEffectName
  , ccGriddlerEffectName
  , ccLensEffectName
  , ccPageTurnEffectName
  , ccPowerPinEffectName
  , ccRipplePulseEffectName
  , ccSlantEffectName
  , ccSmearEffectName
  , ccSplitEffectName
  , ccTilerEffectName
  
  -- * Effect Descriptions
  , describeWarp
  , describeDisplacementMap
  , describeBulge
  , describeTwirl
  , describeWaveWarp
  , describeTurbulentDisplace
  
  -- * Queries
  , isWarpBent
  , isDisplacementActive
  , hasBulgeHeight
  , isTwirlSignificant
  , isWaveWarpAnimated
  , isTurbulentDisplaceComplex
  
  -- * Serialization
  , liquifyToolToString
  , polarTypeToString
  , rippleConversionToString
  , turbulentDisplaceTypeToString
  , waveTypeToString
  , ccSplitDirectionToString
  
  -- * Advanced Utilities
  , scaleWarpBend
  , combineBulgeHeights
  , totalDisplacementMagnitude
  , waveWarpIntensity
  , isBulgeExpanding
  , twirlRevolutions
  , offsetTwirlAngle
  , scaleTurbulentAmount
  , displacementDifference
  , classifyWarpIntensity
  , hasTransformChange
  , hasWarpBothDistortions
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , show
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // ramp // shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of gradient ramp.
data RampShape
  = RSLinear   -- ^ Linear gradient
  | RSRadial   -- ^ Radial gradient

derive instance eqRampShape :: Eq RampShape
derive instance ordRampShape :: Ord RampShape

instance showRampShape :: Show RampShape where
  show RSLinear = "RSLinear"
  show RSRadial = "RSRadial"

-- | All ramp shapes for enumeration
allRampShapes :: Array RampShape
allRampShapes = [ RSLinear, RSRadial ]

rampShapeToString :: RampShape -> String
rampShapeToString RSLinear = "linear"
rampShapeToString RSRadial = "radial"

rampShapeFromString :: String -> Maybe RampShape
rampShapeFromString "linear" = Just RSLinear
rampShapeFromString "radial" = Just RSRadial
rampShapeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // warp // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style of warp distortion (15 variants, matches Photoshop).
data WarpStyle
  = WSArc          -- ^ Arc warp
  | WSArcLower     -- ^ Lower arc
  | WSArcUpper     -- ^ Upper arc
  | WSArch         -- ^ Arch shape
  | WSBulge        -- ^ Bulge outward
  | WSShellLower   -- ^ Lower shell
  | WSShellUpper   -- ^ Upper shell
  | WSFlag         -- ^ Flag wave
  | WSWave         -- ^ Wave distortion
  | WSFish         -- ^ Fish shape
  | WSRise         -- ^ Rising effect
  | WSFisheye      -- ^ Fisheye lens
  | WSInflate      -- ^ Inflate/balloon
  | WSSqueeze      -- ^ Squeeze horizontally
  | WSTwist        -- ^ Twist around center

derive instance eqWarpStyle :: Eq WarpStyle
derive instance ordWarpStyle :: Ord WarpStyle

instance showWarpStyle :: Show WarpStyle where
  show WSArc = "WSArc"
  show WSArcLower = "WSArcLower"
  show WSArcUpper = "WSArcUpper"
  show WSArch = "WSArch"
  show WSBulge = "WSBulge"
  show WSShellLower = "WSShellLower"
  show WSShellUpper = "WSShellUpper"
  show WSFlag = "WSFlag"
  show WSWave = "WSWave"
  show WSFish = "WSFish"
  show WSRise = "WSRise"
  show WSFisheye = "WSFisheye"
  show WSInflate = "WSInflate"
  show WSSqueeze = "WSSqueeze"
  show WSTwist = "WSTwist"

-- | All warp styles for enumeration
allWarpStyles :: Array WarpStyle
allWarpStyles =
  [ WSArc
  , WSArcLower
  , WSArcUpper
  , WSArch
  , WSBulge
  , WSShellLower
  , WSShellUpper
  , WSFlag
  , WSWave
  , WSFish
  , WSRise
  , WSFisheye
  , WSInflate
  , WSSqueeze
  , WSTwist
  ]

warpStyleToString :: WarpStyle -> String
warpStyleToString WSArc = "arc"
warpStyleToString WSArcLower = "arc-lower"
warpStyleToString WSArcUpper = "arc-upper"
warpStyleToString WSArch = "arch"
warpStyleToString WSBulge = "bulge"
warpStyleToString WSShellLower = "shell-lower"
warpStyleToString WSShellUpper = "shell-upper"
warpStyleToString WSFlag = "flag"
warpStyleToString WSWave = "wave"
warpStyleToString WSFish = "fish"
warpStyleToString WSRise = "rise"
warpStyleToString WSFisheye = "fisheye"
warpStyleToString WSInflate = "inflate"
warpStyleToString WSSqueeze = "squeeze"
warpStyleToString WSTwist = "twist"

warpStyleFromString :: String -> Maybe WarpStyle
warpStyleFromString "arc" = Just WSArc
warpStyleFromString "arc-lower" = Just WSArcLower
warpStyleFromString "arc-upper" = Just WSArcUpper
warpStyleFromString "arch" = Just WSArch
warpStyleFromString "bulge" = Just WSBulge
warpStyleFromString "shell-lower" = Just WSShellLower
warpStyleFromString "shell-upper" = Just WSShellUpper
warpStyleFromString "flag" = Just WSFlag
warpStyleFromString "wave" = Just WSWave
warpStyleFromString "fish" = Just WSFish
warpStyleFromString "rise" = Just WSRise
warpStyleFromString "fisheye" = Just WSFisheye
warpStyleFromString "inflate" = Just WSInflate
warpStyleFromString "squeeze" = Just WSSqueeze
warpStyleFromString "twist" = Just WSTwist
warpStyleFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // displacement // map // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of displacement map source.
data DisplacementMapType
  = DMTLayer      -- ^ Use another layer
  | DMTNoise      -- ^ Procedural noise
  | DMTGradientH  -- ^ Horizontal gradient
  | DMTGradientV  -- ^ Vertical gradient
  | DMTRadial     -- ^ Radial gradient
  | DMTSineH      -- ^ Horizontal sine wave
  | DMTSineV      -- ^ Vertical sine wave
  | DMTChecker    -- ^ Checkerboard pattern

derive instance eqDisplacementMapType :: Eq DisplacementMapType
derive instance ordDisplacementMapType :: Ord DisplacementMapType

instance showDisplacementMapType :: Show DisplacementMapType where
  show DMTLayer = "DMTLayer"
  show DMTNoise = "DMTNoise"
  show DMTGradientH = "DMTGradientH"
  show DMTGradientV = "DMTGradientV"
  show DMTRadial = "DMTRadial"
  show DMTSineH = "DMTSineH"
  show DMTSineV = "DMTSineV"
  show DMTChecker = "DMTChecker"

-- | All displacement map types for enumeration
allDisplacementMapTypes :: Array DisplacementMapType
allDisplacementMapTypes =
  [ DMTLayer
  , DMTNoise
  , DMTGradientH
  , DMTGradientV
  , DMTRadial
  , DMTSineH
  , DMTSineV
  , DMTChecker
  ]

displacementMapTypeToString :: DisplacementMapType -> String
displacementMapTypeToString DMTLayer = "layer"
displacementMapTypeToString DMTNoise = "noise"
displacementMapTypeToString DMTGradientH = "gradient-h"
displacementMapTypeToString DMTGradientV = "gradient-v"
displacementMapTypeToString DMTRadial = "radial"
displacementMapTypeToString DMTSineH = "sine-h"
displacementMapTypeToString DMTSineV = "sine-v"
displacementMapTypeToString DMTChecker = "checker"

displacementMapTypeFromString :: String -> Maybe DisplacementMapType
displacementMapTypeFromString "layer" = Just DMTLayer
displacementMapTypeFromString "noise" = Just DMTNoise
displacementMapTypeFromString "gradient-h" = Just DMTGradientH
displacementMapTypeFromString "gradient-v" = Just DMTGradientV
displacementMapTypeFromString "radial" = Just DMTRadial
displacementMapTypeFromString "sine-h" = Just DMTSineH
displacementMapTypeFromString "sine-v" = Just DMTSineV
displacementMapTypeFromString "checker" = Just DMTChecker
displacementMapTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // displacement // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel used for displacement.
data DisplacementChannel
  = DCRed        -- ^ Red channel
  | DCGreen      -- ^ Green channel
  | DCBlue       -- ^ Blue channel
  | DCAlpha      -- ^ Alpha channel
  | DCLuminance  -- ^ Luminance (grayscale)
  | DCOff        -- ^ No displacement

derive instance eqDisplacementChannel :: Eq DisplacementChannel
derive instance ordDisplacementChannel :: Ord DisplacementChannel

instance showDisplacementChannel :: Show DisplacementChannel where
  show DCRed = "DCRed"
  show DCGreen = "DCGreen"
  show DCBlue = "DCBlue"
  show DCAlpha = "DCAlpha"
  show DCLuminance = "DCLuminance"
  show DCOff = "DCOff"

-- | All displacement channels for enumeration
allDisplacementChannels :: Array DisplacementChannel
allDisplacementChannels =
  [ DCRed
  , DCGreen
  , DCBlue
  , DCAlpha
  , DCLuminance
  , DCOff
  ]

displacementChannelToString :: DisplacementChannel -> String
displacementChannelToString DCRed = "red"
displacementChannelToString DCGreen = "green"
displacementChannelToString DCBlue = "blue"
displacementChannelToString DCAlpha = "alpha"
displacementChannelToString DCLuminance = "luminance"
displacementChannelToString DCOff = "off"

displacementChannelFromString :: String -> Maybe DisplacementChannel
displacementChannelFromString "red" = Just DCRed
displacementChannelFromString "green" = Just DCGreen
displacementChannelFromString "blue" = Just DCBlue
displacementChannelFromString "alpha" = Just DCAlpha
displacementChannelFromString "luminance" = Just DCLuminance
displacementChannelFromString "off" = Just DCOff
displacementChannelFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // edge // behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Behavior at image edges.
data EdgeBehavior
  = EBOff     -- ^ No edge handling
  | EBTiles   -- ^ Tile/wrap edges
  | EBMirror  -- ^ Mirror at edges

derive instance eqEdgeBehavior :: Eq EdgeBehavior
derive instance ordEdgeBehavior :: Ord EdgeBehavior

instance showEdgeBehavior :: Show EdgeBehavior where
  show EBOff = "EBOff"
  show EBTiles = "EBTiles"
  show EBMirror = "EBMirror"

-- | All edge behaviors for enumeration
allEdgeBehaviors :: Array EdgeBehavior
allEdgeBehaviors = [ EBOff, EBTiles, EBMirror ]

edgeBehaviorToString :: EdgeBehavior -> String
edgeBehaviorToString EBOff = "off"
edgeBehaviorToString EBTiles = "tiles"
edgeBehaviorToString EBMirror = "mirror"

edgeBehaviorFromString :: String -> Maybe EdgeBehavior
edgeBehaviorFromString "off" = Just EBOff
edgeBehaviorFromString "tiles" = Just EBTiles
edgeBehaviorFromString "mirror" = Just EBMirror
edgeBehaviorFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // warp // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warp Effect — Photoshop-style warp with 15 presets.
-- |
-- | ## AE Properties
-- |
-- | - Warp Style: One of 15 warp presets
-- | - Bend: Primary bend amount (-100 to 100)
-- | - Horizontal Distortion: Horizontal distortion (-100 to 100)
-- | - Vertical Distortion: Vertical distortion (-100 to 100)
type WarpEffect =
  { warpStyle :: WarpStyle              -- ^ Warp preset
  , bend :: Number                       -- ^ Primary bend (-100 to 100)
  , horizontalDistortion :: Number       -- ^ Horizontal distortion (-100 to 100)
  , verticalDistortion :: Number         -- ^ Vertical distortion (-100 to 100)
  }

-- | Default warp: arc with no bend.
defaultWarp :: WarpEffect
defaultWarp =
  { warpStyle: WSArc
  , bend: 0.0
  , horizontalDistortion: 0.0
  , verticalDistortion: 0.0
  }

-- | Create warp with specific style.
warpWithStyle :: WarpStyle -> WarpEffect
warpWithStyle style =
  { warpStyle: style
  , bend: 50.0
  , horizontalDistortion: 0.0
  , verticalDistortion: 0.0
  }

-- | Create warp with specific bend.
warpWithBend :: Number -> WarpEffect
warpWithBend b =
  { warpStyle: WSArc
  , bend: clampNumber (-100.0) 100.0 b
  , horizontalDistortion: 0.0
  , verticalDistortion: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // displacement // map
-- ═════════════════════════════════════════════════════════════════════════════

-- | Displacement Map Effect — Displace pixels using map image.
-- |
-- | ## AE Properties
-- |
-- | - Displacement Map Layer: Source layer for map
-- | - Use For Horizontal Displacement: Channel for X displacement
-- | - Use For Vertical Displacement: Channel for Y displacement
-- | - Max Horizontal Displacement: Max X offset (0-1000 pixels)
-- | - Max Vertical Displacement: Max Y offset (0-1000 pixels)
-- | - Displacement Map Behavior: Edge behavior
-- | - Edge Behavior: How to handle edges
type DisplacementMapEffect =
  { mapLayer :: Int                              -- ^ Source layer index
  , mapType :: DisplacementMapType               -- ^ Map source type
  , horizontalChannel :: DisplacementChannel     -- ^ Channel for X
  , verticalChannel :: DisplacementChannel       -- ^ Channel for Y
  , maxHorizontalDisplacement :: Number          -- ^ Max X offset (0-1000)
  , maxVerticalDisplacement :: Number            -- ^ Max Y offset (0-1000)
  , edgeBehavior :: EdgeBehavior                 -- ^ Edge handling
  , expandOutput :: Boolean                      -- ^ Expand canvas
  }

-- | Default displacement map.
defaultDisplacementMap :: DisplacementMapEffect
defaultDisplacementMap =
  { mapLayer: 1
  , mapType: DMTLayer
  , horizontalChannel: DCRed
  , verticalChannel: DCGreen
  , maxHorizontalDisplacement: 0.0
  , maxVerticalDisplacement: 0.0
  , edgeBehavior: EBOff
  , expandOutput: false
  }

-- | Create displacement map with specific layer.
displacementMapWithLayer :: Int -> Number -> Number -> DisplacementMapEffect
displacementMapWithLayer layer hDisp vDisp =
  { mapLayer: layer
  , mapType: DMTLayer
  , horizontalChannel: DCRed
  , verticalChannel: DCGreen
  , maxHorizontalDisplacement: clampNumber 0.0 1000.0 hDisp
  , maxVerticalDisplacement: clampNumber 0.0 1000.0 vDisp
  , edgeBehavior: EBOff
  , expandOutput: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bezier // warp
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bezier Warp Effect — 4-point bezier mesh deformation.
-- |
-- | ## AE Properties
-- |
-- | 4 corner points with tangent handles for bezier curve control.
type BezierWarpEffect =
  { topLeft :: Point2D                   -- ^ Top-left corner
  , topRight :: Point2D                  -- ^ Top-right corner
  , bottomLeft :: Point2D                -- ^ Bottom-left corner
  , bottomRight :: Point2D               -- ^ Bottom-right corner
  , topLeftTangent :: Point2D            -- ^ Top-left tangent
  , topRightTangent :: Point2D           -- ^ Top-right tangent
  , bottomLeftTangent :: Point2D         -- ^ Bottom-left tangent
  , bottomRightTangent :: Point2D        -- ^ Bottom-right tangent
  , quality :: Int                        -- ^ Render quality (1-10)
  }

-- | Default bezier warp (unit square, no distortion).
defaultBezierWarp :: BezierWarpEffect
defaultBezierWarp =
  { topLeft: point2D 0.0 0.0
  , topRight: point2D 100.0 0.0
  , bottomLeft: point2D 0.0 100.0
  , bottomRight: point2D 100.0 100.0
  , topLeftTangent: point2D 0.0 0.0
  , topRightTangent: point2D 0.0 0.0
  , bottomLeftTangent: point2D 0.0 0.0
  , bottomRightTangent: point2D 0.0 0.0
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bulge // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bulge Effect — Spherical bulge distortion.
-- |
-- | ## AE Properties
-- |
-- | - Horizontal Radius: Horizontal bulge size (0-1000)
-- | - Vertical Radius: Vertical bulge size (0-1000)
-- | - Bulge Center: Center point
-- | - Bulge Height: Distortion amount (-4 to 4)
-- | - Taper Radius: Edge falloff (0-100%)
-- | - Antialiasing: Edge smoothing
type BulgeEffect =
  { horizontalRadius :: Number           -- ^ Horizontal size (0-1000)
  , verticalRadius :: Number             -- ^ Vertical size (0-1000)
  , bulgeCenter :: Point2D               -- ^ Center point
  , bulgeHeight :: Number                -- ^ Distortion (-4 to 4)
  , taperRadius :: Number                -- ^ Edge falloff (0-100)
  , antialiasing :: Boolean              -- ^ Edge smoothing
  , pinAllEdges :: Boolean               -- ^ Lock edges
  }

-- | Default bulge.
defaultBulge :: BulgeEffect
defaultBulge =
  { horizontalRadius: 100.0
  , verticalRadius: 100.0
  , bulgeCenter: point2D 50.0 50.0
  , bulgeHeight: 1.0
  , taperRadius: 0.0
  , antialiasing: true
  , pinAllEdges: false
  }

-- | Create bulge with specific radius.
bulgeWithRadius :: Number -> Number -> Number -> BulgeEffect
bulgeWithRadius hRadius vRadius height =
  { horizontalRadius: clampNumber 0.0 1000.0 hRadius
  , verticalRadius: clampNumber 0.0 1000.0 vRadius
  , bulgeCenter: point2D 50.0 50.0
  , bulgeHeight: clampNumber (-4.0) 4.0 height
  , taperRadius: 0.0
  , antialiasing: true
  , pinAllEdges: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // corner // pin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Corner Pin Effect — 4-corner perspective distortion.
-- |
-- | ## AE Properties
-- |
-- | Move each corner independently for perspective transform.
type CornerPinEffect =
  { upperLeft :: Point2D                 -- ^ Upper-left corner
  , upperRight :: Point2D                -- ^ Upper-right corner
  , lowerLeft :: Point2D                 -- ^ Lower-left corner
  , lowerRight :: Point2D                -- ^ Lower-right corner
  }

-- | Default corner pin (no distortion).
defaultCornerPin :: CornerPinEffect
defaultCornerPin =
  { upperLeft: point2D 0.0 0.0
  , upperRight: point2D 100.0 0.0
  , lowerLeft: point2D 0.0 100.0
  , lowerRight: point2D 100.0 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // liquify // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Liquify tool type.
data LiquifyTool
  = LTWarp             -- ^ Push/warp
  | LTTurbulence       -- ^ Turbulent displacement
  | LTTwirl            -- ^ Twirl clockwise
  | LTTwirlCCW         -- ^ Twirl counter-clockwise
  | LTPucker           -- ^ Pucker (contract)
  | LTBloat            -- ^ Bloat (expand)
  | LTShift            -- ^ Shift pixels
  | LTReflection       -- ^ Reflect
  | LTReconstruction   -- ^ Reconstruct/restore

derive instance eqLiquifyTool :: Eq LiquifyTool
derive instance ordLiquifyTool :: Ord LiquifyTool

instance showLiquifyTool :: Show LiquifyTool where
  show LTWarp = "warp"
  show LTTurbulence = "turbulence"
  show LTTwirl = "twirl"
  show LTTwirlCCW = "twirl-ccw"
  show LTPucker = "pucker"
  show LTBloat = "bloat"
  show LTShift = "shift"
  show LTReflection = "reflection"
  show LTReconstruction = "reconstruction"

-- | Liquify Effect — Brush-based deformation.
-- |
-- | ## AE Properties
-- |
-- | Interactive brush-based distortion (like Photoshop Liquify).
type LiquifyEffect =
  { tool :: LiquifyTool                  -- ^ Active tool
  , brushSize :: Number                  -- ^ Brush size (1-1500)
  , brushPressure :: Number              -- ^ Brush pressure (0-100)
  , brushRate :: Number                  -- ^ Brush rate (0-100)
  , turbulentJitter :: Number            -- ^ Turbulence randomness (0-100)
  , reconstructionMode :: Int            -- ^ Reconstruction mode (0-5)
  , distortionMesh :: Array Point2D      -- ^ Mesh deformation points
  }

-- | Default liquify.
defaultLiquify :: LiquifyEffect
defaultLiquify =
  { tool: LTWarp
  , brushSize: 100.0
  , brushPressure: 50.0
  , brushRate: 50.0
  , turbulentJitter: 0.0
  , reconstructionMode: 0
  , distortionMesh: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // mirror // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mirror Effect — Reflection/mirror effects.
-- |
-- | ## AE Properties
-- |
-- | - Reflection Center: Center of reflection axis
-- | - Reflection Angle: Angle of reflection axis (0-360)
type MirrorEffect =
  { reflectionCenter :: Point2D          -- ^ Center point
  , reflectionAngle :: Number            -- ^ Axis angle (0-360)
  }

-- | Default mirror (vertical reflection at center).
defaultMirror :: MirrorEffect
defaultMirror =
  { reflectionCenter: point2D 50.0 50.0
  , reflectionAngle: 0.0
  }

-- | Create mirror with specific angle.
mirrorWithAngle :: Number -> MirrorEffect
mirrorWithAngle angle =
  { reflectionCenter: point2D 50.0 50.0
  , reflectionAngle: clampNumber 0.0 360.0 angle
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // offset // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Offset Effect — Tile/offset image.
-- |
-- | ## AE Properties
-- |
-- | - Shift Center To: New center point
-- | - Blend With Original: Original blend (0-100%)
type OffsetEffect =
  { shiftCenterTo :: Point2D             -- ^ Offset position
  , blendWithOriginal :: Number          -- ^ Original blend (0-100)
  }

-- | Default offset (no shift).
defaultOffset :: OffsetEffect
defaultOffset =
  { shiftCenterTo: point2D 0.0 0.0
  , blendWithOriginal: 0.0
  }

-- | Create offset with specific shift.
offsetWithShift :: Number -> Number -> OffsetEffect
offsetWithShift x y =
  { shiftCenterTo: point2D x y
  , blendWithOriginal: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // optics // compensation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Optics Compensation Effect — Lens distortion correction.
-- |
-- | ## AE Properties
-- |
-- | - Field of View: FOV angle (0-180)
-- | - Reverse Lens Distortion: Invert correction
-- | - FOV Orientation: Horizontal or vertical FOV
-- | - View Center: Center of distortion
type OpticsCompensationEffect =
  { fieldOfView :: Number                -- ^ FOV angle (0-180)
  , reverseLensDistortion :: Boolean     -- ^ Invert correction
  , fovOrientationHorizontal :: Boolean  -- ^ true = horizontal FOV
  , viewCenter :: Point2D                -- ^ Center point
  , optimizePixels :: Boolean            -- ^ Pixel optimization
  }

-- | Default optics compensation.
defaultOpticsCompensation :: OpticsCompensationEffect
defaultOpticsCompensation =
  { fieldOfView: 45.0
  , reverseLensDistortion: false
  , fovOrientationHorizontal: true
  , viewCenter: point2D 50.0 50.0
  , optimizePixels: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // polar // coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Polar conversion type.
data PolarType
  = PTRectToPolar      -- ^ Rectangular to polar
  | PTPolarToRect      -- ^ Polar to rectangular

derive instance eqPolarType :: Eq PolarType
derive instance ordPolarType :: Ord PolarType

instance showPolarType :: Show PolarType where
  show PTRectToPolar = "rect-to-polar"
  show PTPolarToRect = "polar-to-rect"

-- | Polar Coordinates Effect — Rectangular to polar conversion.
-- |
-- | ## AE Properties
-- |
-- | - Type of Conversion: Rect to polar or polar to rect
-- | - Interpolation: Quality setting (0-100%)
type PolarCoordinatesEffect =
  { typeOfConversion :: PolarType        -- ^ Conversion direction
  , interpolation :: Number              -- ^ Quality (0-100)
  }

-- | Default polar coordinates.
defaultPolarCoordinates :: PolarCoordinatesEffect
defaultPolarCoordinates =
  { typeOfConversion: PTRectToPolar
  , interpolation: 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // ripple // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ripple conversion type.
data RippleConversion
  = RCSymmetric        -- ^ Symmetric ripples
  | RCAsymmetric       -- ^ Asymmetric ripples

derive instance eqRippleConversion :: Eq RippleConversion
derive instance ordRippleConversion :: Ord RippleConversion

instance showRippleConversion :: Show RippleConversion where
  show RCSymmetric = "symmetric"
  show RCAsymmetric = "asymmetric"

-- | Ripple Effect — Radial wave distortion.
-- |
-- | ## AE Properties
-- |
-- | - Radius: Ripple radius (0-2000)
-- | - Wavelength: Distance between ripples (1-1000)
-- | - Phase: Ripple animation phase (0-360)
-- | - Amplitude: Ripple height (-500 to 500)
-- | - Center: Ripple center point
type RippleEffect =
  { radius :: Number                     -- ^ Ripple radius (0-2000)
  , center :: Point2D                    -- ^ Center point
  , conversion :: RippleConversion       -- ^ Ripple type
  , waveSpeed :: Number                  -- ^ Animation speed (0-100)
  , waveWidth :: Number                  -- ^ Wavelength (1-1000)
  , waveHeight :: Number                 -- ^ Amplitude (-500 to 500)
  , ripplePhase :: Number                -- ^ Phase (0-360)
  }

-- | Default ripple.
defaultRipple :: RippleEffect
defaultRipple =
  { radius: 100.0
  , center: point2D 50.0 50.0
  , conversion: RCSymmetric
  , waveSpeed: 1.0
  , waveWidth: 30.0
  , waveHeight: 20.0
  , ripplePhase: 0.0
  }

-- | Create ripple with specific wave count.
rippleWithWaves :: Number -> Number -> RippleEffect
rippleWithWaves width height =
  { radius: 100.0
  , center: point2D 50.0 50.0
  , conversion: RCSymmetric
  , waveSpeed: 1.0
  , waveWidth: clampNumber 1.0 1000.0 width
  , waveHeight: clampNumber (-500.0) 500.0 height
  , ripplePhase: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // spherize // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spherize Effect — Wrap around sphere.
-- |
-- | ## AE Properties
-- |
-- | - Radius: Sphere radius (0-1000)
-- | - Center: Center of sphere
-- | - Normal: Spherize (positive) or pinch (negative)
type SpherizeEffect =
  { radius :: Number                     -- ^ Sphere radius (0-1000)
  , center :: Point2D                    -- ^ Center point
  , amount :: Number                     -- ^ Distortion amount (-100 to 100)
  }

-- | Default spherize.
defaultSpherize :: SpherizeEffect
defaultSpherize =
  { radius: 100.0
  , center: point2D 50.0 50.0
  , amount: 100.0
  }

-- | Create spherize with specific radius.
spherizeWithRadius :: Number -> Number -> SpherizeEffect
spherizeWithRadius r amt =
  { radius: clampNumber 0.0 1000.0 r
  , center: point2D 50.0 50.0
  , amount: clampNumber (-100.0) 100.0 amt
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // transform // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform Effect — Basic spatial transform.
-- |
-- | ## AE Properties
-- |
-- | Independent transform that doesn't affect layer transform.
type TransformEffect =
  { anchorPoint :: Point2D               -- ^ Transform anchor
  , position :: Point2D                  -- ^ Position
  , uniformScale :: Boolean              -- ^ Lock aspect ratio
  , scaleHeight :: Number                -- ^ Height scale (0-1000%)
  , scaleWidth :: Number                 -- ^ Width scale (0-1000%)
  , skew :: Number                       -- ^ Skew amount (-90 to 90)
  , skewAxis :: Number                   -- ^ Skew axis angle (0-360)
  , rotation :: Number                   -- ^ Rotation (degrees)
  , opacity :: Number                    -- ^ Opacity (0-100)
  , shuttleAngle :: Number               -- ^ Motion blur shutter (0-720)
  , useCompositionShutter :: Boolean     -- ^ Use comp shutter angle
  }

-- | Default transform (no change).
defaultTransform :: TransformEffect
defaultTransform =
  { anchorPoint: point2D 50.0 50.0
  , position: point2D 50.0 50.0
  , uniformScale: true
  , scaleHeight: 100.0
  , scaleWidth: 100.0
  , skew: 0.0
  , skewAxis: 0.0
  , rotation: 0.0
  , opacity: 100.0
  , shuttleAngle: 0.0
  , useCompositionShutter: true
  }

-- | Create transform with specific position.
transformWithPosition :: Number -> Number -> TransformEffect
transformWithPosition x y =
  { anchorPoint: point2D 50.0 50.0
  , position: point2D x y
  , uniformScale: true
  , scaleHeight: 100.0
  , scaleWidth: 100.0
  , skew: 0.0
  , skewAxis: 0.0
  , rotation: 0.0
  , opacity: 100.0
  , shuttleAngle: 0.0
  , useCompositionShutter: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // turbulent // displace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Turbulent displace type.
data TurbulentDisplaceType
  = TDTTurbulentSmooth     -- ^ Smooth turbulent
  | TDTTurbulentSharp      -- ^ Sharp turbulent
  | TDTBulgeSmooth         -- ^ Smooth bulge
  | TDTBulgeSharp          -- ^ Sharp bulge
  | TDTTwist               -- ^ Twisting

derive instance eqTurbulentDisplaceType :: Eq TurbulentDisplaceType
derive instance ordTurbulentDisplaceType :: Ord TurbulentDisplaceType

instance showTurbulentDisplaceType :: Show TurbulentDisplaceType where
  show TDTTurbulentSmooth = "turbulent-smooth"
  show TDTTurbulentSharp = "turbulent-sharp"
  show TDTBulgeSmooth = "bulge-smooth"
  show TDTBulgeSharp = "bulge-sharp"
  show TDTTwist = "twist"

-- | Turbulent Displace Effect — Fractal-based displacement.
-- |
-- | ## AE Properties
-- |
-- | - Displacement: Type of displacement
-- | - Amount: Displacement strength (0-1000)
-- | - Size: Scale of turbulence (1-2000)
-- | - Offset: Position offset for animation
-- | - Complexity: Fractal complexity (1-10)
-- | - Evolution: Animation phase (0-360 x n)
type TurbulentDisplaceEffect =
  { displacement :: TurbulentDisplaceType  -- ^ Displacement type
  , amount :: Number                        -- ^ Strength (0-1000)
  , size :: Number                          -- ^ Scale (1-2000)
  , offset :: Point2D                       -- ^ Position offset
  , complexity :: Number                    -- ^ Fractal complexity (1-10)
  , evolution :: Number                     -- ^ Animation phase (degrees)
  , cycleEvolution :: Boolean               -- ^ Loop evolution
  , cycleRevolutions :: Int                 -- ^ Revolutions per cycle
  , randomSeed :: Int                       -- ^ Random seed
  , pinAllEdges :: Boolean                  -- ^ Lock edges
  , antialiasing :: Boolean                 -- ^ Edge smoothing
  }

-- | Default turbulent displace.
defaultTurbulentDisplace :: TurbulentDisplaceEffect
defaultTurbulentDisplace =
  { displacement: TDTTurbulentSmooth
  , amount: 50.0
  , size: 100.0
  , offset: point2D 0.0 0.0
  , complexity: 2.0
  , evolution: 0.0
  , cycleEvolution: false
  , cycleRevolutions: 1
  , randomSeed: 0
  , pinAllEdges: false
  , antialiasing: true
  }

-- | Create turbulent displace with specific amount.
turbulentDisplaceWithAmount :: Number -> Number -> TurbulentDisplaceEffect
turbulentDisplaceWithAmount amt sz =
  { displacement: TDTTurbulentSmooth
  , amount: clampNumber 0.0 1000.0 amt
  , size: clampNumber 1.0 2000.0 sz
  , offset: point2D 0.0 0.0
  , complexity: 2.0
  , evolution: 0.0
  , cycleEvolution: false
  , cycleRevolutions: 1
  , randomSeed: 0
  , pinAllEdges: false
  , antialiasing: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // twirl // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Twirl Effect — Rotational distortion.
-- |
-- | ## AE Properties
-- |
-- | - Angle: Twirl amount (-3600 to 3600 degrees)
-- | - Twirl Radius: Radius of twirl (0-2000)
-- | - Twirl Center: Center point
type TwirlEffect =
  { angle :: Number                      -- ^ Twirl amount (-3600 to 3600)
  , twirlRadius :: Number                -- ^ Radius (0-2000)
  , twirlCenter :: Point2D               -- ^ Center point
  }

-- | Default twirl.
defaultTwirl :: TwirlEffect
defaultTwirl =
  { angle: 0.0
  , twirlRadius: 100.0
  , twirlCenter: point2D 50.0 50.0
  }

-- | Create twirl with specific angle.
twirlWithAngle :: Number -> Number -> TwirlEffect
twirlWithAngle ang radius =
  { angle: clampNumber (-3600.0) 3600.0 ang
  , twirlRadius: clampNumber 0.0 2000.0 radius
  , twirlCenter: point2D 50.0 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // wave // warp
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wave warp type.
data WaveType
  = WTSine             -- ^ Sine wave
  | WTSquare           -- ^ Square wave
  | WTTriangle         -- ^ Triangle wave
  | WTSawtooth         -- ^ Sawtooth wave
  | WTCircle           -- ^ Circular wave
  | WTSemicircle       -- ^ Semicircle wave
  | WTUncircle         -- ^ Inverted circle
  | WTNoise            -- ^ Random noise

derive instance eqWaveType :: Eq WaveType
derive instance ordWaveType :: Ord WaveType

instance showWaveType :: Show WaveType where
  show WTSine = "sine"
  show WTSquare = "square"
  show WTTriangle = "triangle"
  show WTSawtooth = "sawtooth"
  show WTCircle = "circle"
  show WTSemicircle = "semicircle"
  show WTUncircle = "uncircle"
  show WTNoise = "noise"

-- | Wave Warp Effect — Sine wave distortion.
-- |
-- | ## AE Properties
-- |
-- | - Wave Type: Shape of wave
-- | - Wave Height: Amplitude (0-500)
-- | - Wave Width: Wavelength (1-1000)
-- | - Direction: Wave direction (0-360)
-- | - Wave Speed: Animation speed
-- | - Pinning: Edge pinning
-- | - Phase: Wave phase offset
type WaveWarpEffect =
  { waveType :: WaveType                 -- ^ Wave shape
  , waveHeight :: Number                 -- ^ Amplitude (0-500)
  , waveWidth :: Number                  -- ^ Wavelength (1-1000)
  , direction :: Number                  -- ^ Direction angle (0-360)
  , waveSpeed :: Number                  -- ^ Animation speed
  , pinning :: Int                       -- ^ Edge pinning (0-4)
  , phase :: Number                      -- ^ Phase offset (0-360)
  , antialiasing :: Boolean              -- ^ Edge smoothing
  }

-- | Default wave warp.
defaultWaveWarp :: WaveWarpEffect
defaultWaveWarp =
  { waveType: WTSine
  , waveHeight: 25.0
  , waveWidth: 100.0
  , direction: 0.0
  , waveSpeed: 1.0
  , pinning: 0
  , phase: 0.0
  , antialiasing: true
  }

-- | Create wave warp with specific height.
waveWarpWithHeight :: Number -> Number -> WaveWarpEffect
waveWarpWithHeight height width =
  { waveType: WTSine
  , waveHeight: clampNumber 0.0 500.0 height
  , waveWidth: clampNumber 1.0 1000.0 width
  , direction: 0.0
  , waveSpeed: 1.0
  , pinning: 0
  , phase: 0.0
  , antialiasing: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cc // bend // it
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Bend It Effect — Bend layer around axis.
type CCBendItEffect =
  { start :: Point2D                     -- ^ Start point
  , finish :: Point2D                    -- ^ End point
  , bend :: Number                       -- ^ Bend amount (-100 to 100)
  , quality :: Int                       -- ^ Render quality (1-10)
  }

-- | Default CC Bend It.
defaultCCBendIt :: CCBendItEffect
defaultCCBendIt =
  { start: point2D 0.0 50.0
  , finish: point2D 100.0 50.0
  , bend: 0.0
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // cc // blobbylize
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Blobbylize Effect — Organic blob distortion.
type CCBlobbylizeEffect =
  { softness :: Number                   -- ^ Blob softness (0-100)
  , cutAway :: Number                    -- ^ Cut away amount (0-100)
  , blobLayer :: Int                     -- ^ Control layer index
  , property :: Int                      -- ^ Property to use (0-3)
  }

-- | Default CC Blobbylize.
defaultCCBlobbylize :: CCBlobbylizeEffect
defaultCCBlobbylize =
  { softness: 50.0
  , cutAway: 50.0
  , blobLayer: 1
  , property: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // cc // flo // motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Flo Motion Effect — Flow-based motion blur.
type CCFloMotionEffect =
  { gradientLayer :: Int                 -- ^ Flow gradient layer
  , timeStep :: Number                   -- ^ Time step (0-100)
  , motionVectors :: Int                 -- ^ Vector count (1-32)
  , quality :: Int                       -- ^ Render quality (1-10)
  }

-- | Default CC Flo Motion.
defaultCCFloMotion :: CCFloMotionEffect
defaultCCFloMotion =
  { gradientLayer: 1
  , timeStep: 50.0
  , motionVectors: 8
  , quality: 5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // cc // griddler
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Griddler Effect — Grid-based distortion.
type CCGriddlerEffect =
  { horizontalScale :: Number            -- ^ Horizontal scale (0-200)
  , verticalScale :: Number              -- ^ Vertical scale (0-200)
  , rotation :: Number                   -- ^ Grid rotation (0-360)
  , rows :: Int                          -- ^ Grid rows (1-100)
  , columns :: Int                       -- ^ Grid columns (1-100)
  , offset :: Point2D                    -- ^ Grid offset
  }

-- | Default CC Griddler.
defaultCCGriddler :: CCGriddlerEffect
defaultCCGriddler =
  { horizontalScale: 100.0
  , verticalScale: 100.0
  , rotation: 0.0
  , rows: 10
  , columns: 10
  , offset: point2D 0.0 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cc // lens
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Lens Effect — Lens distortion.
type CCLensEffect =
  { center :: Point2D                    -- ^ Lens center
  , size :: Number                       -- ^ Lens size (0-1000)
  , convergence :: Number                -- ^ Convergence (-100 to 100)
  }

-- | Default CC Lens.
defaultCCLens :: CCLensEffect
defaultCCLens =
  { center: point2D 50.0 50.0
  , size: 100.0
  , convergence: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // cc // page // turn
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Page Turn Effect — Page turn effect.
type CCPageTurnEffect =
  { foldPosition :: Number               -- ^ Fold position (0-100)
  , foldRadius :: Number                 -- ^ Fold radius (0-200)
  , foldDirection :: Number              -- ^ Fold direction (0-360)
  , lightDirection :: Number             -- ^ Light angle (0-360)
  , lightIntensity :: Number             -- ^ Light strength (0-100)
  , backPageOpacity :: Number            -- ^ Back opacity (0-100)
  , backPageColor :: Boolean             -- ^ Use solid color for back
  }

-- | Default CC Page Turn.
defaultCCPageTurn :: CCPageTurnEffect
defaultCCPageTurn =
  { foldPosition: 50.0
  , foldRadius: 25.0
  , foldDirection: 0.0
  , lightDirection: 135.0
  , lightIntensity: 50.0
  , backPageOpacity: 100.0
  , backPageColor: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // cc // power // pin
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Power Pin Effect — Advanced corner pin.
type CCPowerPinEffect =
  { topLeft :: Point2D                   -- ^ Top-left corner
  , topRight :: Point2D                  -- ^ Top-right corner
  , bottomLeft :: Point2D                -- ^ Bottom-left corner
  , bottomRight :: Point2D               -- ^ Bottom-right corner
  , perspective :: Boolean               -- ^ Perspective mode
  , autoFocal :: Boolean                 -- ^ Auto focal length
  , focalLength :: Number                -- ^ Manual focal length
  }

-- | Default CC Power Pin.
defaultCCPowerPin :: CCPowerPinEffect
defaultCCPowerPin =
  { topLeft: point2D 0.0 0.0
  , topRight: point2D 100.0 0.0
  , bottomLeft: point2D 0.0 100.0
  , bottomRight: point2D 100.0 100.0
  , perspective: true
  , autoFocal: true
  , focalLength: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // cc // ripple // pulse
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Ripple Pulse Effect — Expanding ripple.
type CCRipplePulseEffect =
  { center :: Point2D                    -- ^ Ripple center
  , radius :: Number                     -- ^ Ripple radius (0-2000)
  , amplitude :: Number                  -- ^ Wave height (0-200)
  , pulseLevel :: Number                 -- ^ Pulse intensity (0-100)
  , waveWidth :: Number                  -- ^ Wavelength (1-500)
  , phase :: Number                      -- ^ Phase offset (0-360)
  , waveSpeed :: Number                  -- ^ Animation speed
  }

-- | Default CC Ripple Pulse.
defaultCCRipplePulse :: CCRipplePulseEffect
defaultCCRipplePulse =
  { center: point2D 50.0 50.0
  , radius: 100.0
  , amplitude: 25.0
  , pulseLevel: 100.0
  , waveWidth: 50.0
  , phase: 0.0
  , waveSpeed: 1.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // slant
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Slant Effect — Perspective slant.
type CCSlantEffect =
  { slant :: Number                      -- ^ Slant amount (-100 to 100)
  , floor :: Number                      -- ^ Floor position (0-100)
  , height :: Number                     -- ^ Height (0-200)
  , direction :: Number                  -- ^ Slant direction (0-360)
  }

-- | Default CC Slant.
defaultCCSlant :: CCSlantEffect
defaultCCSlant =
  { slant: 0.0
  , floor: 50.0
  , height: 100.0
  , direction: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // smear
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Smear Effect — Directional smear.
type CCSmearEffect =
  { sourcePoint :: Point2D               -- ^ Source position
  , destinationPoint :: Point2D          -- ^ Destination position
  , percentSource :: Number              -- ^ Source influence (0-100)
  , percentDestination :: Number         -- ^ Destination influence (0-100)
  }

-- | Default CC Smear.
defaultCCSmear :: CCSmearEffect
defaultCCSmear =
  { sourcePoint: point2D 25.0 50.0
  , destinationPoint: point2D 75.0 50.0
  , percentSource: 50.0
  , percentDestination: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // split
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Split direction.
data CCSplitDirection
  = CSDHorizontal      -- ^ Horizontal split
  | CSDVertical        -- ^ Vertical split
  | CSDBoth            -- ^ Both directions

derive instance eqCCSplitDirection :: Eq CCSplitDirection
derive instance ordCCSplitDirection :: Ord CCSplitDirection

instance showCCSplitDirection :: Show CCSplitDirection where
  show CSDHorizontal = "horizontal"
  show CSDVertical = "vertical"
  show CSDBoth = "both"

-- | CC Split Effect — Split/duplicate effect.
type CCSplitEffect =
  { splitPoint :: Point2D                -- ^ Split position
  , direction :: CCSplitDirection        -- ^ Split direction
  , splitWidth :: Number                 -- ^ Split gap (0-500)
  }

-- | Default CC Split.
defaultCCSplit :: CCSplitEffect
defaultCCSplit =
  { splitPoint: point2D 50.0 50.0
  , direction: CSDHorizontal
  , splitWidth: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cc // tiler
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Tiler Effect — Tiling effect.
type CCTilerEffect =
  { scale :: Number                      -- ^ Tile scale (1-1000)
  , offset :: Point2D                    -- ^ Tile offset
  , rotation :: Number                   -- ^ Tile rotation (0-360)
  , blendOriginal :: Number              -- ^ Original blend (0-100)
  , mirrorEdges :: Boolean               -- ^ Mirror at edges
  }

-- | Default CC Tiler.
defaultCCTiler :: CCTilerEffect
defaultCCTiler =
  { scale: 100.0
  , offset: point2D 0.0 0.0
  , rotation: 0.0
  , blendOriginal: 0.0
  , mirrorEdges: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

warpEffectName :: WarpEffect -> String
warpEffectName _ = "Warp"

displacementMapEffectName :: DisplacementMapEffect -> String
displacementMapEffectName _ = "Displacement Map"

bezierWarpEffectName :: BezierWarpEffect -> String
bezierWarpEffectName _ = "Bezier Warp"

bulgeEffectName :: BulgeEffect -> String
bulgeEffectName _ = "Bulge"

cornerPinEffectName :: CornerPinEffect -> String
cornerPinEffectName _ = "Corner Pin"

liquifyEffectName :: LiquifyEffect -> String
liquifyEffectName _ = "Liquify"

mirrorEffectName :: MirrorEffect -> String
mirrorEffectName _ = "Mirror"

offsetEffectName :: OffsetEffect -> String
offsetEffectName _ = "Offset"

opticsCompensationEffectName :: OpticsCompensationEffect -> String
opticsCompensationEffectName _ = "Optics Compensation"

polarCoordinatesEffectName :: PolarCoordinatesEffect -> String
polarCoordinatesEffectName _ = "Polar Coordinates"

rippleEffectName :: RippleEffect -> String
rippleEffectName _ = "Ripple"

spherizeEffectName :: SpherizeEffect -> String
spherizeEffectName _ = "Spherize"

transformEffectName :: TransformEffect -> String
transformEffectName _ = "Transform"

turbulentDisplaceEffectName :: TurbulentDisplaceEffect -> String
turbulentDisplaceEffectName _ = "Turbulent Displace"

twirlEffectName :: TwirlEffect -> String
twirlEffectName _ = "Twirl"

waveWarpEffectName :: WaveWarpEffect -> String
waveWarpEffectName _ = "Wave Warp"

ccBendItEffectName :: CCBendItEffect -> String
ccBendItEffectName _ = "CC Bend It"

ccBlobbylizeEffectName :: CCBlobbylizeEffect -> String
ccBlobbylizeEffectName _ = "CC Blobbylize"

ccFloMotionEffectName :: CCFloMotionEffect -> String
ccFloMotionEffectName _ = "CC Flo Motion"

ccGriddlerEffectName :: CCGriddlerEffect -> String
ccGriddlerEffectName _ = "CC Griddler"

ccLensEffectName :: CCLensEffect -> String
ccLensEffectName _ = "CC Lens"

ccPageTurnEffectName :: CCPageTurnEffect -> String
ccPageTurnEffectName _ = "CC Page Turn"

ccPowerPinEffectName :: CCPowerPinEffect -> String
ccPowerPinEffectName _ = "CC Power Pin"

ccRipplePulseEffectName :: CCRipplePulseEffect -> String
ccRipplePulseEffectName _ = "CC Ripple Pulse"

ccSlantEffectName :: CCSlantEffect -> String
ccSlantEffectName _ = "CC Slant"

ccSmearEffectName :: CCSmearEffect -> String
ccSmearEffectName _ = "CC Smear"

ccSplitEffectName :: CCSplitEffect -> String
ccSplitEffectName _ = "CC Split"

ccTilerEffectName :: CCTilerEffect -> String
ccTilerEffectName _ = "CC Tiler"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

describeWarp :: WarpEffect -> String
describeWarp e =
  "Warp(" <> show e.warpStyle <> ", bend: " <> show e.bend <> ")"

describeDisplacementMap :: DisplacementMapEffect -> String
describeDisplacementMap e =
  "DisplacementMap(layer: " <> show e.mapLayer 
    <> ", h: " <> show e.maxHorizontalDisplacement
    <> ", v: " <> show e.maxVerticalDisplacement <> ")"

describeBulge :: BulgeEffect -> String
describeBulge e =
  "Bulge(radius: " <> show e.horizontalRadius <> "x" <> show e.verticalRadius
    <> ", height: " <> show e.bulgeHeight <> ")"

describeTwirl :: TwirlEffect -> String
describeTwirl e =
  "Twirl(angle: " <> show e.angle <> "°, radius: " <> show e.twirlRadius <> ")"

describeWaveWarp :: WaveWarpEffect -> String
describeWaveWarp e =
  "WaveWarp(" <> show e.waveType 
    <> ", height: " <> show e.waveHeight
    <> ", width: " <> show e.waveWidth <> ")"

describeTurbulentDisplace :: TurbulentDisplaceEffect -> String
describeTurbulentDisplace e =
  "TurbulentDisplace(" <> show e.displacement
    <> ", amount: " <> show e.amount
    <> ", complexity: " <> show e.complexity <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if warp has any bend applied.
isWarpBent :: WarpEffect -> Boolean
isWarpBent e = e.bend > 0.0 || e.bend < 0.0

-- | Check if displacement is active (non-zero displacement).
isDisplacementActive :: DisplacementMapEffect -> Boolean
isDisplacementActive e = 
  e.maxHorizontalDisplacement > 0.0 || e.maxVerticalDisplacement > 0.0

-- | Check if bulge has significant height.
hasBulgeHeight :: BulgeEffect -> Boolean
hasBulgeHeight e = e.bulgeHeight > 0.1 || e.bulgeHeight < (-0.1)

-- | Check if twirl angle is significant (> 10 degrees).
isTwirlSignificant :: TwirlEffect -> Boolean
isTwirlSignificant e = e.angle >= 10.0 || e.angle <= (-10.0)

-- | Check if wave warp has animation speed.
isWaveWarpAnimated :: WaveWarpEffect -> Boolean
isWaveWarpAnimated e = e.waveSpeed > 0.0

-- | Check if turbulent displace is complex (complexity >= 5).
isTurbulentDisplaceComplex :: TurbulentDisplaceEffect -> Boolean
isTurbulentDisplaceComplex e = e.complexity >= 5.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // additional // serialization
-- ═════════════════════════════════════════════════════════════════════════════

liquifyToolToString :: LiquifyTool -> String
liquifyToolToString = show

polarTypeToString :: PolarType -> String
polarTypeToString = show

rippleConversionToString :: RippleConversion -> String
rippleConversionToString = show

turbulentDisplaceTypeToString :: TurbulentDisplaceType -> String
turbulentDisplaceTypeToString = show

waveTypeToString :: WaveType -> String
waveTypeToString = show

ccSplitDirectionToString :: CCSplitDirection -> String
ccSplitDirectionToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // advanced // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale warp bend by a factor.
scaleWarpBend :: Number -> WarpEffect -> WarpEffect
scaleWarpBend factor e =
  { warpStyle: e.warpStyle
  , bend: clampNumber (-100.0) 100.0 $ e.bend * factor
  , horizontalDistortion: e.horizontalDistortion
  , verticalDistortion: e.verticalDistortion
  }

-- | Combine two bulge effects (average heights).
combineBulgeHeights :: BulgeEffect -> BulgeEffect -> Number
combineBulgeHeights a b = (a.bulgeHeight + b.bulgeHeight) / 2.0

-- | Compute total displacement magnitude.
totalDisplacementMagnitude :: DisplacementMapEffect -> Number
totalDisplacementMagnitude e = 
  e.maxHorizontalDisplacement + e.maxVerticalDisplacement

-- | Compute wave warp intensity (height * width ratio).
waveWarpIntensity :: WaveWarpEffect -> Number
waveWarpIntensity e = e.waveHeight * (100.0 / e.waveWidth)

-- | Check if bulge is expanding or contracting.
isBulgeExpanding :: BulgeEffect -> Boolean
isBulgeExpanding e = e.bulgeHeight > 0.0

-- | Compute effective twirl revolutions.
twirlRevolutions :: TwirlEffect -> Number
twirlRevolutions e = e.angle / 360.0

-- | Adjust twirl angle by offset.
offsetTwirlAngle :: Number -> TwirlEffect -> TwirlEffect
offsetTwirlAngle offset e =
  { angle: clampNumber (-3600.0) 3600.0 $ e.angle + offset
  , twirlRadius: e.twirlRadius
  , twirlCenter: e.twirlCenter
  }

-- | Scale turbulent displace amount.
scaleTurbulentAmount :: Number -> TurbulentDisplaceEffect -> TurbulentDisplaceEffect
scaleTurbulentAmount factor e =
  { displacement: e.displacement
  , amount: clampNumber 0.0 1000.0 $ e.amount * factor
  , size: e.size
  , offset: e.offset
  , complexity: e.complexity
  , evolution: e.evolution
  , cycleEvolution: e.cycleEvolution
  , cycleRevolutions: e.cycleRevolutions
  , randomSeed: e.randomSeed
  , pinAllEdges: e.pinAllEdges
  , antialiasing: e.antialiasing
  }

-- | Compute displacement difference.
displacementDifference :: DisplacementMapEffect -> DisplacementMapEffect -> Number
displacementDifference a b =
  let
    hDiff = a.maxHorizontalDisplacement - b.maxHorizontalDisplacement
    vDiff = a.maxVerticalDisplacement - b.maxVerticalDisplacement
  in
    hDiff + vDiff

-- | Classify warp intensity by bend amount.
classifyWarpIntensity :: WarpEffect -> String
classifyWarpIntensity e
  | e.bend >= 75.0 || e.bend <= (-75.0) = "extreme"
  | e.bend >= 50.0 || e.bend <= (-50.0) = "strong"
  | e.bend >= 25.0 || e.bend <= (-25.0) = "moderate"
  | e.bend > 0.0 || e.bend < 0.0 = "subtle"
  | otherwise = "none"

-- | Check if transform has any spatial change.
hasTransformChange :: TransformEffect -> Boolean
hasTransformChange e =
  e.scaleHeight > 100.0 || e.scaleHeight < 100.0 ||
  e.scaleWidth > 100.0 || e.scaleWidth < 100.0 ||
  e.rotation > 0.0 || e.rotation < 0.0 ||
  e.skew > 0.0 || e.skew < 0.0

-- | Check if both warp distortions are active.
hasWarpBothDistortions :: WarpEffect -> Boolean
hasWarpBothDistortions e =
  (e.horizontalDistortion > 0.0 || e.horizontalDistortion < 0.0) &&
  (e.verticalDistortion > 0.0 || e.verticalDistortion < 0.0)
