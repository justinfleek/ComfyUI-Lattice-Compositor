-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // motion // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect types, enums, and parameters for motion graphics.
-- |
-- | This is the leader module that re-exports all Effects submodules.
-- | Effects are visual filters and transformations applied to layers.
-- | Each effect has parameters that can be animated.
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Effects` from the Haskell backend.
-- |
-- | ## Categories
-- |
-- | - Blur/Sharpen: Gaussian, directional, radial blur
-- | - Color Correction: Levels, curves, color balance
-- | - Distort: Warp, displacement, mesh deform
-- | - Generate: Fractal noise, gradients
-- | - Stylize: Glow, shadows, scanlines
-- | - Time: Echo, time displacement
-- |
-- | ## Submodules
-- |
-- | - Effects.Core: Parameter types, effect categories, effect instances
-- | - Effects.Blur: Blur dimension, radial blur type, antialiasing
-- | - Effects.Distortion: Warp styles, displacement maps, edge behavior
-- | - Effects.Glow: Composite modes, falloff, tonemapping, bloom
-- | - Effects.Noise: Fractal types, noise types
-- | - Effects.Time: Echo operators, time resolution
-- | - Effects.Mesh: Pin falloff, turbulent displacement, pinning modes
-- | - Effects.Stylize: Scanlines, dithering, halftone, pixel sorting

module Hydrogen.Schema.Motion.Effects
  ( -- * Re-exports from Core
    module Core
    
    -- * Re-exports from Blur
  , module Blur
  
    -- * Re-exports from Distortion
  , module Distortion
  
    -- * Re-exports from Glow
  , module Glow
  
    -- * Re-exports from Noise
  , module Noise
  
    -- * Re-exports from Time
  , module Time
  
    -- * Re-exports from Mesh
  , module Mesh
  
    -- * Re-exports from Stylize
  , module Stylize
  ) where

import Hydrogen.Schema.Motion.Effects.Core
  ( EffectParameterType(..)
  , allEffectParameterTypes
  , effectParameterTypeToString
  , effectParameterTypeFromString
  , EffectAnimatableType(..)
  , allEffectAnimatableTypes
  , effectAnimatableTypeToString
  , effectAnimatableTypeFromString
  , EffectCategory(..)
  , allEffectCategories
  , effectCategoryToString
  , effectCategoryFromString
  , EffectPoint2D
  , mkEffectPoint2D
  , EffectPoint3D
  , mkEffectPoint3D
  , EffectRGBA
  , mkEffectRGBA
  , effectRGBAOpaque
  , CurvePoint
  , mkCurvePoint
  , EffectParameterValue(..)
  , EffectDropdownOption
  , EffectParameterDef
  , defaultEffectParameterDef
  , EffectParameter
  , defaultEffectParameter
  , EffectId(..)
  , mkEffectId
  , Effect
  , defaultEffect
  , effectEnabled
  , EffectInstance
  , defaultEffectInstance
  , MeshDeformEffectInstance
  , EffectDefinition
  , EffectCategoryInfo
  ) as Core

import Hydrogen.Schema.Motion.Effects.Blur
  ( BlurDimension(..)
  , allBlurDimensions
  , blurDimensionToString
  , blurDimensionFromString
  , RadialBlurType(..)
  , allRadialBlurTypes
  , radialBlurTypeToString
  , radialBlurTypeFromString
  , AntialiasingQuality(..)
  , allAntialiasingQualities
  , antialiasingQualityToString
  , antialiasingQualityFromString
  ) as Blur

import Hydrogen.Schema.Motion.Effects.Distortion
  ( RampShape(..)
  , allRampShapes
  , rampShapeToString
  , rampShapeFromString
  , WarpStyle(..)
  , allWarpStyles
  , warpStyleToString
  , warpStyleFromString
  , DisplacementMapType(..)
  , allDisplacementMapTypes
  , displacementMapTypeToString
  , displacementMapTypeFromString
  , DisplacementChannel(..)
  , allDisplacementChannels
  , displacementChannelToString
  , displacementChannelFromString
  , EdgeBehavior(..)
  , allEdgeBehaviors
  , edgeBehaviorToString
  , edgeBehaviorFromString
  ) as Distortion

import Hydrogen.Schema.Motion.Effects.Glow
  ( GlowCompositeMode(..)
  , allGlowCompositeModes
  , glowCompositeModeToString
  , glowCompositeModeFromString
  , GlowColorsMode(..)
  , allGlowColorsModes
  , glowColorsModeToString
  , glowColorsModeFromString
  , ColorLooping(..)
  , allColorLoopings
  , colorLoopingToString
  , colorLoopingFromString
  , FalloffMode(..)
  , allFalloffModes
  , falloffModeToString
  , falloffModeFromString
  , TonemapMode(..)
  , allTonemapModes
  , tonemapModeToString
  , tonemapModeFromString
  , BloomBlendMode(..)
  , allBloomBlendModes
  , bloomBlendModeToString
  , bloomBlendModeFromString
  ) as Glow

import Hydrogen.Schema.Motion.Effects.Noise
  ( FractalType(..)
  , allFractalTypes
  , fractalTypeToString
  , fractalTypeFromString
  , NoiseType(..)
  , allNoiseTypes
  , noiseTypeToString
  , noiseTypeFromString
  ) as Noise

import Hydrogen.Schema.Motion.Effects.Time
  ( EchoOperator(..)
  , allEchoOperators
  , echoOperatorToString
  , echoOperatorFromString
  , TimeResolution(..)
  , allTimeResolutions
  , timeResolutionToString
  , timeResolutionFromString
  ) as Time

import Hydrogen.Schema.Motion.Effects.Mesh
  ( PinFalloff(..)
  , allPinFalloffs
  , pinFalloffToString
  , pinFalloffFromString
  , TurbulentDisplaceType(..)
  , allTurbulentDisplaceTypes
  , turbulentDisplaceTypeToString
  , turbulentDisplaceTypeFromString
  , PinningMode(..)
  , allPinningModes
  , pinningModeToString
  , pinningModeFromString
  ) as Mesh

import Hydrogen.Schema.Motion.Effects.Stylize
  ( ScanlinesDirection(..)
  , allScanlinesDirections
  , scanlinesDirectionToString
  , scanlinesDirectionFromString
  , RGBSplitBlendMode(..)
  , allRGBSplitBlendModes
  , rgbSplitBlendModeToString
  , rgbSplitBlendModeFromString
  , PixelSortDirection(..)
  , allPixelSortDirections
  , pixelSortDirectionToString
  , pixelSortDirectionFromString
  , SortByCriterion(..)
  , allSortByCriteria
  , sortByCriterionToString
  , sortByCriterionFromString
  , HalftoneColorMode(..)
  , allHalftoneColorModes
  , halftoneColorModeToString
  , halftoneColorModeFromString
  , DitherMethod(..)
  , allDitherMethods
  , ditherMethodToString
  , ditherMethodFromString
  , DitherMatrixSize(..)
  , allDitherMatrixSizes
  , ditherMatrixSizeToString
  , ditherMatrixSizeFromString
  , EffectColorChannel(..)
  , allEffectColorChannels
  , effectColorChannelToString
  , effectColorChannelFromString
  , HSLChannel(..)
  , allHSLChannels
  , hslChannelToString
  , hslChannelFromString
  ) as Stylize
