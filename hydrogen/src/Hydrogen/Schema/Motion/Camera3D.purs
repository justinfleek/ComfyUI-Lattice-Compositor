-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // camera-3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Camera system for motion graphics compositions.
-- |
-- | Provides complete camera functionality matching After Effects' 3D camera
-- | system, including depth of field, iris properties, and viewport states.
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Camera` from the Haskell backend exactly.
-- |
-- | ## Features
-- |
-- | - One-node and two-node cameras
-- | - Full depth of field with iris simulation
-- | - Bokeh highlight properties
-- | - Custom viewport states for 3D views
-- | - Camera keyframe animation
-- |
-- | ## Submodules
-- |
-- | - `Camera3D.Enums` — All enumeration types with `all*` arrays
-- | - `Camera3D.Vectors` — Vec2, Vec3 types
-- | - `Camera3D.DepthOfField` — DOF, Iris, Highlight properties
-- | - `Camera3D.Camera` — CameraId, Camera3D type
-- | - `Camera3D.Presets` — Standard camera presets
-- | - `Camera3D.Viewport` — Custom views and viewport state
-- | - `Camera3D.ViewOptions` — Display settings for 3D views
-- | - `Camera3D.Keyframe` — Camera animation keyframes

module Hydrogen.Schema.Motion.Camera3D
  ( -- * Enumerations
    module Hydrogen.Schema.Motion.Camera3D.Enums
  
    -- * Vector Types
  , module Hydrogen.Schema.Motion.Camera3D.Vectors
  
    -- * Depth of Field
  , module Hydrogen.Schema.Motion.Camera3D.DepthOfField
  
    -- * Camera3D
  , module Hydrogen.Schema.Motion.Camera3D.Camera
  
    -- * Camera Preset
  , module Hydrogen.Schema.Motion.Camera3D.Presets
  
    -- * Viewport State
  , module Hydrogen.Schema.Motion.Camera3D.Viewport
  
    -- * View Options
  , module Hydrogen.Schema.Motion.Camera3D.ViewOptions
  
    -- * Camera Keyframe
  , module Hydrogen.Schema.Motion.Camera3D.Keyframe
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.Camera3D.Enums
  ( CameraType(CTOneNode, CTTwoNode)
  , allCameraTypes
  , cameraTypeToString
  , cameraTypeFromString
  
  , AutoOrientMode(AOMOff, AOMOrientAlongPath, AOMOrientTowardsPOI)
  , allAutoOrientModes
  , autoOrientModeToString
  , autoOrientModeFromString
  
  , MeasureFilmSize(MFSHorizontal, MFSVertical, MFSDiagonal)
  , allMeasureFilmSizes
  , measureFilmSizeToString
  , measureFilmSizeFromString
  
  , WireframeVisibility(WVAlways, WVSelected, WVOff)
  , allWireframeVisibilities
  , wireframeVisibilityToString
  , wireframeVisibilityFromString
  
  , ViewType
      ( VTActiveCamera
      , VTCustom1
      , VTCustom2
      , VTCustom3
      , VTFront
      , VTBack
      , VTLeft
      , VTRight
      , VTTop
      , VTBottom
      )
  , allViewTypes
  , viewTypeToString
  , viewTypeFromString
  
  , ViewLayout(VLOneView, VLTwoViewHorizontal, VLTwoViewVertical, VLFourView)
  , allViewLayouts
  , viewLayoutToString
  , viewLayoutFromString
  
  , SpatialInterpolation(SILinear, SIBezier, SIAutoBezier, SIContinuousBezier)
  , allSpatialInterpolations
  , spatialInterpolationToString
  , spatialInterpolationFromString
  
  , TemporalInterpolation(TILinear, TIBezier, TIHold)
  , allTemporalInterpolations
  , temporalInterpolationToString
  , temporalInterpolationFromString
  )

import Hydrogen.Schema.Motion.Camera3D.Vectors
  ( Vec2(Vec2)
  , mkVec2
  , vec2Zero
  
  , Vec3(Vec3)
  , mkVec3
  , vec3Zero
  )

import Hydrogen.Schema.Motion.Camera3D.DepthOfField
  ( DepthOfFieldSettings(DepthOfFieldSettings)
  , mkDepthOfFieldSettings
  , defaultDepthOfFieldSettings
  , dofDisabled
  
  , IrisProperties(IrisProperties)
  , mkIrisProperties
  , defaultIrisProperties
  
  , HighlightProperties(HighlightProperties)
  , mkHighlightProperties
  , defaultHighlightProperties
  )

import Hydrogen.Schema.Motion.Camera3D.Camera
  ( CameraId(CameraId)
  , mkCameraId
  
  , Camera3D(Camera3D)
  , mkCamera3D
  , defaultCamera3D
  )

import Hydrogen.Schema.Motion.Camera3D.Presets
  ( CameraPreset(CameraPreset)
  , mkCameraPreset
  , allCameraPresets
  , preset15mm
  , preset20mm
  , preset24mm
  , preset35mm
  , preset50mm
  , preset80mm
  , preset135mm
  , preset200mm
  )

import Hydrogen.Schema.Motion.Camera3D.Viewport
  ( CustomViewState(CustomViewState)
  , mkCustomViewState
  , defaultCustomViewState
  
  , CustomViews(CustomViews)
  , mkCustomViews
  , defaultCustomViews
  
  , ViewportState(ViewportState)
  , mkViewportState
  , defaultViewportState
  )

import Hydrogen.Schema.Motion.Camera3D.ViewOptions
  ( ViewOptions(ViewOptions)
  , mkViewOptions
  , defaultViewOptions
  )

import Hydrogen.Schema.Motion.Camera3D.Keyframe
  ( CameraKeyframe(CameraKeyframe)
  , mkCameraKeyframe
  , cameraKeyframeAtFrame
  )
