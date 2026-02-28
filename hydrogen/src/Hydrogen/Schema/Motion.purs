-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // schema // motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Motion Graphics Schema - Atoms for animation and video production
-- |
-- | This module provides the foundational types for motion graphics:
-- | - **Timecode**: SMPTE timecode representation
-- | - **TimeRange**: In/out point pairs for clips and layers
-- | - **Keyframe**: Animation keyframe data with tangents
-- | - **Easing**: Interpolation curves
-- | - **ZoomLevel**: Timeline zoom state
-- |
-- | ## Usage
-- |
-- | Import submodules with qualification:
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Timecode as TC
-- | import Hydrogen.Schema.Motion.TimeRange as TR
-- | import Hydrogen.Schema.Motion.Keyframe as KF
-- | import Hydrogen.Schema.Motion.Easing as Easing
-- | import Hydrogen.Schema.Motion.ZoomLevel as Zoom
-- | ```
-- |
-- | ## Integration with Temporal
-- |
-- | Motion types integrate with `Hydrogen.Schema.Dimension.Temporal`:
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Dimension.Temporal (Frames, FrameRate, fps24)
-- | import Hydrogen.Schema.Motion.Timecode as TC
-- |
-- | -- Convert between frames and timecode
-- | tc = TC.fromFrames (frames 2880.0) fps24 false
-- | -- Result: 00:02:00:00 (2 minutes at 24fps)
-- | ```
-- |
-- | ## For LATTICE
-- |
-- | These types are the foundation for LATTICE motion graphics components:
-- | - AnimationTimeline uses Timecode, TimeRange, ZoomLevel
-- | - KeyframeMarker uses Keyframe, Easing
-- | - CurveEditor uses Keyframe, Easing
-- |
-- | Do NOT import this module directly. Import submodules with qualification.
-- |
-- | This module exists for documentation purposes. Use qualified imports:
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Timecode as TC
-- | import Hydrogen.Schema.Motion.TimeRange as TR
-- | ```
module Hydrogen.Schema.Motion
  ( -- * Types (re-exported for convenience)
    module Timecode
  , module TimeRange
  , module Keyframe
  , module Easing
  , module ZoomLevel
  ) where

-- Only export types, not functions with name collisions
import Hydrogen.Schema.Motion.Timecode (Timecode, TimecodeComponents) as Timecode
import Hydrogen.Schema.Motion.TimeRange (TimeRange) as TimeRange
import Hydrogen.Schema.Motion.Keyframe (Keyframe, KeyframeId, KeyframeValue, Tangent, InterpolationType(Linear, Bezier, Hold, Auto)) as Keyframe
import Hydrogen.Schema.Motion.Easing (Easing, CubicBezier) as Easing
import Hydrogen.Schema.Motion.ZoomLevel (ZoomLevel) as ZoomLevel
