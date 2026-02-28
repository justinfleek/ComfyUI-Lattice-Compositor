-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // gpu // frame-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FrameState — Per-Frame Animation and Interaction State
-- |
-- | ## Design Philosophy
-- |
-- | Hyper-responsive UIs like Frame.io and Ghostty achieve their fluidity by
-- | treating animation as **external state** that flows into effects, not
-- | internal state that effects manage themselves.
-- |
-- | FrameState captures everything a render pass needs to know about "now":
-- |
-- | - **Time**: Current timestamp, delta time, frame number
-- | - **Input**: Mouse, touch, stylus, gestures (via Input submodule)
-- | - **Animations**: Keyframe animations, spring physics (via Animation submodule)
-- | - **Viewport**: Size, DPI, orientation
-- | - **Performance**: FPS target, GPU budget remaining
-- |
-- | ## Why External State?
-- |
-- | At billion-agent scale, internal animation state creates chaos:
-- | - Each agent has its own timers → clock drift
-- | - Animation state scattered across components → hard to serialize
-- | - No global coordination → janky frame timing
-- |
-- | With external state:
-- | - One clock source → frame-perfect sync
-- | - All animation state in FrameState → serializable, replayable
-- | - Deterministic renders → same FrameState = same pixels
-- |
-- | ## Module Structure
-- |
-- | - `FrameState` (this module) — Leader, composite type, time, construction
-- | - `FrameState.Animation` — AnimationRegistry, SpringRegistry, temporal interpolation
-- | - `FrameState.Input` — (future) Unified PointerState, Touch, Stylus, Gesture
-- | - `FrameState.Viewport` — (future) ViewportState, PerformanceState

module Hydrogen.GPU.FrameState
  ( -- * Core Types
    FrameState
  , FrameTime
  , FrameNumber
  
  -- * Time State
  , TimeState
  , mkTimeState
  , advanceTime
  , deltaMs
  , elapsedMs
  , frameNumber
  , fps
  
  -- * Mouse State (will move to Input submodule)
  , MouseState
  , MouseButton(MouseLeft, MouseMiddle, MouseRight, MouseBack, MouseForward)
  , mkMouseState
  , mousePosition
  , mouseButtons
  , mouseHoverTarget
  , mouseDelta
  , mouseVelocity
  
  -- * Animation Types (re-exported from FrameState.Animation)
  -- | Import Hydrogen.GPU.FrameState.Animation directly for full API
  , module Anim
  
  -- * Viewport State
  , ViewportState
  , ViewportOrientation(OrientationPortrait, OrientationLandscape, OrientationSquare)
  , mkViewportState
  , viewportWidth
  , viewportHeight
  , viewportDPI
  , viewportOrientation
  
  -- * Viewport Change Detection
  , viewportResized
  , viewportOrientationChanged
  , viewportDPRChanged
  , viewportShapeChanged
  , viewportAnyChange
  
  -- * Viewport Tensor (for diffusion/GPU rendering)
  , viewportTensor
  , viewportLatentWidth
  , viewportLatentHeight
  , viewportLatentSize
  
  -- * Viewport Shape (for non-rectangular displays)
  , viewportClipShape
  , viewportSafeArea
  , mkViewportStateWithShape
  , mkCircularViewport
  , mkRoundedRectViewport
  , mkPathViewport
  , mkEllipticalViewport
  
  -- * Viewport Deltas
  , viewportWidthDelta
  , viewportHeightDelta
  
  -- * Performance State
  , PerformanceState
  , mkPerformanceState
  , targetFPS
  , actualFPS
  , gpuBudgetMs
  , gpuUsedMs
  , frameDropped
  
  -- * FrameState Construction
  , mkFrameState
  , emptyFrameState
  
  -- * Default Values (documented rationale)
  , defaultViewportWidth
  , defaultViewportHeight
  , defaultDevicePixelRatio
  , defaultTargetFPS
  , defaultStartTime
  
  -- * FrameState Updates
  , updateTime
  , updateMouse
  , updateViewport
  , updatePerformance
  , tick
  
  -- * FrameState Queries
  , isHovering
  , isPressed
  , animationProgress
  , springValue
  , springValueOr
  , timeSinceStart
  , framesPerSecond
  , animationCount
  , clampedFPS
  , hasActiveAnimations
  , frameNumberAsNumber
  
  -- * Debug Output (SHOW_DEBUG_CONVENTION)
  , showTimeState
  , showMouseState
  , showViewportState
  , showPerformanceState
  , showFrameState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , (<>)
  , (==)
  , (/=)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , ($)
  , (||)
  , min
  , max
  )

import Data.Array as Array
import Data.Int as Int
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)

-- Viewport tensor abstraction (Schema.Spatial.Viewport)
import Hydrogen.Schema.Spatial.Viewport as Viewport
import Hydrogen.Schema.Spatial.Viewport
  ( ViewportTensor(ViewportTensor)
  , viewportFromPixels
  , pixelWidth
  , pixelHeight
  , latentWidth
  , latentHeight
  , totalLatents
  )

-- Geometric shape for viewport clipping (rectangle, circle, bezier paths, etc.)
import Hydrogen.Schema.Geometry.Shape as GeoShape
import Hydrogen.Schema.Geometry.Shape
  ( Shape
      ( ShapeRectangle
      , ShapeEllipse
      , ShapePath
      , ShapePolygon
      , ShapeCompound
      )
  , RectangleShape
  , rectangleShape
  , EllipseShape
  , circleShape
  , PathShape
  , pathShape
  , PathCommand
      ( MoveTo
      , LineTo
      , CubicTo
      , QuadraticTo
      , ArcTo
      , ClosePath
      )
  , PixelPoint2D
  , pixelPoint2D
  , pixelOrigin
  )

-- Corner radius for rounded rectangles
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Radius (Corners, cornersAll, none)

-- Device units for viewport dimensions
import Hydrogen.Schema.Dimension.Device 
  ( Pixel(Pixel)
  , DevicePixelRatio(DevicePixelRatio)
  , dpr
  , unwrapPixel
  , unwrapDpr
  )

-- Animation types (re-exported via `module Anim`)
-- Full explicit list for documentation — this IS what gets re-exported:
--   AnimationHandle, AnimationPhase(..), AnimationInstance
--   EasingType(..), AnimationDirection(..), AnimationIteration(..)
--   AnimationRegistry, mkAnimationRegistry, registerAnimation, unregisterAnimation
--   getAnimationPhase, getAllAnimations, tickAnimations
--   SpringHandle, SpringInstance, SpringRegistry
--   mkSpringRegistry, registerSpring, getSpringValue, getSpringValueMaybe
--   setSpringTarget, tickSprings
--   animationsAsList, springsAsList, runningAnimations, completedAnimations
--   animationHandles, springHandles, findAnimationByPhase
--   anyAnimationRunning, allAnimationsComplete
-- Note: FrameTime is NOT re-exported here — use the one from this module
import Hydrogen.GPU.FrameState.Animation
  ( AnimationHandle
  , AnimationPhase
      ( AnimationIdle
      , AnimationRunning
      , AnimationComplete
      , AnimationReversing
      )
  , AnimationInstance
  , EasingType
      ( EasingLinear
      , EasingEaseIn
      , EasingEaseOut
      , EasingEaseInOut
      , EasingSpring
      )
  , AnimationDirection
      ( DirectionNormal
      , DirectionReverse
      , DirectionAlternate
      , DirectionAlternateReverse
      )
  , AnimationIteration
      ( IterateOnce
      , IterateCount
      , IterateInfinite
      )
  , AnimationRegistry
  , mkAnimationRegistry
  , registerAnimation
  , unregisterAnimation
  , getAnimationPhase
  , getAllAnimations
  , tickAnimations
  , SpringHandle
  , SpringInstance
  , SpringRegistry
  , mkSpringRegistry
  , registerSpring
  , getSpringValue
  , getSpringValueMaybe
  , setSpringTarget
  , tickSprings
  , animationsAsList
  , springsAsList
  , runningAnimations
  , completedAnimations
  , animationHandles
  , springHandles
  , findAnimationByPhase
  , anyAnimationRunning
  , allAnimationsComplete
  ) as Anim

-- Qualified import for internal use (same module, different alias)
import Hydrogen.GPU.FrameState.Animation as Animation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time in milliseconds since epoch or start
type FrameTime = Number

-- | Frame counter (monotonically increasing)
type FrameNumber = Int

-- | Complete frame state for a render pass
type FrameState =
  { time :: TimeState
  , mouse :: MouseState
  , animations :: Animation.AnimationRegistry
  , springs :: Animation.SpringRegistry
  , viewport :: ViewportState
  , performance :: PerformanceState
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // time state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal state for the current frame
type TimeState =
  { current :: FrameTime       -- Current timestamp (ms since start)
  , delta :: FrameTime         -- Time since last frame (ms)
  , frame :: FrameNumber       -- Frame counter
  , start :: FrameTime         -- Timestamp when app started
  , targetFPS :: Number        -- Target frames per second
  }

-- | Create initial time state
mkTimeState :: FrameTime -> Number -> TimeState
mkTimeState startTime targetFrameRate =
  { current: startTime
  , delta: 0.0
  , frame: 0
  , start: startTime
  , targetFPS: targetFrameRate
  }

-- | Advance time by delta milliseconds
advanceTime :: FrameTime -> TimeState -> TimeState
advanceTime newTime state =
  { current: newTime
  , delta: newTime - state.current
  , frame: state.frame + 1
  , start: state.start
  , targetFPS: state.targetFPS
  }

-- | Get delta time in milliseconds
deltaMs :: TimeState -> FrameTime
deltaMs state = state.delta

-- | Get elapsed time since start in milliseconds
elapsedMs :: TimeState -> FrameTime
elapsedMs state = state.current - state.start

-- | Get current frame number
frameNumber :: TimeState -> FrameNumber
frameNumber state = state.frame

-- | Calculate actual FPS from delta time
fps :: TimeState -> Number
fps state = if state.delta > 0.0 then 1000.0 / state.delta else 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // mouse state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mouse button identifiers
data MouseButton
  = MouseLeft
  | MouseMiddle
  | MouseRight
  | MouseBack
  | MouseForward

derive instance eqMouseButton :: Eq MouseButton

instance showMouseButton :: Show MouseButton where
  show MouseLeft = "(MouseButton Left)"
  show MouseMiddle = "(MouseButton Middle)"
  show MouseRight = "(MouseButton Right)"
  show MouseBack = "(MouseButton Back)"
  show MouseForward = "(MouseButton Forward)"

-- | Mouse interaction state
type MouseState =
  { x :: Number                -- X position in viewport pixels
  , y :: Number                -- Y position in viewport pixels
  , prevX :: Number            -- Previous X position
  , prevY :: Number            -- Previous Y position
  , velocityX :: Number        -- X velocity (pixels per frame)
  , velocityY :: Number        -- Y velocity (pixels per frame)
  , buttons :: Array MouseButton  -- Currently pressed buttons
  , hoverTarget :: Maybe Int   -- PickId of element under cursor
  , activeTarget :: Maybe Int  -- PickId of element being pressed
  , dragStartX :: Number       -- Drag start X (if dragging)
  , dragStartY :: Number       -- Drag start Y (if dragging)
  , isDragging :: Boolean      -- Is a drag in progress
  }

-- | Create initial mouse state
mkMouseState :: MouseState
mkMouseState =
  { x: 0.0
  , y: 0.0
  , prevX: 0.0
  , prevY: 0.0
  , velocityX: 0.0
  , velocityY: 0.0
  , buttons: []
  , hoverTarget: Nothing
  , activeTarget: Nothing
  , dragStartX: 0.0
  , dragStartY: 0.0
  , isDragging: false
  }

-- | Get mouse position
mousePosition :: MouseState -> { x :: Number, y :: Number }
mousePosition state = { x: state.x, y: state.y }

-- | Get pressed buttons
mouseButtons :: MouseState -> Array MouseButton
mouseButtons state = state.buttons

-- | Get hover target PickId
mouseHoverTarget :: MouseState -> Maybe Int
mouseHoverTarget state = state.hoverTarget

-- | Get mouse movement since last frame
mouseDelta :: MouseState -> { dx :: Number, dy :: Number }
mouseDelta state = { dx: state.x - state.prevX, dy: state.y - state.prevY }

-- | Get mouse velocity
mouseVelocity :: MouseState -> { vx :: Number, vy :: Number }
mouseVelocity state = { vx: state.velocityX, vy: state.velocityY }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport/window state
-- |
-- | Tracks current viewport as a tensor computation target, with geometric
-- | shape for non-rectangular displays, and change detection for reactivity.
-- |
-- | ## Tensor Architecture
-- |
-- | The viewport is fundamentally a `ViewportTensor` — a tensor computation
-- | target with both pixel-space and latent-space shapes. This enables:
-- |
-- | - Resolution-independent rendering via latent space
-- | - Same computation for 20ft LED wall and smartwatch
-- | - Diffusion model integration with standard 8× downsample
-- |
-- | ## Viewport Shape
-- |
-- | Not all viewports are rectangles. The `clipShape` field defines the
-- | geometric shape of the visible area:
-- |
-- | - **Rectangle**: Standard monitors, most windows
-- | - **RoundedRectangle**: Modern phones, tablets, rounded monitors
-- | - **Circle**: Round smartwatches (Galaxy Watch, some Wear OS)
-- | - **RectangleWithCutout**: Phones with notches, punch-holes
-- | - **Polygon**: AR/VR viewports, unconventional displays
-- |
-- | The `safeAreaInsets` define regions that may be obscured (notches,
-- | home indicators, etc.).
-- |
-- | ## Change Detection
-- |
-- | The `resized`, `orientationChanged`, `dprChanged`, and `shapeChanged`
-- | flags indicate whether the viewport changed this frame. Use these to
-- | trigger re-computation of latent tensors or layout recalculation.
type ViewportState =
  { -- Tensor abstraction (full viewport-as-tensor)
    tensor :: Viewport.ViewportTensor
  
    -- Previous tensor (for delta detection)
  , prevTensor :: Viewport.ViewportTensor
  
    -- Geometric shape of the viewport (for non-rectangular displays)
    -- Can be rectangle, circle, bezier path, or any Shape from Geometry.Shape
  , clipShape :: GeoShape.Shape
  
    -- Safe area insets (for notches, cutouts, home indicators)
  , safeAreaTop :: Pixel         -- Inset from top (notch, status bar)
  , safeAreaRight :: Pixel       -- Inset from right
  , safeAreaBottom :: Pixel      -- Inset from bottom (home indicator)
  , safeAreaLeft :: Pixel        -- Inset from left
  
    -- Bounding dimensions (derived from tensor, in device-independent pixels)
  , width :: Pixel               -- Viewport width in pixels
  , height :: Pixel              -- Viewport height in pixels
  , devicePixelRatio :: DevicePixelRatio  -- DPR (1.0 standard, 2.0 retina)
  , orientation :: ViewportOrientation
  
    -- Change flags (set by updateViewport)
  , resized :: Boolean           -- Pixel dimensions changed
  , orientationChanged :: Boolean -- Orientation changed
  , dprChanged :: Boolean        -- Device pixel ratio changed
  , shapeChanged :: Boolean      -- Clip shape changed
  }

-- | Viewport orientation
data ViewportOrientation
  = OrientationPortrait
  | OrientationLandscape
  | OrientationSquare

derive instance eqViewportOrientation :: Eq ViewportOrientation

instance showViewportOrientation :: Show ViewportOrientation where
  show OrientationPortrait = "(ViewportOrientation Portrait)"
  show OrientationLandscape = "(ViewportOrientation Landscape)"
  show OrientationSquare = "(ViewportOrientation Square)"

-- | Create viewport state with rectangular clip shape
-- |
-- | Initializes viewport with given dimensions. Creates a ViewportTensor
-- | with the specified pixel dimensions and standard 8× latent downsample.
-- | Default clip shape is a rectangle matching the dimensions.
-- | Safe area insets are zero (no notches/cutouts).
-- | Previous tensor is set to current (no delta on first frame).
mkViewportState :: Pixel -> Pixel -> DevicePixelRatio -> ViewportState
mkViewportState width height devicePixelRatioVal =
  let
    -- Unwrap for comparisons and tensor construction
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    
    -- Create tensor from pixel dimensions (uses 8× downsample)
    tensor = Viewport.viewportFromPixels (Int.floor widthNum) (Int.floor heightNum)
    
    orientation = if widthNum > heightNum then OrientationLandscape
                  else if heightNum > widthNum then OrientationPortrait
                  else OrientationSquare
    
    -- Default clip shape: rectangle at origin with given dimensions
    defaultClipShape = GeoShape.ShapeRectangle $ rectangleShape
      pixelOrigin
      width
      height
      (cornersAll none)  -- Sharp corners (no radius)
  in
    { tensor
    , prevTensor: tensor  -- No delta on first frame
    , clipShape: defaultClipShape
    -- Safe area: no insets by default (Pixel values)
    , safeAreaTop: Pixel 0.0
    , safeAreaRight: Pixel 0.0
    , safeAreaBottom: Pixel 0.0
    , safeAreaLeft: Pixel 0.0
    , width
    , height
    , devicePixelRatio: devicePixelRatioVal
    , orientation
    -- No changes on first frame
    , resized: false
    , orientationChanged: false
    , dprChanged: false
    , shapeChanged: false
    }

-- | Get viewport width
viewportWidth :: ViewportState -> Pixel
viewportWidth state = state.width

-- | Get viewport height
viewportHeight :: ViewportState -> Pixel
viewportHeight state = state.height

-- | Get device pixel ratio
viewportDPI :: ViewportState -> DevicePixelRatio
viewportDPI state = state.devicePixelRatio

-- | Get viewport orientation
viewportOrientation :: ViewportState -> ViewportOrientation
viewportOrientation state = state.orientation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // viewport change detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if viewport was resized this frame
-- |
-- | Returns true if width or height changed since last updateViewport call.
-- | Use this to trigger re-computation of latent tensors.
viewportResized :: ViewportState -> Boolean
viewportResized state = state.resized

-- | Check if viewport orientation changed this frame
-- |
-- | Returns true if orientation (portrait/landscape/square) changed.
-- | May trigger layout re-computation.
viewportOrientationChanged :: ViewportState -> Boolean
viewportOrientationChanged state = state.orientationChanged

-- | Check if device pixel ratio changed this frame
-- |
-- | Returns true if DPR changed (e.g., window moved between monitors).
-- | May trigger texture resolution updates.
viewportDPRChanged :: ViewportState -> Boolean
viewportDPRChanged state = state.dprChanged

-- | Check if viewport clip shape changed this frame
-- |
-- | Returns true if the clip shape changed (resize triggers this for rectangular
-- | viewports, or explicit shape changes for non-rectangular viewports).
viewportShapeChanged :: ViewportState -> Boolean
viewportShapeChanged state = state.shapeChanged

-- | Check if any viewport property changed this frame
-- |
-- | Convenience function: resized OR orientationChanged OR dprChanged OR shapeChanged.
viewportAnyChange :: ViewportState -> Boolean
viewportAnyChange state = 
  state.resized || state.orientationChanged || state.dprChanged || state.shapeChanged

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // viewport tensor access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the ViewportTensor for tensor/GPU computation
-- |
-- | Use this when you need access to the full tensor abstraction:
-- | pixel shape, latent shape, color space, memory layout, etc.
viewportTensor :: ViewportState -> Viewport.ViewportTensor
viewportTensor state = state.tensor

-- | Get latent width (for tensor/diffusion rendering)
-- |
-- | Returns width / 8, the standard downsample factor for Stable Diffusion.
-- | A 1920px viewport has latentWidth = 240.
viewportLatentWidth :: ViewportState -> Int
viewportLatentWidth state = Viewport.latentWidth state.tensor

-- | Get latent height (for tensor/diffusion rendering)
-- |
-- | Returns height / 8, the standard downsample factor for Stable Diffusion.
-- | A 1080px viewport has latentHeight = 135.
viewportLatentHeight :: ViewportState -> Int
viewportLatentHeight state = Viewport.latentHeight state.tensor

-- | Get total latent count (for GPU memory budgeting)
-- |
-- | Returns latentWidth × latentHeight × 4 (4 latent channels).
-- | A 1920×1080 viewport has ~130K latents vs ~8.3M pixels.
viewportLatentSize :: ViewportState -> Int
viewportLatentSize state = Viewport.totalLatents state.tensor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the geometric clip shape of the viewport
-- |
-- | Can be rectangle, circle, rounded rect, bezier path, etc.
-- | Use this for non-rectangular displays (watches, notched phones, etc.)
viewportClipShape :: ViewportState -> GeoShape.Shape
viewportClipShape state = state.clipShape

-- | Get safe area insets as a record
-- |
-- | Safe area is the region not obscured by notches, home indicators, etc.
viewportSafeArea :: ViewportState -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }
viewportSafeArea state = 
  { top: state.safeAreaTop
  , right: state.safeAreaRight
  , bottom: state.safeAreaBottom
  , left: state.safeAreaLeft
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // viewport shape constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create viewport state with a custom clip shape
-- |
-- | For non-rectangular displays (watches, notched phones, etc.), this allows
-- | specifying an arbitrary Shape as the viewport clip region.
-- |
-- | ## Example: Circular watch viewport
-- |
-- | ```purescript
-- | watchViewport = mkViewportStateWithShape
-- |   (Pixel 390.0) (Pixel 390.0) (dpr 2.0)
-- |   (ShapeEllipse $ circleShape center (Pixel 195.0))
-- |   { top: Pixel 0.0, right: Pixel 0.0, bottom: Pixel 0.0, left: Pixel 0.0 }
-- | ```
mkViewportStateWithShape 
  :: Pixel                -- ^ Width
  -> Pixel                -- ^ Height
  -> DevicePixelRatio     -- ^ Device pixel ratio
  -> GeoShape.Shape       -- ^ Clip shape
  -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }  -- ^ Safe area insets
  -> ViewportState
mkViewportStateWithShape width height devicePixelRatioVal clipShape safeArea =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    
    tensor = Viewport.viewportFromPixels (Int.floor widthNum) (Int.floor heightNum)
    
    orientation = if widthNum > heightNum then OrientationLandscape
                  else if heightNum > widthNum then OrientationPortrait
                  else OrientationSquare
  in
    { tensor
    , prevTensor: tensor  -- No delta on first frame
    , clipShape
    , safeAreaTop: safeArea.top
    , safeAreaRight: safeArea.right
    , safeAreaBottom: safeArea.bottom
    , safeAreaLeft: safeArea.left
    , width
    , height
    , devicePixelRatio: devicePixelRatioVal
    , orientation
    , resized: false
    , orientationChanged: false
    , dprChanged: false
    , shapeChanged: false
    }

-- | Create a circular viewport (for round smartwatches)
-- |
-- | Creates a viewport with a circular clip shape centered in the bounding box.
-- | Common for: Galaxy Watch, some Wear OS devices, circular fitness trackers.
-- |
-- | The viewport is square (diameter × diameter) with a circular clip region.
-- | Safe area is zero (circular displays typically have no notches).
-- |
-- | ## Example: Galaxy Watch 4 (396×396 at 2.0 DPR)
-- |
-- | ```purescript
-- | galaxyWatch = mkCircularViewport (Pixel 396.0) (dpr 2.0)
-- | ```
mkCircularViewport :: Pixel -> DevicePixelRatio -> ViewportState
mkCircularViewport diameter devicePixelRatioVal =
  let
    diameterNum = unwrapPixel diameter
    radiusNum = diameterNum / 2.0
    radius = Pixel radiusNum
    center = pixelPoint2D radius radius
    
    clipShape = GeoShape.ShapeEllipse $ circleShape center radius
    
    noInsets = { top: Pixel 0.0, right: Pixel 0.0, bottom: Pixel 0.0, left: Pixel 0.0 }
  in
    mkViewportStateWithShape diameter diameter devicePixelRatioVal clipShape noInsets

-- | Create a rounded rectangle viewport (for modern phones/tablets)
-- |
-- | Creates a viewport with rounded corners matching modern device displays.
-- | Common for: iPhone, Android phones, iPads, most modern mobile devices.
-- |
-- | ## Parameters
-- |
-- | - width, height: Viewport dimensions
-- | - dpr: Device pixel ratio
-- | - cornerRadius: Radius for all corners
-- | - safeArea: Insets for notches, home indicators, etc.
-- |
-- | ## Example: iPhone-style viewport
-- |
-- | ```purescript
-- | iphoneViewport = mkRoundedRectViewport
-- |   (Pixel 390.0) (Pixel 844.0) (dpr 3.0)
-- |   (Radius.px 44.0)  -- iOS corner radius
-- |   { top: Pixel 47.0, right: Pixel 0.0, bottom: Pixel 34.0, left: Pixel 0.0 }
-- | ```
mkRoundedRectViewport 
  :: Pixel                -- ^ Width
  -> Pixel                -- ^ Height
  -> DevicePixelRatio     -- ^ Device pixel ratio
  -> Radius.Radius        -- ^ Corner radius (applied to all corners)
  -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }  -- ^ Safe area insets
  -> ViewportState
mkRoundedRectViewport width height devicePixelRatioVal cornerRadius safeArea =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    centerX = widthNum / 2.0
    centerY = heightNum / 2.0
    center = pixelPoint2D (Pixel centerX) (Pixel centerY)
    
    clipShape = GeoShape.ShapeRectangle $ rectangleShape
      center
      width
      height
      (cornersAll cornerRadius)
  in
    mkViewportStateWithShape width height devicePixelRatioVal clipShape safeArea

-- | Create a viewport with a custom bezier path shape.
-- |
-- | For unconventional displays: AR/VR viewports, unusual aspect ratios,
-- | custom-shaped kiosk displays, etc.
-- |
-- | The path should be closed and define the visible region.
-- |
-- | ## Example: Pill-shaped display
-- |
-- | ```purescript
-- | pillViewport = mkPathViewport
-- |   (Pixel 400.0) (Pixel 150.0) (dpr 2.0)
-- |   (pathShape 
-- |     [ MoveTo (pixelPoint2D (Pixel 75.0) (Pixel 0.0))
-- |     , LineTo (pixelPoint2D (Pixel 325.0) (Pixel 0.0))
-- |     , ArcTo arcParams (pixelPoint2D (Pixel 325.0) (Pixel 150.0))
-- |     , LineTo (pixelPoint2D (Pixel 75.0) (Pixel 150.0))
-- |     , ArcTo arcParams (pixelPoint2D (Pixel 75.0) (Pixel 0.0))
-- |     , ClosePath
-- |     ])
-- |   { top: Pixel 0.0, right: Pixel 0.0, bottom: Pixel 0.0, left: Pixel 0.0 }
-- | ```
mkPathViewport
  :: Pixel                -- ^ Bounding width
  -> Pixel                -- ^ Bounding height
  -> DevicePixelRatio     -- ^ Device pixel ratio
  -> PathShape            -- ^ Custom path defining the clip region
  -> { top :: Pixel, right :: Pixel, bottom :: Pixel, left :: Pixel }  -- ^ Safe area insets
  -> ViewportState
mkPathViewport width height devicePixelRatioVal path safeArea =
  let
    clipShape = ShapePath path
  in
    mkViewportStateWithShape width height devicePixelRatioVal clipShape safeArea

-- | Create a viewport with an elliptical (oval) shape.
-- |
-- | For non-circular watches or oval displays.
mkEllipticalViewport
  :: Pixel                -- ^ Width (horizontal diameter)
  -> Pixel                -- ^ Height (vertical diameter)  
  -> DevicePixelRatio     -- ^ Device pixel ratio
  -> ViewportState
mkEllipticalViewport width height devicePixelRatioVal =
  let
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    center = pixelPoint2D (Pixel (widthNum / 2.0)) (Pixel (heightNum / 2.0))
    radiusX = Pixel (widthNum / 2.0)
    radiusY = Pixel (heightNum / 2.0)
    
    ellipse :: EllipseShape
    ellipse = { center, radiusX, radiusY }
    
    clipShape = ShapeEllipse ellipse
    noInsets = { top: Pixel 0.0, right: Pixel 0.0, bottom: Pixel 0.0, left: Pixel 0.0 }
  in
    mkViewportStateWithShape width height devicePixelRatioVal clipShape noInsets

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // viewport deltas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get viewport width delta (current - previous)
-- |
-- | Positive = viewport got wider, negative = narrower.
-- | Compares current tensor pixel width to previous tensor pixel width.
viewportWidthDelta :: ViewportState -> Int
viewportWidthDelta state = 
  Viewport.pixelWidth state.tensor - Viewport.pixelWidth state.prevTensor

-- | Get viewport height delta (current - previous)
-- |
-- | Positive = viewport got taller, negative = shorter.
-- | Compares current tensor pixel height to previous tensor pixel height.
viewportHeightDelta :: ViewportState -> Int
viewportHeightDelta state = 
  Viewport.pixelHeight state.tensor - Viewport.pixelHeight state.prevTensor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // performance state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Performance metrics for frame budgeting
type PerformanceState =
  { targetFPS :: Number        -- Target frame rate
  , actualFPS :: Number        -- Measured frame rate
  , gpuBudgetMs :: Number      -- GPU time budget per frame
  , gpuUsedMs :: Number        -- GPU time used this frame
  , cpuBudgetMs :: Number      -- CPU time budget per frame
  , cpuUsedMs :: Number        -- CPU time used this frame
  , droppedFrames :: Int       -- Count of dropped frames
  , lastDropTime :: FrameTime  -- Time of last frame drop
  }

-- | Create performance state
mkPerformanceState :: Number -> PerformanceState
mkPerformanceState targetFrameRate =
  let budgetMs = 1000.0 / targetFrameRate
  in
    { targetFPS: targetFrameRate
    , actualFPS: targetFrameRate
    , gpuBudgetMs: budgetMs * 0.8  -- 80% for GPU
    , gpuUsedMs: 0.0
    , cpuBudgetMs: budgetMs * 0.2  -- 20% for CPU
    , cpuUsedMs: 0.0
    , droppedFrames: 0
    , lastDropTime: 0.0
    }

-- | Get target FPS
targetFPS :: PerformanceState -> Number
targetFPS state = state.targetFPS

-- | Get actual measured FPS
actualFPS :: PerformanceState -> Number
actualFPS state = state.actualFPS

-- | Get GPU budget in milliseconds
gpuBudgetMs :: PerformanceState -> Number
gpuBudgetMs state = state.gpuBudgetMs

-- | Get GPU time used in milliseconds
gpuUsedMs :: PerformanceState -> Number
gpuUsedMs state = state.gpuUsedMs

-- | Check if last frame was dropped
frameDropped :: PerformanceState -> Boolean
frameDropped state = state.gpuUsedMs > state.gpuBudgetMs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // framestate construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create frame state with initial values
mkFrameState 
  :: FrameTime      -- Start time
  -> Number              -- Target FPS
  -> Pixel               -- Viewport width
  -> Pixel               -- Viewport height
  -> DevicePixelRatio    -- Device pixel ratio
  -> FrameState
mkFrameState startTime targetFrameRate width height devicePixelRatioVal =
  { time: mkTimeState startTime targetFrameRate
  , mouse: mkMouseState
  , animations: Animation.mkAnimationRegistry
  , springs: Animation.mkSpringRegistry
  , viewport: mkViewportState width height devicePixelRatioVal
  , performance: mkPerformanceState targetFrameRate
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // default values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default viewport width (1920 pixels)
-- |
-- | Rationale: Full HD (1920×1080) is the most common desktop resolution globally.
-- | This is a reasonable starting point for testing and initial state before
-- | the actual viewport dimensions are known. Agents should always use real
-- | viewport dimensions once available — these defaults exist only for:
-- |
-- | - Testing and development
-- | - Initial state before first resize event
-- | - Fallback when viewport queries fail
-- |
-- | Bounded: Minimum sensible viewport is ~320px (small mobile).
-- | Maximum is effectively unbounded (8K displays exist at 7680px).
defaultViewportWidth :: Pixel
defaultViewportWidth = Pixel 1920.0

-- | Default viewport height (1080 pixels)
-- |
-- | Rationale: Full HD (1920×1080) is the most common desktop resolution globally.
-- | See `defaultViewportWidth` for full rationale on when defaults are appropriate.
defaultViewportHeight :: Pixel
defaultViewportHeight = Pixel 1080.0

-- | Default device pixel ratio (1.0)
-- |
-- | Rationale: Standard DPR for non-retina displays.
-- | Retina displays use 2.0, some high-DPI displays use 1.5 or 3.0.
-- | 1.0 is conservative — better to under-render than over-allocate VRAM.
-- |
-- | Bounded: Minimum is 0.5 (rare, low-DPI mode), maximum is ~4.0 (highest-end displays).
defaultDevicePixelRatio :: DevicePixelRatio
defaultDevicePixelRatio = dpr 1.0

-- | Default target FPS (60 frames per second)
-- |
-- | Rationale: 60 FPS is the standard for smooth animation on most displays.
-- | Higher rates (120, 144, 240 Hz) exist but 60 is universal baseline.
-- | Lower rates (30 FPS) are acceptable for content but feel sluggish for UI.
-- |
-- | Bounded: Minimum sensible is ~24 FPS (film), maximum is ~240 FPS (gaming displays).
defaultTargetFPS :: Number
defaultTargetFPS = 60.0

-- | Default start time (0.0 milliseconds)
-- |
-- | Rationale: Time is measured from application start, so 0.0 is the natural origin.
-- | Real applications will provide actual timestamps from performance.now() or similar.
defaultStartTime :: FrameTime
defaultStartTime = 0.0

-- | Create empty/default frame state
-- |
-- | Uses documented default values for testing and initial state:
-- | - Viewport: 1920×1080 at 1.0 DPR (Full HD, standard desktop)
-- | - FPS target: 60 (universal baseline)
-- | - Start time: 0.0 (application origin)
-- |
-- | **Important**: Real applications should call `mkFrameState` with actual
-- | viewport dimensions as soon as they're known. These defaults exist only
-- | for testing, development, and the brief moment before first resize event.
emptyFrameState :: FrameState
emptyFrameState = mkFrameState 
  defaultStartTime 
  defaultTargetFPS 
  defaultViewportWidth 
  defaultViewportHeight 
  defaultDevicePixelRatio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // framestate updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update time state
updateTime :: FrameTime -> FrameState -> FrameState
updateTime newTime state =
  state { time = advanceTime newTime state.time }

-- | Update mouse state
updateMouse 
  :: Number         -- New X
  -> Number         -- New Y
  -> Array MouseButton  -- Current buttons
  -> Maybe Int      -- Hover target
  -> FrameState 
  -> FrameState
updateMouse x y buttons hoverTarget state =
  let
    prevMouse = state.mouse
    newMouse = prevMouse
      { x = x
      , y = y
      , prevX = prevMouse.x
      , prevY = prevMouse.y
      , velocityX = x - prevMouse.x
      , velocityY = y - prevMouse.y
      , buttons = buttons
      , hoverTarget = hoverTarget
      }
  in
    state { mouse = newMouse }

-- | Update viewport state (dimensions only, keeps existing clip shape)
-- |
-- | Compares new dimensions against previous and sets change flags.
-- | Previous tensor is updated to current before applying new values.
-- | Clip shape is updated to match new dimensions.
updateViewport :: Pixel -> Pixel -> DevicePixelRatio -> FrameState -> FrameState
updateViewport width height devicePixelRatioVal state =
  let
    prev = state.viewport
    widthNum = unwrapPixel width
    heightNum = unwrapPixel height
    prevWidthNum = unwrapPixel prev.width
    prevHeightNum = unwrapPixel prev.height
    
    newOrientation = if widthNum > heightNum then OrientationLandscape
                     else if heightNum > widthNum then OrientationPortrait
                     else OrientationSquare
    -- Detect changes
    sizeChanged = widthNum /= prevWidthNum || heightNum /= prevHeightNum
    orientationDiff = newOrientation /= prev.orientation
    dprDiff = unwrapDpr devicePixelRatioVal /= unwrapDpr prev.devicePixelRatio
    -- Create new tensor from pixel dimensions
    newTensor = Viewport.viewportFromPixels (Int.floor widthNum) (Int.floor heightNum)
    -- Create new clip shape (rectangle matching new dimensions)
    newClipShape = GeoShape.ShapeRectangle $ rectangleShape
      pixelOrigin
      width
      height
      (cornersAll none)  -- Sharp corners (no radius)
    newViewport =
      { tensor: newTensor
      , prevTensor: prev.tensor
      , clipShape: newClipShape
      , safeAreaTop: prev.safeAreaTop
      , safeAreaRight: prev.safeAreaRight
      , safeAreaBottom: prev.safeAreaBottom
      , safeAreaLeft: prev.safeAreaLeft
      , width
      , height
      , devicePixelRatio: devicePixelRatioVal
      , orientation: newOrientation
      -- Change flags
      , resized: sizeChanged
      , orientationChanged: orientationDiff
      , dprChanged: dprDiff
      , shapeChanged: sizeChanged  -- Shape changes when dimensions change
      }
  in
    state { viewport = newViewport }

-- | Update performance state
updatePerformance :: Number -> Number -> FrameState -> FrameState
updatePerformance gpuMs cpuMs state =
  let
    newPerf = state.performance
      { gpuUsedMs = gpuMs
      , cpuUsedMs = cpuMs
      , actualFPS = if state.time.delta > 0.0 then 1000.0 / state.time.delta else 0.0
      }
  in
    state { performance = newPerf }

-- | Tick all animations and springs
tick :: FrameTime -> FrameState -> FrameState
tick newTime state =
  let
    timeState = advanceTime newTime state.time
    deltaTime = timeState.delta
  in
    state
      { time = timeState
      , animations = Animation.tickAnimations newTime deltaTime state.animations
      , springs = Animation.tickSprings deltaTime state.springs
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // framestate queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if mouse is hovering over element with given PickId
isHovering :: Int -> FrameState -> Boolean
isHovering pickId state = state.mouse.hoverTarget == Just pickId

-- | Check if mouse button is pressed
isPressed :: MouseButton -> FrameState -> Boolean
isPressed button state = Array.elem button state.mouse.buttons

-- | Get animation progress (0.0-1.0)
animationProgress :: Animation.AnimationHandle -> FrameState -> Number
animationProgress handle state =
  case Animation.getAnimationPhase handle state.animations of
    Animation.AnimationIdle -> 0.0
    Animation.AnimationRunning p -> p
    Animation.AnimationComplete -> 1.0
    Animation.AnimationReversing p -> p

-- | Get spring current value
springValue :: Animation.SpringHandle -> FrameState -> Number
springValue handle state = Animation.getSpringValue handle state.springs

-- | Get spring value with default (if spring not found)
springValueOr :: Number -> Animation.SpringHandle -> FrameState -> Number
springValueOr defaultValue handle state =
  fromMaybe defaultValue $ Animation.getSpringValueMaybe handle state.springs

-- | Get time since app start in milliseconds
timeSinceStart :: FrameState -> FrameTime
timeSinceStart state = elapsedMs state.time

-- | Get frames per second
framesPerSecond :: FrameState -> Number
framesPerSecond state = fps state.time

-- | Get total number of active animations
animationCount :: FrameState -> Int
animationCount state = Map.size state.animations.animations

-- | Clamp FPS to reasonable bounds
clampedFPS :: FrameState -> Number
clampedFPS state = 
  let rawFPS = fps state.time
  in min 240.0 $ max 1.0 rawFPS

-- | Check if any animations are running
hasActiveAnimations :: FrameState -> Boolean
hasActiveAnimations state = not $ Map.isEmpty state.animations.animations

-- | Get frame number as a Number (for interpolation calculations)
frameNumberAsNumber :: FrameState -> Number
frameNumberAsNumber state = Int.toNumber $ frameNumber state.time

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // debug output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug string for TimeState.
-- |
-- | Follows SHOW_DEBUG_CONVENTION: structured, parseable output.
showTimeState :: TimeState -> String
showTimeState t = 
  "(TimeState frame:" <> show t.frame 
  <> " current:" <> show t.current <> "ms"
  <> " delta:" <> show t.delta <> "ms"
  <> " fps:" <> show t.targetFPS
  <> ")"

-- | Debug string for MouseState.
-- |
-- | Shows position, velocity, and interaction state.
showMouseState :: MouseState -> String
showMouseState m =
  "(MouseState pos:(" <> show m.x <> "," <> show m.y <> ")"
  <> " vel:(" <> show m.velocityX <> "," <> show m.velocityY <> ")"
  <> " buttons:" <> show m.buttons
  <> " hover:" <> show m.hoverTarget
  <> " dragging:" <> show m.isDragging
  <> ")"

-- | Debug string for ViewportState.
-- |
-- | Shows dimensions, orientation, and change flags.
showViewportState :: ViewportState -> String
showViewportState v =
  "(ViewportState " <> show v.width <> "×" <> show v.height
  <> " @" <> show v.devicePixelRatio
  <> " " <> show v.orientation
  <> " latent:" <> show (viewportLatentWidth v) <> "×" <> show (viewportLatentHeight v)
  <> " changed:[" 
  <> (if v.resized then "resize " else "")
  <> (if v.orientationChanged then "orient " else "")
  <> (if v.dprChanged then "dpr " else "")
  <> (if v.shapeChanged then "shape" else "")
  <> "])"

-- | Debug string for PerformanceState.
-- |
-- | Shows FPS targets and GPU budget utilization.
showPerformanceState :: PerformanceState -> String
showPerformanceState p =
  "(PerformanceState target:" <> show p.targetFPS <> "fps"
  <> " actual:" <> show p.actualFPS <> "fps"
  <> " gpu:" <> show p.gpuUsedMs <> "/" <> show p.gpuBudgetMs <> "ms"
  <> " dropped:" <> show p.droppedFrames
  <> ")"

-- | Debug string for complete FrameState.
-- |
-- | Provides full introspection for debugging at billion-agent scale.
-- | Same FrameState = same debug string = reproducible debugging.
showFrameState :: FrameState -> String
showFrameState fs =
  "(FrameState\n"
  <> "  time: " <> showTimeState fs.time <> "\n"
  <> "  mouse: " <> showMouseState fs.mouse <> "\n"
  <> "  viewport: " <> showViewportState fs.viewport <> "\n"
  <> "  performance: " <> showPerformanceState fs.performance <> "\n"
  <> "  animations: " <> show (animationCount fs) <> " active\n"
  <> ")"
