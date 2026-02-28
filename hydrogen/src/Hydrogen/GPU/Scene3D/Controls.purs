-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // scene3d // controls
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera controls — Pure state machines for interactive 3D navigation.
-- |
-- | ## Design Philosophy
-- | These are PURE STATE MACHINES. No FFI. Gesture events come in as messages,
-- | state updates happen purely, camera position is derived from state.
-- |
-- | ## Three.js Parity
-- | - OrbitControls: Rotate around target point
-- | - (Future) TrackballControls: Unconstrained spherical rotation
-- | - (Future) FlyControls: WASD flight mode
-- |
-- | ## Usage
-- | ```purescript
-- | update msg state = case msg of
-- |   GestureMsg gesture -> 
-- |     state { controls = updateOrbitControls (gestureToControlsMsg gesture) state.controls }
-- | 
-- | view state =
-- |   scene3D (orbitControlsToCamera state.controls) state.scene
-- | ```

module Hydrogen.GPU.Scene3D.Controls
  ( -- * Orbit Controls State
    OrbitControlsState
  , Spherical
  , defaultOrbitControls
  
  -- * Orbit Controls Messages
  , OrbitControlsMsg
      ( RotateDelta
      , PanDelta
      , ZoomDelta
      , SetTarget
      , ResetView
      )
  
  -- * Update Functions
  , updateOrbitControls
  , applyDamping
  
  -- * Camera Conversion
  , orbitControlsToCamera
  , orbitControlsToPosition
  , sphericalToCartesian
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , max
  , min
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, addVec3, scaleVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spherical coordinates for camera positioning.
-- |
-- | Uses Three.js convention:
-- | - radius: distance from target
-- | - phi: polar angle from Y axis (0 = top, PI = bottom)
-- | - theta: azimuthal angle in XZ plane
type Spherical =
  { radius :: Number
  , phi :: Number      -- 0 to PI
  , theta :: Number    -- 0 to 2*PI
  }

-- | Orbit controls state — pure data describing camera orbit state.
-- |
-- | This is the complete state needed to position a camera orbiting
-- | around a target point. All updates are pure functions.
type OrbitControlsState =
  { target :: Vec3 Number           -- Point to orbit around
  , spherical :: Spherical          -- Current camera position
  , sphericalDelta :: Spherical     -- Pending rotation (for damping)
  , panOffset :: Vec3 Number        -- Accumulated pan offset
  , zoomScale :: Number             -- Current zoom multiplier
  -- Configuration
  , enableDamping :: Boolean
  , dampingFactor :: Number         -- 0-1, lower = more damping
  , rotateSpeed :: Number           -- Multiplier for mouse rotation
  , panSpeed :: Number              -- Multiplier for mouse pan
  , zoomSpeed :: Number             -- Multiplier for zoom
  -- Limits
  , minDistance :: Number
  , maxDistance :: Number
  , minPhi :: Number                -- Minimum polar angle (avoid gimbal lock)
  , maxPhi :: Number                -- Maximum polar angle
  }

-- | Messages that update orbit controls state.
-- |
-- | These map directly to gesture events:
-- | - Left mouse drag → RotateDelta
-- | - Right mouse drag or shift+left → PanDelta  
-- | - Scroll wheel or pinch → ZoomDelta
data OrbitControlsMsg
  = RotateDelta Number Number     -- dx, dy in pixels (or normalized)
  | PanDelta Number Number        -- dx, dy for panning
  | ZoomDelta Number              -- scale factor (>1 = zoom in)
  | SetTarget (Vec3 Number)       -- Change orbit target
  | ResetView                     -- Return to default position

derive instance eqOrbitControlsMsg :: Eq OrbitControlsMsg

instance showOrbitControlsMsg :: Show OrbitControlsMsg where
  show (RotateDelta dx dy) = "RotateDelta(" <> show dx <> ", " <> show dy <> ")"
  show (PanDelta dx dy) = "PanDelta(" <> show dx <> ", " <> show dy <> ")"
  show (ZoomDelta s) = "ZoomDelta(" <> show s <> ")"
  show (SetTarget t) = "SetTarget(" <> show t <> ")"
  show ResetView = "ResetView"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default spherical position: 45 degrees from top, 45 degrees around
defaultSpherical :: Spherical
defaultSpherical =
  { radius: 10.0
  , phi: Math.pi / 4.0        -- 45 degrees from top
  , theta: Math.pi / 4.0      -- 45 degrees around
  }

-- | Zero spherical delta (no pending rotation)
zeroSphericalDelta :: Spherical
zeroSphericalDelta =
  { radius: 1.0               -- Multiplicative identity for zoom
  , phi: 0.0
  , theta: 0.0
  }

-- | Default orbit controls state.
-- |
-- | Camera starts at distance 10, looking at origin from above-right.
defaultOrbitControls :: OrbitControlsState
defaultOrbitControls =
  { target: vec3 0.0 0.0 0.0
  , spherical: defaultSpherical
  , sphericalDelta: zeroSphericalDelta
  , panOffset: vec3 0.0 0.0 0.0
  , zoomScale: 1.0
  -- Configuration
  , enableDamping: true
  , dampingFactor: 0.05
  , rotateSpeed: 1.0
  , panSpeed: 1.0
  , zoomSpeed: 1.0
  -- Limits
  , minDistance: 0.1
  , maxDistance: 1000.0
  , minPhi: 0.01              -- Avoid gimbal lock at poles
  , maxPhi: Math.pi - 0.01
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // update
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update orbit controls state from a message.
-- |
-- | This is a pure function — no side effects.
updateOrbitControls :: OrbitControlsMsg -> OrbitControlsState -> OrbitControlsState
updateOrbitControls msg state = case msg of
  
  RotateDelta dx dy ->
    -- Convert pixel delta to radians
    let
      thetaDelta = dx * state.rotateSpeed * 0.01
      phiDelta = dy * state.rotateSpeed * 0.01
    in
      state 
        { sphericalDelta = state.sphericalDelta
            { theta = state.sphericalDelta.theta - thetaDelta
            , phi = state.sphericalDelta.phi - phiDelta
            }
        }
  
  PanDelta dx dy ->
    -- Pan perpendicular to view direction
    let
      -- Scale by distance for consistent feel
      scale = state.spherical.radius * state.panSpeed * 0.002
      panX = dx * scale
      panY = dy * scale
      -- Simple pan in XZ plane for now
      offset = vec3 (0.0 - panX) panY 0.0
    in
      state { panOffset = addVec3 state.panOffset offset }
  
  ZoomDelta scale ->
    state { zoomScale = state.zoomScale * scale }
  
  SetTarget newTarget ->
    state { target = newTarget }
  
  ResetView ->
    defaultOrbitControls { target = state.target }

-- | Apply damping and update spherical coordinates.
-- |
-- | Call this once per frame to smoothly animate the camera.
-- | If damping is disabled, changes apply immediately.
applyDamping :: OrbitControlsState -> OrbitControlsState
applyDamping state =
  let
    factor = if state.enableDamping then state.dampingFactor else 1.0
    
    -- Apply rotation delta with damping
    newTheta = state.spherical.theta + state.sphericalDelta.theta * factor
    newPhi = clampPhi state (state.spherical.phi + state.sphericalDelta.phi * factor)
    newRadius = clampRadius state (state.spherical.radius * state.zoomScale)
    
    -- Decay the deltas
    remainingFactor = 1.0 - factor
  in
    state
      { spherical = 
          { radius: newRadius
          , phi: newPhi
          , theta: newTheta
          }
      , sphericalDelta =
          { radius: 1.0
          , phi: state.sphericalDelta.phi * remainingFactor
          , theta: state.sphericalDelta.theta * remainingFactor
          }
      , zoomScale = 1.0 + (state.zoomScale - 1.0) * remainingFactor
      , target = addVec3 state.target (scaleVec3 factor state.panOffset)
      , panOffset = scaleVec3 remainingFactor state.panOffset
      }

-- | Clamp phi to configured limits
clampPhi :: OrbitControlsState -> Number -> Number
clampPhi state phi = max state.minPhi (min state.maxPhi phi)

-- | Clamp radius to configured limits
clampRadius :: OrbitControlsState -> Number -> Number
clampRadius state radius = max state.minDistance (min state.maxDistance radius)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert spherical coordinates to Cartesian position.
-- |
-- | Uses Three.js convention:
-- | - Y is up
-- | - phi is angle from Y axis
-- | - theta is angle in XZ plane from Z axis
sphericalToCartesian :: Spherical -> Vec3 Number
sphericalToCartesian s =
  let
    sinPhi = Math.sin s.phi
    cosPhi = Math.cos s.phi
    sinTheta = Math.sin s.theta
    cosTheta = Math.cos s.theta
  in
    vec3 
      (s.radius * sinPhi * sinTheta)   -- X
      (s.radius * cosPhi)               -- Y (up)
      (s.radius * sinPhi * cosTheta)   -- Z

-- | Get the camera position from orbit controls state.
-- |
-- | Position = target + sphericalToCartesian(spherical)
orbitControlsToPosition :: OrbitControlsState -> Vec3 Number
orbitControlsToPosition state =
  addVec3 state.target (sphericalToCartesian state.spherical)

-- | Convert orbit controls state to camera parameters.
-- |
-- | Returns a record with position and target, suitable for
-- | constructing a Camera3D or passing to makeLookAt.
orbitControlsToCamera 
  :: OrbitControlsState 
  -> { position :: Vec3 Number, target :: Vec3 Number, up :: Vec3 Number }
orbitControlsToCamera state =
  { position: orbitControlsToPosition state
  , target: state.target
  , up: vec3 0.0 1.0 0.0          -- Y-up convention
  }

