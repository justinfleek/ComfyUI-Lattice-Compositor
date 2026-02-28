-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // spatial // xr // tracking
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | XR Tracking — Input devices and world sensing.
-- |
-- | ## XRHand
-- | Hand tracking with 25 joints per hand (WebXR Hand Input).
-- | Enables gesture recognition, hand physics, virtual keyboards.
-- |
-- | ## XRController
-- | 6DOF controller with buttons, triggers, and haptics.
-- | Standard VR input device.
-- |
-- | ## XRHitTest
-- | Raycast against real-world geometry.
-- | Used for placing objects on surfaces in AR.
-- |
-- | ## XRLight
-- | Real-world light estimation.
-- | Enables virtual objects to match real lighting.

module Hydrogen.Schema.Spatial.XR.Tracking
  ( -- * Hand Tracking
    HandJoint(..)
  , allHandJoints
  , XRHandedness(..)
  , XRJointPose(..)
  , XRHand(..)
  
  -- * Controller
  , XRControllerProfile(..)
  , XRButton(..)
  , XRButtonState(..)
  , XRAxis(..)
  , XRController(..)
  
  -- * Hit Testing
  , XRHitTestSource(..)
  , XRHitTestResult(..)
  , XRHitTest(..)
  
  -- * Light Estimation
  , XRLightProbe(..)
  , XRLight(..)
  
  -- * Constructors
  , emptyHand
  , controller
  , hitTestFromRay
  , lightProbe
  
  -- * Accessors
  , jointPosition
  , jointRotation
  , buttonPressed
  , buttonValue
  , axisValue
  , hitPosition
  , hitNormal
  , estimatedIntensity
  
  -- * Operations
  , fingerTipDistance
  , isPinching
  , isGripping
  ) where

import Prelude

import Data.Array (length, foldl, (!!))
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, addVec3, scaleVec3, lengthVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hand joints
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebXR hand joints (25 per hand)
-- |
-- | Standard hand skeleton following OpenXR/WebXR specification.
data HandJoint
  -- Wrist
  = Wrist
  -- Thumb (4 joints)
  | ThumbMetacarpal
  | ThumbProximal
  | ThumbDistal
  | ThumbTip
  -- Index finger (5 joints)
  | IndexMetacarpal
  | IndexProximal
  | IndexIntermediate
  | IndexDistal
  | IndexTip
  -- Middle finger (5 joints)
  | MiddleMetacarpal
  | MiddleProximal
  | MiddleIntermediate
  | MiddleDistal
  | MiddleTip
  -- Ring finger (5 joints)
  | RingMetacarpal
  | RingProximal
  | RingIntermediate
  | RingDistal
  | RingTip
  -- Pinky finger (5 joints)
  | PinkyMetacarpal
  | PinkyProximal
  | PinkyIntermediate
  | PinkyDistal
  | PinkyTip

derive instance eqHandJoint :: Eq HandJoint
derive instance ordHandJoint :: Ord HandJoint

instance showHandJoint :: Show HandJoint where
  show Wrist = "wrist"
  show ThumbMetacarpal = "thumb-metacarpal"
  show ThumbProximal = "thumb-proximal"
  show ThumbDistal = "thumb-distal"
  show ThumbTip = "thumb-tip"
  show IndexMetacarpal = "index-metacarpal"
  show IndexProximal = "index-proximal"
  show IndexIntermediate = "index-intermediate"
  show IndexDistal = "index-distal"
  show IndexTip = "index-tip"
  show MiddleMetacarpal = "middle-metacarpal"
  show MiddleProximal = "middle-proximal"
  show MiddleIntermediate = "middle-intermediate"
  show MiddleDistal = "middle-distal"
  show MiddleTip = "middle-tip"
  show RingMetacarpal = "ring-metacarpal"
  show RingProximal = "ring-proximal"
  show RingIntermediate = "ring-intermediate"
  show RingDistal = "ring-distal"
  show RingTip = "ring-tip"
  show PinkyMetacarpal = "pinky-metacarpal"
  show PinkyProximal = "pinky-proximal"
  show PinkyIntermediate = "pinky-intermediate"
  show PinkyDistal = "pinky-distal"
  show PinkyTip = "pinky-tip"

-- | All 25 hand joints in order
allHandJoints :: Array HandJoint
allHandJoints =
  [ Wrist
  , ThumbMetacarpal, ThumbProximal, ThumbDistal, ThumbTip
  , IndexMetacarpal, IndexProximal, IndexIntermediate, IndexDistal, IndexTip
  , MiddleMetacarpal, MiddleProximal, MiddleIntermediate, MiddleDistal, MiddleTip
  , RingMetacarpal, RingProximal, RingIntermediate, RingDistal, RingTip
  , PinkyMetacarpal, PinkyProximal, PinkyIntermediate, PinkyDistal, PinkyTip
  ]

-- | Which hand
data XRHandedness
  = LeftHand
  | RightHand

derive instance eqXRHandedness :: Eq XRHandedness
derive instance ordXRHandedness :: Ord XRHandedness

instance showXRHandedness :: Show XRHandedness where
  show LeftHand = "left"
  show RightHand = "right"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // hand
-- ═════════════════════════════════════════════════════════════════════════════

-- | Joint pose (position + rotation + radius)
type XRJointPose =
  { position :: Vec3 Number
  , rotation :: Vec3 Number         -- ^ Euler XYZ
  , radius :: Number                -- ^ Joint radius (for collision)
  }

-- | Tracked hand
newtype XRHand = XRHand
  { handedness :: XRHandedness
  , joints :: Array XRJointPose     -- ^ 25 joints in HandJoint order
  , isTracking :: Boolean
  }

derive instance eqXRHand :: Eq XRHand

instance showXRHand :: Show XRHand where
  show (XRHand h) =
    "XRHand { handedness: " <> show h.handedness <>
    ", tracking: " <> show h.isTracking <> " }"

-- | Create an empty (untracked) hand
emptyHand :: XRHandedness -> XRHand
emptyHand handedness = XRHand
  { handedness
  , joints: map (\_ -> emptyPose) allHandJoints
  , isTracking: false
  }
  where
  emptyPose :: XRJointPose
  emptyPose = { position: vec3 0.0 0.0 0.0, rotation: vec3 0.0 0.0 0.0, radius: 0.01 }

-- | Get joint position
jointPosition :: HandJoint -> XRHand -> Maybe (Vec3 Number)
jointPosition joint (XRHand h) =
  case jointIndex joint of
    Just idx -> case h.joints !! idx of
      Just pose -> Just pose.position
      Nothing -> Nothing
    Nothing -> Nothing

-- | Get joint rotation
jointRotation :: HandJoint -> XRHand -> Maybe (Vec3 Number)
jointRotation joint (XRHand h) =
  case jointIndex joint of
    Just idx -> case h.joints !! idx of
      Just pose -> Just pose.rotation
      Nothing -> Nothing
    Nothing -> Nothing

-- | Get index of a hand joint
jointIndex :: HandJoint -> Maybe Int
jointIndex Wrist = Just 0
jointIndex ThumbMetacarpal = Just 1
jointIndex ThumbProximal = Just 2
jointIndex ThumbDistal = Just 3
jointIndex ThumbTip = Just 4
jointIndex IndexMetacarpal = Just 5
jointIndex IndexProximal = Just 6
jointIndex IndexIntermediate = Just 7
jointIndex IndexDistal = Just 8
jointIndex IndexTip = Just 9
jointIndex MiddleMetacarpal = Just 10
jointIndex MiddleProximal = Just 11
jointIndex MiddleIntermediate = Just 12
jointIndex MiddleDistal = Just 13
jointIndex MiddleTip = Just 14
jointIndex RingMetacarpal = Just 15
jointIndex RingProximal = Just 16
jointIndex RingIntermediate = Just 17
jointIndex RingDistal = Just 18
jointIndex RingTip = Just 19
jointIndex PinkyMetacarpal = Just 20
jointIndex PinkyProximal = Just 21
jointIndex PinkyIntermediate = Just 22
jointIndex PinkyDistal = Just 23
jointIndex PinkyTip = Just 24

-- | Distance between two finger tips (meters)
fingerTipDistance :: HandJoint -> HandJoint -> XRHand -> Maybe Number
fingerTipDistance j1 j2 hand =
  case jointPosition j1 hand of
    Nothing -> Nothing
    Just p1 ->
      case jointPosition j2 hand of
        Nothing -> Nothing
        Just p2 ->
          let diff = subtractVec3 p2 p1
          in Just (lengthVec3 diff)
  where
  subtractVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  subtractVec3 v1 v2 = addVec3 v1 (scaleVec3 (-1.0) v2)

-- | Check if thumb and index are pinching (< 2cm apart)
isPinching :: XRHand -> Boolean
isPinching hand =
  case fingerTipDistance ThumbTip IndexTip hand of
    Nothing -> false
    Just d -> d < 0.02  -- 2cm threshold

-- | Check if hand is making a grip gesture
-- |
-- | All fingers curled toward palm.
isGripping :: XRHand -> Boolean
isGripping (XRHand h) =
  let tipIndices = [4, 9, 14, 19, 24]  -- Thumb, Index, Middle, Ring, Pinky tips
      wristIdx = 0
  in case h.joints !! wristIdx of
    Nothing -> false
    Just wrist ->
      let distances = map (\tipIdx -> tipToWristDistance tipIdx wrist h.joints) tipIndices
          allClose = foldl (\acc d -> acc && d < 0.08) true distances  -- 8cm threshold
      in allClose
  where
  tipToWristDistance :: Int -> XRJointPose -> Array XRJointPose -> Number
  tipToWristDistance idx wrist joints =
    case joints !! idx of
      Nothing -> 1.0  -- Far if not found
      Just tip ->
        let diff = subtractVec3 tip.position wrist.position
        in lengthVec3 diff
  
  subtractVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  subtractVec3 v1 v2 = addVec3 v1 (scaleVec3 (-1.0) v2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // controller
-- ═════════════════════════════════════════════════════════════════════════════

-- | Controller profile (standardized input mapping)
data XRControllerProfile
  = GenericController
  | OculusTouch
  | ValveIndex
  | HTCVive
  | MicrosoftMixed
  | PicoNeo

derive instance eqXRControllerProfile :: Eq XRControllerProfile
derive instance ordXRControllerProfile :: Ord XRControllerProfile

instance showXRControllerProfile :: Show XRControllerProfile where
  show GenericController = "generic"
  show OculusTouch = "oculus-touch"
  show ValveIndex = "valve-index"
  show HTCVive = "htc-vive"
  show MicrosoftMixed = "microsoft-mixed"
  show PicoNeo = "pico-neo"

-- | Controller buttons
data XRButton
  = Trigger
  | Squeeze
  | Thumbstick
  | Touchpad
  | ButtonA
  | ButtonB
  | ButtonX
  | ButtonY
  | Menu
  | System

derive instance eqXRButton :: Eq XRButton
derive instance ordXRButton :: Ord XRButton

instance showXRButton :: Show XRButton where
  show Trigger = "trigger"
  show Squeeze = "squeeze"
  show Thumbstick = "thumbstick"
  show Touchpad = "touchpad"
  show ButtonA = "a"
  show ButtonB = "b"
  show ButtonX = "x"
  show ButtonY = "y"
  show Menu = "menu"
  show System = "system"

-- | Button state
type XRButtonState =
  { pressed :: Boolean
  , touched :: Boolean
  , value :: Number                 -- ^ 0.0 to 1.0 for analog
  }

-- | Controller axis
data XRAxis
  = ThumbstickX
  | ThumbstickY
  | TouchpadX
  | TouchpadY

derive instance eqXRAxis :: Eq XRAxis
derive instance ordXRAxis :: Ord XRAxis

instance showXRAxis :: Show XRAxis where
  show ThumbstickX = "thumbstick-x"
  show ThumbstickY = "thumbstick-y"
  show TouchpadX = "touchpad-x"
  show TouchpadY = "touchpad-y"

-- | XR Controller
newtype XRController = XRController
  { handedness :: XRHandedness
  , profile :: XRControllerProfile
  , position :: Vec3 Number
  , rotation :: Vec3 Number         -- ^ Euler XYZ
  , buttons :: Array { button :: XRButton, state :: XRButtonState }
  , axes :: Array { axis :: XRAxis, value :: Number }
  , isTracking :: Boolean
  }

derive instance eqXRController :: Eq XRController

instance showXRController :: Show XRController where
  show (XRController c) =
    "XRController { handedness: " <> show c.handedness <>
    ", profile: " <> show c.profile <>
    ", tracking: " <> show c.isTracking <> " }"

-- | Create a controller
controller :: XRHandedness -> XRControllerProfile -> XRController
controller handedness profile = XRController
  { handedness
  , profile
  , position: vec3 0.0 0.0 0.0
  , rotation: vec3 0.0 0.0 0.0
  , buttons: []
  , axes: []
  , isTracking: false
  }

-- | Check if a button is pressed
buttonPressed :: XRButton -> XRController -> Boolean
buttonPressed btn (XRController c) =
  foldl (\acc b -> acc || (b.button == btn && b.state.pressed)) false c.buttons

-- | Get analog button value (0-1)
buttonValue :: XRButton -> XRController -> Number
buttonValue btn (XRController c) =
  foldl (\acc b -> if b.button == btn then b.state.value else acc) 0.0 c.buttons

-- | Get axis value (-1 to 1)
axisValue :: XRAxis -> XRController -> Number
axisValue ax (XRController c) =
  foldl (\acc a -> if a.axis == ax then a.value else acc) 0.0 c.axes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // hit test
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hit test source (ray origin)
data XRHitTestSource
  = ViewerRay              -- ^ From user's view
  | ControllerRay XRHandedness  -- ^ From controller
  | TransientInput         -- ^ Touch/tap on screen

derive instance eqXRHitTestSource :: Eq XRHitTestSource

instance showXRHitTestSource :: Show XRHitTestSource where
  show ViewerRay = "viewer"
  show (ControllerRay h) = "controller-" <> show h
  show TransientInput = "transient"

-- | Single hit test result
type XRHitTestResult =
  { position :: Vec3 Number         -- ^ World position of hit
  , normal :: Vec3 Number           -- ^ Surface normal at hit
  , distance :: Number              -- ^ Distance from ray origin
  }

-- | Hit test with results
newtype XRHitTest = XRHitTest
  { source :: XRHitTestSource
  , results :: Array XRHitTestResult
  }

derive instance eqXRHitTest :: Eq XRHitTest

instance showXRHitTest :: Show XRHitTest where
  show (XRHitTest h) =
    "XRHitTest { source: " <> show h.source <>
    ", hits: " <> show (length h.results) <> " }"

-- | Create a hit test from ray source
hitTestFromRay :: XRHitTestSource -> XRHitTest
hitTestFromRay source = XRHitTest { source, results: [] }

-- | Get hit position (first result)
hitPosition :: XRHitTest -> Maybe (Vec3 Number)
hitPosition (XRHitTest h) =
  case h.results !! 0 of
    Just r -> Just r.position
    Nothing -> Nothing

-- | Get hit normal (first result)
hitNormal :: XRHitTest -> Maybe (Vec3 Number)
hitNormal (XRHitTest h) =
  case h.results !! 0 of
    Just r -> Just r.normal
    Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // light estimation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light probe (spherical harmonics)
-- |
-- | 9 coefficients for ambient lighting (SH2).
newtype XRLightProbe = XRLightProbe
  { coefficients :: Array (Vec3 Number)  -- ^ 9 RGB coefficients
  , primaryDirection :: Vec3 Number      -- ^ Main light direction
  , primaryIntensity :: Number           -- ^ Main light intensity
  }

derive instance eqXRLightProbe :: Eq XRLightProbe

instance showXRLightProbe :: Show XRLightProbe where
  show (XRLightProbe p) =
    "XRLightProbe { intensity: " <> show p.primaryIntensity <> " }"

-- | Real-world light estimation
newtype XRLight = XRLight
  { probe :: Maybe XRLightProbe
  , ambientIntensity :: Number      -- ^ Overall ambient (0-1)
  , colorTemperature :: Number      -- ^ Kelvin (2000-10000)
  }

derive instance eqXRLight :: Eq XRLight

instance showXRLight :: Show XRLight where
  show (XRLight l) =
    "XRLight { ambient: " <> show l.ambientIntensity <>
    ", temperature: " <> show l.colorTemperature <> "K }"

-- | Create a light probe
lightProbe :: Array (Vec3 Number) -> Vec3 Number -> Number -> XRLightProbe
lightProbe coefficients primaryDirection primaryIntensity =
  XRLightProbe { coefficients, primaryDirection, primaryIntensity }

-- | Get estimated intensity (combines probe and ambient)
estimatedIntensity :: XRLight -> Number
estimatedIntensity (XRLight l) =
  case l.probe of
    Nothing -> l.ambientIntensity
    Just (XRLightProbe p) ->
      -- Combine ambient with probe intensity
      let probeContribution = p.primaryIntensity
          ambient = l.ambientIntensity
      in Math.sqrt (ambient * ambient + probeContribution * probeContribution)
