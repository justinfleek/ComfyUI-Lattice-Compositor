-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // spatial // xr // session
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | XR Session — WebXR session configuration and world understanding.
-- |
-- | ## XRSession
-- | Configuration for AR/VR sessions. Defines mode, features, and reference space.
-- |
-- | ## XRAnchor
-- | World-locked position. Persists across sessions in some implementations.
-- | Used for placing virtual objects in real space.
-- |
-- | ## XRPlane
-- | Detected real-world surface (floor, wall, table).
-- | Provides position, orientation, and boundary polygon.
-- |
-- | ## XRMesh
-- | Scanned environment geometry. Dense reconstruction of real space.
-- | Used for occlusion, physics, and spatial understanding.

module Hydrogen.Schema.Spatial.XR.Session
  ( -- * Session
    XRSessionMode(..)
  , XRSessionFeature(..)
  , XRReferenceSpace(..)
  , XRSession(..)
  
  -- * Anchors
  , XRAnchorId
  , xrAnchorId
  , unwrapAnchorId
  , XRAnchorState(..)
  , XRAnchor(..)
  
  -- * Planes
  , XRPlaneId
  , xrPlaneId
  , XRPlaneOrientation(..)
  , XRPlane(..)
  
  -- * Meshes
  , XRMeshId
  , xrMeshId
  , XRMesh(..)
  
  -- * Constructors
  , immersiveVR
  , immersiveAR
  , inlineSession
  , anchor
  , planeFromPolygon
  
  -- * Accessors
  , sessionSupportsFeature
  , anchorPosition
  , anchorRotation
  , anchorDistance
  , planeCenter
  , planeArea
  , planeDistance
  , meshVertexCount
  
  -- * Session State
  , XRSessionState(..)
  , XRVisibilityState(..)
  ) where

import Prelude

import Data.Array (length, foldl, (!!))
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, addVec3, scaleVec3, crossVec3, lengthVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // session mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | XR session mode
-- |
-- | Defines the type of XR experience.
data XRSessionMode
  = Inline               -- ^ Non-immersive (in-page 3D)
  | ImmersiveVR          -- ^ Full VR (headset takes over display)
  | ImmersiveAR          -- ^ Full AR (passthrough with overlays)

derive instance eqXRSessionMode :: Eq XRSessionMode
derive instance ordXRSessionMode :: Ord XRSessionMode

instance showXRSessionMode :: Show XRSessionMode where
  show Inline = "inline"
  show ImmersiveVR = "immersive-vr"
  show ImmersiveAR = "immersive-ar"

-- | XR session features
-- |
-- | Optional capabilities requested during session creation.
data XRSessionFeature
  = LocalFloor           -- ^ Floor-level tracking
  | BoundedFloor         -- ^ Room-scale with bounds
  | Unbounded            -- ^ Large-scale (warehouse, outdoor)
  | HandTracking         -- ^ Hand joint tracking
  | HitTest              -- ^ Raycasting against real world
  | DomOverlay           -- ^ HTML overlay in AR
  | LightEstimation      -- ^ Real-world lighting info
  | Anchors              -- ^ Persistent world anchors
  | PlaneDetection       -- ^ Surface detection
  | MeshDetection        -- ^ Environment mesh scanning
  | DepthSensing         -- ^ Depth buffer access
  | CameraAccess         -- ^ Raw camera feed

derive instance eqXRSessionFeature :: Eq XRSessionFeature
derive instance ordXRSessionFeature :: Ord XRSessionFeature

instance showXRSessionFeature :: Show XRSessionFeature where
  show LocalFloor = "local-floor"
  show BoundedFloor = "bounded-floor"
  show Unbounded = "unbounded"
  show HandTracking = "hand-tracking"
  show HitTest = "hit-test"
  show DomOverlay = "dom-overlay"
  show LightEstimation = "light-estimation"
  show Anchors = "anchors"
  show PlaneDetection = "plane-detection"
  show MeshDetection = "mesh-detection"
  show DepthSensing = "depth-sensing"
  show CameraAccess = "camera-access"

-- | XR reference space type
-- |
-- | Defines the coordinate system origin and behavior.
data XRReferenceSpace
  = Viewer               -- ^ Head-locked (follows user's view)
  | Local                -- ^ Seated, origin at initial position
  | LocalFloorSpace      -- ^ Standing, origin at floor level
  | BoundedFloorSpace    -- ^ Room-scale with safe bounds
  | UnboundedSpace       -- ^ Large-scale tracking

derive instance eqXRReferenceSpace :: Eq XRReferenceSpace
derive instance ordXRReferenceSpace :: Ord XRReferenceSpace

instance showXRReferenceSpace :: Show XRReferenceSpace where
  show Viewer = "viewer"
  show Local = "local"
  show LocalFloorSpace = "local-floor"
  show BoundedFloorSpace = "bounded-floor"
  show UnboundedSpace = "unbounded"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // session state
-- ═════════════════════════════════════════════════════════════════════════════

-- | XR session lifecycle state
data XRSessionState
  = SessionPending       -- ^ Waiting for user permission
  | SessionActive        -- ^ Running and rendering
  | SessionEnded         -- ^ Terminated

derive instance eqXRSessionState :: Eq XRSessionState
derive instance ordXRSessionState :: Ord XRSessionState

instance showXRSessionState :: Show XRSessionState where
  show SessionPending = "pending"
  show SessionActive = "active"
  show SessionEnded = "ended"

-- | XR visibility state
-- |
-- | Indicates whether content is visible to user.
data XRVisibilityState
  = Visible              -- ^ Content fully visible
  | VisibleBlurred       -- ^ Visible but obscured (system UI)
  | Hidden               -- ^ Not visible (paused)

derive instance eqXRVisibilityState :: Eq XRVisibilityState
derive instance ordXRVisibilityState :: Ord XRVisibilityState

instance showXRVisibilityState :: Show XRVisibilityState where
  show Visible = "visible"
  show VisibleBlurred = "visible-blurred"
  show Hidden = "hidden"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // session
-- ═════════════════════════════════════════════════════════════════════════════

-- | XR session configuration
newtype XRSession = XRSession
  { mode :: XRSessionMode
  , requiredFeatures :: Array XRSessionFeature
  , optionalFeatures :: Array XRSessionFeature
  , referenceSpace :: XRReferenceSpace
  , frameRate :: Maybe Number       -- ^ Target frame rate (90, 120, etc.)
  , state :: XRSessionState
  , visibility :: XRVisibilityState
  }

derive instance eqXRSession :: Eq XRSession

instance showXRSession :: Show XRSession where
  show (XRSession s) =
    "XRSession { mode: " <> show s.mode <>
    ", referenceSpace: " <> show s.referenceSpace <>
    ", state: " <> show s.state <> " }"

-- | Create an immersive VR session
immersiveVR :: Array XRSessionFeature -> XRSession
immersiveVR features = XRSession
  { mode: ImmersiveVR
  , requiredFeatures: [LocalFloor]
  , optionalFeatures: features
  , referenceSpace: LocalFloorSpace
  , frameRate: Just 90.0
  , state: SessionPending
  , visibility: Hidden
  }

-- | Create an immersive AR session
immersiveAR :: Array XRSessionFeature -> XRSession
immersiveAR features = XRSession
  { mode: ImmersiveAR
  , requiredFeatures: [LocalFloor, HitTest]
  , optionalFeatures: features
  , referenceSpace: LocalFloorSpace
  , frameRate: Nothing  -- Match device
  , state: SessionPending
  , visibility: Hidden
  }

-- | Create an inline (non-immersive) session
inlineSession :: XRSession
inlineSession = XRSession
  { mode: Inline
  , requiredFeatures: []
  , optionalFeatures: []
  , referenceSpace: Viewer
  , frameRate: Nothing
  , state: SessionPending
  , visibility: Visible
  }

-- | Check if session supports a feature
sessionSupportsFeature :: XRSessionFeature -> XRSession -> Boolean
sessionSupportsFeature feature (XRSession s) =
  elem feature s.requiredFeatures || elem feature s.optionalFeatures
  where
  elem :: forall a. Eq a => a -> Array a -> Boolean
  elem x arr = foldl (\acc y -> acc || x == y) false arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // anchors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique anchor identifier
newtype XRAnchorId = XRAnchorId String

derive instance eqXRAnchorId :: Eq XRAnchorId
derive instance ordXRAnchorId :: Ord XRAnchorId

instance showXRAnchorId :: Show XRAnchorId where
  show (XRAnchorId id) = "Anchor:" <> id

-- | Create an anchor ID
xrAnchorId :: String -> XRAnchorId
xrAnchorId = XRAnchorId

-- | Extract anchor ID string
unwrapAnchorId :: XRAnchorId -> String
unwrapAnchorId (XRAnchorId id) = id

-- | Anchor tracking state
data XRAnchorState
  = AnchorTracking       -- ^ Actively tracked
  | AnchorPaused         -- ^ Temporarily lost
  | AnchorLost           -- ^ Cannot be recovered

derive instance eqXRAnchorState :: Eq XRAnchorState
derive instance ordXRAnchorState :: Ord XRAnchorState

instance showXRAnchorState :: Show XRAnchorState where
  show AnchorTracking = "tracking"
  show AnchorPaused = "paused"
  show AnchorLost = "lost"

-- | World-locked anchor
newtype XRAnchor = XRAnchor
  { id :: XRAnchorId
  , position :: Vec3 Number         -- ^ World position
  , rotation :: Vec3 Number         -- ^ Euler angles (XYZ)
  , state :: XRAnchorState
  , createdAt :: Number             -- ^ Timestamp (ms)
  , persistent :: Boolean           -- ^ Survives across sessions?
  }

derive instance eqXRAnchor :: Eq XRAnchor

instance showXRAnchor :: Show XRAnchor where
  show (XRAnchor a) =
    "XRAnchor { id: " <> show a.id <>
    ", position: " <> show a.position <>
    ", state: " <> show a.state <> " }"

-- | Create an anchor at a position
anchor :: XRAnchorId -> Vec3 Number -> Vec3 Number -> XRAnchor
anchor id position rotation = XRAnchor
  { id
  , position
  , rotation
  , state: AnchorTracking
  , createdAt: 0.0
  , persistent: false
  }

-- | Get anchor position
anchorPosition :: XRAnchor -> Vec3 Number
anchorPosition (XRAnchor a) = a.position

-- | Get anchor rotation (Euler XYZ)
anchorRotation :: XRAnchor -> Vec3 Number
anchorRotation (XRAnchor a) = a.rotation

-- | Compute distance between two anchors (meters)
anchorDistance :: XRAnchor -> XRAnchor -> Number
anchorDistance (XRAnchor a1) (XRAnchor a2) =
  let diff = subtractVec3 a2.position a1.position
  in lengthVec3 diff
  where
  subtractVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  subtractVec3 v1 v2 = addVec3 v1 (scaleVec3 (-1.0) v2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // planes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique plane identifier
newtype XRPlaneId = XRPlaneId String

derive instance eqXRPlaneId :: Eq XRPlaneId
derive instance ordXRPlaneId :: Ord XRPlaneId

instance showXRPlaneId :: Show XRPlaneId where
  show (XRPlaneId id) = "Plane:" <> id

-- | Create a plane ID
xrPlaneId :: String -> XRPlaneId
xrPlaneId = XRPlaneId

-- | Plane orientation
data XRPlaneOrientation
  = Horizontal           -- ^ Floor, ceiling, table
  | Vertical             -- ^ Wall, door

derive instance eqXRPlaneOrientation :: Eq XRPlaneOrientation
derive instance ordXRPlaneOrientation :: Ord XRPlaneOrientation

instance showXRPlaneOrientation :: Show XRPlaneOrientation where
  show Horizontal = "horizontal"
  show Vertical = "vertical"

-- | Detected real-world plane
newtype XRPlane = XRPlane
  { id :: XRPlaneId
  , position :: Vec3 Number         -- ^ Center of plane
  , rotation :: Vec3 Number         -- ^ Normal orientation (Euler)
  , polygon :: Array (Vec3 Number)  -- ^ Boundary vertices (local space)
  , orientation :: XRPlaneOrientation
  , semanticLabel :: Maybe String   -- ^ "floor", "wall", "table", etc.
  }

derive instance eqXRPlane :: Eq XRPlane

instance showXRPlane :: Show XRPlane where
  show (XRPlane p) =
    "XRPlane { id: " <> show p.id <>
    ", orientation: " <> show p.orientation <>
    ", vertices: " <> show (length p.polygon) <> " }"

-- | Create a plane from polygon vertices
planeFromPolygon :: XRPlaneId -> Array (Vec3 Number) -> XRPlaneOrientation -> XRPlane
planeFromPolygon id polygon orientation = XRPlane
  { id
  , position: computeCenter polygon
  , rotation: vec3 0.0 0.0 0.0
  , polygon
  , orientation
  , semanticLabel: Nothing
  }
  where
  computeCenter :: Array (Vec3 Number) -> Vec3 Number
  computeCenter [] = vec3 0.0 0.0 0.0
  computeCenter pts =
    let n = length pts
        sum = foldl addVec3 (vec3 0.0 0.0 0.0) pts
    in scaleVec3 (1.0 / Int.toNumber n) sum

-- | Get plane center position
planeCenter :: XRPlane -> Vec3 Number
planeCenter (XRPlane p) = p.position

-- | Compute distance between two plane centers (meters)
planeDistance :: XRPlane -> XRPlane -> Number
planeDistance (XRPlane p1) (XRPlane p2) =
  let diff = subtractVec3 p2.position p1.position
      lenSq = dotProduct diff diff
  in Math.sqrt lenSq
  where
  subtractVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  subtractVec3 v1 v2 = addVec3 v1 (scaleVec3 (-1.0) v2)
  
  -- Compute dot product using |a+b|² = |a|² + |b|² + 2(a·b)
  dotProduct :: Vec3 Number -> Vec3 Number -> Number
  dotProduct v1 v2 =
    let l1 = lengthVec3 v1
        l2 = lengthVec3 v2
        combined = lengthVec3 (addVec3 v1 v2)
    in (combined * combined - l1 * l1 - l2 * l2) / 2.0

-- | Compute approximate plane area
-- |
-- | Uses cross product magnitude for triangle fan area approximation.
planeArea :: XRPlane -> Number
planeArea (XRPlane p) = computePolygonArea p.polygon
  where
  computePolygonArea :: Array (Vec3 Number) -> Number
  computePolygonArea pts
    | length pts < 3 = 0.0
    | otherwise =
        -- Sum triangle areas using fan from first vertex
        let center = case pts !! 0 of
              Just v -> v
              Nothing -> vec3 0.0 0.0 0.0
        in foldl (\acc i -> acc + triangleArea center i pts) 0.0 (indices (length pts - 2))
  
  triangleArea :: Vec3 Number -> Int -> Array (Vec3 Number) -> Number
  triangleArea center i pts =
    case pts !! (i + 1) of
      Nothing -> 0.0
      Just p1 ->
        case pts !! (i + 2) of
          Nothing -> 0.0
          Just p2 ->
            let edge1 = subtractVec3 p1 center
                edge2 = subtractVec3 p2 center
                cross = crossVec3 edge1 edge2
            in lengthVec3 cross / 2.0
  
  subtractVec3 :: Vec3 Number -> Vec3 Number -> Vec3 Number
  subtractVec3 a b = addVec3 a (scaleVec3 (-1.0) b)
  
  indices :: Int -> Array Int
  indices n = buildIndices n 0 []
  
  buildIndices :: Int -> Int -> Array Int -> Array Int
  buildIndices total current acc
    | current >= total = acc
    | otherwise = buildIndices total (current + 1) (acc <> [current])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // meshes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique mesh identifier
newtype XRMeshId = XRMeshId String

derive instance eqXRMeshId :: Eq XRMeshId
derive instance ordXRMeshId :: Ord XRMeshId

instance showXRMeshId :: Show XRMeshId where
  show (XRMeshId id) = "Mesh:" <> id

-- | Create a mesh ID
xrMeshId :: String -> XRMeshId
xrMeshId = XRMeshId

-- | Scanned environment mesh
newtype XRMesh = XRMesh
  { id :: XRMeshId
  , positions :: Array Number       -- ^ Vertex positions (flat, x3)
  , indices :: Array Int            -- ^ Triangle indices
  , normals :: Maybe (Array Number) -- ^ Vertex normals (optional)
  , lastUpdated :: Number           -- ^ Timestamp (ms)
  , semanticLabels :: Maybe (Array String) -- ^ Per-vertex labels
  }

derive instance eqXRMesh :: Eq XRMesh

instance showXRMesh :: Show XRMesh where
  show (XRMesh m) =
    "XRMesh { id: " <> show m.id <>
    ", vertices: " <> show (length m.positions / 3) <>
    ", triangles: " <> show (length m.indices / 3) <> " }"

-- | Get mesh vertex count
meshVertexCount :: XRMesh -> Int
meshVertexCount (XRMesh m) = length m.positions / 3
