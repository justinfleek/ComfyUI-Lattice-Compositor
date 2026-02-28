-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // scene3d // snap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Snapping — Constrain transforms to discrete values.
-- |
-- | ## Design Philosophy
-- | Snapping is pure math. Given a position/rotation, compute the nearest
-- | snap target. No FFI. Snap targets can be grid points, vertices, edges,
-- | faces, or angle increments.
-- |
-- | ## Three.js Parity
-- | - TransformControls snap option
-- | - Grid snapping
-- | - Rotation snapping
-- |
-- | ## Cinema4D/Blender Parity
-- | - Vertex snapping
-- | - Edge snapping (midpoint and along-edge)
-- | - Face snapping (centroid and surface)
-- | - Angle snapping (15°, 45°, 90° increments)
-- | - Incremental snapping (relative to start)

module Hydrogen.GPU.Scene3D.Snap
  ( -- * Snap Target Types
    SnapTarget
      ( SnapToGrid
      , SnapToVertex
      , SnapToEdge
      , SnapToEdgeMidpoint
      , SnapToFace
      , SnapToFaceCentroid
      , SnapToAngle
      , SnapToIncrement
      , SnapToPath
      , SnapDisabled
      )
  
  -- * Snap Configuration
  , SnapConfig
  , defaultSnapConfig
  
  -- * Snap Result
  , SnapResult
  , noSnap
  
  -- * Position Snapping
  , snapPosition
  , snapToGrid
  , snapToNearestVertex
  , snapToNearestEdge
  , snapToEdgeMidpoints
  
  -- * Rotation Snapping
  , snapRotation
  , snapAngle
  
  -- * Edge Snapping Helpers
  , Edge
  , edgeFromVertices
  , closestPointOnEdge
  , distanceToEdge
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , class Ord
  , show
  , compare
  , map
  , min
  , max
  , negate
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  )

import Data.Array (head, sortBy)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ord (abs)

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3(Vec3)
  , vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , dotVec3
  , lengthVec3
  , distanceVec3
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // snap target
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of snapping to apply.
-- |
-- | Multiple snap types can be active — the nearest result wins.
data SnapTarget
  = SnapToGrid                -- Snap to grid intersections
  | SnapToVertex              -- Snap to mesh vertices
  | SnapToEdge                -- Snap along edge (any point)
  | SnapToEdgeMidpoint        -- Snap to edge midpoints only
  | SnapToFace                -- Snap to face surface
  | SnapToFaceCentroid        -- Snap to face centers only
  | SnapToAngle               -- Snap rotation to angle increments
  | SnapToIncrement           -- Snap by fixed increment from start
  | SnapToPath                -- Snap to spline/path curve
  | SnapDisabled              -- No snapping

derive instance eqSnapTarget :: Eq SnapTarget

instance showSnapTarget :: Show SnapTarget where
  show SnapToGrid = "SnapToGrid"
  show SnapToVertex = "SnapToVertex"
  show SnapToEdge = "SnapToEdge"
  show SnapToEdgeMidpoint = "SnapToEdgeMidpoint"
  show SnapToFace = "SnapToFace"
  show SnapToFaceCentroid = "SnapToFaceCentroid"
  show SnapToAngle = "SnapToAngle"
  show SnapToIncrement = "SnapToIncrement"
  show SnapToPath = "SnapToPath"
  show SnapDisabled = "SnapDisabled"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // snap config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for snapping behavior.
type SnapConfig =
  { enabled :: Boolean                -- Global snap enable
  , targets :: Array SnapTarget       -- Active snap types (priority order)
  , gridSize :: Number                -- Grid cell size for grid snapping
  , angleIncrement :: Number          -- Angle increment in degrees
  , positionIncrement :: Number       -- Position increment for incremental snap
  , snapRadius :: Number              -- Max distance to consider for snapping
  , vertexSnapRadius :: Number        -- Specific radius for vertex snapping
  , edgeSnapRadius :: Number          -- Specific radius for edge snapping
  }

-- | Default snap configuration — grid snapping at 1 unit.
defaultSnapConfig :: SnapConfig
defaultSnapConfig =
  { enabled: true
  , targets: [SnapToGrid]
  , gridSize: 1.0
  , angleIncrement: 15.0              -- 15 degree increments
  , positionIncrement: 0.1
  , snapRadius: 0.5
  , vertexSnapRadius: 0.3
  , edgeSnapRadius: 0.2
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // snap result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a snap operation.
-- |
-- | Contains the snapped position and which snap type was used.
type SnapResult =
  { position :: Vec3 Number           -- Snapped position
  , snapType :: SnapTarget            -- Which snap was applied
  , distance :: Number                -- Distance moved to snap
  , didSnap :: Boolean                -- Whether snapping occurred
  }

-- | No snap result — position unchanged.
noSnap :: Vec3 Number -> SnapResult
noSnap pos =
  { position: pos
  , snapType: SnapDisabled
  , distance: 0.0
  , didSnap: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // position snapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snap a position according to configuration.
-- |
-- | Tries each enabled snap target and returns the nearest result.
snapPosition :: SnapConfig -> Vec3 Number -> Array (Vec3 Number) -> Array Edge -> SnapResult
snapPosition config pos vertices edges =
  if config.enabled
    then findBestSnap config pos vertices edges
    else noSnap pos

-- | Find the best snap among all enabled targets.
findBestSnap :: SnapConfig -> Vec3 Number -> Array (Vec3 Number) -> Array Edge -> SnapResult
findBestSnap config pos vertices edges =
  let
    candidates = map (trySnapTarget config pos vertices edges) config.targets
    validSnaps = sortBy compareDistance candidates
  in
    case head validSnaps of
      Just result -> if result.didSnap then result else noSnap pos
      Nothing -> noSnap pos
  where
    compareDistance a b = compare a.distance b.distance

-- | Try a specific snap target.
trySnapTarget :: SnapConfig -> Vec3 Number -> Array (Vec3 Number) -> Array Edge -> SnapTarget -> SnapResult
trySnapTarget config pos vertices edges target = case target of
  SnapToGrid -> snapToGrid config.gridSize pos
  SnapToVertex -> snapToNearestVertex config.vertexSnapRadius vertices pos
  SnapToEdge -> snapToNearestEdge config.edgeSnapRadius edges pos
  SnapToEdgeMidpoint -> snapToEdgeMidpoints config.edgeSnapRadius edges pos
  SnapToIncrement -> snapToIncrement config.positionIncrement pos
  _ -> noSnap pos  -- Face, Path, etc. require more context

-- | Snap to nearest grid intersection.
snapToGrid :: Number -> Vec3 Number -> SnapResult
snapToGrid gridSize (Vec3 x y z) =
  let
    snapCoord c = Math.round (c / gridSize) * gridSize
    snappedX = snapCoord x
    snappedY = snapCoord y
    snappedZ = snapCoord z
    snapped = vec3 snappedX snappedY snappedZ
    dist = distanceVec3 (Vec3 x y z) snapped
  in
    { position: snapped
    , snapType: SnapToGrid
    , distance: dist
    , didSnap: true
    }

-- | Snap to increment from origin.
snapToIncrement :: Number -> Vec3 Number -> SnapResult
snapToIncrement increment (Vec3 x y z) =
  let
    snapCoord c = Math.round (c / increment) * increment
    snapped = vec3 (snapCoord x) (snapCoord y) (snapCoord z)
    dist = distanceVec3 (Vec3 x y z) snapped
  in
    { position: snapped
    , snapType: SnapToIncrement
    , distance: dist
    , didSnap: true
    }

-- | Snap to nearest vertex within radius.
snapToNearestVertex :: Number -> Array (Vec3 Number) -> Vec3 Number -> SnapResult
snapToNearestVertex radius vertices pos =
  let
    withDistances = map (\v -> { vertex: v, dist: distanceVec3 pos v }) vertices
    sorted = sortBy (\a b -> compare a.dist b.dist) withDistances
  in
    case head sorted of
      Just nearest ->
        if nearest.dist <= radius
          then { position: nearest.vertex
               , snapType: SnapToVertex
               , distance: nearest.dist
               , didSnap: true
               }
          else noSnap pos
      Nothing -> noSnap pos

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // edge
-- ═════════════════════════════════════════════════════════════════════════════

-- | An edge defined by two endpoints.
type Edge =
  { start :: Vec3 Number
  , end :: Vec3 Number
  }

-- | Create an edge from two vertices.
edgeFromVertices :: Vec3 Number -> Vec3 Number -> Edge
edgeFromVertices start end = { start, end }

-- | Find the closest point on an edge to a given point.
-- |
-- | Clamps the parameter to [0, 1] so result is always on the segment.
closestPointOnEdge :: Edge -> Vec3 Number -> Vec3 Number
closestPointOnEdge edge point =
  let
    edgeVec = subtractVec3 edge.end edge.start
    pointVec = subtractVec3 point edge.start
    edgeLenSq = dotVec3 edgeVec edgeVec
    t = if edgeLenSq < 1.0e-10
          then 0.0
          else max 0.0 (min 1.0 (dotVec3 pointVec edgeVec / edgeLenSq))
  in
    addVec3 edge.start (scaleVec3 t edgeVec)

-- | Distance from a point to an edge.
distanceToEdge :: Edge -> Vec3 Number -> Number
distanceToEdge edge point = distanceVec3 point (closestPointOnEdge edge point)

-- | Compute the midpoint of an edge.
edgeMidpoint :: Edge -> Vec3 Number
edgeMidpoint edge = scaleVec3 0.5 (addVec3 edge.start edge.end)

-- | Snap to nearest edge within radius.
snapToNearestEdge :: Number -> Array Edge -> Vec3 Number -> SnapResult
snapToNearestEdge radius edges pos =
  let
    withDistances = map (\e -> 
      let closest = closestPointOnEdge e pos
          dist = distanceVec3 pos closest
      in { point: closest, dist: dist }) edges
    sorted = sortBy (\a b -> compare a.dist b.dist) withDistances
  in
    case head sorted of
      Just nearest ->
        if nearest.dist <= radius
          then { position: nearest.point
               , snapType: SnapToEdge
               , distance: nearest.dist
               , didSnap: true
               }
          else noSnap pos
      Nothing -> noSnap pos

-- | Snap to nearest edge midpoint within radius.
snapToEdgeMidpoints :: Number -> Array Edge -> Vec3 Number -> SnapResult
snapToEdgeMidpoints radius edges pos =
  let
    midpoints = map edgeMidpoint edges
  in
    case snapToNearestVertex radius midpoints pos of
      result -> 
        if result.didSnap
          then result { snapType = SnapToEdgeMidpoint }
          else noSnap pos

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // rotation snapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snap an angle (in degrees) to nearest increment.
snapAngle :: Number -> Number -> Number
snapAngle increment angle =
  Math.round (angle / increment) * increment

-- | Snap rotation (as Euler angles in degrees).
snapRotation :: Number -> Vec3 Number -> Vec3 Number
snapRotation increment (Vec3 rx ry rz) =
  vec3 (snapAngle increment rx) (snapAngle increment ry) (snapAngle increment rz)
