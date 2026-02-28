-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // scene3d // raycaster
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Raycaster — Pure functions for ray-based object picking and intersection.
-- |
-- | ## Proof Reference
-- | - Ray intersection: `proofs/Hydrogen/Math/Ray.lean`
-- | - Matrix operations: `proofs/Hydrogen/Math/Mat4.lean`, `Mat4Projection.lean`
-- |
-- | ## Key Function
-- | `rayFromCamera` — constructs a ray from camera through NDC point.
-- | This is THE function that makes mouse picking work.
-- |
-- | ## Pipeline
-- | 1. Mouse event → NDC coordinates (-1 to 1)
-- | 2. rayFromCamera → Ray in world space
-- | 3. intersectScene → sorted list of hits
-- | 4. Application handles hit (select, hover, etc.)
-- |
-- | ## Three.js Parity
-- | - Raycaster.setFromCamera
-- | - Raycaster.intersectObject/intersectObjects

module Hydrogen.GPU.Scene3D.Raycaster
  ( -- * Ray From Camera
    rayFromCamera
  , rayFromCameraMatrices
  
  -- * NDC Conversion
  , screenToNDC
  , ndcToScreen
  
  -- * Intersection Types
  , Intersection
  , intersectionPoint
  , intersectionDistance
  , intersectionNormal
  , intersectionUV
  , showIntersection
  , eqIntersection
  
  -- * Scene Intersection
  , intersectSphere3D
  , intersectBox3D
  , intersectPlane3D
  , intersectTriangle3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<>)
  , (==)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2(Vec2))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, subtractVec3, normalizeVec3)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4(Vec4), vec4)
import Hydrogen.Schema.Dimension.Matrix.Mat4 
  ( Mat4
  , mulMat4
  , mulVec4Mat4
  , invertMat4
  , makePerspective
  , makeLookAt
  )
import Hydrogen.Schema.Geometry.Ray (Ray, ray, pointAt)
import Hydrogen.Schema.Geometry.Ray as Ray
import Hydrogen.Schema.Geometry.Triangle (Triangle, getBarycoord, Barycentric(Barycentric), normalUnnormalized, getA, getB, getC)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // intersection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a ray intersection test.
-- |
-- | Contains the intersection point, distance from ray origin,
-- | and optionally the surface normal and UV coordinates.
type Intersection =
  { point :: Vec3 Number      -- World-space intersection point
  , distance :: Number        -- Distance from ray origin (t parameter)
  , normal :: Maybe (Vec3 Number)  -- Surface normal at intersection (if available)
  , uv :: Maybe (Vec2 Number)      -- Texture coordinates (if available)
  }

-- | Get the intersection point
intersectionPoint :: Intersection -> Vec3 Number
intersectionPoint i = i.point

-- | Get the distance from ray origin
intersectionDistance :: Intersection -> Number
intersectionDistance i = i.distance

-- | Get the surface normal (if available)
intersectionNormal :: Intersection -> Maybe (Vec3 Number)
intersectionNormal i = i.normal

-- | Get the UV coordinates (if available)
intersectionUV :: Intersection -> Maybe (Vec2 Number)
intersectionUV i = i.uv

-- | Debug string representation of an intersection.
-- |
-- | Used for logging, debugging, and development.
showIntersection :: Intersection -> String
showIntersection i = 
  "Intersection { point: " <> show i.point 
    <> ", distance: " <> show i.distance
    <> ", normal: " <> show i.normal
    <> ", uv: " <> show i.uv
    <> " }"

-- | Equality test for intersections.
-- |
-- | Two intersections are equal if their points and distances match.
-- | Compares all fields: point, distance, normal, and uv.
eqIntersection :: Intersection -> Intersection -> Boolean
eqIntersection a b =
  a.point == b.point
    && a.distance == b.distance
    && a.normal == b.normal
    && a.uv == b.uv

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // ndc conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert screen coordinates to Normalized Device Coordinates (NDC).
-- |
-- | Screen coordinates: (0, 0) is top-left, (width, height) is bottom-right
-- | NDC coordinates: (-1, -1) is bottom-left, (1, 1) is top-right
-- |
-- | Note: Y is flipped because screen Y grows downward but NDC Y grows upward.
screenToNDC 
  :: Number  -- screenX
  -> Number  -- screenY
  -> Number  -- viewportWidth
  -> Number  -- viewportHeight
  -> Vec2 Number
screenToNDC screenX screenY width height =
  Vec2
    ((screenX / width) * 2.0 - 1.0)
    (negate ((screenY / height) * 2.0 - 1.0))

-- | Convert NDC coordinates back to screen coordinates.
ndcToScreen
  :: Number  -- ndcX
  -> Number  -- ndcY
  -> Number  -- viewportWidth
  -> Number  -- viewportHeight
  -> Vec2 Number
ndcToScreen ndcX ndcY width height =
  Vec2
    ((ndcX + 1.0) * 0.5 * width)
    ((1.0 - ndcY) * 0.5 * height)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // ray from camera
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a ray from camera through a point in NDC space.
-- |
-- | This is THE critical function for mouse picking.
-- |
-- | ## Algorithm
-- | 1. Compute view-projection matrix: VP = projection × view
-- | 2. Compute inverse: VP⁻¹
-- | 3. Unproject near point: VP⁻¹ × (ndcX, ndcY, -1, 1)
-- | 4. Unproject far point: VP⁻¹ × (ndcX, ndcY, 1, 1)
-- | 5. Ray origin = near point (after perspective divide)
-- | 6. Ray direction = normalize(far - near)
-- |
-- | ## Parameters
-- | - ndcX: X in Normalized Device Coordinates (-1 = left, 1 = right)
-- | - ndcY: Y in Normalized Device Coordinates (-1 = bottom, 1 = top)
-- | - cameraPosition: Camera position in world space
-- | - cameraTarget: Point the camera looks at
-- | - cameraUp: Camera up vector
-- | - fov: Vertical field of view in radians
-- | - aspect: Viewport width / height
-- | - near: Near clipping plane
-- | - far: Far clipping plane
-- |
-- | Returns Nothing if the view-projection matrix is not invertible.
-- |
-- | Proof reference: Raycaster.lean rayFromCamera_origin_on_nearPlane (theorem pending)
rayFromCamera
  :: Number  -- ndcX
  -> Number  -- ndcY
  -> Vec3 Number  -- cameraPosition
  -> Vec3 Number  -- cameraTarget
  -> Vec3 Number  -- cameraUp
  -> Number  -- fov (radians)
  -> Number  -- aspect
  -> Number  -- near
  -> Number  -- far
  -> Maybe Ray
rayFromCamera ndcX ndcY position target up fov aspect near far =
  let
    viewMatrix = makeLookAt position target up
    projMatrix = makePerspective fov aspect near far
    viewProj = mulMat4 projMatrix viewMatrix
  in
    rayFromCameraMatrices ndcX ndcY viewProj

-- | Create a ray from pre-computed view-projection matrix.
-- |
-- | Use this when you already have the VP matrix (avoids recomputing it).
rayFromCameraMatrices
  :: Number  -- ndcX
  -> Number  -- ndcY
  -> Mat4    -- viewProjection matrix
  -> Maybe Ray
rayFromCameraMatrices ndcX ndcY viewProj =
  case invertMat4 viewProj of
    Nothing -> Nothing
    Just invVP ->
      let
        -- Unproject near point (z = -1 in NDC for OpenGL convention)
        nearClip = unprojectPoint invVP ndcX ndcY (negate 1.0)
        -- Unproject far point (z = 1 in NDC)
        farClip = unprojectPoint invVP ndcX ndcY 1.0
        -- Ray direction: from near to far
        direction = normalizeVec3 (subtractVec3 farClip nearClip)
      in
        Just (ray nearClip direction)

-- | Unproject a point from NDC to world space.
-- |
-- | Applies the inverse view-projection matrix and performs perspective divide.
unprojectPoint :: Mat4 -> Number -> Number -> Number -> Vec3 Number
unprojectPoint invVP x y z =
  let
    -- Create homogeneous coordinate
    clipSpace = vec4 x y z 1.0
    -- Transform by inverse VP
    Vec4 wx wy wz ww = mulVec4Mat4 invVP clipSpace
    -- Perspective divide (w should be non-zero after valid unproject)
    invW = if Math.abs ww < 1.0e-10 then 1.0 else 1.0 / ww
  in
    vec3 (wx * invW) (wy * invW) (wz * invW)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // primitive intersection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Intersect ray with a sphere, returning full intersection info.
intersectSphere3D
  :: Ray
  -> Vec3 Number  -- center
  -> Number       -- radius
  -> Maybe Intersection
intersectSphere3D r center radius =
  case Ray.intersectSphereParameter r center radius of
    Nothing -> Nothing
    Just t ->
      let
        p = pointAt r t
        -- Normal points outward from center
        normal = normalizeVec3 (subtractVec3 p center)
      in
        Just
          { point: p
          , distance: t
          , normal: Just normal
          , uv: Nothing  -- UV would require spherical mapping
          }

-- | Intersect ray with an axis-aligned box, returning full intersection info.
-- |
-- | Computes the face normal by determining which face was hit based on
-- | the intersection point's position relative to the box faces.
intersectBox3D
  :: Ray
  -> Vec3 Number  -- boxMin
  -> Vec3 Number  -- boxMax
  -> Maybe Intersection
intersectBox3D r boxMin boxMax =
  case Ray.intersectBoxParameter r boxMin boxMax of
    Nothing -> Nothing
    Just t ->
      let
        p = pointAt r t
        normal = computeBoxNormal p boxMin boxMax
      in
        Just
          { point: p
          , distance: t
          , normal: Just normal
          , uv: Nothing  -- UV would require face-specific parametrization
          }

-- | Compute the outward-facing normal for a point on an AABB surface.
-- |
-- | Determines which face the point is closest to and returns the
-- | corresponding axis-aligned normal vector.
computeBoxNormal :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number
computeBoxNormal (Vec3 px py pz) (Vec3 minX minY minZ) (Vec3 maxX maxY maxZ) =
  let
    -- Compute distance to each face
    dMinX = Math.abs (px - minX)
    dMaxX = Math.abs (px - maxX)
    dMinY = Math.abs (py - minY)
    dMaxY = Math.abs (py - maxY)
    dMinZ = Math.abs (pz - minZ)
    dMaxZ = Math.abs (pz - maxZ)
    
    -- Find minimum distance (which face we're on)
    minDist = Math.min dMinX (Math.min dMaxX (Math.min dMinY (Math.min dMaxY (Math.min dMinZ dMaxZ))))
  in
    -- Return the normal for the closest face
    if dMinX < minDist + epsilon then vec3 (negate 1.0) 0.0 0.0  -- -X face
    else if dMaxX < minDist + epsilon then vec3 1.0 0.0 0.0       -- +X face
    else if dMinY < minDist + epsilon then vec3 0.0 (negate 1.0) 0.0  -- -Y face
    else if dMaxY < minDist + epsilon then vec3 0.0 1.0 0.0       -- +Y face
    else if dMinZ < minDist + epsilon then vec3 0.0 0.0 (negate 1.0)  -- -Z face
    else vec3 0.0 0.0 1.0  -- +Z face (default)
  where
    epsilon = 1.0e-6

-- | Intersect ray with an infinite plane, returning full intersection info.
intersectPlane3D
  :: Ray
  -> Vec3 Number  -- planeNormal (should be normalized for correct distance)
  -> Number       -- planeConstant
  -> Maybe Intersection
intersectPlane3D r planeNormal planeConstant =
  case Ray.intersectPlaneParameter r planeNormal planeConstant of
    Nothing -> Nothing
    Just t ->
      let
        p = pointAt r t
      in
        Just
          { point: p
          , distance: t
          , normal: Just planeNormal
          , uv: Nothing  -- UV would require plane parametrization
          }

-- | Intersect ray with a triangle, returning full intersection info including UV.
-- |
-- | The UV coordinates are computed from the barycentric coordinates of the
-- | intersection point. For texture mapping:
-- | - uv.x corresponds to the v-coordinate (weight of vertex B)
-- | - uv.y corresponds to the w-coordinate (weight of vertex C)
-- |
-- | This allows texture interpolation: tex(hit) = u*texA + v*texB + w*texC
-- |
-- | The normal is computed as the geometric face normal (cross product of edges).
-- | For smooth shading, interpolate vertex normals using the barycentric coords.
-- |
-- | Proof reference: Ray.lean intersectTriangle_pointAt_onTriangle (pending)
-- | Three.js parity: Raycaster.intersectObject for mesh
intersectTriangle3D
  :: Ray
  -> Triangle
  -> Boolean  -- backfaceCulling: if true, skip triangles facing away
  -> Maybe Intersection
intersectTriangle3D r tri backfaceCulling =
  let
    -- Extract triangle vertices
    v0 = getA tri
    v1 = getB tri
    v2 = getC tri
  in
    case Ray.intersectTriangleParameter r v0 v1 v2 backfaceCulling of
      Nothing -> Nothing
      Just t ->
        let
          p = pointAt r t
          -- Get barycentric coordinates for UV
          Barycentric _ v w = getBarycoord tri p
          -- Face normal from the triangle (normalized)
          normal = normalizeVec3 (normalUnnormalized tri)
        in
          Just
            { point: p
            , distance: t
            , normal: Just normal
            , uv: Just (Vec2 v w)  -- UV from barycentric (v, w) for vertices B, C
            }
