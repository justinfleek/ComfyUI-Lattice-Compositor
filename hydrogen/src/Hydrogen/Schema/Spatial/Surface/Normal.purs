-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // spatial // surface // normal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Surface Vectors — Normal, Tangent, and Bitangent for surface definition.
-- |
-- | In 3D graphics, surfaces are defined by three orthogonal vectors:
-- |
-- | ## Normal (N)
-- | Perpendicular to the surface, points "outward". Used for:
-- | - Lighting calculations (diffuse, specular)
-- | - Backface culling
-- | - Collision detection
-- |
-- | ## Tangent (T)
-- | Parallel to the surface along the U texture direction. Used for:
-- | - Normal mapping (tangent-space normals)
-- | - Anisotropic reflections (hair, brushed metal)
-- |
-- | ## Bitangent (B)
-- | Perpendicular to both Normal and Tangent (V texture direction).
-- | Together N, T, B form the TBN matrix for tangent-space transformations.
-- |
-- | All three are unit vectors (length = 1.0).

module Hydrogen.Schema.Spatial.Surface.Normal
  ( -- * Types
    Normal(..)
  , Tangent(..)
  , Bitangent(..)
  , TBNFrame(..)
  
  -- * Constructors
  , normal
  , tangent
  , bitangent
  , tbnFrame
  , tbnFromNormalTangent
  
  -- * Accessors
  , normalVec
  , tangentVec
  , bitangentVec
  , tbnMatrix
  
  -- * Operations
  , flipNormal
  , transformToTangentSpace
  , transformFromTangentSpace
  , faceNormal
  
  -- * Predicates
  , isUnitLength
  , isOrthogonal
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3(Vec3), vec3, crossVec3, dotVec3, normalizeVec3, lengthVec3, scaleVec3, negateVec3, subtractVec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // normal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface normal vector (unit length, perpendicular to surface)
-- |
-- | Normals must be unit length. The constructor normalizes the input.
newtype Normal = Normal (Vec3 Number)

derive instance eqNormal :: Eq Normal

instance showNormal :: Show Normal where
  show (Normal v) = "Normal " <> show v

-- | Create a normal from a Vec3 (normalizes automatically)
normal :: Vec3 Number -> Maybe Normal
normal v =
  let len = lengthVec3 v
  in if len < 0.0001
     then Nothing  -- Zero vector cannot be normalized
     else Just (Normal (normalizeVec3 v))

-- | Get the underlying vector
normalVec :: Normal -> Vec3 Number
normalVec (Normal v) = v

-- | Flip normal direction (for backfaces)
flipNormal :: Normal -> Normal
flipNormal (Normal v) = Normal (negateVec3 v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // tangent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface tangent vector (unit length, along U texture direction)
-- |
-- | Tangents must be unit length. The constructor normalizes the input.
newtype Tangent = Tangent (Vec3 Number)

derive instance eqTangent :: Eq Tangent

instance showTangent :: Show Tangent where
  show (Tangent v) = "Tangent " <> show v

-- | Create a tangent from a Vec3 (normalizes automatically)
tangent :: Vec3 Number -> Maybe Tangent
tangent v =
  let len = lengthVec3 v
  in if len < 0.0001
     then Nothing
     else Just (Tangent (normalizeVec3 v))

-- | Get the underlying vector
tangentVec :: Tangent -> Vec3 Number
tangentVec (Tangent v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bitangent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface bitangent vector (unit length, along V texture direction)
-- |
-- | Bitangent = cross(Normal, Tangent) in a right-handed coordinate system.
newtype Bitangent = Bitangent (Vec3 Number)

derive instance eqBitangent :: Eq Bitangent

instance showBitangent :: Show Bitangent where
  show (Bitangent v) = "Bitangent " <> show v

-- | Create a bitangent from a Vec3 (normalizes automatically)
bitangent :: Vec3 Number -> Maybe Bitangent
bitangent v =
  let len = lengthVec3 v
  in if len < 0.0001
     then Nothing
     else Just (Bitangent (normalizeVec3 v))

-- | Get the underlying vector
bitangentVec :: Bitangent -> Vec3 Number
bitangentVec (Bitangent v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tbn frame
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tangent-Bitangent-Normal frame for surface orientation
-- |
-- | The TBN frame defines a local coordinate system at each point on a surface.
-- | Used for normal mapping and anisotropic shading.
newtype TBNFrame = TBNFrame
  { tangent :: Tangent
  , bitangent :: Bitangent
  , normal :: Normal
  }

derive instance eqTBNFrame :: Eq TBNFrame

instance showTBNFrame :: Show TBNFrame where
  show (TBNFrame f) = 
    "TBNFrame { tangent: " <> show f.tangent <>
    ", bitangent: " <> show f.bitangent <>
    ", normal: " <> show f.normal <> " }"

-- | Create a TBN frame from explicit vectors
tbnFrame :: Tangent -> Bitangent -> Normal -> TBNFrame
tbnFrame t b n = TBNFrame { tangent: t, bitangent: b, normal: n }

-- | Create a TBN frame from normal and tangent
-- |
-- | Bitangent is computed as cross(normal, tangent).
tbnFromNormalTangent :: Normal -> Tangent -> TBNFrame
tbnFromNormalTangent n@(Normal nv) t@(Tangent tv) =
  let bv = crossVec3 nv tv
      b = Bitangent (normalizeVec3 bv)
  in TBNFrame { tangent: t, bitangent: b, normal: n }

-- | Get the TBN matrix as column vectors (for shader use)
-- |
-- | Returns (T, B, N) as a tuple of Vec3s.
-- | Multiply by this matrix to transform from tangent space to world space.
tbnMatrix :: TBNFrame -> { t :: Vec3 Number, b :: Vec3 Number, n :: Vec3 Number }
tbnMatrix (TBNFrame f) =
  { t: tangentVec f.tangent
  , b: bitangentVec f.bitangent
  , n: normalVec f.normal
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transform a vector from world space to tangent space
-- |
-- | Used for normal mapping: transform light direction to tangent space.
transformToTangentSpace :: TBNFrame -> Vec3 Number -> Vec3 Number
transformToTangentSpace (TBNFrame f) (Vec3 x y z) =
  let t = tangentVec f.tangent
      b = bitangentVec f.bitangent
      n = normalVec f.normal
      -- Dot product with each basis vector
      x' = dotVec3 (vec3 x y z) t
      y' = dotVec3 (vec3 x y z) b
      z' = dotVec3 (vec3 x y z) n
  in vec3 x' y' z'

-- | Transform a vector from tangent space to world space
-- |
-- | Used for normal mapping: transform normal map sample to world space.
transformFromTangentSpace :: TBNFrame -> Vec3 Number -> Vec3 Number
transformFromTangentSpace (TBNFrame f) (Vec3 tx ty tz) =
  let t = tangentVec f.tangent
      b = bitangentVec f.bitangent
      n = normalVec f.normal
      -- Linear combination of basis vectors
      Vec3 tx' ty' tz' = scaleVec3 tx t
      Vec3 bx by bz = scaleVec3 ty b
      Vec3 nx ny nz = scaleVec3 tz n
  in vec3 (tx' + bx + nx) (ty' + by + ny) (tz' + bz + nz)

-- | Compute face normal from three vertices (counter-clockwise winding)
-- |
-- | Given triangle vertices p0, p1, p2, computes the normal as:
-- | normalize(cross(p1 - p0, p2 - p0))
faceNormal :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Maybe Normal
faceNormal p0 p1 p2 =
  let edge1 = subtractVec3 p1 p0
      edge2 = subtractVec3 p2 p0
      n = crossVec3 edge1 edge2
  in normal n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a vector is approximately unit length
isUnitLength :: Vec3 Number -> Boolean
isUnitLength v =
  let len = lengthVec3 v
  in len > 0.999 && len < 1.001

-- | Check if two vectors are approximately orthogonal
isOrthogonal :: Vec3 Number -> Vec3 Number -> Boolean
isOrthogonal a b =
  let d = dotVec3 a b
  in d > -0.001 && d < 0.001
