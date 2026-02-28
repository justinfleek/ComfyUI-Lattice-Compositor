-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // scene3d // mesh
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh3D — Geometry primitive definitions.
-- |
-- | ## Categories
-- | - **Basic**: Box, Sphere, Cylinder, Cone, Plane
-- | - **Parametric**: Torus, TorusKnot, Ring, Circle, Capsule
-- | - **Platonic Solids**: Icosahedron, Octahedron, Tetrahedron, Dodecahedron
-- | - **Procedural**: Lathe (revolution), Extrude (along path)
-- | - **Custom**: BufferGeometry (arbitrary vertex data)
-- |
-- | ## Proof Reference
-- | Primitive geometry: `proofs/Hydrogen/Geometry/Primitives.lean`

module Hydrogen.GPU.Scene3D.Mesh
  ( -- * Mesh3D
    Mesh3D
      ( BoxMesh3D
      , SphereMesh3D
      , CylinderMesh3D
      , ConeMesh3D
      , PlaneMesh3D
      , TorusMesh3D
      , TorusKnotMesh3D
      , RingMesh3D
      , CircleMesh3D
      , CapsuleMesh3D
      , IcosahedronMesh3D
      , OctahedronMesh3D
      , TetrahedronMesh3D
      , DodecahedronMesh3D
      , LatheMesh3D
      , ExtrudeMesh3D
      , BufferGeometry3D
      )
  
  -- * Basic Primitives
  , BoxMeshParams
  , boxMesh3D
  , SphereMeshParams
  , sphereMesh3D
  , CylinderMeshParams
  , cylinderMesh3D
  , ConeMeshParams
  , coneMesh3D
  , PlaneMeshParams
  , planeMesh3D
  
  -- * Parametric Primitives
  , TorusMeshParams
  , torusMesh3D
  , TorusKnotMeshParams
  , torusKnotMesh3D
  , RingMeshParams
  , ringMesh3D
  , CircleMeshParams
  , circleMesh3D
  , CapsuleMeshParams
  , capsuleMesh3D
  
  -- * Platonic Solids
  , IcosahedronMeshParams
  , icosahedronMesh3D
  , OctahedronMeshParams
  , octahedronMesh3D
  , TetrahedronMeshParams
  , tetrahedronMesh3D
  , DodecahedronMeshParams
  , dodecahedronMesh3D
  
  -- * Procedural
  , LatheMeshParams
  , latheMesh3D
  , Point2DProfile
  , ExtrudeMeshParams
  , extrudeMesh3D
  , Shape2D
  
  -- * Buffer Geometry (Raw)
  , BufferGeometryParams
  , bufferGeometry3D
  , VertexAttribute
      ( PositionAttr
      , NormalAttr
      , UVAttr
      , ColorAttr
      , TangentAttr
      , CustomAttr
      )
  , AttributeData
  , IndexData
  , DrawGroup
  
  -- * Mesh Rendering Params
  , MeshParams
  
  -- * Pick ID
  , PickId3D
  , pickId3D
  , unwrapPickId3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)

import Hydrogen.GPU.Scene3D.Position (Position3D)
import Hydrogen.GPU.Scene3D.Material (Material3D)
import Hydrogen.Schema.Dimension.Physical.SI (Meter)
import Hydrogen.Schema.Dimension.Rotation.Quaternion (Quaternion)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3)
import Hydrogen.Schema.Geometry.Angle (Degrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // pick id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for 3D pick buffer hit testing.
-- | When a raycast or click occurs, the pick buffer pixel maps to this ID.
newtype PickId3D = PickId3D Int

derive instance eqPickId3D :: Eq PickId3D
derive instance ordPickId3D :: Ord PickId3D

instance showPickId3D :: Show PickId3D where
  show (PickId3D n) = "PickId3D(" <> show n <> ")"

-- | Create a PickId3D from an Int.
pickId3D :: Int -> PickId3D
pickId3D = PickId3D

-- | Unwrap a PickId3D to its Int value.
unwrapPickId3D :: PickId3D -> Int
unwrapPickId3D (PickId3D n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // meshes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mesh geometry primitives.
data Mesh3D
  = BoxMesh3D BoxMeshParams
  | SphereMesh3D SphereMeshParams
  | CylinderMesh3D CylinderMeshParams
  | ConeMesh3D ConeMeshParams
  | PlaneMesh3D PlaneMeshParams
  | TorusMesh3D TorusMeshParams
  | TorusKnotMesh3D TorusKnotMeshParams
  | RingMesh3D RingMeshParams
  | CircleMesh3D CircleMeshParams
  | CapsuleMesh3D CapsuleMeshParams
  | IcosahedronMesh3D IcosahedronMeshParams
  | OctahedronMesh3D OctahedronMeshParams
  | TetrahedronMesh3D TetrahedronMeshParams
  | DodecahedronMesh3D DodecahedronMeshParams
  | LatheMesh3D LatheMeshParams
  | ExtrudeMesh3D ExtrudeMeshParams
  | BufferGeometry3D BufferGeometryParams

derive instance eqMesh3D :: Eq Mesh3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // basic primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Box (rectangular cuboid) mesh parameters.
type BoxMeshParams =
  { width :: Meter
  , height :: Meter
  , depth :: Meter
  , widthSegments :: Int
  , heightSegments :: Int
  , depthSegments :: Int
  }

boxMesh3D :: BoxMeshParams -> Mesh3D
boxMesh3D = BoxMesh3D

-- | Sphere mesh parameters.
-- |
-- | Phi: horizontal angle (longitude), 0 to 2π for full sphere
-- | Theta: vertical angle (latitude), 0 to π for full sphere
type SphereMeshParams =
  { radius :: Meter
  , widthSegments :: Int      -- Longitude divisions (min 3)
  , heightSegments :: Int     -- Latitude divisions (min 2)
  , phiStart :: Degrees       -- Horizontal start angle (default 0)
  , phiLength :: Degrees      -- Horizontal sweep (default 360)
  , thetaStart :: Degrees     -- Vertical start angle (default 0)
  , thetaLength :: Degrees    -- Vertical sweep (default 180)
  }

sphereMesh3D :: SphereMeshParams -> Mesh3D
sphereMesh3D = SphereMesh3D

-- | Cylinder mesh parameters.
-- |
-- | Theta controls the arc of the cylinder (360 for full cylinder).
type CylinderMeshParams =
  { radiusTop :: Meter
  , radiusBottom :: Meter
  , height :: Meter
  , radialSegments :: Int
  , heightSegments :: Int
  , openEnded :: Boolean
  , thetaStart :: Degrees     -- Start angle (default 0)
  , thetaLength :: Degrees    -- Arc sweep (default 360)
  }

cylinderMesh3D :: CylinderMeshParams -> Mesh3D
cylinderMesh3D = CylinderMesh3D

-- | Cone mesh parameters.
-- |
-- | A cone is a cylinder with zero top radius.
-- | Theta controls the arc of the base (360 for full cone).
type ConeMeshParams =
  { radius :: Meter
  , height :: Meter
  , radialSegments :: Int
  , heightSegments :: Int
  , openEnded :: Boolean
  , thetaStart :: Degrees     -- Start angle (default 0)
  , thetaLength :: Degrees    -- Arc sweep (default 360)
  }

coneMesh3D :: ConeMeshParams -> Mesh3D
coneMesh3D = ConeMesh3D

-- | Plane mesh parameters.
type PlaneMeshParams =
  { width :: Meter
  , height :: Meter
  , widthSegments :: Int
  , heightSegments :: Int
  }

planeMesh3D :: PlaneMeshParams -> Mesh3D
planeMesh3D = PlaneMesh3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // parametric primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Torus (donut) mesh parameters.
type TorusMeshParams =
  { radius :: Meter           -- Distance from center to tube center
  , tube :: Meter             -- Radius of the tube
  , radialSegments :: Int
  , tubularSegments :: Int
  , arc :: Degrees            -- Arc angle (360 for full torus)
  }

torusMesh3D :: TorusMeshParams -> Mesh3D
torusMesh3D = TorusMesh3D

-- | Torus knot mesh parameters.
-- |
-- | A torus knot lies on the surface of a torus.
-- | The (p,q) parameters define winding: p around axis, q around interior.
-- | Must be coprime for a single-strand knot.
type TorusKnotMeshParams =
  { radius :: Meter           -- Overall size
  , tube :: Meter             -- Tube thickness
  , tubularSegments :: Int    -- Segments along the knot
  , radialSegments :: Int     -- Segments around the tube
  , p :: Int                  -- Winds around axis (default 2)
  , q :: Int                  -- Winds around interior (default 3)
  }

torusKnotMesh3D :: TorusKnotMeshParams -> Mesh3D
torusKnotMesh3D = TorusKnotMesh3D

-- | Ring (annulus) mesh parameters.
type RingMeshParams =
  { innerRadius :: Meter
  , outerRadius :: Meter
  , thetaSegments :: Int      -- Segments around the ring
  , phiSegments :: Int        -- Segments radially
  , thetaStart :: Degrees     -- Start angle
  , thetaLength :: Degrees    -- Arc length
  }

ringMesh3D :: RingMeshParams -> Mesh3D
ringMesh3D = RingMesh3D

-- | Circle mesh parameters (flat disc).
type CircleMeshParams =
  { radius :: Meter
  , segments :: Int           -- Number of segments (min 3)
  , thetaStart :: Degrees
  , thetaLength :: Degrees
  }

circleMesh3D :: CircleMeshParams -> Mesh3D
circleMesh3D = CircleMesh3D

-- | Capsule mesh parameters (cylinder with hemispherical caps).
type CapsuleMeshParams =
  { radius :: Meter
  , length :: Meter           -- Length of cylindrical section
  , capSegments :: Int        -- Segments on each cap
  , radialSegments :: Int
  }

capsuleMesh3D :: CapsuleMeshParams -> Mesh3D
capsuleMesh3D = CapsuleMesh3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // platonic solids
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icosahedron mesh parameters (20-faced regular polyhedron).
-- |
-- | Detail level controls subdivision:
-- | - 0: 20 triangles
-- | - 1: 80 triangles
-- | - 2: 320 triangles
-- | - n: 20 × 4^n triangles
type IcosahedronMeshParams =
  { radius :: Meter
  , detail :: Int             -- Subdivision level (0 = base)
  }

icosahedronMesh3D :: IcosahedronMeshParams -> Mesh3D
icosahedronMesh3D = IcosahedronMesh3D

-- | Octahedron mesh parameters (8-faced regular polyhedron).
type OctahedronMeshParams =
  { radius :: Meter
  , detail :: Int
  }

octahedronMesh3D :: OctahedronMeshParams -> Mesh3D
octahedronMesh3D = OctahedronMesh3D

-- | Tetrahedron mesh parameters (4-faced regular polyhedron).
type TetrahedronMeshParams =
  { radius :: Meter
  , detail :: Int
  }

tetrahedronMesh3D :: TetrahedronMeshParams -> Mesh3D
tetrahedronMesh3D = TetrahedronMesh3D

-- | Dodecahedron mesh parameters (12-faced regular polyhedron).
type DodecahedronMeshParams =
  { radius :: Meter
  , detail :: Int
  }

dodecahedronMesh3D :: DodecahedronMeshParams -> Mesh3D
dodecahedronMesh3D = DodecahedronMesh3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // procedural
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D point for lathe profile (in XY plane, will rotate around Y).
type Point2DProfile =
  { x :: Meter    -- Distance from axis
  , y :: Meter    -- Height
  }

-- | Lathe mesh parameters (surface of revolution).
-- |
-- | Creates geometry by rotating a 2D profile around the Y axis.
type LatheMeshParams =
  { points :: Array Point2DProfile   -- Profile points (x, y)
  , segments :: Int                  -- Segments around axis
  , phiStart :: Degrees              -- Start angle
  , phiLength :: Degrees             -- Revolution arc (360 = full)
  }

latheMesh3D :: LatheMeshParams -> Mesh3D
latheMesh3D = LatheMesh3D

-- | 2D shape definition for extrusion.
-- |
-- | Shapes are defined by an outer contour and optional holes.
type Shape2D =
  { contour :: Array Point2DProfile  -- Outer boundary
  , holes :: Array (Array Point2DProfile)  -- Inner holes
  }

-- | Extrude mesh parameters (2D shape extruded along path).
-- |
-- | Takes a 2D shape and extrudes it in the Z direction, optionally
-- | with beveling.
type ExtrudeMeshParams =
  { shape :: Shape2D                 -- 2D shape to extrude
  , depth :: Meter                   -- Extrusion depth
  , bevelEnabled :: Boolean          -- Enable bevel
  , bevelThickness :: Meter          -- Bevel depth
  , bevelSize :: Meter               -- Bevel width
  , bevelSegments :: Int             -- Bevel detail
  , curveSegments :: Int             -- Segments for curves
  }

extrudeMesh3D :: ExtrudeMeshParams -> Mesh3D
extrudeMesh3D = ExtrudeMesh3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // buffer geometry (raw)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer geometry parameters (arbitrary vertex data).
-- |
-- | For custom geometry not covered by primitives. Provides direct
-- | access to vertex buffers.
type BufferGeometryParams =
  { attributes :: Array VertexAttribute
  , index :: Maybe IndexData
  , groups :: Array DrawGroup
  }

-- | Vertex attribute data.
data VertexAttribute
  = PositionAttr AttributeData    -- vec3: x, y, z positions
  | NormalAttr AttributeData      -- vec3: x, y, z normals
  | UVAttr AttributeData          -- vec2: u, v texture coords
  | ColorAttr AttributeData       -- vec3 or vec4: r, g, b, [a]
  | TangentAttr AttributeData     -- vec4: x, y, z, w tangents
  | CustomAttr String AttributeData  -- named custom attribute

derive instance eqVertexAttribute :: Eq VertexAttribute

-- | Raw attribute data.
-- |
-- | Item size determines how many numbers per vertex:
-- | - 2: vec2 (UV)
-- | - 3: vec3 (position, normal, color)
-- | - 4: vec4 (tangent, RGBA color)
type AttributeData =
  { data_ :: Array Number    -- Flat array of vertex data
  , itemSize :: Int          -- Components per vertex (2, 3, or 4)
  , normalized :: Boolean    -- Normalize integers to 0-1?
  }

-- | Index buffer data for indexed geometry.
type IndexData =
  { indices :: Array Int     -- Triangle indices
  }

-- | Draw group for multi-material geometry.
type DrawGroup =
  { start :: Int             -- First index
  , count :: Int             -- Number of indices
  , materialIndex :: Int     -- Which material to use
  }

bufferGeometry3D :: BufferGeometryParams -> Mesh3D
bufferGeometry3D = BufferGeometry3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // mesh params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full mesh parameters for rendering.
type MeshParams msg =
  { geometry :: Mesh3D
  , material :: Material3D
  , position :: Position3D
  , rotation :: Quaternion
  , scale :: Vec3 Number
  , castShadow :: Boolean
  , receiveShadow :: Boolean
  , pickId :: Maybe PickId3D
  , onClick :: Maybe msg
  , onHover :: Maybe msg
  }
