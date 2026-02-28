-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // spatial // geometry // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geometry Types — Abstract 3D geometry data structures.
-- |
-- | ## Mesh
-- | Raw vertex buffer geometry. Vertices, indices, normals, UVs.
-- |
-- | ## SkinnedMesh
-- | Mesh with skeletal animation support. Bones and vertex weights.
-- |
-- | ## InstancedMesh
-- | Single mesh rendered many times with different transforms.
-- | Efficient for forests, crowds, particle systems.
-- |
-- | ## PointCloud
-- | Discrete points without connectivity. LiDAR, photogrammetry.
-- |
-- | ## Line3D
-- | 3D polyline. Edges, wireframes, trajectories.
-- |
-- | ## Sprite3D
-- | Billboard quad that always faces camera. Particles, impostors.

module Hydrogen.Schema.Spatial.Geometry.Types
  ( -- * Mesh Data
    VertexBuffer(..)
  , IndexBuffer(..)
  , MeshData(..)
  
  -- * Skinning
  , BoneIndex
  , boneIndex
  , BoneWeight
  , boneWeight
  , SkinWeight(..)
  , Bone(..)
  , Skeleton(..)
  , SkinnedMesh(..)
  
  -- * Instancing
  , InstanceData(..)
  , InstancedMesh(..)
  
  -- * Point Cloud
  , PointCloudData(..)
  , PointCloud(..)
  
  -- * Lines
  , LineVertex(..)
  , Line3D(..)
  , LineStyle(..)
  
  -- * Sprites
  , Sprite3D(..)
  , SpriteAlignment(..)
  
  -- * Unified Geometry
  , Geometry(..)
  
  -- * Constructors
  , meshData
  , skinnedMesh
  , instancedMesh
  , pointCloud
  , line3D
  , sprite3D
  
  -- * Accessors
  , vertexCount
  , triangleCount
  , hasNormals
  , hasUVs
  ) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // mesh data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertex buffer (positions as flat array of floats)
-- |
-- | Every 3 consecutive numbers form one vertex position (x, y, z).
newtype VertexBuffer = VertexBuffer (Array Number)

derive instance eqVertexBuffer :: Eq VertexBuffer

instance showVertexBuffer :: Show VertexBuffer where
  show (VertexBuffer arr) = "VertexBuffer[" <> show (length arr / 3) <> " vertices]"

-- | Index buffer (triangle indices)
-- |
-- | Every 3 consecutive integers form one triangle.
newtype IndexBuffer = IndexBuffer (Array Int)

derive instance eqIndexBuffer :: Eq IndexBuffer

instance showIndexBuffer :: Show IndexBuffer where
  show (IndexBuffer arr) = "IndexBuffer[" <> show (length arr / 3) <> " triangles]"

-- | Complete mesh data
-- |
-- | Contains all vertex attributes needed for rendering.
newtype MeshData = MeshData
  { positions :: VertexBuffer       -- ^ Vertex positions (required)
  , normals :: Maybe VertexBuffer   -- ^ Vertex normals (for lighting)
  , uvs :: Maybe (Array Number)     -- ^ Texture coordinates (2 per vertex)
  , tangents :: Maybe VertexBuffer  -- ^ Tangent vectors (for normal mapping)
  , colors :: Maybe (Array Number)  -- ^ Vertex colors (4 per vertex: RGBA)
  , indices :: Maybe IndexBuffer    -- ^ Triangle indices (or draw order)
  }

derive instance eqMeshData :: Eq MeshData

instance showMeshData :: Show MeshData where
  show (MeshData m) =
    "MeshData { vertices: " <> show (vertexCountFromBuffer m.positions) <>
    ", indexed: " <> show (hasIndices m.indices) <> " }"
    where
    vertexCountFromBuffer (VertexBuffer arr) = length arr / 3
    hasIndices Nothing = false
    hasIndices (Just _) = true

-- | Create mesh data from positions only
meshData :: VertexBuffer -> MeshData
meshData positions = MeshData
  { positions
  , normals: Nothing
  , uvs: Nothing
  , tangents: Nothing
  , colors: Nothing
  , indices: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // skinning
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bone index (into skeleton's bone array)
newtype BoneIndex = BoneIndex Int

derive instance eqBoneIndex :: Eq BoneIndex
derive instance ordBoneIndex :: Ord BoneIndex

instance showBoneIndex :: Show BoneIndex where
  show (BoneIndex i) = "Bone#" <> show i

-- | Create a bone index (clamped to non-negative)
boneIndex :: Int -> BoneIndex
boneIndex i = BoneIndex (if i < 0 then 0 else i)

-- | Bone weight (0-1)
newtype BoneWeight = BoneWeight Number

derive instance eqBoneWeight :: Eq BoneWeight
derive instance ordBoneWeight :: Ord BoneWeight

instance showBoneWeight :: Show BoneWeight where
  show (BoneWeight w) = show w

-- | Create a bone weight (clamped to 0-1)
boneWeight :: Number -> BoneWeight
boneWeight w
  | w < 0.0 = BoneWeight 0.0
  | w > 1.0 = BoneWeight 1.0
  | otherwise = BoneWeight w

-- | Skin weight for a single vertex
-- |
-- | Up to 4 bones can influence each vertex (standard GPU skinning).
-- | Weights should sum to 1.0 for normalized skinning.
type SkinWeight =
  { bone0 :: BoneIndex, weight0 :: BoneWeight
  , bone1 :: BoneIndex, weight1 :: BoneWeight
  , bone2 :: BoneIndex, weight2 :: BoneWeight
  , bone3 :: BoneIndex, weight3 :: BoneWeight
  }

-- | A bone in a skeleton
-- |
-- | Defines local transform and parent relationship.
newtype Bone = Bone
  { name :: String
  , parent :: Maybe BoneIndex       -- ^ Parent bone (Nothing for root)
  , position :: Vec3 Number         -- ^ Local position
  , rotation :: Vec3 Number         -- ^ Local rotation (Euler XYZ)
  , scale :: Vec3 Number            -- ^ Local scale
  , bindPose :: Array Number        -- ^ 4x4 inverse bind matrix (16 floats)
  }

derive instance eqBone :: Eq Bone

instance showBone :: Show Bone where
  show (Bone b) = "Bone { name: " <> show b.name <> " }"

-- | Skeleton (hierarchy of bones)
newtype Skeleton = Skeleton
  { bones :: Array Bone
  , rootBones :: Array BoneIndex    -- ^ Bones with no parent
  }

derive instance eqSkeleton :: Eq Skeleton

instance showSkeleton :: Show Skeleton where
  show (Skeleton s) = "Skeleton[" <> show (length s.bones) <> " bones]"

-- | Skinned mesh (mesh + skeleton + weights)
newtype SkinnedMesh = SkinnedMesh
  { mesh :: MeshData
  , skeleton :: Skeleton
  , weights :: Array SkinWeight     -- ^ One per vertex
  }

derive instance eqSkinnedMesh :: Eq SkinnedMesh

instance showSkinnedMesh :: Show SkinnedMesh where
  show (SkinnedMesh s) =
    "SkinnedMesh { mesh: " <> show s.mesh <>
    ", skeleton: " <> show s.skeleton <> " }"

-- | Create a skinned mesh
skinnedMesh :: MeshData -> Skeleton -> Array SkinWeight -> SkinnedMesh
skinnedMesh mesh skeleton weights = SkinnedMesh { mesh, skeleton, weights }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // instancing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-instance data
-- |
-- | Each instance has its own transform and optional color/ID.
type InstanceData =
  { position :: Vec3 Number
  , rotation :: Vec3 Number         -- ^ Euler XYZ
  , scale :: Vec3 Number
  , color :: Maybe (Vec3 Number)    -- ^ Instance color tint
  , instanceId :: Int               -- ^ For picking/selection
  }

-- | Instanced mesh (single geometry, many transforms)
-- |
-- | Efficient for rendering many identical objects.
newtype InstancedMesh = InstancedMesh
  { mesh :: MeshData
  , instances :: Array InstanceData
  }

derive instance eqInstancedMesh :: Eq InstancedMesh

instance showInstancedMesh :: Show InstancedMesh where
  show (InstancedMesh im) =
    "InstancedMesh[" <> show (length im.instances) <> " instances]"

-- | Create an instanced mesh
instancedMesh :: MeshData -> Array InstanceData -> InstancedMesh
instancedMesh mesh instances = InstancedMesh { mesh, instances }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // point cloud
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point cloud data
-- |
-- | Arrays must have matching lengths (one entry per point).
type PointCloudData =
  { positions :: Array (Vec3 Number)
  , colors :: Maybe (Array (Vec3 Number))   -- ^ Per-point RGB
  , intensities :: Maybe (Array Number)     -- ^ LiDAR intensity
  , normals :: Maybe (Array (Vec3 Number))  -- ^ Estimated normals
  }

-- | Point cloud geometry
newtype PointCloud = PointCloud
  { data :: PointCloudData
  , pointSize :: Number             -- ^ Render size (screen pixels or meters)
  , sizeAttenuation :: Boolean      -- ^ Scale with distance?
  }

derive instance eqPointCloud :: Eq PointCloud

instance showPointCloud :: Show PointCloud where
  show (PointCloud pc) =
    "PointCloud[" <> show (length pc.data.positions) <> " points]"

-- | Create a point cloud
pointCloud :: Array (Vec3 Number) -> Number -> PointCloud
pointCloud positions pointSize = PointCloud
  { data:
      { positions
      , colors: Nothing
      , intensities: Nothing
      , normals: Nothing
      }
  , pointSize
  , sizeAttenuation: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // line3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line vertex with optional color
type LineVertex =
  { position :: Vec3 Number
  , color :: Maybe (Vec3 Number)
  }

-- | Line rendering style
data LineStyle
  = LineSolid              -- ^ Continuous line
  | LineDashed             -- ^ Dashed pattern
  | LineDotted             -- ^ Dotted pattern

derive instance eqLineStyle :: Eq LineStyle
derive instance ordLineStyle :: Ord LineStyle

instance showLineStyle :: Show LineStyle where
  show LineSolid = "Solid"
  show LineDashed = "Dashed"
  show LineDotted = "Dotted"

-- | 3D polyline
newtype Line3D = Line3D
  { vertices :: Array LineVertex
  , width :: Number                 -- ^ Line width (pixels or meters)
  , style :: LineStyle
  , closed :: Boolean               -- ^ Connect last to first?
  }

derive instance eqLine3D :: Eq Line3D

instance showLine3D :: Show Line3D where
  show (Line3D l) =
    "Line3D[" <> show (length l.vertices) <> " vertices, " <> show l.style <> "]"

-- | Create a line from positions
line3D :: Array (Vec3 Number) -> Number -> Line3D
line3D positions width = Line3D
  { vertices: map (\p -> { position: p, color: Nothing }) positions
  , width
  , style: LineSolid
  , closed: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // sprite3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sprite alignment mode
data SpriteAlignment
  = AlignCamera           -- ^ Always face camera (billboard)
  | AlignCameraY          -- ^ Face camera but stay vertical
  | AlignWorld            -- ^ Fixed world orientation

derive instance eqSpriteAlignment :: Eq SpriteAlignment
derive instance ordSpriteAlignment :: Ord SpriteAlignment

instance showSpriteAlignment :: Show SpriteAlignment where
  show AlignCamera = "Camera"
  show AlignCameraY = "CameraY"
  show AlignWorld = "World"

-- | 3D sprite (billboard quad)
newtype Sprite3D = Sprite3D
  { position :: Vec3 Number
  , size :: { width :: Number, height :: Number }
  , alignment :: SpriteAlignment
  , color :: Vec3 Number            -- ^ Tint color
  , opacity :: Number               -- ^ 0-1
  , textureRegion :: Maybe { u :: Number, v :: Number, w :: Number, h :: Number }
  }

derive instance eqSprite3D :: Eq Sprite3D

instance showSprite3D :: Show Sprite3D where
  show (Sprite3D s) =
    "Sprite3D { position: " <> show s.position <>
    ", size: " <> show s.size.width <> "x" <> show s.size.height <> " }"

-- | Create a sprite
sprite3D :: Vec3 Number -> Number -> Number -> Sprite3D
sprite3D position width height = Sprite3D
  { position
  , size: { width, height }
  , alignment: AlignCamera
  , color: vec3 1.0 1.0 1.0
  , opacity: 1.0
  , textureRegion: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // unified geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified geometry type
data Geometry
  = GeoMesh MeshData
  | GeoSkinned SkinnedMesh
  | GeoInstanced InstancedMesh
  | GeoPoints PointCloud
  | GeoLine Line3D
  | GeoSprite Sprite3D

derive instance eqGeometry :: Eq Geometry

instance showGeometry :: Show Geometry where
  show (GeoMesh m) = show m
  show (GeoSkinned s) = show s
  show (GeoInstanced i) = show i
  show (GeoPoints p) = show p
  show (GeoLine l) = show l
  show (GeoSprite s) = show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get vertex count for any geometry
vertexCount :: Geometry -> Int
vertexCount (GeoMesh (MeshData m)) = bufferVertexCount m.positions
vertexCount (GeoSkinned (SkinnedMesh s)) = bufferVertexCount (getMeshPositions s.mesh)
vertexCount (GeoInstanced (InstancedMesh im)) = bufferVertexCount (getMeshPositions im.mesh)
vertexCount (GeoPoints (PointCloud pc)) = length pc.data.positions
vertexCount (GeoLine (Line3D l)) = length l.vertices
vertexCount (GeoSprite _) = 4  -- Quad

-- | Get triangle count (0 for non-triangle geometry)
triangleCount :: Geometry -> Int
triangleCount (GeoMesh (MeshData m)) = indexTriangleCount m.indices m.positions
triangleCount (GeoSkinned (SkinnedMesh s)) =
  let (MeshData m) = s.mesh
  in indexTriangleCount m.indices m.positions
triangleCount (GeoInstanced (InstancedMesh im)) =
  let (MeshData m) = im.mesh
      baseTriangles = indexTriangleCount m.indices m.positions
  in baseTriangles * length im.instances
triangleCount (GeoPoints _) = 0
triangleCount (GeoLine _) = 0
triangleCount (GeoSprite _) = 2  -- Quad = 2 triangles

-- | Check if geometry has normals
hasNormals :: Geometry -> Boolean
hasNormals (GeoMesh (MeshData m)) = hasValue m.normals
hasNormals (GeoSkinned (SkinnedMesh s)) =
  let (MeshData m) = s.mesh in hasValue m.normals
hasNormals (GeoInstanced (InstancedMesh im)) =
  let (MeshData m) = im.mesh in hasValue m.normals
hasNormals (GeoPoints (PointCloud pc)) = hasValue pc.data.normals
hasNormals (GeoLine _) = false
hasNormals (GeoSprite _) = true  -- Implicit face normal

-- | Check if geometry has UVs
hasUVs :: Geometry -> Boolean
hasUVs (GeoMesh (MeshData m)) = hasValue m.uvs
hasUVs (GeoSkinned (SkinnedMesh s)) =
  let (MeshData m) = s.mesh in hasValue m.uvs
hasUVs (GeoInstanced (InstancedMesh im)) =
  let (MeshData m) = im.mesh in hasValue m.uvs
hasUVs (GeoPoints _) = false
hasUVs (GeoLine _) = false
hasUVs (GeoSprite _) = true  -- Implicit quad UVs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

bufferVertexCount :: VertexBuffer -> Int
bufferVertexCount (VertexBuffer arr) = length arr / 3

getMeshPositions :: MeshData -> VertexBuffer
getMeshPositions (MeshData m) = m.positions

indexTriangleCount :: Maybe IndexBuffer -> VertexBuffer -> Int
indexTriangleCount (Just (IndexBuffer idx)) _ = length idx / 3
indexTriangleCount Nothing positions = bufferVertexCount positions / 3

hasValue :: forall a. Maybe a -> Boolean
hasValue (Just _) = true
hasValue Nothing = false
