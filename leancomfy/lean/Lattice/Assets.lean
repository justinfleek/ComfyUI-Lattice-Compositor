/-
  Lattice.Assets - Asset types and references

  Max 500 lines.

  Source: ui/src/types/assets.ts (157 lines)
-/

import Lattice.Primitives

namespace Lattice.Assets

open Lattice.Primitives

/-! ## Asset Type -/

/-- Asset types supported by the compositor -/
inductive AssetType where
  | depthMap     -- Depth map image
  | image        -- Standard image (PNG, JPG, WebP)
  | video        -- Video file (MP4, WebM)
  | audio        -- Audio file (MP3, WAV, OGG)
  | model        -- 3D model (GLTF, OBJ, FBX, USD)
  | pointcloud   -- Point cloud (PLY, PCD, LAS)
  | texture      -- PBR texture map
  | material     -- Material definition
  | hdri         -- Environment map (HDR, EXR)
  | svg          -- Vector graphic (for extrusion)
  | sprite       -- Single image for particles
  | spritesheet  -- Sprite sheet (grid of frames)
  | lut          -- Color lookup table
  deriving Repr, BEq, DecidableEq

/-! ## Texture Map Type -/

/-- PBR texture map types -/
inductive TextureMapType where
  | albedo       -- Base color / diffuse
  | normal       -- Normal map
  | roughness    -- Roughness map
  | metalness    -- Metalness map
  | ao           -- Ambient occlusion
  | emissive     -- Emissive map
  | height       -- Height/displacement
  | opacity      -- Alpha/opacity
  | specular     -- Specular (non-PBR)
  deriving Repr, BEq, DecidableEq

/-! ## Model Format -/

/-- 3D model formats -/
inductive ModelFormat where
  | gltf | glb | obj | fbx | usd | usda | usdc | usdz
  deriving Repr, BEq, DecidableEq

/-! ## Point Cloud Format -/

/-- Point cloud formats -/
inductive PointCloudFormat where
  | ply | pcd | las | laz | xyz | pts
  deriving Repr, BEq, DecidableEq

/-! ## Texture Color Space -/

/-- Texture color space -/
inductive TextureColorSpace where
  | srgb | linear
  deriving Repr, BEq, DecidableEq

/-! ## Asset Source -/

/-- Source of asset -/
inductive AssetSource where
  | comfyuiNode
  | file
  | generated
  | url
  deriving Repr, BEq, DecidableEq

/-! ## Model Bounding Box -/

/-- 3D bounding box -/
structure ModelBoundingBox where
  minX : Float
  minY : Float
  minZ : Float
  maxX : Float
  maxY : Float
  maxZ : Float
  centerX : Float
  centerY : Float
  centerZ : Float
  sizeX : Float
  sizeY : Float
  sizeZ : Float
  all_finite : minX.isFinite ∧ minY.isFinite ∧ minZ.isFinite ∧
               maxX.isFinite ∧ maxY.isFinite ∧ maxZ.isFinite ∧
               centerX.isFinite ∧ centerY.isFinite ∧ centerZ.isFinite ∧
               sizeX.isFinite ∧ sizeY.isFinite ∧ sizeZ.isFinite
  deriving Repr

/-! ## SVG View Box -/

/-- SVG view box -/
structure SvgViewBox where
  x : Float
  y : Float
  width : Float
  height : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  width_positive : width > 0
  width_finite : width.isFinite
  height_positive : height > 0
  height_finite : height.isFinite
  deriving Repr

/-! ## Sprite Validation -/

/-- Sprite validation metadata -/
structure SpriteValidation where
  isPowerOfTwo : Bool
  hasAlpha : Bool
  originalFormat : NonEmptyString
  warnings : Array String
  deriving Repr

/-! ## Material Maps -/

/-- Material texture map references (asset IDs) -/
structure MaterialMaps where
  albedo : Option NonEmptyString
  normal : Option NonEmptyString
  roughness : Option NonEmptyString
  metalness : Option NonEmptyString
  ao : Option NonEmptyString
  emissive : Option NonEmptyString
  height : Option NonEmptyString
  opacity : Option NonEmptyString
  deriving Repr

/-! ## Asset Reference -/

/-- Asset reference with metadata -/
structure AssetReference where
  id : NonEmptyString
  assetType : AssetType
  source : AssetSource
  nodeId : Option NonEmptyString
  width : Nat
  height : Nat
  data : String                      -- Base64 or URL
  filename : Option NonEmptyString
  -- Video/Audio metadata
  frameCount : Option Nat
  duration : Option Float            -- Seconds
  fps : Option Float                 -- Source FPS
  hasAudio : Option Bool
  audioChannels : Option Nat         -- 1=mono, 2=stereo
  sampleRate : Option Nat
  -- 3D Model metadata
  modelFormat : Option ModelFormat
  modelBoundingBox : Option ModelBoundingBox
  modelAnimations : Array String     -- Animation clip names
  modelMeshCount : Option Nat
  modelVertexCount : Option Nat
  -- Point cloud metadata
  pointCloudFormat : Option PointCloudFormat
  pointCount : Option Nat
  -- Texture metadata
  textureMapType : Option TextureMapType
  textureColorSpace : Option TextureColorSpace
  -- Material definition
  materialMaps : Option MaterialMaps
  -- HDRI metadata
  hdriExposure : Option Float
  hdriRotation : Option Float
  -- SVG metadata
  svgPaths : Option Nat
  svgViewBox : Option SvgViewBox
  -- Sprite sheet metadata
  spriteColumns : Option Nat
  spriteRows : Option Nat
  spriteCount : Option Nat
  spriteFrameRate : Option Float
  spriteValidation : Option SpriteValidation
  -- Proofs
  width_positive : width > 0
  height_positive : height > 0
  deriving Repr

/-! ## Data Asset -/

/-- Data asset type -/
inductive DataAssetType where
  | json | csv | tsv | mgjson
  deriving Repr, BEq, DecidableEq

/-- Data asset reference for expressions -/
structure DataAssetReference where
  id : NonEmptyString
  name : NonEmptyString              -- Original filename
  dataType : DataAssetType
  rawContent : String
  lastModified : Nat                 -- Timestamp
  -- For CSV/TSV
  headers : Array String
  rows : Array (Array String)
  numRows : Option Nat
  numColumns : Option Nat
  deriving Repr

end Lattice.Assets
