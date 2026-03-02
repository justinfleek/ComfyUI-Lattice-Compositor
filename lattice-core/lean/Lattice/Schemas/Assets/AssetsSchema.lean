/-
  Lattice.Schemas.Assets.AssetsSchema

  Asset type enums and reference types.

  Source: ui/src/schemas/assets/assets-schema.ts
-/

namespace Lattice.Schemas.Assets.AssetsSchema

--------------------------------------------------------------------------------
-- Asset Type
--------------------------------------------------------------------------------

/-- Asset type options -/
inductive AssetType where
  | depth_map
  | image
  | video
  | audio
  | model
  | pointcloud
  | texture
  | material
  | hdri
  | svg
  | sprite
  | spritesheet
  | lut
  deriving Repr, DecidableEq, Inhabited

def assetTypeFromString : String → Option AssetType
  | "depth_map" => some .depth_map
  | "image" => some .image
  | "video" => some .video
  | "audio" => some .audio
  | "model" => some .model
  | "pointcloud" => some .pointcloud
  | "texture" => some .texture
  | "material" => some .material
  | "hdri" => some .hdri
  | "svg" => some .svg
  | "sprite" => some .sprite
  | "spritesheet" => some .spritesheet
  | "lut" => some .lut
  | _ => Option.none

def assetTypeToString : AssetType → String
  | .depth_map => "depth_map"
  | .image => "image"
  | .video => "video"
  | .audio => "audio"
  | .model => "model"
  | .pointcloud => "pointcloud"
  | .texture => "texture"
  | .material => "material"
  | .hdri => "hdri"
  | .svg => "svg"
  | .sprite => "sprite"
  | .spritesheet => "spritesheet"
  | .lut => "lut"

--------------------------------------------------------------------------------
-- Texture Map Type
--------------------------------------------------------------------------------

/-- Texture map type options -/
inductive TextureMapType where
  | albedo
  | normal
  | roughness
  | metalness
  | ao
  | emissive
  | height
  | opacity
  | specular
  deriving Repr, DecidableEq, Inhabited

def textureMapTypeFromString : String → Option TextureMapType
  | "albedo" => some .albedo
  | "normal" => some .normal
  | "roughness" => some .roughness
  | "metalness" => some .metalness
  | "ao" => some .ao
  | "emissive" => some .emissive
  | "height" => some .height
  | "opacity" => some .opacity
  | "specular" => some .specular
  | _ => Option.none

def textureMapTypeToString : TextureMapType → String
  | .albedo => "albedo"
  | .normal => "normal"
  | .roughness => "roughness"
  | .metalness => "metalness"
  | .ao => "ao"
  | .emissive => "emissive"
  | .height => "height"
  | .opacity => "opacity"
  | .specular => "specular"

--------------------------------------------------------------------------------
-- Model Format
--------------------------------------------------------------------------------

/-- 3D model format options -/
inductive ModelFormat where
  | gltf
  | glb
  | obj
  | fbx
  | usd
  | usda
  | usdc
  | usdz
  deriving Repr, DecidableEq, Inhabited

def modelFormatFromString : String → Option ModelFormat
  | "gltf" => some .gltf
  | "glb" => some .glb
  | "obj" => some .obj
  | "fbx" => some .fbx
  | "usd" => some .usd
  | "usda" => some .usda
  | "usdc" => some .usdc
  | "usdz" => some .usdz
  | _ => Option.none

def modelFormatToString : ModelFormat → String
  | .gltf => "gltf"
  | .glb => "glb"
  | .obj => "obj"
  | .fbx => "fbx"
  | .usd => "usd"
  | .usda => "usda"
  | .usdc => "usdc"
  | .usdz => "usdz"

--------------------------------------------------------------------------------
-- Point Cloud Format
--------------------------------------------------------------------------------

/-- Point cloud format options -/
inductive PointCloudFormat where
  | ply
  | pcd
  | las
  | laz
  | xyz
  | pts
  deriving Repr, DecidableEq, Inhabited

def pointCloudFormatFromString : String → Option PointCloudFormat
  | "ply" => some .ply
  | "pcd" => some .pcd
  | "las" => some .las
  | "laz" => some .laz
  | "xyz" => some .xyz
  | "pts" => some .pts
  | _ => Option.none

def pointCloudFormatToString : PointCloudFormat → String
  | .ply => "ply"
  | .pcd => "pcd"
  | .las => "las"
  | .laz => "laz"
  | .xyz => "xyz"
  | .pts => "pts"

--------------------------------------------------------------------------------
-- Asset Source
--------------------------------------------------------------------------------

/-- Asset source options -/
inductive AssetSource where
  | comfyui_node
  | file
  | generated
  | url
  deriving Repr, DecidableEq, Inhabited

def assetSourceFromString : String → Option AssetSource
  | "comfyui_node" => some .comfyui_node
  | "file" => some .file
  | "generated" => some .generated
  | "url" => some .url
  | _ => Option.none

def assetSourceToString : AssetSource → String
  | .comfyui_node => "comfyui_node"
  | .file => "file"
  | .generated => "generated"
  | .url => "url"

--------------------------------------------------------------------------------
-- Texture Color Space
--------------------------------------------------------------------------------

/-- Texture color space options -/
inductive TextureColorSpace where
  | srgb
  | linear
  deriving Repr, DecidableEq, Inhabited

def textureColorSpaceFromString : String → Option TextureColorSpace
  | "srgb" => some .srgb
  | "linear" => some .linear
  | _ => Option.none

def textureColorSpaceToString : TextureColorSpace → String
  | .srgb => "srgb"
  | .linear => "linear"

--------------------------------------------------------------------------------
-- Data Asset Type
--------------------------------------------------------------------------------

/-- Data asset type options -/
inductive DataAssetType where
  | json
  | csv
  | tsv
  | mgjson
  deriving Repr, DecidableEq, Inhabited

def dataAssetTypeFromString : String → Option DataAssetType
  | "json" => some .json
  | "csv" => some .csv
  | "tsv" => some .tsv
  | "mgjson" => some .mgjson
  | _ => Option.none

def dataAssetTypeToString : DataAssetType → String
  | .json => "json"
  | .csv => "csv"
  | .tsv => "tsv"
  | .mgjson => "mgjson"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- SVG viewbox -/
structure SVGViewBox where
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_DIMENSION : Nat := 16384
def MAX_FRAME_COUNT : Nat := 100000
def MAX_DURATION : Float := 86400.0  -- 24 hours
def MAX_FPS : Float := 120.0
def MAX_SAMPLE_RATE : Nat := 192000
def MAX_MESH_COUNT : Nat := 100000
def MAX_VERTEX_COUNT : Nat := 10000000
def MAX_POINT_COUNT : Nat := 100000000
def MAX_SPRITE_COLS : Nat := 1000
def MAX_SPRITE_ROWS : Nat := 1000
def MAX_SPRITE_COUNT : Nat := 1000000
def MAX_SVG_PATHS : Nat := 100000
def MAX_HDRI_EXPOSURE : Float := 10.0
def MIN_HDRI_EXPOSURE : Float := (-10.0)

end Lattice.Schemas.Assets.AssetsSchema
