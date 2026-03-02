/-
  Lattice.Schemas.Project.ProjectSchema - Project-level enums

  Project, composition, and asset type enums.

  Source: ui/src/schemas/project-schema.ts
-/

namespace Lattice.Schemas.Project.ProjectSchema

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def projectVersion : String := "1.0.0"
def maxDimension : Nat := 16384
def maxFps : Nat := 120
def maxFrameCount : Nat := 100000

--------------------------------------------------------------------------------
-- Color Settings
--------------------------------------------------------------------------------

/-- Working color spaces -/
inductive ColorSpace where
  | sRGB
  | linearSRGB
  | wideGamutRGB
  | displayP3
  | proPhotoRGB
  | ACEScg
  | rec709
  | rec2020
  deriving Repr, DecidableEq, Inhabited

def ColorSpace.fromString : String → Option ColorSpace
  | "sRGB" => some ColorSpace.sRGB
  | "linear-sRGB" => some ColorSpace.linearSRGB
  | "Wide-Gamut-RGB" => some ColorSpace.wideGamutRGB
  | "Display-P3" => some ColorSpace.displayP3
  | "ProPhoto-RGB" => some ColorSpace.proPhotoRGB
  | "ACEScg" => some ColorSpace.ACEScg
  | "Rec709" => some ColorSpace.rec709
  | "Rec2020" => some ColorSpace.rec2020
  | _ => none

def ColorSpace.toString : ColorSpace → String
  | ColorSpace.sRGB => "sRGB"
  | ColorSpace.linearSRGB => "linear-sRGB"
  | ColorSpace.wideGamutRGB => "Wide-Gamut-RGB"
  | ColorSpace.displayP3 => "Display-P3"
  | ColorSpace.proPhotoRGB => "ProPhoto-RGB"
  | ColorSpace.ACEScg => "ACEScg"
  | ColorSpace.rec709 => "Rec709"
  | ColorSpace.rec2020 => "Rec2020"

/-- View transforms -/
inductive ViewTransform where
  | sRGB
  | displayP3
  | rec709
  | ACESsRGB
  | filmic
  deriving Repr, DecidableEq, Inhabited

def ViewTransform.fromString : String → Option ViewTransform
  | "sRGB" => some ViewTransform.sRGB
  | "Display-P3" => some ViewTransform.displayP3
  | "Rec709" => some ViewTransform.rec709
  | "ACES-sRGB" => some ViewTransform.ACESsRGB
  | "Filmic" => some ViewTransform.filmic
  | _ => none

def ViewTransform.toString : ViewTransform → String
  | ViewTransform.sRGB => "sRGB"
  | ViewTransform.displayP3 => "Display-P3"
  | ViewTransform.rec709 => "Rec709"
  | ViewTransform.ACESsRGB => "ACES-sRGB"
  | ViewTransform.filmic => "Filmic"

--------------------------------------------------------------------------------
-- Workflow Types
--------------------------------------------------------------------------------

/-- Workflow input types -/
inductive WorkflowInputType where
  | image
  | video
  | latent
  | mask
  | number
  | string_
  deriving Repr, DecidableEq, Inhabited

def WorkflowInputType.fromString : String → Option WorkflowInputType
  | "image" => some WorkflowInputType.image
  | "video" => some WorkflowInputType.video
  | "latent" => some WorkflowInputType.latent
  | "mask" => some WorkflowInputType.mask
  | "number" => some WorkflowInputType.number
  | "string" => some WorkflowInputType.string_
  | _ => none

def WorkflowInputType.toString : WorkflowInputType → String
  | WorkflowInputType.image => "image"
  | WorkflowInputType.video => "video"
  | WorkflowInputType.latent => "latent"
  | WorkflowInputType.mask => "mask"
  | WorkflowInputType.number => "number"
  | WorkflowInputType.string_ => "string"

/-- Workflow output types -/
inductive WorkflowOutputType where
  | image
  | video
  | latent
  deriving Repr, DecidableEq, Inhabited

def WorkflowOutputType.fromString : String → Option WorkflowOutputType
  | "image" => some WorkflowOutputType.image
  | "video" => some WorkflowOutputType.video
  | "latent" => some WorkflowOutputType.latent
  | _ => none

def WorkflowOutputType.toString : WorkflowOutputType → String
  | WorkflowOutputType.image => "image"
  | WorkflowOutputType.video => "video"
  | WorkflowOutputType.latent => "latent"

--------------------------------------------------------------------------------
-- Asset Types
--------------------------------------------------------------------------------

/-- Asset types -/
inductive AssetType where
  | depthMap
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

def AssetType.fromString : String → Option AssetType
  | "depth_map" => some AssetType.depthMap
  | "image" => some AssetType.image
  | "video" => some AssetType.video
  | "audio" => some AssetType.audio
  | "model" => some AssetType.model
  | "pointcloud" => some AssetType.pointcloud
  | "texture" => some AssetType.texture
  | "material" => some AssetType.material
  | "hdri" => some AssetType.hdri
  | "svg" => some AssetType.svg
  | "sprite" => some AssetType.sprite
  | "spritesheet" => some AssetType.spritesheet
  | "lut" => some AssetType.lut
  | _ => none

def AssetType.toString : AssetType → String
  | AssetType.depthMap => "depth_map"
  | AssetType.image => "image"
  | AssetType.video => "video"
  | AssetType.audio => "audio"
  | AssetType.model => "model"
  | AssetType.pointcloud => "pointcloud"
  | AssetType.texture => "texture"
  | AssetType.material => "material"
  | AssetType.hdri => "hdri"
  | AssetType.svg => "svg"
  | AssetType.sprite => "sprite"
  | AssetType.spritesheet => "spritesheet"
  | AssetType.lut => "lut"

/-- Asset sources -/
inductive AssetSource where
  | comfyuiNode
  | file
  | generated
  | url
  deriving Repr, DecidableEq, Inhabited

def AssetSource.fromString : String → Option AssetSource
  | "comfyui_node" => some AssetSource.comfyuiNode
  | "file" => some AssetSource.file
  | "generated" => some AssetSource.generated
  | "url" => some AssetSource.url
  | _ => none

def AssetSource.toString : AssetSource → String
  | AssetSource.comfyuiNode => "comfyui_node"
  | AssetSource.file => "file"
  | AssetSource.generated => "generated"
  | AssetSource.url => "url"

/-- Texture map types -/
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

def TextureMapType.fromString : String → Option TextureMapType
  | "albedo" => some TextureMapType.albedo
  | "normal" => some TextureMapType.normal
  | "roughness" => some TextureMapType.roughness
  | "metalness" => some TextureMapType.metalness
  | "ao" => some TextureMapType.ao
  | "emissive" => some TextureMapType.emissive
  | "height" => some TextureMapType.height
  | "opacity" => some TextureMapType.opacity
  | "specular" => some TextureMapType.specular
  | _ => none

def TextureMapType.toString : TextureMapType → String
  | TextureMapType.albedo => "albedo"
  | TextureMapType.normal => "normal"
  | TextureMapType.roughness => "roughness"
  | TextureMapType.metalness => "metalness"
  | TextureMapType.ao => "ao"
  | TextureMapType.emissive => "emissive"
  | TextureMapType.height => "height"
  | TextureMapType.opacity => "opacity"
  | TextureMapType.specular => "specular"

/-- Model formats -/
inductive ModelFormat where
  | gltf
  | glb
  | obj
  | fbx
  | usd
  deriving Repr, DecidableEq, Inhabited

def ModelFormat.fromString : String → Option ModelFormat
  | "gltf" => some ModelFormat.gltf
  | "glb" => some ModelFormat.glb
  | "obj" => some ModelFormat.obj
  | "fbx" => some ModelFormat.fbx
  | "usd" => some ModelFormat.usd
  | _ => none

def ModelFormat.toString : ModelFormat → String
  | ModelFormat.gltf => "gltf"
  | ModelFormat.glb => "glb"
  | ModelFormat.obj => "obj"
  | ModelFormat.fbx => "fbx"
  | ModelFormat.usd => "usd"

/-- Point cloud formats -/
inductive PointCloudFormat where
  | ply
  | pcd
  | las
  | xyz
  deriving Repr, DecidableEq, Inhabited

def PointCloudFormat.fromString : String → Option PointCloudFormat
  | "ply" => some PointCloudFormat.ply
  | "pcd" => some PointCloudFormat.pcd
  | "las" => some PointCloudFormat.las
  | "xyz" => some PointCloudFormat.xyz
  | _ => none

def PointCloudFormat.toString : PointCloudFormat → String
  | PointCloudFormat.ply => "ply"
  | PointCloudFormat.pcd => "pcd"
  | PointCloudFormat.las => "las"
  | PointCloudFormat.xyz => "xyz"

/-- Texture color spaces -/
inductive TextureColorSpace where
  | srgb
  | linear
  deriving Repr, DecidableEq, Inhabited

def TextureColorSpace.fromString : String → Option TextureColorSpace
  | "srgb" => some TextureColorSpace.srgb
  | "linear" => some TextureColorSpace.linear
  | _ => none

def TextureColorSpace.toString : TextureColorSpace → String
  | TextureColorSpace.srgb => "srgb"
  | TextureColorSpace.linear => "linear"

--------------------------------------------------------------------------------
-- Data Asset Types
--------------------------------------------------------------------------------

/-- Data asset types -/
inductive DataAssetType where
  | json
  | csv
  | tsv
  | mgjson
  deriving Repr, DecidableEq, Inhabited

def DataAssetType.fromString : String → Option DataAssetType
  | "json" => some DataAssetType.json
  | "csv" => some DataAssetType.csv
  | "tsv" => some DataAssetType.tsv
  | "mgjson" => some DataAssetType.mgjson
  | _ => none

def DataAssetType.toString : DataAssetType → String
  | DataAssetType.json => "json"
  | DataAssetType.csv => "csv"
  | DataAssetType.tsv => "tsv"
  | DataAssetType.mgjson => "mgjson"

end Lattice.Schemas.Project.ProjectSchema
