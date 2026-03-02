/**
 * Asset Types - Asset references and metadata
 *
 * Extracted from project.ts for better modularity.
 */

// ============================================================
// ASSET TYPE DEFINITIONS
// ============================================================

/** Asset types supported by the compositor */
export type AssetType =
  | "depth_map" // Depth map image
  | "image" // Standard image (PNG, JPG, WebP)
  | "video" // Video file (MP4, WebM)
  | "audio" // Audio file (MP3, WAV, OGG)
  | "model" // 3D model (GLTF, OBJ, FBX, USD)
  | "pointcloud" // Point cloud (PLY, PCD, LAS)
  | "texture" // PBR texture map
  | "material" // Material definition (with texture refs)
  | "hdri" // Environment map (HDR, EXR)
  | "svg" // Vector graphic (for extrusion)
  | "sprite" // Single image for particles (no grid)
  | "spritesheet" // Sprite sheet for particles (grid of frames)
  | "lut"; // Color lookup table

/** PBR texture map types */
export type TextureMapType =
  | "albedo" // Base color / diffuse
  | "normal" // Normal map
  | "roughness" // Roughness map
  | "metalness" // Metalness map
  | "ao" // Ambient occlusion
  | "emissive" // Emissive map
  | "height" // Height/displacement map
  | "opacity" // Alpha/opacity map
  | "specular"; // Specular map (for non-PBR workflows)

/** 3D model formats */
export type ModelFormat =
  | "gltf"
  | "glb"
  | "obj"
  | "fbx"
  | "usd"
  | "usda"
  | "usdc"
  | "usdz";

/** Point cloud formats */
export type PointCloudFormat = "ply" | "pcd" | "las" | "laz" | "xyz" | "pts";

/** Model bounding box */
export interface ModelBoundingBox {
  min: { x: number; y: number; z: number };
  max: { x: number; y: number; z: number };
  center: { x: number; y: number; z: number };
  size: { x: number; y: number; z: number };
}

// ============================================================
// ASSET REFERENCE
// ============================================================

export interface AssetReference {
  id: string;
  type: AssetType;
  source: "comfyui_node" | "file" | "generated" | "url";
  nodeId?: string;
  width: number;
  height: number;
  data: string; // Base64 or URL - always required for valid assets
  filename?: string; // Original filename

  // Video/Audio specific metadata
  frameCount?: number; // Total frames in video
  duration?: number; // Duration in seconds
  fps?: number; // Source FPS (for video)
  hasAudio?: boolean; // Video has audio track
  audioChannels?: number; // 1=mono, 2=stereo
  sampleRate?: number; // Audio sample rate

  // 3D Model metadata
  modelFormat?: ModelFormat;
  modelBoundingBox?: ModelBoundingBox;
  modelAnimations?: string[]; // Animation clip names
  modelMeshCount?: number;
  modelVertexCount?: number;

  // Point cloud metadata
  pointCloudFormat?: PointCloudFormat;
  pointCount?: number;

  // Texture metadata
  textureMapType?: TextureMapType;
  textureColorSpace?: "srgb" | "linear";

  // Material definition (references other texture assets)
  materialMaps?: {
    albedo?: string; // Asset ID for albedo texture
    normal?: string; // Asset ID for normal map
    roughness?: string; // Asset ID for roughness map
    metalness?: string; // Asset ID for metalness map
    ao?: string; // Asset ID for AO map
    emissive?: string; // Asset ID for emissive map
    height?: string; // Asset ID for height map
    opacity?: string; // Asset ID for opacity map
  };

  // HDRI metadata
  hdriExposure?: number;
  hdriRotation?: number;

  // SVG metadata (for extrusion)
  svgPaths?: number; // Number of paths in SVG
  svgViewBox?: { x: number; y: number; width: number; height: number };

  // Sprite sheet metadata
  spriteColumns?: number;
  spriteRows?: number;
  spriteCount?: number;
  spriteFrameRate?: number;

  // Sprite validation metadata (stored from import validation)
  spriteValidation?: {
    isPowerOfTwo: boolean;
    hasAlpha: boolean;
    originalFormat: string;
    warnings?: string[];
  };
}

// ============================================================
// DATA ASSET REFERENCE
// ============================================================

/**
 * Reference to a data asset (JSON, CSV, TSV) for expressions
 * Used for data-driven animation - chart data, CSV tables, JSON configs
 */
export interface DataAssetReference {
  id: string;
  name: string; // Original filename
  type: "json" | "csv" | "tsv" | "mgjson";
  rawContent: string; // Original file content
  lastModified: number; // Timestamp

  // For JSON: the parsed data (type-safe JSON value)
  sourceData?: import("@/types/dataAsset").JSONValue;

  // For CSV/TSV: tabular structure
  headers?: string[];
  rows?: string[][];
  numRows?: number;
  numColumns?: number;
}
