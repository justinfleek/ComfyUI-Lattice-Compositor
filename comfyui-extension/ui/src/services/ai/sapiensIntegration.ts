/**
 * Sapiens Integration Service
 *
 * Integrates Meta's Sapiens foundation models for human-centric vision:
 * - Depth estimation (human subjects)
 * - Surface normal estimation (human subjects)
 * - Pose estimation (308 keypoints)
 * - Body part segmentation (28 parts)
 *
 * These capabilities enhance camera tracking for Uni3C workflows
 * where humans are the primary subject.
 *
 * Reference: https://github.com/facebookresearch/sapiens
 * ECCV 2024 Best Paper Candidate
 */

import { isFiniteNumber } from "@/utils/typeGuards";

/**
 * Sapiens model sizes
 */
export type SapiensModelSize = "0.3B" | "0.6B" | "1B" | "2B";

/**
 * Sapiens API result structure (from backend)
 */
interface SapiensAPIResult {
  depthMap?: string;
  normalMap?: string;
  mask?: string;
  width?: number;
  height?: number;
  minDepth?: number;
  maxDepth?: number;
  labels?: SapiensBodyPart[];
}

/**
 * Sapiens task types
 */
export type SapiensTask = "depth" | "normal" | "pose" | "segmentation";

/**
 * Sapiens inference configuration
 */
export interface SapiensConfig {
  /** Model size (0.3B to 2B) */
  modelSize: SapiensModelSize;
  /** Backend URL (ComfyUI server) */
  backendUrl: string;
  /** Use BF16 precision (requires Ampere+ GPU) */
  useBfloat16: boolean;
  /** Batch size for inference */
  batchSize: number;
}

/**
 * Sapiens depth estimation result
 */
export interface SapiensDepthResult {
  /** Frame index */
  frame: number;
  /** Depth map as Float32Array (normalized 0-1) */
  depthMap: Float32Array;
  /** Width */
  width: number;
  /** Height */
  height: number;
  /** Min depth value (meters, if calibrated) */
  minDepth?: number;
  /** Max depth value (meters, if calibrated) */
  maxDepth?: number;
}

/**
 * Sapiens normal estimation result
 */
export interface SapiensNormalResult {
  /** Frame index */
  frame: number;
  /** Normal map as Float32Array (RGB, normalized -1 to 1) */
  normalMap: Float32Array;
  /** Width */
  width: number;
  /** Height */
  height: number;
}

/**
 * Sapiens pose keypoint (308 total in GOLIATH skeleton)
 */
export interface SapiensKeypoint {
  /** Keypoint name */
  name: string;
  /** X coordinate (0-1 normalized) */
  x: number;
  /** Y coordinate (0-1 normalized) */
  y: number;
  /** Confidence score (0-1) */
  confidence: number;
  /** Visibility flag */
  visible: boolean;
}

/**
 * Sapiens pose estimation result
 */
export interface SapiensPoseResult {
  /** Frame index */
  frame: number;
  /** Detected people */
  people: Array<{
    /** Person ID (for tracking) */
    id: number;
    /** Bounding box [x, y, width, height] */
    bbox: [number, number, number, number];
    /** 308 keypoints */
    keypoints: SapiensKeypoint[];
    /** Overall confidence */
    confidence: number;
  }>;
}

/**
 * Body part segmentation labels (28 parts)
 */
export const SAPIENS_BODY_PARTS = [
  "background",
  "head",
  "neck",
  "torso",
  "left_upper_arm",
  "left_lower_arm",
  "left_hand",
  "right_upper_arm",
  "right_lower_arm",
  "right_hand",
  "left_upper_leg",
  "left_lower_leg",
  "left_foot",
  "right_upper_leg",
  "right_lower_leg",
  "right_foot",
  "left_eye",
  "right_eye",
  "left_ear",
  "right_ear",
  "nose",
  "upper_lip",
  "lower_lip",
  "hair",
  "left_eyebrow",
  "right_eyebrow",
  "left_shoulder",
  "right_shoulder",
] as const;

export type SapiensBodyPart = (typeof SAPIENS_BODY_PARTS)[number];

/**
 * Sapiens segmentation result
 */
export interface SapiensSegmentationResult {
  /** Frame index */
  frame: number;
  /** Segmentation mask (Uint8Array with body part indices) */
  mask: Uint8Array;
  /** Width */
  width: number;
  /** Height */
  height: number;
  /** Part labels for each unique value in mask */
  labels: SapiensBodyPart[];
}

/**
 * Default Sapiens configuration
 */
export const DEFAULT_SAPIENS_CONFIG: SapiensConfig = {
  modelSize: "1B",
  backendUrl: "/lattice/api/sapiens",
  useBfloat16: true,
  batchSize: 4,
};

/**
 * Sapiens inference service
 */
export class SapiensService {
  private config: SapiensConfig;

  constructor(config: Partial<SapiensConfig> = {}) {
    this.config = { ...DEFAULT_SAPIENS_CONFIG, ...config };
  }

  /**
   * Estimate depth for human subjects in video frames
   */
  async estimateDepth(
    frames: ImageData[],
    segmentationMasks?: Uint8Array[],
  ): Promise<SapiensDepthResult[]> {
    // If no segmentation masks provided, run segmentation first
    const masks =
      segmentationMasks ||
      (await this.runSegmentation(frames)).map((r) => r.mask);

    const response = await fetch(`${this.config.backendUrl}/depth`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames: frames.map((f) => imageDataToBase64(f)),
        masks: masks.map((m) => uint8ArrayToBase64(m)),
        modelSize: this.config.modelSize,
        useBfloat16: this.config.useBfloat16,
        batchSize: this.config.batchSize,
      }),
    });

    if (!response.ok) {
      throw new Error(
        `Sapiens depth estimation failed: ${response.statusText}`,
      );
    }

    const data = await response.json();
    // Type guard for Sapiens API result structure
    interface SapiensAPIResult {
      depthMap?: string;
      normalMap?: string;
      mask?: string;
      width?: number;
      height?: number;
      minDepth?: number;
      maxDepth?: number;
      labels?: SapiensBodyPart[];
    }
    return (data.results as SapiensAPIResult[]).map((r, i) => {
      // Type proof: depthMap ∈ string | undefined → string
      const depthMapBase64 =
        typeof r.depthMap === "string" && r.depthMap.length > 0
          ? r.depthMap
          : "";
      // Type proof: width ∈ number | undefined → number
      const width = isFiniteNumber(r.width) && r.width > 0
        ? Math.floor(r.width)
        : 0;
      // Type proof: height ∈ number | undefined → number
      const height = isFiniteNumber(r.height) && r.height > 0
        ? Math.floor(r.height)
        : 0;

      return {
        frame: i,
        depthMap: new Float32Array(base64ToArrayBuffer(depthMapBase64)),
        width,
        height,
        minDepth: r.minDepth,
        maxDepth: r.maxDepth,
      };
    });
  }

  /**
   * Estimate surface normals for human subjects
   */
  async estimateNormals(
    frames: ImageData[],
    segmentationMasks?: Uint8Array[],
  ): Promise<SapiensNormalResult[]> {
    const masks =
      segmentationMasks ||
      (await this.runSegmentation(frames)).map((r) => r.mask);

    const response = await fetch(`${this.config.backendUrl}/normal`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames: frames.map((f) => imageDataToBase64(f)),
        masks: masks.map((m) => uint8ArrayToBase64(m)),
        modelSize: this.config.modelSize,
        useBfloat16: this.config.useBfloat16,
        batchSize: this.config.batchSize,
      }),
    });

    if (!response.ok) {
      throw new Error(
        `Sapiens normal estimation failed: ${response.statusText}`,
      );
    }

    const data = await response.json();
    // Type guard for Sapiens API result structure
    interface SapiensAPIResult {
      depthMap?: string;
      normalMap?: string;
      mask?: string;
      width?: number;
      height?: number;
      minDepth?: number;
      maxDepth?: number;
      labels?: SapiensBodyPart[];
    }
    return (data.results as SapiensAPIResult[]).map((r, i) => {
      // Type proof: normalMap ∈ string | undefined → string
      const normalMapBase64 =
        typeof r.normalMap === "string" && r.normalMap.length > 0
          ? r.normalMap
          : "";
      // Type proof: width ∈ number | undefined → number
      const width = isFiniteNumber(r.width) && r.width > 0
        ? Math.floor(r.width)
        : 0;
      // Type proof: height ∈ number | undefined → number
      const height = isFiniteNumber(r.height) && r.height > 0
        ? Math.floor(r.height)
        : 0;

      return {
        frame: i,
        normalMap: new Float32Array(base64ToArrayBuffer(normalMapBase64)),
        width,
        height,
      };
    });
  }

  /**
   * Estimate 2D pose (308 keypoints)
   */
  async estimatePose(frames: ImageData[]): Promise<SapiensPoseResult[]> {
    const response = await fetch(`${this.config.backendUrl}/pose`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames: frames.map((f) => imageDataToBase64(f)),
        modelSize: this.config.modelSize,
        useBfloat16: this.config.useBfloat16,
        batchSize: this.config.batchSize,
      }),
    });

    if (!response.ok) {
      throw new Error(`Sapiens pose estimation failed: ${response.statusText}`);
    }

    const data = await response.json();
    return data.results;
  }

  /**
   * Run body part segmentation
   */
  async runSegmentation(
    frames: ImageData[],
  ): Promise<SapiensSegmentationResult[]> {
    const response = await fetch(`${this.config.backendUrl}/segmentation`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        frames: frames.map((f) => imageDataToBase64(f)),
        modelSize: this.config.modelSize,
        useBfloat16: this.config.useBfloat16,
        batchSize: this.config.batchSize,
      }),
    });

    if (!response.ok) {
      throw new Error(`Sapiens segmentation failed: ${response.statusText}`);
    }

    const data = await response.json();
    // Type guard for Sapiens API result structure
    interface SapiensAPIResult {
      depthMap?: string;
      normalMap?: string;
      mask?: string;
      width?: number;
      height?: number;
      minDepth?: number;
      maxDepth?: number;
      labels?: SapiensBodyPart[];
    }
    return (data.results as SapiensAPIResult[]).map((r, i) => {
      // Type proof: mask ∈ string | undefined → string
      const maskBase64 =
        typeof r.mask === "string" && r.mask.length > 0 ? r.mask : "";
      // Type proof: width ∈ number | undefined → number
      const width = isFiniteNumber(r.width) && r.width > 0
        ? Math.floor(r.width)
        : 0;
      // Type proof: height ∈ number | undefined → number
      const height = isFiniteNumber(r.height) && r.height > 0
        ? Math.floor(r.height)
        : 0;
      // Type proof: labels ∈ SapiensBodyPart[] | undefined → SapiensBodyPart[]
      const labels = Array.isArray(r.labels) ? r.labels : [];

      return {
        frame: i,
        mask: new Uint8Array(base64ToArrayBuffer(maskBase64)),
        width,
        height,
        labels,
      };
    });
  }

  /**
   * Run all Sapiens tasks on frames
   */
  async analyzeFrames(frames: ImageData[]): Promise<{
    depth: SapiensDepthResult[];
    normals: SapiensNormalResult[];
    pose: SapiensPoseResult[];
    segmentation: SapiensSegmentationResult[];
  }> {
    // Run segmentation first (required for depth/normal)
    const segmentation = await this.runSegmentation(frames);
    const masks = segmentation.map((s) => s.mask);

    // Run other tasks in parallel
    const [depth, normals, pose] = await Promise.all([
      this.estimateDepth(frames, masks),
      this.estimateNormals(frames, masks),
      this.estimatePose(frames),
    ]);

    return { depth, normals, pose, segmentation };
  }
}

/**
 * Convert ImageData to base64 PNG
 */
function imageDataToBase64(imageData: ImageData): string {
  const canvas = document.createElement("canvas");
  canvas.width = imageData.width;
  canvas.height = imageData.height;
  const ctx = canvas.getContext("2d")!;
  ctx.putImageData(imageData, 0, 0);
  return canvas.toDataURL("image/png").split(",")[1];
}

/**
 * Convert Uint8Array to base64
 */
function uint8ArrayToBase64(array: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < array.length; i++) {
    binary += String.fromCharCode(array[i]);
  }
  return btoa(binary);
}

/**
 * Convert base64 to ArrayBuffer
 */
function base64ToArrayBuffer(base64: string): ArrayBuffer {
  const binaryString = atob(base64);
  const bytes = new Uint8Array(binaryString.length);
  for (let i = 0; i < binaryString.length; i++) {
    bytes[i] = binaryString.charCodeAt(i);
  }
  return bytes.buffer;
}

/**
 * Convert Sapiens depth results to camera tracking point cloud
 *
 * This is useful for Uni3C PCDController integration
 */
export function depthToPointCloud(
  depthResult: SapiensDepthResult,
  rgbFrame: ImageData,
  intrinsics: { fx: number; fy: number; cx: number; cy: number },
): {
  points: Array<{ x: number; y: number; z: number }>;
  colors: Array<{ r: number; g: number; b: number }>;
} {
  const points: Array<{ x: number; y: number; z: number }> = [];
  const colors: Array<{ r: number; g: number; b: number }> = [];

  const { fx, fy, cx, cy } = intrinsics;
  const { width, height, depthMap } = depthResult;

  // Sample every Nth pixel (for performance)
  const sampleRate = 4;

  for (let y = 0; y < height; y += sampleRate) {
    for (let x = 0; x < width; x += sampleRate) {
      const idx = y * width + x;
      const depth = depthMap[idx];

      // Skip invalid depths
      if (depth <= 0 || depth > 10) continue;

      // Backproject to 3D
      const px = ((x - cx) * depth) / fx;
      const py = ((y - cy) * depth) / fy;
      const pz = depth;

      points.push({ x: px, y: py, z: pz });

      // Get RGB color
      const rgbIdx = (y * width + x) * 4;
      colors.push({
        r: rgbFrame.data[rgbIdx] / 255,
        g: rgbFrame.data[rgbIdx + 1] / 255,
        b: rgbFrame.data[rgbIdx + 2] / 255,
      });
    }
  }

  return { points, colors };
}

/**
 * Create Uni3C-compatible camera data from Sapiens analysis
 */
export function createUni3CCameraData(
  depthResults: SapiensDepthResult[],
  rgbFrames: ImageData[],
  _fps: number = 16,
): {
  K: number[][];
  depth_maps: Float32Array[];
  point_clouds: Array<{ points: number[][]; colors: number[][] }>;
} {
  // Estimate intrinsics from first frame
  // Type proof: width ∈ number | undefined → number
  const firstResult = depthResults[0];
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const firstResultWidth = (firstResult != null && typeof firstResult === "object" && "width" in firstResult && typeof firstResult.width === "number") ? firstResult.width : undefined;
  const width = isFiniteNumber(firstResultWidth) && firstResultWidth > 0
    ? Math.floor(firstResultWidth)
    : 1920;
  // Type proof: height ∈ number | undefined → number
  const firstResultHeight = (firstResult != null && typeof firstResult === "object" && "height" in firstResult && typeof firstResult.height === "number") ? firstResult.height : undefined;
  const height = isFiniteNumber(firstResultHeight) && firstResultHeight > 0
    ? Math.floor(firstResultHeight)
    : 1080;

  // Approximate focal length (assuming ~50mm on full-frame equivalent)
  const fx = width * 0.8;
  const fy = fx;
  const cx = width / 2;
  const cy = height / 2;

  const K = [
    [fx, 0, cx],
    [0, fy, cy],
    [0, 0, 1],
  ];

  const depth_maps = depthResults.map((r) => r.depthMap);

  const point_clouds = depthResults.map((depth, i) => {
    const pc = depthToPointCloud(depth, rgbFrames[i], { fx, fy, cx, cy });
    return {
      points: pc.points.map((p) => [p.x, p.y, p.z]),
      colors: pc.colors.map((c) => [c.r, c.g, c.b]),
    };
  });

  return { K, depth_maps, point_clouds };
}

// Singleton instance
let sapiensService: SapiensService | null = null;

/**
 * Get the Sapiens service singleton
 */
export function getSapiensService(
  config?: Partial<SapiensConfig>,
): SapiensService {
  if (!sapiensService || config) {
    sapiensService = new SapiensService(config);
  }
  return sapiensService;
}
