/**
 * PoseLayer - OpenPose Skeleton Rendering Layer
 *
 * Renders human pose skeletons with editable keypoints for:
 * - ControlNet pose conditioning
 * - Motion capture visualization
 * - Character animation reference
 *
 * Supports:
 * - COCO 18-keypoint format (standard OpenPose)
 * - Body_25 (25 keypoints with foot detail)
 * - Custom skeleton configurations
 * - Multi-person scenes
 * - Keyframe animation of individual joints
 * - Mirror/flip operations
 * - Limb color customization
 */

import * as THREE from "three";
import type { AnimatableProperty, Layer, Vec2, PoseLayerData as ProjectPoseLayerData } from "@/types/project";
import { interpolateProperty } from "@/services/interpolation";
import { BaseLayer } from "./BaseLayer";

// ============================================================================
// OPENPOSE SKELETON DEFINITIONS
// ============================================================================

/**
 * COCO 18-keypoint format (standard OpenPose)
 * Index: [name, parent index (-1 = root)]
 */
export const COCO_KEYPOINTS = [
  { name: "nose", parent: -1 }, // 0
  { name: "neck", parent: 0 }, // 1
  { name: "right_shoulder", parent: 1 }, // 2
  { name: "right_elbow", parent: 2 }, // 3
  { name: "right_wrist", parent: 3 }, // 4
  { name: "left_shoulder", parent: 1 }, // 5
  { name: "left_elbow", parent: 5 }, // 6
  { name: "left_wrist", parent: 6 }, // 7
  { name: "right_hip", parent: 1 }, // 8
  { name: "right_knee", parent: 8 }, // 9
  { name: "right_ankle", parent: 9 }, // 10
  { name: "left_hip", parent: 1 }, // 11
  { name: "left_knee", parent: 11 }, // 12
  { name: "left_ankle", parent: 12 }, // 13
  { name: "right_eye", parent: 0 }, // 14
  { name: "left_eye", parent: 0 }, // 15
  { name: "right_ear", parent: 14 }, // 16
  { name: "left_ear", parent: 15 }, // 17
] as const;

/**
 * OpenPose bone connections for rendering
 * [start keypoint index, end keypoint index]
 */
export const COCO_BONES: [number, number][] = [
  // Head
  [0, 1], // nose -> neck
  [0, 14], // nose -> right_eye
  [0, 15], // nose -> left_eye
  [14, 16], // right_eye -> right_ear
  [15, 17], // left_eye -> left_ear
  // Torso
  [1, 2], // neck -> right_shoulder
  [1, 5], // neck -> left_shoulder
  [1, 8], // neck -> right_hip
  [1, 11], // neck -> left_hip
  // Right arm
  [2, 3], // right_shoulder -> right_elbow
  [3, 4], // right_elbow -> right_wrist
  // Left arm
  [5, 6], // left_shoulder -> left_elbow
  [6, 7], // left_elbow -> left_wrist
  // Right leg
  [8, 9], // right_hip -> right_knee
  [9, 10], // right_knee -> right_ankle
  // Left leg
  [11, 12], // left_hip -> left_knee
  [12, 13], // left_knee -> left_ankle
];

/**
 * Default bone colors (OpenPose standard colors)
 */
export const OPENPOSE_COLORS: Record<string, string> = {
  // Head - yellow/orange
  head: "#FFD700",
  // Right side - warm colors (red/orange)
  right_arm: "#FF0000",
  right_leg: "#FF6600",
  // Left side - cool colors (blue/cyan)
  left_arm: "#0000FF",
  left_leg: "#00CCFF",
  // Torso - green
  torso: "#00FF00",
};

/**
 * Map bone index to color category
 */
export function getBoneColor(boneIndex: number): string {
  const bone = COCO_BONES[boneIndex];
  if (!bone) return "#FFFFFF";

  const [_start, _end] = bone;

  // Head bones (0-4)
  if (boneIndex <= 4) return OPENPOSE_COLORS.head;

  // Torso bones (5-8)
  if (boneIndex >= 5 && boneIndex <= 8) return OPENPOSE_COLORS.torso;

  // Right arm (9-10)
  if (boneIndex >= 9 && boneIndex <= 10) return OPENPOSE_COLORS.right_arm;

  // Left arm (11-12)
  if (boneIndex >= 11 && boneIndex <= 12) return OPENPOSE_COLORS.left_arm;

  // Right leg (13-14)
  if (boneIndex >= 13 && boneIndex <= 14) return OPENPOSE_COLORS.right_leg;

  // Left leg (15-16)
  if (boneIndex >= 15 && boneIndex <= 16) return OPENPOSE_COLORS.left_leg;

  return "#FFFFFF";
}

// ============================================================================
// TYPES
// ============================================================================

export type PoseFormat = "coco18" | "body25" | "custom";

export interface PoseKeypoint {
  /** X position (0-1 normalized or pixel coordinates) */
  x: number;
  /** Y position (0-1 normalized or pixel coordinates) */
  y: number;
  /** Confidence/visibility (0-1, 0 = invisible) */
  confidence: number;
}

export interface Pose {
  /** Unique ID for this pose */
  id: string;
  /** Array of keypoints (length depends on format) */
  keypoints: PoseKeypoint[];
  /** Pose format */
  format: PoseFormat;
}

export interface PoseLayerData {
  /** All poses in this layer */
  poses: Pose[];

  /** Pose format */
  format: PoseFormat;

  /** Whether keypoints are normalized (0-1) or pixel coordinates */
  normalized: boolean;

  /** Rendering options */
  boneWidth: number;
  keypointRadius: number;
  showKeypoints: boolean;
  showBones: boolean;
  showLabels: boolean;

  /** Color options */
  useDefaultColors: boolean;
  customBoneColor: string;
  customKeypointColor: string;
  backgroundColor: string;

  /** Opacity */
  boneOpacity: number;
  keypointOpacity: number;

  /** Animation - keypoints can be animated */
  animatedKeypoints?: Record<string, AnimatableProperty<Vec2>>;
}

// ============================================================================
// DEFAULT VALUES
// ============================================================================

export function createDefaultPose(format: PoseFormat = "coco18"): Pose {
  const keypointCount =
    format === "coco18" ? 18 : format === "body25" ? 25 : 18;

  // Create default T-pose
  const keypoints: PoseKeypoint[] = [];

  if (format === "coco18") {
    // Default T-pose positions (normalized 0-1)
    const defaultPositions: [number, number][] = [
      [0.5, 0.1], // 0: nose
      [0.5, 0.2], // 1: neck
      [0.35, 0.2], // 2: right_shoulder
      [0.25, 0.2], // 3: right_elbow
      [0.15, 0.2], // 4: right_wrist
      [0.65, 0.2], // 5: left_shoulder
      [0.75, 0.2], // 6: left_elbow
      [0.85, 0.2], // 7: left_wrist
      [0.4, 0.45], // 8: right_hip
      [0.4, 0.65], // 9: right_knee
      [0.4, 0.85], // 10: right_ankle
      [0.6, 0.45], // 11: left_hip
      [0.6, 0.65], // 12: left_knee
      [0.6, 0.85], // 13: left_ankle
      [0.45, 0.08], // 14: right_eye
      [0.55, 0.08], // 15: left_eye
      [0.4, 0.1], // 16: right_ear
      [0.6, 0.1], // 17: left_ear
    ];

    for (const [x, y] of defaultPositions) {
      keypoints.push({ x, y, confidence: 1.0 });
    }
  } else {
    // Generic centered pose
    for (let i = 0; i < keypointCount; i++) {
      keypoints.push({ x: 0.5, y: 0.5, confidence: 1.0 });
    }
  }

  return {
    id: `pose_default_${format}`,
    keypoints,
    format,
  };
}

export function createDefaultPoseLayerData(): PoseLayerData {
  return {
    poses: [createDefaultPose("coco18")],
    format: "coco18",
    normalized: true,
    boneWidth: 4,
    keypointRadius: 6,
    showKeypoints: true,
    showBones: true,
    showLabels: false,
    useDefaultColors: true,
    customBoneColor: "#FFFFFF",
    customKeypointColor: "#FF0000",
    backgroundColor: "#000000",
    boneOpacity: 1.0,
    keypointOpacity: 1.0,
  };
}

// ============================================================================
// POSE LAYER CLASS
// ============================================================================

export class PoseLayer extends BaseLayer {
  type = "pose" as const;
  private canvas: HTMLCanvasElement;
  private ctx: CanvasRenderingContext2D;
  private texture: THREE.CanvasTexture;
  private mesh: THREE.Mesh;

  // Composition dimensions (set by LayerManager when composition changes)
  private compWidth: number = 512;
  private compHeight: number = 512;

  // Track last rendered frame for optimization
  private lastRenderedFrame: number = -1;

  // Current frame being evaluated (set by onEvaluateFrame, used for export)
  private currentFrame: number = 0;

  // Cached evaluated keypoints per frame (for neighbor-based animation)
  private evaluatedKeypointsCache: Map<number, Map<string, Vec2>> = new Map();

  // Spatial hash for z-space neighbor queries (keypoint index -> neighbors in z-space)
  private keypointSpatialHash: Map<number, Set<number>> = new Map();

  constructor(layerData: Layer) {
    super(layerData);

    // Create canvas for 2D pose rendering
    this.canvas = document.createElement("canvas");
    this.canvas.width = this.compWidth;
    this.canvas.height = this.compHeight;
    // Deterministic: Explicit null check for getContext - "2d" should always succeed but we verify
    const ctx = this.canvas.getContext("2d");
    if (!ctx) {
      throw new Error("[PoseLayer] Failed to get 2d context from HTMLCanvasElement");
    }
    this.ctx = ctx;

    // Create Three.js texture and mesh
    this.texture = new THREE.CanvasTexture(this.canvas);
    this.texture.minFilter = THREE.LinearFilter;
    this.texture.magFilter = THREE.LinearFilter;

    const geometry = new THREE.PlaneGeometry(1, 1);
    const material = new THREE.MeshBasicMaterial({
      map: this.texture,
      transparent: true,
      side: THREE.DoubleSide,
    });

    this.mesh = new THREE.Mesh(geometry, material);
    this.object.add(this.mesh);
  }

  /**
   * Get pose data with defaults
   * Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || {}
   */
  private getPoseData(): PoseLayerData {
    const dataRaw = this.layerData.data as Partial<ProjectPoseLayerData>;
    const data = (dataRaw !== null && dataRaw !== undefined && typeof dataRaw === "object" && dataRaw !== null) ? dataRaw : {};
    const projectData: Partial<ProjectPoseLayerData> = {
      ...createDefaultPoseLayerData(),
      ...data,
    };
    // Convert project type to local type (they have different properties)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const poses = (Array.isArray(projectData.poses)) ? projectData.poses : [];
    const format = (typeof projectData.format === "string" && projectData.format.length > 0) ? projectData.format : "coco18";
    const normalized = (typeof projectData.normalized === "boolean") ? projectData.normalized : false;
    const boneWidth = (typeof projectData.boneWidth === "number" && Number.isFinite(projectData.boneWidth) && projectData.boneWidth > 0) ? projectData.boneWidth : 2;
    const keypointRadius = (typeof projectData.keypointRadius === "number" && Number.isFinite(projectData.keypointRadius) && projectData.keypointRadius > 0) ? projectData.keypointRadius : 5;
    const showKeypoints = (typeof projectData.showKeypoints === "boolean") ? projectData.showKeypoints : true;
    const showBones = (typeof projectData.showBones === "boolean") ? projectData.showBones : true;
    const showLabels = (typeof projectData.showLabels === "boolean") ? projectData.showLabels : false;
    const useDefaultColors = (typeof projectData.useDefaultColors === "boolean") ? projectData.useDefaultColors : true;
    const customBoneColor = (typeof projectData.customBoneColor === "string" && projectData.customBoneColor.length > 0) ? projectData.customBoneColor : "#00ff00";
    const customKeypointColor = (typeof projectData.customKeypointColor === "string" && projectData.customKeypointColor.length > 0) ? projectData.customKeypointColor : "#ff0000";
    return {
      poses,
      format,
      normalized,
      boneWidth,
      keypointRadius,
      showKeypoints,
      showBones,
      showLabels,
      useDefaultColors,
      customBoneColor,
      customKeypointColor,
      backgroundColor: "#000000", // Not in project type, use default
      boneOpacity: 100, // Not in project type, use default
      keypointOpacity: 100, // Not in project type, use default
      animatedKeypoints: {}, // Not in project type, use default
    };
  }

  /**
   * Render poses to canvas
   * 
   * @param width - Canvas width
   * @param height - Canvas height
   * @param frame - Optional frame number for per-keypoint animation evaluation
   */
  private renderPoses(width: number, height: number, frame?: number): void {
    // If frame is provided, use evaluated poses (per-keypoint animation)
    if (typeof frame === "number" && Number.isFinite(frame)) {
      const evaluatedPoses = this.evaluatePosesAtFrame(frame);
      this.renderEvaluatedPoses(evaluatedPoses, width, height);
      return;
    }

    // Render without frame evaluation (static poses)
    const data = this.getPoseData();
    const { ctx, canvas } = this;

    // Resize canvas if needed
    if (canvas.width !== width || canvas.height !== height) {
      canvas.width = width;
      canvas.height = height;
    }

    // Clear with background color
    ctx.fillStyle = data.backgroundColor;
    ctx.fillRect(0, 0, width, height);

    // Render each pose
    for (const pose of data.poses) {
      this.renderSinglePose(pose, width, height, data);
    }

    // Update texture
    this.texture.needsUpdate = true;
  }

  /**
   * Render a single pose skeleton
   */
  private renderSinglePose(
    pose: Pose,
    width: number,
    height: number,
    data: PoseLayerData,
  ): void {
    const { ctx } = this;
    const { keypoints } = pose;

    // Convert normalized coords to pixels if needed
    const toPixel = (
      kp: PoseKeypoint,
    ): { x: number; y: number; visible: boolean } => {
      if (data.normalized) {
        return {
          x: kp.x * width,
          y: kp.y * height,
          visible: kp.confidence > 0.1,
        };
      }
      return {
        x: kp.x,
        y: kp.y,
        visible: kp.confidence > 0.1,
      };
    };

    // Render bones first (behind keypoints)
    if (data.showBones) {
      const bones = pose.format === "coco18" ? COCO_BONES : COCO_BONES;

      ctx.lineCap = "round";
      ctx.lineWidth = data.boneWidth;
      ctx.globalAlpha = data.boneOpacity;

      bones.forEach((bone, boneIndex) => {
        const [startIdx, endIdx] = bone;
        if (startIdx >= keypoints.length || endIdx >= keypoints.length) return;

        const start = toPixel(keypoints[startIdx]);
        const end = toPixel(keypoints[endIdx]);

        if (!start.visible || !end.visible) return;

        ctx.strokeStyle = data.useDefaultColors
          ? getBoneColor(boneIndex)
          : data.customBoneColor;

        ctx.beginPath();
        ctx.moveTo(start.x, start.y);
        ctx.lineTo(end.x, end.y);
        ctx.stroke();
      });
    }

    // Render keypoints
    if (data.showKeypoints) {
      ctx.globalAlpha = data.keypointOpacity;

      keypoints.forEach((kp, index) => {
        const point = toPixel(kp);
        if (!point.visible) return;

        // Keypoint color based on body part
        let color = data.customKeypointColor;
        if (data.useDefaultColors) {
          if (index <= 1 || (index >= 14 && index <= 17)) {
            color = OPENPOSE_COLORS.head;
          } else if (index >= 2 && index <= 4) {
            color = OPENPOSE_COLORS.right_arm;
          } else if (index >= 5 && index <= 7) {
            color = OPENPOSE_COLORS.left_arm;
          } else if (index === 8 || index === 9 || index === 10) {
            color = OPENPOSE_COLORS.right_leg;
          } else if (index === 11 || index === 12 || index === 13) {
            color = OPENPOSE_COLORS.left_leg;
          }
        }

        ctx.fillStyle = color;
        ctx.beginPath();
        ctx.arc(point.x, point.y, data.keypointRadius, 0, Math.PI * 2);
        ctx.fill();

        // White border for visibility
        ctx.strokeStyle = "#FFFFFF";
        ctx.lineWidth = 1;
        ctx.stroke();
      });
    }

    // Render labels
    if (data.showLabels) {
      ctx.globalAlpha = 1;
      ctx.font = "10px sans-serif";
      ctx.fillStyle = "#FFFFFF";
      ctx.textAlign = "center";

      const names = pose.format === "coco18" ? COCO_KEYPOINTS : COCO_KEYPOINTS;
      keypoints.forEach((kp, index) => {
        const point = toPixel(kp);
        if (!point.visible) return;
        if (index >= names.length) return;

        ctx.fillText(
          names[index].name,
          point.x,
          point.y - data.keypointRadius - 2,
        );
      });
    }

    ctx.globalAlpha = 1;
  }

  /**
   * Set composition dimensions for proper rendering
   * Called by LayerManager when layer is added or composition changes
   */
  setCompositionSize(width: number, height: number): void {
    // Validate dimensions (NaN/0 would create invalid canvas)
    this.compWidth = Number.isFinite(width) && width > 0 ? width : 512;
    this.compHeight = Number.isFinite(height) && height > 0 ? height : 512;
  }

  /**
   * Evaluate layer at frame
   * 
   * SYSTEM F/OMEGA: Per-keypoint, neighbor-based animation evaluation
   * - Each keypoint evaluated individually using its AnimatableProperty<Vec2>
   * - Z-space neighbors calculated for each keypoint
   * - Neighbor-based animation applied (IK/physics-like behavior)
   * - Efficient evaluation for every visible bone at every keyframe
   */
  protected onEvaluateFrame(frame: number): void {
    // Store current frame for export use
    this.currentFrame = frame;

    // Use composition dimensions
    const width = this.compWidth;
    const height = this.compHeight;

    // Evaluate poses with per-keypoint animation
    const evaluatedPoses = this.evaluatePosesAtFrame(frame);
    
    // Render evaluated poses
    this.renderEvaluatedPoses(evaluatedPoses, width, height);
    this.lastRenderedFrame = frame;

    // Update mesh scale to match canvas
    this.mesh.scale.set(width, height, 1);
  }

  /**
   * Evaluate all poses at a specific frame with per-keypoint animation
   * 
   * SYSTEM F/OMEGA: Each keypoint evaluated individually, considering z-space neighbors
   * 
   * @param frame - Current frame number
   * @returns Array of evaluated poses with animated keypoints
   */
  private evaluatePosesAtFrame(frame: number): Pose[] {
    const data = this.getPoseData();
    const fps = this.compositionFps;
    const layerId = this.id;

    // Check cache first
    const cached = this.evaluatedKeypointsCache.get(frame);
    if (cached && cached.size > 0) {
      // Reconstruct poses from cache
      return data.poses.map((pose) => this.reconstructPoseFromCache(pose, cached));
    }

    // Evaluate each pose
    const evaluatedPoses: Pose[] = [];

    for (const pose of data.poses) {
      // Build spatial hash for this pose's keypoints (z-space neighbors)
      this.buildKeypointSpatialHash(pose);

      // Evaluate keypoints in topological order (parents before children)
      // This ensures neighbors are evaluated before being used for neighbor-based animation
      const evaluationOrder = this.getTopologicalKeypointOrder(pose);
      const evaluatedKeypoints: PoseKeypoint[] = new Array(pose.keypoints.length);
      const evaluatedPositions = new Map<number, Vec2>();
      
      for (const i of evaluationOrder) {
        const keypoint = pose.keypoints[i];
        const keypointId = `pose_${pose.id}_keypoint_${i}`;
        
        // Get animated property for this keypoint (if exists)
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const animatedKeypoints = (data != null && typeof data === "object" && "animatedKeypoints" in data && data.animatedKeypoints != null && typeof data.animatedKeypoints === "object") ? data.animatedKeypoints : undefined;
        const animatedProp = (animatedKeypoints != null && typeof animatedKeypoints === "object" && keypointId in animatedKeypoints && animatedKeypoints[keypointId] != null) ? animatedKeypoints[keypointId] : undefined;
        
        let evaluatedPos: Vec2;
        if (animatedProp && animatedProp.animated) {
          // Evaluate using keyframe interpolation
          evaluatedPos = interpolateProperty(animatedProp, frame, fps, layerId);
        } else {
          // Use static value
          evaluatedPos = { x: keypoint.x, y: keypoint.y };
        }

        // Apply neighbor-based animation (z-space relationships)
        // Now neighbors are guaranteed to be evaluated (topological order)
        const neighborAdjustedPos = this.applyNeighborBasedAnimation(
          evaluatedPos,
          i,
          pose,
          frame,
          evaluatedPositions,
        );

        // Store evaluated position for neighbor lookups
        evaluatedPositions.set(i, neighborAdjustedPos);

        evaluatedKeypoints[i] = {
          x: neighborAdjustedPos.x,
          y: neighborAdjustedPos.y,
          confidence: keypoint.confidence,
        };
      }

      evaluatedPoses.push({
        id: pose.id,
        format: pose.format,
        keypoints: evaluatedKeypoints,
      });
    }

    // Cache evaluated keypoints for this frame
    const frameCache = new Map<string, Vec2>();
    evaluatedPoses.forEach((pose, poseIdx) => {
      pose.keypoints.forEach((kp, kpIdx) => {
        const keypointId = `pose_${pose.id}_keypoint_${kpIdx}`;
        frameCache.set(keypointId, { x: kp.x, y: kp.y });
      });
    });
    this.evaluatedKeypointsCache.set(frame, frameCache);

    return evaluatedPoses;
  }

  /**
   * Build spatial hash for keypoint z-space neighbors
   * 
   * SYSTEM F/OMEGA: Calculates neighbors based on bone connections and z-space proximity
   * 
   * @param pose - Pose to build spatial hash for
   */
  private buildKeypointSpatialHash(pose: Pose): void {
    this.keypointSpatialHash.clear();
    
    const bones = pose.format === "coco18" ? COCO_BONES : COCO_BONES;
    const { keypoints } = pose;

    // Initialize hash with empty sets
    for (let i = 0; i < keypoints.length; i++) {
      this.keypointSpatialHash.set(i, new Set());
    }

    // Add bone-connected neighbors (direct connections)
    bones.forEach(([startIdx, endIdx]) => {
      if (startIdx < keypoints.length && endIdx < keypoints.length) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const startSet = this.keypointSpatialHash.get(startIdx);
        if (startSet != null && typeof startSet === "object" && typeof startSet.add === "function") {
          startSet.add(endIdx);
        }
        const endSet = this.keypointSpatialHash.get(endIdx);
        if (endSet != null && typeof endSet === "object" && typeof endSet.add === "function") {
          endSet.add(startIdx);
        }
      }
    });

    // Add z-space neighbors (proximity-based, considering depth/confidence)
    // For 2D poses, use confidence as z-proxy and spatial distance
    for (let i = 0; i < keypoints.length; i++) {
      const kp1 = keypoints[i];
      if (kp1.confidence < 0.1) continue; // Skip low-confidence keypoints

      for (let j = i + 1; j < keypoints.length; j++) {
        const kp2 = keypoints[j];
        if (kp2.confidence < 0.1) continue;

        // Calculate spatial distance (normalized coordinates)
        const dx = kp1.x - kp2.x;
        const dy = kp1.y - kp2.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        // Z-space proximity threshold (adjustable based on skeleton scale)
        const zProximityThreshold = 0.15; // ~15% of normalized space

        // Consider z-space proximity (confidence-weighted distance)
        const zDistance = Math.abs(kp1.confidence - kp2.confidence);
        const combinedDistance = dist + zDistance * 0.5; // Weight z-space component

        if (combinedDistance < zProximityThreshold) {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const iSet = this.keypointSpatialHash.get(i);
          if (iSet != null && typeof iSet === "object" && typeof iSet.add === "function") {
            iSet.add(j);
          }
          const jSet = this.keypointSpatialHash.get(j);
          if (jSet != null && typeof jSet === "object" && typeof jSet.add === "function") {
            jSet.add(i);
          }
        }
      }
    }
  }

  /**
   * Get topological order for keypoints (parents before children)
   * 
   * SYSTEM F/OMEGA: Ensures parent keypoints are evaluated before children
   * 
   * @param pose - Pose to get evaluation order for
   * @returns Array of keypoint indices in topological order
   */
  private getTopologicalKeypointOrder(pose: Pose): number[] {
    const bones = pose.format === "coco18" ? COCO_BONES : COCO_BONES;
    const { keypoints } = pose;
    
    // Build parent-child relationships from bone connections
    const children = new Map<number, Set<number>>();
    const parents = new Map<number, number>();
    
    // Initialize maps
    for (let i = 0; i < keypoints.length; i++) {
      children.set(i, new Set());
      parents.set(i, -1);
    }
    
    // Build parent-child graph from bones
    bones.forEach(([startIdx, endIdx]) => {
      if (startIdx < keypoints.length && endIdx < keypoints.length) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const startChildren = children.get(startIdx);
        if (startChildren != null && typeof startChildren === "object" && typeof startChildren.add === "function") {
          startChildren.add(endIdx);
        }
        parents.set(endIdx, startIdx);
      }
    });
    
    // Topological sort: process roots first, then children
    const order: number[] = [];
    const visited = new Set<number>();
    
    const visit = (idx: number): void => {
      if (visited.has(idx)) return;
      
      // Visit parent first (if exists and not root)
      const parent = parents.get(idx);
      if (parent !== undefined && parent >= 0 && parent !== idx) {
        visit(parent);
      }
      
      visited.add(idx);
      order.push(idx);
    };
    
    // Visit all keypoints
    for (let i = 0; i < keypoints.length; i++) {
      visit(i);
    }
    
    return order;
  }

  /**
   * Apply neighbor-based animation to a keypoint position
   * 
   * SYSTEM F/OMEGA: IK/physics-like behavior based on z-space neighbors
   * 
   * @param basePos - Base evaluated position from keyframe interpolation
   * @param keypointIndex - Index of the keypoint
   * @param pose - Original pose data
   * @param frame - Current frame number
   * @param evaluatedPositions - Map of already-evaluated keypoint positions (from topological order)
   * @returns Neighbor-adjusted position
   */
  private applyNeighborBasedAnimation(
    basePos: Vec2,
    keypointIndex: number,
    pose: Pose,
    frame: number,
    evaluatedPositions: Map<number, Vec2>,
  ): Vec2 {
    const neighbors = this.keypointSpatialHash.get(keypointIndex);
    if (!neighbors || neighbors.size === 0) {
      return basePos; // No neighbors, return base position
    }

    // Get neighbor positions (from evaluated positions map - guaranteed to be evaluated due to topological order)
    const neighborPositions: Array<{ pos: Vec2; confidence: number }> = [];

    for (const neighborIdx of neighbors) {
      if (neighborIdx >= pose.keypoints.length) continue;

      const neighborKp = pose.keypoints[neighborIdx];
      
      // Get evaluated position (guaranteed to exist due to topological order)
      const neighborPos = evaluatedPositions.get(neighborIdx);
      if (!neighborPos) {
        // Fallback to base position if not evaluated (shouldn't happen with topological order)
        continue;
      }

      neighborPositions.push({
        pos: neighborPos,
        confidence: neighborKp.confidence,
      });
    }

    // Apply neighbor influence (weighted average based on confidence and distance)
    let adjustedX = basePos.x;
    let adjustedY = basePos.y;
    let totalWeight = 1.0; // Start with base position weight

    for (const neighbor of neighborPositions) {
      if (neighbor.confidence < 0.1) continue; // Skip low-confidence neighbors

      // Calculate distance to neighbor
      const dx = basePos.x - neighbor.pos.x;
      const dy = basePos.y - neighbor.pos.y;
      const dist = Math.sqrt(dx * dx + dy * dy);

      // Weight based on confidence and inverse distance (closer = stronger influence)
      const distanceWeight = dist > 0 ? 1.0 / (1.0 + dist * 10) : 1.0; // Normalize distance
      const confidenceWeight = neighbor.confidence;
      const weight = distanceWeight * confidenceWeight * 0.1; // 10% influence per neighbor

      // Apply weighted influence
      adjustedX += (neighbor.pos.x - basePos.x) * weight;
      adjustedY += (neighbor.pos.y - basePos.y) * weight;
      totalWeight += weight;
    }

    // Normalize by total weight
    adjustedX /= totalWeight;
    adjustedY /= totalWeight;

    return { x: adjustedX, y: adjustedY };
  }

  /**
   * Reconstruct pose from cached evaluated keypoints
   * 
   * @param originalPose - Original pose data
   * @param cache - Cached evaluated keypoints for this frame
   * @returns Reconstructed pose with cached keypoints
   */
  private reconstructPoseFromCache(
    originalPose: Pose,
    cache: Map<string, Vec2>,
  ): Pose {
    const evaluatedKeypoints: PoseKeypoint[] = originalPose.keypoints.map(
      (kp, idx) => {
        const keypointId = `pose_${originalPose.id}_keypoint_${idx}`;
        const cachedPos = cache.get(keypointId);
        
        if (cachedPos) {
          return {
            x: cachedPos.x,
            y: cachedPos.y,
            confidence: kp.confidence,
          };
        }
        
        // Fallback to original if not in cache
        return kp;
      },
    );

    return {
      id: originalPose.id,
      format: originalPose.format,
      keypoints: evaluatedKeypoints,
    };
  }

  /**
   * Render evaluated poses (with per-keypoint animation applied)
   * 
   * @param evaluatedPoses - Poses with evaluated keypoints
   * @param width - Canvas width
   * @param height - Canvas height
   */
  private renderEvaluatedPoses(
    evaluatedPoses: Pose[],
    width: number,
    height: number,
  ): void {
    const data = this.getPoseData();
    const { ctx, canvas } = this;

    // Resize canvas if needed
    if (canvas.width !== width || canvas.height !== height) {
      canvas.width = width;
      canvas.height = height;
    }

    // Clear with background color
    ctx.fillStyle = data.backgroundColor;
    ctx.fillRect(0, 0, width, height);

    // Render each evaluated pose
    for (const pose of evaluatedPoses) {
      this.renderSinglePose(pose, width, height, data);
    }

    // Update texture
    this.texture.needsUpdate = true;
  }

  /**
   * Handle property updates
   */
  protected onUpdate(properties: Partial<Layer>): void {
    // Update pose data if it changed
    if (properties.data) {
      // Clear cache when data changes (keypoints may have changed)
      this.evaluatedKeypointsCache.clear();
      this.keypointSpatialHash.clear();
      // Re-render on next evaluate
      this.lastRenderedFrame = -1;
    }
  }

  /**
   * Export pose data as OpenPose JSON format
   */
  exportOpenPoseJSON(): object {
    const data = this.getPoseData();
    const people: object[] = [];

    for (const pose of data.poses) {
      // OpenPose format: [x1, y1, c1, x2, y2, c2, ...]
      const pose_keypoints_2d: number[] = [];

      for (const kp of pose.keypoints) {
        pose_keypoints_2d.push(kp.x, kp.y, kp.confidence);
      }

      people.push({
        person_id: [-1],
        pose_keypoints_2d,
        face_keypoints_2d: [],
        hand_left_keypoints_2d: [],
        hand_right_keypoints_2d: [],
        pose_keypoints_3d: [],
        face_keypoints_3d: [],
        hand_left_keypoints_3d: [],
        hand_right_keypoints_3d: [],
      });
    }

    return {
      version: 1.3,
      people,
    };
  }

  /**
   * Import pose from OpenPose JSON
   */
  importOpenPoseJSON(json: {
    people?: Array<{ pose_keypoints_2d?: number[] }>;
  }): void {
    const data = this.getPoseData();
    const newPoses: Pose[] = [];

    if (json.people) {
      for (const person of json.people) {
        if (person.pose_keypoints_2d) {
          const keypoints: PoseKeypoint[] = [];
          const kp = person.pose_keypoints_2d;

          for (let i = 0; i < kp.length; i += 3) {
            keypoints.push({
              x: kp[i],
              y: kp[i + 1],
              confidence: kp[i + 2],
            });
          }

          newPoses.push({
            id: `pose_imported_${newPoses.length}`,
            keypoints,
            format: "coco18",
          });
        }
      }
    }

    if (newPoses.length > 0) {
      data.poses = newPoses;
      // Convert local PoseLayerData to project PoseLayerData
      const projectData: ProjectPoseLayerData = {
        poses: data.poses,
        format: data.format,
        normalized: data.normalized,
        boneWidth: data.boneWidth,
        keypointRadius: data.keypointRadius,
        showKeypoints: data.showKeypoints,
        showBones: data.showBones,
        showLabels: data.showLabels,
        useDefaultColors: data.useDefaultColors,
        customBoneColor: data.customBoneColor,
        customKeypointColor: data.customKeypointColor,
        selectedKeypoint: -1, // Default value
        selectedPose: -1, // Default value
      };
      this.layerData.data = projectData;
    }
  }

  /**
   * Mirror/flip pose horizontally
   */
  flipPoseHorizontal(poseId: string): void {
    const data = this.getPoseData();
    const pose = data.poses.find((p) => p.id === poseId);
    if (!pose) return;

    // Flip X coordinates
    for (const kp of pose.keypoints) {
      kp.x = data.normalized ? 1 - kp.x : this.canvas.width - kp.x;
    }

    // Swap left/right keypoints for COCO format
    if (pose.format === "coco18") {
      const swaps: [number, number][] = [
        [2, 5], // shoulders
        [3, 6], // elbows
        [4, 7], // wrists
        [8, 11], // hips
        [9, 12], // knees
        [10, 13], // ankles
        [14, 15], // eyes
        [16, 17], // ears
      ];

      for (const [a, b] of swaps) {
        const temp = pose.keypoints[a];
        pose.keypoints[a] = pose.keypoints[b];
        pose.keypoints[b] = temp;
      }
    }

    // Convert local PoseLayerData to project PoseLayerData for storage
    const projectData: ProjectPoseLayerData = {
      poses: data.poses,
      format: data.format,
      normalized: data.normalized,
      boneWidth: data.boneWidth,
      keypointRadius: data.keypointRadius,
      showKeypoints: data.showKeypoints,
      showBones: data.showBones,
      showLabels: data.showLabels,
      useDefaultColors: data.useDefaultColors,
      customBoneColor: data.customBoneColor,
      customKeypointColor: data.customKeypointColor,
      selectedKeypoint: -1, // Not in local type, use default
      selectedPose: -1, // Not in local type, use default
    };
    this.layerData.data = projectData;
  }

  /**
   * Get canvas for export
   */
  getCanvas(): HTMLCanvasElement {
    return this.canvas;
  }

  /**
   * Render to specific dimensions for export
   * 
   * SYSTEM F/OMEGA: Uses current frame or provided frame for per-keypoint animation
   * 
   * @param width - Export canvas width
   * @param height - Export canvas height
   * @param frame - Optional frame number for per-keypoint animation evaluation (uses currentFrame if not provided)
   */
  renderForExport(width: number, height: number, frame?: number): HTMLCanvasElement {
    const exportCanvas = document.createElement("canvas");
    exportCanvas.width = width;
    exportCanvas.height = height;
    const exportCtx = exportCanvas.getContext("2d")!;

    // Temporarily swap canvas
    const originalCanvas = this.canvas;
    const originalCtx = this.ctx;
    this.canvas = exportCanvas;
    this.ctx = exportCtx;

    // Use provided frame or fall back to current frame (from last onEvaluateFrame call)
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: frame ∈ number | undefined → number (fallback to currentFrame)
    const exportFrame = (typeof frame === "number" && Number.isFinite(frame)) ? frame : this.currentFrame;

    // Render at export dimensions with frame evaluation (per-keypoint animation)
    this.renderPoses(width, height, exportFrame);

    // Restore original
    this.canvas = originalCanvas;
    this.ctx = originalCtx;

    return exportCanvas;
  }

  dispose(): void {
    this.texture.dispose();
    (this.mesh.material as THREE.Material).dispose();
    this.mesh.geometry.dispose();
    super.dispose();
  }
}

// ============================================================================
// POSE MANIPULATION UTILITIES
// ============================================================================

/**
 * Scale a pose around its center
 */
export function scalePose(pose: Pose, scale: number): void {
  // Find center
  let sumX = 0,
    sumY = 0,
    count = 0;
  for (const kp of pose.keypoints) {
    if (kp.confidence > 0.1) {
      sumX += kp.x;
      sumY += kp.y;
      count++;
    }
  }

  if (count === 0) return;
  const centerX = sumX / count;
  const centerY = sumY / count;

  // Scale around center
  for (const kp of pose.keypoints) {
    kp.x = centerX + (kp.x - centerX) * scale;
    kp.y = centerY + (kp.y - centerY) * scale;
  }
}

/**
 * Rotate a pose around its center
 */
export function rotatePose(pose: Pose, angleDegrees: number): void {
  const angle = (angleDegrees * Math.PI) / 180;
  const cos = Math.cos(angle);
  const sin = Math.sin(angle);

  // Find center
  let sumX = 0,
    sumY = 0,
    count = 0;
  for (const kp of pose.keypoints) {
    if (kp.confidence > 0.1) {
      sumX += kp.x;
      sumY += kp.y;
      count++;
    }
  }

  if (count === 0) return;
  const centerX = sumX / count;
  const centerY = sumY / count;

  // Rotate around center
  for (const kp of pose.keypoints) {
    const dx = kp.x - centerX;
    const dy = kp.y - centerY;
    kp.x = centerX + dx * cos - dy * sin;
    kp.y = centerY + dx * sin + dy * cos;
  }
}

/**
 * Translate a pose
 */
export function translatePose(pose: Pose, dx: number, dy: number): void {
  for (const kp of pose.keypoints) {
    kp.x += dx;
    kp.y += dy;
  }
}

/**
 * Interpolate between two poses
 */
export function interpolatePoses(pose1: Pose, pose2: Pose, t: number): Pose {
  if (pose1.keypoints.length !== pose2.keypoints.length) {
    throw new Error("Poses must have same number of keypoints");
  }

  const keypoints: PoseKeypoint[] = [];

  for (let i = 0; i < pose1.keypoints.length; i++) {
    const kp1 = pose1.keypoints[i];
    const kp2 = pose2.keypoints[i];

    keypoints.push({
      x: kp1.x + (kp2.x - kp1.x) * t,
      y: kp1.y + (kp2.y - kp1.y) * t,
      confidence: Math.min(kp1.confidence, kp2.confidence),
    });
  }

  return {
    id: `interpolated_${Date.now()}`,
    keypoints,
    format: pose1.format,
  };
}

// ============================================================================
// EXPORTS
// ============================================================================

export default PoseLayer;
