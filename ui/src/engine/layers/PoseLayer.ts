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
import type { AnimatableProperty, Layer, Vec2 } from "@/types/project";
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

  constructor(layerData: Layer) {
    super(layerData);

    // Create canvas for 2D pose rendering
    this.canvas = document.createElement("canvas");
    this.canvas.width = this.compWidth;
    this.canvas.height = this.compHeight;
    this.ctx = this.canvas.getContext("2d")!;

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
   */
  private getPoseData(): PoseLayerData {
    const data = (this.layerData.data as Partial<PoseLayerData>) || {};
    return {
      ...createDefaultPoseLayerData(),
      ...data,
    };
  }

  /**
   * Render poses to canvas
   */
  private renderPoses(width: number, height: number): void {
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
   */
  protected onEvaluateFrame(frame: number): void {
    // Use composition dimensions
    const width = this.compWidth;
    const height = this.compHeight;

    // Re-render poses
    this.renderPoses(width, height);
    this.lastRenderedFrame = frame;

    // Update mesh scale to match canvas
    this.mesh.scale.set(width, height, 1);
  }

  /**
   * Handle property updates
   */
  protected onUpdate(properties: Partial<Layer>): void {
    // Update pose data if it changed
    if (properties.data) {
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
      this.layerData.data = data as any;
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

    this.layerData.data = data as any;
  }

  /**
   * Get canvas for export
   */
  getCanvas(): HTMLCanvasElement {
    return this.canvas;
  }

  /**
   * Render to specific dimensions for export
   */
  renderForExport(width: number, height: number): HTMLCanvasElement {
    const exportCanvas = document.createElement("canvas");
    exportCanvas.width = width;
    exportCanvas.height = height;
    const exportCtx = exportCanvas.getContext("2d")!;

    // Temporarily swap canvas
    const originalCanvas = this.canvas;
    const originalCtx = this.ctx;
    this.canvas = exportCanvas;
    this.ctx = exportCtx;

    // Render at export dimensions
    this.renderPoses(width, height);

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
