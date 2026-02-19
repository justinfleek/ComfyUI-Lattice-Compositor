/**
 * ControlNet Pose Export Service
 *
 * Exports pose data for ControlNet conditioning:
 * - OpenPose JSON format
 * - Pose image sequences (black background, colored skeleton)
 * - DWPose/RTMW format support
 * - Multi-person batch export
 */

import {
  COCO_BONES,
  getBoneColor,
  interpolatePoses,
  OPENPOSE_COLORS,
  type Pose,
  type PoseFormat,
  type PoseKeypoint,
} from "@/engine/layers/PoseLayer";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export interface PoseExportConfig {
  /** Output dimensions */
  width: number;
  height: number;

  /** Frame range */
  startFrame: number;
  endFrame: number;

  /** Rendering style */
  boneWidth: number;
  keypointRadius: number;
  showKeypoints: boolean;
  showBones: boolean;

  /** Colors */
  useOpenPoseColors: boolean;
  customColor?: string;
  backgroundColor: string;

  /** Output format */
  outputFormat: "images" | "json" | "both";
}

export interface PoseFrame {
  frameNumber: number;
  poses: Pose[];
}

export interface PoseSequence {
  frames: PoseFrame[];
  format: PoseFormat;
  fps: number;
}

export interface OpenPoseJSON {
  version: number;
  people: Array<{
    person_id: number[];
    pose_keypoints_2d: number[];
    face_keypoints_2d: number[];
    hand_left_keypoints_2d: number[];
    hand_right_keypoints_2d: number[];
    pose_keypoints_3d: number[];
    face_keypoints_3d: number[];
    hand_left_keypoints_3d: number[];
    hand_right_keypoints_3d: number[];
  }>;
}

export interface PoseExportResult {
  /** Array of rendered canvases (one per frame) */
  images?: HTMLCanvasElement[];

  /** Array of OpenPose JSON objects (one per frame) */
  jsonFrames?: OpenPoseJSON[];

  /** Combined JSON with all frames */
  sequenceJson?: {
    frames: OpenPoseJSON[];
    metadata: {
      frameCount: number;
      fps: number;
      width: number;
      height: number;
    };
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                         // pose // rendering
// ════════════════════════════════════════════════════════════════════════════

/**
 * Render a single pose frame to canvas
 */
export function renderPoseFrame(
  poses: Pose[],
  config: PoseExportConfig,
): HTMLCanvasElement {
  const canvas = document.createElement("canvas");
  canvas.width = config.width;
  canvas.height = config.height;
  const ctx = canvas.getContext("2d")!;

  // Fill background
  ctx.fillStyle = config.backgroundColor;
  ctx.fillRect(0, 0, config.width, config.height);

  // Render each pose
  for (const pose of poses) {
    renderSinglePose(ctx, pose, config);
  }

  return canvas;
}

/**
 * Render a single skeleton
 */
function renderSinglePose(
  ctx: CanvasRenderingContext2D,
  pose: Pose,
  config: PoseExportConfig,
): void {
  const { keypoints } = pose;
  const { width, height } = config;

  // Convert normalized coords to pixels
  const toPixel = (
    kp: PoseKeypoint,
  ): { x: number; y: number; visible: boolean } => ({
    x: kp.x * width,
    y: kp.y * height,
    visible: kp.confidence > 0.1,
  });

  // Render bones
  if (config.showBones) {
    ctx.lineCap = "round";
    ctx.lineWidth = config.boneWidth;

    COCO_BONES.forEach((bone, boneIndex) => {
      const [startIdx, endIdx] = bone;
      if (startIdx >= keypoints.length || endIdx >= keypoints.length) return;

      const start = toPixel(keypoints[startIdx]);
      const end = toPixel(keypoints[endIdx]);

      if (!start.visible || !end.visible) return;

      ctx.strokeStyle = config.useOpenPoseColors
        ? getBoneColor(boneIndex)
        : config.customColor || "#FFFFFF";

      ctx.beginPath();
      ctx.moveTo(start.x, start.y);
      ctx.lineTo(end.x, end.y);
      ctx.stroke();
    });
  }

  // Render keypoints
  if (config.showKeypoints) {
    keypoints.forEach((kp, index) => {
      const point = toPixel(kp);
      if (!point.visible) return;

      let color = config.customColor || "#FFFFFF";
      if (config.useOpenPoseColors) {
        if (index <= 1 || (index >= 14 && index <= 17)) {
          color = OPENPOSE_COLORS.head;
        } else if (index >= 2 && index <= 4) {
          color = OPENPOSE_COLORS.right_arm;
        } else if (index >= 5 && index <= 7) {
          color = OPENPOSE_COLORS.left_arm;
        } else if ([8, 9, 10].includes(index)) {
          color = OPENPOSE_COLORS.right_leg;
        } else if ([11, 12, 13].includes(index)) {
          color = OPENPOSE_COLORS.left_leg;
        }
      }

      ctx.fillStyle = color;
      ctx.beginPath();
      ctx.arc(point.x, point.y, config.keypointRadius, 0, Math.PI * 2);
      ctx.fill();
    });
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                             // pose // sequence // animation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create an animated pose sequence from keyframe poses
 */
export function createPoseSequence(
  keyframePoses: Array<{ frame: number; poses: Pose[] }>,
  totalFrames: number,
  fps: number = 16,
): PoseSequence {
  const frames: PoseFrame[] = [];

  // Sort keyframes by frame number
  const sortedKeyframes = [...keyframePoses].sort((a, b) => a.frame - b.frame);

  for (let frameNum = 0; frameNum < totalFrames; frameNum++) {
    // Find surrounding keyframes
    let prevKf = sortedKeyframes[0];
    let nextKf = sortedKeyframes[sortedKeyframes.length - 1];

    for (let i = 0; i < sortedKeyframes.length - 1; i++) {
      if (
        sortedKeyframes[i].frame <= frameNum &&
        sortedKeyframes[i + 1].frame >= frameNum
      ) {
        prevKf = sortedKeyframes[i];
        nextKf = sortedKeyframes[i + 1];
        break;
      }
    }

    // Interpolate
    if (prevKf.frame === nextKf.frame || frameNum <= prevKf.frame) {
      frames.push({ frameNumber: frameNum, poses: prevKf.poses });
    } else if (frameNum >= nextKf.frame) {
      frames.push({ frameNumber: frameNum, poses: nextKf.poses });
    } else {
      const t = (frameNum - prevKf.frame) / (nextKf.frame - prevKf.frame);
      const interpolatedPoses: Pose[] = [];

      // Interpolate each pose
      const numPoses = Math.min(prevKf.poses.length, nextKf.poses.length);
      for (let i = 0; i < numPoses; i++) {
        interpolatedPoses.push(
          interpolatePoses(prevKf.poses[i], nextKf.poses[i], t),
        );
      }

      frames.push({ frameNumber: frameNum, poses: interpolatedPoses });
    }
  }

  return {
    frames,
    format: "coco18",
    fps,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // export // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Export pose sequence to OpenPose JSON format
 */
export function exportToOpenPoseJSON(poses: Pose[]): OpenPoseJSON {
  const people = poses.map((pose) => {
    const pose_keypoints_2d: number[] = [];

    for (const kp of pose.keypoints) {
      pose_keypoints_2d.push(kp.x, kp.y, kp.confidence);
    }

    return {
      person_id: [-1],
      pose_keypoints_2d,
      face_keypoints_2d: [],
      hand_left_keypoints_2d: [],
      hand_right_keypoints_2d: [],
      pose_keypoints_3d: [],
      face_keypoints_3d: [],
      hand_left_keypoints_3d: [],
      hand_right_keypoints_3d: [],
    };
  });

  return {
    version: 1.3,
    people,
  };
}

/**
 * Export full pose sequence
 */
export function exportPoseSequence(
  sequence: PoseSequence,
  config: PoseExportConfig,
): PoseExportResult {
  const result: PoseExportResult = {};

  // Filter frames by range
  const framesToExport = sequence.frames.filter(
    (f) =>
      f.frameNumber >= config.startFrame && f.frameNumber <= config.endFrame,
  );

  // Export images
  if (config.outputFormat === "images" || config.outputFormat === "both") {
    result.images = framesToExport.map((frame) =>
      renderPoseFrame(frame.poses, config),
    );
  }

  // Export JSON
  if (config.outputFormat === "json" || config.outputFormat === "both") {
    result.jsonFrames = framesToExport.map((frame) =>
      exportToOpenPoseJSON(frame.poses),
    );

    result.sequenceJson = {
      frames: result.jsonFrames,
      metadata: {
        frameCount: framesToExport.length,
        fps: sequence.fps,
        width: config.width,
        height: config.height,
      },
    };
  }

  return result;
}

/**
 * Export single frame for ControlNet
 */
export function exportPoseForControlNet(
  poses: Pose[],
  width: number,
  height: number,
): { canvas: HTMLCanvasElement; json: OpenPoseJSON } {
  const config: PoseExportConfig = {
    width,
    height,
    startFrame: 0,
    endFrame: 0,
    boneWidth: 4,
    keypointRadius: 4,
    showKeypoints: true,
    showBones: true,
    useOpenPoseColors: true,
    backgroundColor: "#000000",
    outputFormat: "both",
  };

  return {
    canvas: renderPoseFrame(poses, config),
    json: exportToOpenPoseJSON(poses),
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // import // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Import pose from OpenPose JSON
 */
export function importFromOpenPoseJSON(json: OpenPoseJSON): Pose[] {
  const poses: Pose[] = [];

  for (const person of json.people) {
    if (person.pose_keypoints_2d && person.pose_keypoints_2d.length > 0) {
      const keypoints: PoseKeypoint[] = [];
      const kp = person.pose_keypoints_2d;

      for (let i = 0; i < kp.length; i += 3) {
        keypoints.push({
          x: kp[i],
          y: kp[i + 1],
          confidence: kp[i + 2],
        });
      }

      poses.push({
        id: `imported_${Date.now()}_${poses.length}`,
        keypoints,
        format: "coco18",
      });
    }
  }

  return poses;
}

/**
 * Import pose sequence from array of OpenPose JSON
 */
export function importPoseSequence(
  jsonFrames: OpenPoseJSON[],
  fps: number = 16,
): PoseSequence {
  const frames: PoseFrame[] = jsonFrames.map((json, index) => ({
    frameNumber: index,
    poses: importFromOpenPoseJSON(json),
  }));

  return {
    frames,
    format: "coco18",
    fps,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                         // default // config
// ════════════════════════════════════════════════════════════════════════════

export function createDefaultPoseExportConfig(): PoseExportConfig {
  return {
    width: 512,
    height: 512,
    startFrame: 0,
    endFrame: 80,
    boneWidth: 4,
    keypointRadius: 4,
    showKeypoints: true,
    showBones: true,
    useOpenPoseColors: true,
    backgroundColor: "#000000",
    outputFormat: "both",
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // exports
// ════════════════════════════════════════════════════════════════════════════

export default {
  renderPoseFrame,
  createPoseSequence,
  exportToOpenPoseJSON,
  exportPoseSequence,
  exportPoseForControlNet,
  importFromOpenPoseJSON,
  importPoseSequence,
  createDefaultPoseExportConfig,
};
