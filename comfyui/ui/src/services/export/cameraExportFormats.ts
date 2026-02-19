/**
 * Camera Export Formats
 * Export camera animations to various AI video generation formats
 */

import { isFiniteNumber, hasXY } from "@/utils/typeGuards";
import { focalLengthToFOV } from "@/services/math3d";
import type { Camera3D, CameraKeyframe } from "@/types/camera";
import type {
  CameraCtrlMotionType,
  CameraCtrlPoses,
  FullCameraExport,
  FullCameraFrame,
  MotionCtrlCameraData,
  MotionCtrlPose,
  MotionCtrlSVDCameraData,
  MotionCtrlSVDPreset,
  Uni3CCameraData,
  Uni3CCameraTrajectory,
  Uni3CTrajType,
  Wan22CameraMotion,
  Wan22FunCameraData,
} from "@/types/export";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Camera Interpolation
// ═══════════════════════════════════════════════════════════════════════════

interface InterpolatedCamera {
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  focalLength: number;
  zoom: number;
  focusDistance: number;
}

/**
 * Interpolate camera properties at a specific frame
 */
export function interpolateCameraAtFrame(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frame: number,
): InterpolatedCamera {
  if (!keyframes || keyframes.length === 0) {
    return {
      position: camera.position,
      rotation: camera.orientation,
      focalLength: camera.focalLength,
      zoom: camera.zoom,
      focusDistance: camera.depthOfField.focusDistance,
    };
  }

  // Find surrounding keyframes
  let prev: CameraKeyframe | null = null;
  let next: CameraKeyframe | null = null;

  for (const kf of keyframes) {
    if (kf.frame <= frame) {
      prev = kf;
    }
    if (kf.frame >= frame && !next) {
      next = kf;
    }
  }

  // If no keyframes found, use camera defaults
  if (!prev && !next) {
    return {
      position: camera.position,
      rotation: camera.orientation,
      focalLength: camera.focalLength,
      zoom: camera.zoom,
      focusDistance: camera.depthOfField.focusDistance,
    };
  }

  // If only one keyframe or same frame
  if (!prev) prev = next;
  if (!next) next = prev;

  // Helper to get value with fallback
  // Type proof: position ∈ {x, y, z} | undefined → {x, y, z}
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const getPos = (kf: CameraKeyframe | null | undefined) => {
    const posValue = (kf != null && typeof kf === "object" && "position" in kf && kf.position != null && typeof kf.position === "object") ? kf.position : undefined;
    return hasXY(posValue) && isFiniteNumber(posValue.z) ? posValue : camera.position;
  };
  const getOri = (kf: CameraKeyframe | null | undefined) => {
    const oriValue = (kf != null && typeof kf === "object" && "orientation" in kf && kf.orientation != null && typeof kf.orientation === "object") ? kf.orientation : undefined;
    return hasXY(oriValue) && isFiniteNumber(oriValue.z) ? oriValue : camera.orientation;
  };
  // Type proof: focalLength ∈ ℝ ∪ {undefined} → ℝ
  const getFocal = (kf: CameraKeyframe | null | undefined) => {
    const focalValue = (kf != null && typeof kf === "object" && "focalLength" in kf && typeof kf.focalLength === "number") ? kf.focalLength : undefined;
    return isFiniteNumber(focalValue) && focalValue > 0 ? focalValue : camera.focalLength;
  };
  const getZoom = (kf: CameraKeyframe | null | undefined) => {
    const zoomValue = (kf != null && typeof kf === "object" && "zoom" in kf && typeof kf.zoom === "number") ? kf.zoom : undefined;
    return isFiniteNumber(zoomValue) && zoomValue > 0 ? zoomValue : camera.zoom;
  };
  const getFocusDist = (kf: CameraKeyframe | null | undefined) => {
    const focusValue = (kf != null && typeof kf === "object" && "focusDistance" in kf && typeof kf.focusDistance === "number") ? kf.focusDistance : undefined;
    return isFiniteNumber(focusValue) && focusValue > 0 ? focusValue : camera.depthOfField.focusDistance;
  };

  // Interpolate
  // Type proof: frame ∈ ℕ ∪ {undefined} → ℕ
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const prevFrameValue = (prev != null && typeof prev === "object" && "frame" in prev && typeof prev.frame === "number") ? prev.frame : undefined;
  const prevFrame = isFiniteNumber(prevFrameValue) && Number.isInteger(prevFrameValue) && prevFrameValue >= 0 ? prevFrameValue : 0;
  const nextFrameValue = (next != null && typeof next === "object" && "frame" in next && typeof next.frame === "number") ? next.frame : undefined;
  const nextFrame = isFiniteNumber(nextFrameValue) && Number.isInteger(nextFrameValue) && nextFrameValue >= 0 ? nextFrameValue : prevFrame;
  
  // Early return if frames are identical
  if (prevFrame === nextFrame) {
    return {
      position: getPos(prev),
      rotation: getOri(prev),
      focalLength: getFocal(prev),
      zoom: getZoom(prev),
      focusDistance: getFocusDist(prev),
    };
  }
  const t = nextFrame === prevFrame ? 0 : (frame - prevFrame) / (nextFrame - prevFrame);

  const prevPos = getPos(prev);
  const nextPos = getPos(next);
  const prevOri = getOri(prev);
  const nextOri = getOri(next);

  return {
    position: {
      x: lerp(prevPos.x, nextPos.x, t),
      y: lerp(prevPos.y, nextPos.y, t),
      z: lerp(prevPos.z, nextPos.z, t),
    },
    rotation: {
      x: lerpAngle(prevOri.x, nextOri.x, t),
      y: lerpAngle(prevOri.y, nextOri.y, t),
      z: lerpAngle(prevOri.z, nextOri.z, t),
    },
    focalLength: lerp(getFocal(prev), getFocal(next), t),
    zoom: lerp(getZoom(prev), getZoom(next), t),
    focusDistance: lerp(getFocusDist(prev), getFocusDist(next), t),
  };
}

function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

function lerpAngle(a: number, b: number, t: number): number {
  // Handle angle wrapping - take the shortest path around the circle
  let diff = b - a;
  if (diff > 180) diff -= 360;
  if (diff < -180) diff += 360;
  let result = a + diff * t;
  // Normalize result to [0, 360] range for camera exports
  // Note: 360 is kept as-is (equivalent to 0) for compatibility
  while (result > 360) result -= 360;
  while (result < 0) result += 360;
  return result;
}

// ═══════════════════════════════════════════════════════════════════════════
// Matrix Utilities
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Compute 4x4 view matrix from camera state
 */
export function computeViewMatrix(cam: InterpolatedCamera): number[][] {
  const { position, rotation } = cam;

  // Guard against NaN/Infinity from invalid keyframe interpolation or corrupted
  // camera state. NaN values would propagate through matrix math and produce
  // an invalid view matrix. Fallback to identity-like values (0) for safety.
  const rotX = Number.isFinite(rotation.x) ? rotation.x : 0;
  const rotY = Number.isFinite(rotation.y) ? rotation.y : 0;
  const rotZ = Number.isFinite(rotation.z) ? rotation.z : 0;
  const posX = Number.isFinite(position.x) ? position.x : 0;
  const posY = Number.isFinite(position.y) ? position.y : 0;
  const posZ = Number.isFinite(position.z) ? position.z : 0;

  // Convert degrees to radians
  const rx = (rotX * Math.PI) / 180;
  const ry = (rotY * Math.PI) / 180;
  const rz = (rotZ * Math.PI) / 180;

  // Rotation matrices
  const cosX = Math.cos(rx),
    sinX = Math.sin(rx);
  const cosY = Math.cos(ry),
    sinY = Math.sin(ry);
  const cosZ = Math.cos(rz),
    sinZ = Math.sin(rz);

  // Combined rotation (Y * X * Z order)
  const r00 = cosY * cosZ + sinY * sinX * sinZ;
  const r01 = -cosY * sinZ + sinY * sinX * cosZ;
  const r02 = sinY * cosX;

  const r10 = cosX * sinZ;
  const r11 = cosX * cosZ;
  const r12 = -sinX;

  const r20 = -sinY * cosZ + cosY * sinX * sinZ;
  const r21 = sinY * sinZ + cosY * sinX * cosZ;
  const r22 = cosY * cosX;

  // View matrix = inverse of camera transform
  // For orthonormal rotation, inverse is transpose
  // Translation is -R^T * position (using validated position values)
  const tx = -(r00 * posX + r10 * posY + r20 * posZ);
  const ty = -(r01 * posX + r11 * posY + r21 * posZ);
  const tz = -(r02 * posX + r12 * posY + r22 * posZ);

  return [
    [r00, r01, r02, tx],
    [r10, r11, r12, ty],
    [r20, r21, r22, tz],
    [0, 0, 0, 1],
  ];
}

/**
 * Compute projection matrix
 */
export function computeProjectionMatrix(
  cam: InterpolatedCamera,
  aspectRatio: number,
  nearClip: number = 0.1,
  farClip: number = 1000,
): number[][] {
  // Aspect ratio must be positive and finite for valid projection matrix
  if (!Number.isFinite(aspectRatio) || aspectRatio <= 0) {
    throw new Error(
      `Invalid aspectRatio: ${aspectRatio}. Must be a positive finite number.`,
    );
  }

  // Ensure clip planes are valid to prevent NaN in perspective division.
  // Near must be positive, far must be greater than near.
  let validNear = nearClip;
  let validFar = farClip;

  if (!Number.isFinite(nearClip) || nearClip <= 0) {
    console.warn(
      `Invalid nearClip: ${nearClip}. Using fallback value 0.1.`,
    );
    validNear = 0.1;
  }

  if (!Number.isFinite(farClip) || farClip <= validNear) {
    console.warn(
      `Invalid farClip: ${farClip} (must be > nearClip ${validNear}). Using fallback value 1000.`,
    );
    validFar = 1000;
  }

  // Default to 50mm focal length (standard lens) if value is invalid
  let focalLength = cam.focalLength;
  if (!Number.isFinite(cam.focalLength)) {
    console.warn(
      `Invalid focalLength: ${cam.focalLength}. Using fallback value 50mm.`,
    );
    focalLength = 50;
  }

  // focalLengthToFOV returns radians - do NOT convert again!
  const fovRad = focalLengthToFOV(focalLength, 36); // 36mm film, returns radians
  const tanHalfFov = Math.tan(fovRad / 2);

  // Handle edge case where tanHalfFov could be 0 or very small
  const f = tanHalfFov > 0.001 ? 1 / tanHalfFov : 1000;
  const nf = 1 / (validNear - validFar);

  return [
    [f / aspectRatio, 0, 0, 0],
    [0, f, 0, 0],
    [0, 0, (validFar + validNear) * nf, 2 * validFar * validNear * nf],
    [0, 0, -1, 0],
  ];
}

// ═══════════════════════════════════════════════════════════════════════════
// MotionCtrl Format Export
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Export camera animation to MotionCtrl format (4x4 RT matrices)
 */
export function exportToMotionCtrl(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
): MotionCtrlCameraData {
  const poses: MotionCtrlPose[] = [];

  for (let frame = 0; frame < frameCount; frame++) {
    const interpolated = interpolateCameraAtFrame(camera, keyframes, frame);
    const viewMatrix = computeViewMatrix(interpolated);

    poses.push({
      RT: viewMatrix,
    });
  }

  return { camera_poses: poses };
}

/**
 * Detect best MotionCtrl-SVD preset from keyframes
 */
export function detectMotionCtrlSVDPreset(
  keyframes: CameraKeyframe[],
): MotionCtrlSVDPreset {
  if (!keyframes || keyframes.length < 2) return "static";

  const first = keyframes[0];
  const last = keyframes[keyframes.length - 1];

  // Get positions and orientations with defaults
  // Type proof: position, orientation ∈ {x, y, z} | undefined → {x, y, z}
  const firstPosValue = first.position;
  const firstPos = hasXY(firstPosValue) && isFiniteNumber(firstPosValue.z) ? firstPosValue : { x: 0, y: 0, z: 0 };
  const lastPosValue = last.position;
  const lastPos = hasXY(lastPosValue) && isFiniteNumber(lastPosValue.z) ? lastPosValue : { x: 0, y: 0, z: 0 };
  const firstOriValue = first.orientation;
  const firstOri = hasXY(firstOriValue) && isFiniteNumber(firstOriValue.z) ? firstOriValue : { x: 0, y: 0, z: 0 };
  const lastOriValue = last.orientation;
  const lastOri = hasXY(lastOriValue) && isFiniteNumber(lastOriValue.z) ? lastOriValue : { x: 0, y: 0, z: 0 };

  const deltaX = lastPos.x - firstPos.x;
  const deltaY = lastPos.y - firstPos.y;
  const deltaZ = lastPos.z - firstPos.z;
  const deltaRy = lastOri.y - firstOri.y;

  const threshold = 50; // Movement threshold

  // Detect zoom by comparing distance from origin rather than raw Z delta.
  // This correctly handles cameras positioned on either side of the origin -
  // "zoom in" means moving closer to the scene (origin), regardless of
  // whether the camera starts at positive or negative Z.
  if (Math.abs(deltaZ) > threshold) {
    const distStart = Math.abs(firstPos.z);
    const distEnd = Math.abs(lastPos.z);
    return distEnd < distStart ? "zoom_in" : "zoom_out";
  }

  // Check for rotation
  if (Math.abs(deltaRy) > 15) {
    return deltaRy > 0 ? "rotate_cw" : "rotate_ccw";
  }

  // Check for pan
  if (Math.abs(deltaX) > threshold) {
    return deltaX > 0 ? "pan_right" : "pan_left";
  }

  if (Math.abs(deltaY) > threshold) {
    return deltaY > 0 ? "pan_down" : "pan_up";
  }

  return "static";
}

/**
 * Export to MotionCtrl-SVD format
 */
export function exportToMotionCtrlSVD(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
): MotionCtrlSVDCameraData {
  const preset = detectMotionCtrlSVDPreset(keyframes);

  if (preset !== "static" && keyframes.length <= 2) {
    // Use preset for simple motions
    return { motion_camera: preset };
  }

  // Export full poses for complex motions
  const motionctrlData = exportToMotionCtrl(camera, keyframes, frameCount);

  return {
    motion_camera: preset,
    camera_poses: JSON.stringify(motionctrlData.camera_poses),
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Wan 2.2 Fun Camera Format
// ═══════════════════════════════════════════════════════════════════════════

interface CameraMotionAnalysis {
  hasPan: boolean;
  panDirection?: "up" | "down" | "left" | "right";
  panMagnitude: number;
  hasZoom: boolean;
  zoomDirection?: "in" | "out";
  zoomMagnitude: number;
  hasOrbit: boolean;
  orbitDirection?: "left" | "right";
  orbitMagnitude: number;
  hasRotation: boolean;
  rotationMagnitude: number;
}

/**
 * Analyze camera motion pattern from keyframes
 */
export function analyzeCameraMotion(
  keyframes: CameraKeyframe[],
): CameraMotionAnalysis {
  if (!keyframes || keyframes.length < 2) {
    return {
      hasPan: false,
      panMagnitude: 0,
      hasZoom: false,
      zoomMagnitude: 0,
      hasOrbit: false,
      orbitMagnitude: 0,
      hasRotation: false,
      rotationMagnitude: 0,
    };
  }

  const first = keyframes[0];
  const last = keyframes[keyframes.length - 1];

  // Get positions and orientations with defaults
  // Type proof: position, orientation ∈ {x, y, z} | undefined → {x, y, z}
  const firstPosValue = first.position;
  const firstPos = hasXY(firstPosValue) && isFiniteNumber(firstPosValue.z) ? firstPosValue : { x: 0, y: 0, z: 0 };
  const lastPosValue = last.position;
  const lastPos = hasXY(lastPosValue) && isFiniteNumber(lastPosValue.z) ? lastPosValue : { x: 0, y: 0, z: 0 };
  const firstOriValue = first.orientation;
  const firstOri = hasXY(firstOriValue) && isFiniteNumber(firstOriValue.z) ? firstOriValue : { x: 0, y: 0, z: 0 };
  const lastOriValue = last.orientation;
  const lastOri = hasXY(lastOriValue) && isFiniteNumber(lastOriValue.z) ? lastOriValue : { x: 0, y: 0, z: 0 };

  const deltaX = lastPos.x - firstPos.x;
  const deltaY = lastPos.y - firstPos.y;
  const deltaZ = lastPos.z - firstPos.z;
  const deltaRy = lastOri.y - firstOri.y;

  // Thresholds
  const panThreshold = 30;
  const zoomThreshold = 50;
  const orbitThreshold = 20;

  // Determine pan
  let panDirection: "up" | "down" | "left" | "right" | undefined;
  const panX = Math.abs(deltaX);
  const panY = Math.abs(deltaY);

  if (panX > panThreshold || panY > panThreshold) {
    if (panX > panY) {
      panDirection = deltaX > 0 ? "right" : "left";
    } else {
      panDirection = deltaY > 0 ? "down" : "up";
    }
  }

  // Determine zoom
  let zoomDirection: "in" | "out" | undefined;
  if (Math.abs(deltaZ) > zoomThreshold) {
    zoomDirection = deltaZ < 0 ? "in" : "out";
  }

  // Determine orbit (rotation around Y with position change)
  let orbitDirection: "left" | "right" | undefined;
  if (Math.abs(deltaRy) > orbitThreshold && Math.abs(deltaX) > panThreshold) {
    orbitDirection = deltaRy > 0 ? "right" : "left";
  }

  return {
    hasPan: !!panDirection,
    panDirection,
    panMagnitude: Math.max(panX, panY),
    hasZoom: !!zoomDirection,
    zoomDirection,
    zoomMagnitude: Math.abs(deltaZ),
    hasOrbit: !!orbitDirection,
    orbitDirection,
    orbitMagnitude: Math.abs(deltaRy),
    hasRotation: Math.abs(deltaRy) > 5,
    rotationMagnitude: Math.abs(deltaRy),
  };
}

/**
 * Map compositor camera motion to Wan 2.2 Fun Camera preset
 */
export function mapToWan22FunCamera(
  keyframes: CameraKeyframe[],
): Wan22FunCameraData {
  const motion = analyzeCameraMotion(keyframes);

  let preset: Wan22CameraMotion = "Static";

  // Priority: Orbit > Zoom+Pan > Zoom > Pan
  if (motion.hasOrbit) {
    preset =
      motion.orbitDirection === "left" ? "Orbital Left" : "Orbital Right";
  } else if (motion.hasZoom && motion.hasPan) {
    const panDir = capitalize(motion.panDirection || "up");
    const zoomDir = motion.zoomDirection === "in" ? "Zoom In" : "Zoom Out";
    preset = `Pan ${panDir} + ${zoomDir}` as Wan22CameraMotion;
  } else if (motion.hasZoom) {
    preset = motion.zoomDirection === "in" ? "Zoom In" : "Zoom Out";
  } else if (motion.hasPan) {
    preset =
      `Pan ${capitalize(motion.panDirection || "up")}` as Wan22CameraMotion;
  }

  return { camera_motion: preset };
}

function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1);
}

// ═══════════════════════════════════════════════════════════════════════════
// Uni3C Camera Format
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Detect Uni3C trajectory type from keyframes
 */
export function detectUni3CTrajectoryType(
  keyframes: CameraKeyframe[],
): Uni3CTrajType {
  const motion = analyzeCameraMotion(keyframes);

  if (motion.hasOrbit && motion.orbitMagnitude > 45) {
    return "orbit";
  }

  if (motion.hasPan && motion.hasZoom) {
    // Complex motion -> custom
    return "custom";
  }

  // Simple motions might match presets
  if (!motion.hasPan && !motion.hasZoom && !motion.hasOrbit) {
    return "free1"; // Minimal motion
  }

  return "custom";
}

/**
 * Export camera animation to Uni3C format
 *
 * @deprecated This export format is non-functional with current Uni3C models.
 * The trajectory format does not match the expected input structure.
 * Use exportToCameraCtrl or exportToMotionCtrl instead.
 */
export function exportToUni3C(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
  compWidth: number,
  compHeight: number,
): Uni3CCameraData {
  console.warn(
    "exportToUni3C is non-functional with current Uni3C models. " +
      "Consider using exportToCameraCtrl or exportToMotionCtrl instead.",
  );

  const detectedType = detectUni3CTrajectoryType(keyframes);

  if (detectedType !== "custom") {
    return { traj_type: detectedType };
  }

  // Generate custom trajectory
  const trajectory: Uni3CCameraTrajectory[] = [];
  const baseCamera = interpolateCameraAtFrame(camera, keyframes, 0);

  for (let frame = 0; frame < frameCount; frame++) {
    const cam = interpolateCameraAtFrame(camera, keyframes, frame);

    trajectory.push({
      zoom: cam.zoom / baseCamera.zoom,
      x_offset: (cam.position.x - baseCamera.position.x) / compWidth,
      y_offset: (cam.position.y - baseCamera.position.y) / compHeight,
      z_offset: (cam.position.z - baseCamera.position.z) / 1000,
      pitch: cam.rotation.x,
      yaw: cam.rotation.y,
      roll: cam.rotation.z,
    });
  }

  return {
    traj_type: "custom",
    custom_trajectory: trajectory,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// AnimateDiff CameraCtrl Format
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Detect AnimateDiff CameraCtrl motion type
 */
export function detectCameraCtrlMotionType(
  keyframes: CameraKeyframe[],
): CameraCtrlMotionType {
  const motion = analyzeCameraMotion(keyframes);

  if (!motion.hasPan && !motion.hasZoom && !motion.hasRotation) {
    return "Static";
  }

  // Check zoom
  if (motion.hasZoom) {
    return motion.zoomDirection === "in" ? "Move Forward" : "Move Backward";
  }

  // Check pan
  if (motion.hasPan) {
    switch (motion.panDirection) {
      case "left":
        return "Move Left";
      case "right":
        return "Move Right";
      case "up":
        return "Move Up";
      case "down":
        return "Move Down";
    }
  }

  // Check rotation
  if (motion.hasRotation) {
    const first = keyframes[0];
    const last = keyframes[keyframes.length - 1];

    // Type proof: orientation ∈ {x, y, z} | undefined → {x, y, z}
    const firstOriValue = first.orientation;
    const firstOri = hasXY(firstOriValue) && isFiniteNumber(firstOriValue.z) ? firstOriValue : { x: 0, y: 0, z: 0 };
    const lastOriValue = last.orientation;
    const lastOri = hasXY(lastOriValue) && isFiniteNumber(lastOriValue.z) ? lastOriValue : { x: 0, y: 0, z: 0 };

    const deltaRx = lastOri.x - firstOri.x;
    const deltaRy = lastOri.y - firstOri.y;
    const deltaRz = lastOri.z - firstOri.z;

    if (
      Math.abs(deltaRy) > Math.abs(deltaRx) &&
      Math.abs(deltaRy) > Math.abs(deltaRz)
    ) {
      return deltaRy > 0 ? "Rotate Right" : "Rotate Left";
    }
    if (Math.abs(deltaRx) > Math.abs(deltaRz)) {
      return deltaRx > 0 ? "Rotate Down" : "Rotate Up";
    }
    return deltaRz > 0 ? "Roll Right" : "Roll Left";
  }

  return "Static";
}

/**
 * Export to AnimateDiff CameraCtrl format
 */
export function exportToCameraCtrl(
  keyframes: CameraKeyframe[],
  frameCount: number,
): CameraCtrlPoses {
  const motionType = detectCameraCtrlMotionType(keyframes);

  // Calculate speed based on motion magnitude
  const motion = analyzeCameraMotion(keyframes);
  let speed = 0;

  if (motion.hasZoom) {
    speed = Math.min(100, motion.zoomMagnitude / 5);
  } else if (motion.hasPan) {
    speed = Math.min(100, motion.panMagnitude / 3);
  } else if (motion.hasRotation) {
    speed = Math.min(100, motion.rotationMagnitude * 2);
  }

  return {
    motion_type: motionType,
    speed: Math.round(speed),
    frame_length: frameCount,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Full Camera Export (Generic Format)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Export camera with full 4x4 matrices for generic/custom use
 */
export function exportCameraMatrices(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  options: {
    frameCount: number;
    width: number;
    height: number;
    fps: number;
  },
): FullCameraExport {
  const { width, height, fps, frameCount } = options;

  // Validate dimensions - throw for any invalid value (zero, negative, NaN, Infinity)
  if (!Number.isFinite(width) || width <= 0) {
    throw new Error(
      `Invalid dimensions: ${width}x${height}. Width and height must be positive finite numbers.`,
    );
  }
  if (!Number.isFinite(height) || height <= 0) {
    throw new Error(
      `Invalid dimensions: ${width}x${height}. Width and height must be positive finite numbers.`,
    );
  }

  // Validate FPS - throw for any invalid value
  if (!Number.isFinite(fps) || fps <= 0) {
    throw new Error(
      `Invalid fps: ${fps}. FPS must be a positive finite number.`,
    );
  }

  // Validate frame count - throw for any invalid value
  if (!Number.isFinite(frameCount) || frameCount < 1) {
    throw new Error(
      `Invalid frameCount: ${frameCount}. Frame count must be at least 1.`,
    );
  }

  const frames: FullCameraFrame[] = [];
  const aspectRatio = width / height;

  for (let frame = 0; frame < frameCount; frame++) {
    const cam = interpolateCameraAtFrame(camera, keyframes, frame);

    const viewMatrix = computeViewMatrix(cam);
    const projMatrix = computeProjectionMatrix(cam, aspectRatio);

    frames.push({
      frame,
      timestamp: frame / fps,
      view_matrix: viewMatrix,
      projection_matrix: projMatrix,
      position: [cam.position.x, cam.position.y, cam.position.z],
      rotation: [cam.rotation.x, cam.rotation.y, cam.rotation.z],
      fov: focalLengthToFOV(cam.focalLength, camera.filmSize),
      focal_length: cam.focalLength,
      focus_distance: cam.focusDistance,
    });
  }

  return {
    frames,
    metadata: {
      width,
      height,
      fps,
      total_frames: frameCount,
      camera_type: camera.type,
      film_size: camera.filmSize,
    },
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// CameraCtrl Poses Format (CAMERACTRL_POSES)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Single CameraCtrl pose entry
 *
 * Format: [time, fx, fy, cx, cy, aspect, 0, 0, w2c[0], w2c[1], ..., w2c[11]]
 * - time: frame timestamp (normalized or frame number)
 * - fx, fy: focal length in pixels (fx = fy for square pixels)
 * - cx, cy: principal point (usually image center)
 * - aspect: aspect ratio
 * - 0, 0: flags (unused)
 * - w2c[0..11]: 3x4 world-to-camera matrix, flattened row-major
 */
export type CameraCtrlPoseEntry = number[];

/**
 * Compute world-to-camera (w2c) matrix from camera state
 *
 * The w2c matrix transforms world coordinates to camera coordinates.
 * It's the inverse of the camera-to-world (c2w) matrix.
 */
function computeW2CMatrix(cam: InterpolatedCamera): number[][] {
  const { position, rotation } = cam;

  // Guard against NaN/Infinity
  const rotX = Number.isFinite(rotation.x) ? rotation.x : 0;
  const rotY = Number.isFinite(rotation.y) ? rotation.y : 0;
  const rotZ = Number.isFinite(rotation.z) ? rotation.z : 0;
  const posX = Number.isFinite(position.x) ? position.x : 0;
  const posY = Number.isFinite(position.y) ? position.y : 0;
  const posZ = Number.isFinite(position.z) ? position.z : 0;

  // Convert degrees to radians
  const rx = (rotX * Math.PI) / 180;
  const ry = (rotY * Math.PI) / 180;
  const rz = (rotZ * Math.PI) / 180;

  // Rotation matrices
  const cosX = Math.cos(rx),
    sinX = Math.sin(rx);
  const cosY = Math.cos(ry),
    sinY = Math.sin(ry);
  const cosZ = Math.cos(rz),
    sinZ = Math.sin(rz);

  // Combined rotation (Y * X * Z order) - this gives us R for c2w
  const r00 = cosY * cosZ + sinY * sinX * sinZ;
  const r01 = -cosY * sinZ + sinY * sinX * cosZ;
  const r02 = sinY * cosX;

  const r10 = cosX * sinZ;
  const r11 = cosX * cosZ;
  const r12 = -sinX;

  const r20 = -sinY * cosZ + cosY * sinX * sinZ;
  const r21 = sinY * sinZ + cosY * sinX * cosZ;
  const r22 = cosY * cosX;

  // For w2c, rotation is transposed (R^T) and translation is -R^T * t
  // w2c rotation (transpose of c2w rotation)
  const w2c_r00 = r00,
    w2c_r01 = r10,
    w2c_r02 = r20;
  const w2c_r10 = r01,
    w2c_r11 = r11,
    w2c_r12 = r21;
  const w2c_r20 = r02,
    w2c_r21 = r12,
    w2c_r22 = r22;

  // w2c translation = -R^T * t
  const tx = -(w2c_r00 * posX + w2c_r01 * posY + w2c_r02 * posZ);
  const ty = -(w2c_r10 * posX + w2c_r11 * posY + w2c_r12 * posZ);
  const tz = -(w2c_r20 * posX + w2c_r21 * posY + w2c_r22 * posZ);

  // Return 3x4 w2c matrix
  return [
    [w2c_r00, w2c_r01, w2c_r02, tx],
    [w2c_r10, w2c_r11, w2c_r12, ty],
    [w2c_r20, w2c_r21, w2c_r22, tz],
  ];
}

/**
 * Export camera animation as CameraCtrl poses for WanVideoWrapper
 *
 * This produces the CAMERACTRL_POSES format used by:
 * - WanVideoFunCameraEmbeds node
 * - AnimateDiff-Evolved CameraCtrl integration
 *
 * Each pose entry format: [time, fx, fy, cx, cy, aspect, 0, 0, w2c[0..11]]
 *
 * @see https://github.com/kijai/ComfyUI-WanVideoWrapper/blob/main/fun_camera/nodes.py
 * @see https://github.com/hehao13/CameraCtrl
 */
export function exportAsCameraCtrlPoses(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
  width: number,
  height: number,
): CameraCtrlPoseEntry[] {
  const poses: CameraCtrlPoseEntry[] = [];

  // Compute focal length in pixels from camera properties
  // fx = focal_length_mm * width / sensor_width_mm
  // For 36mm sensor (full frame), fx = focalLength * width / 36
  const sensorWidth = camera.filmSize || 36; // Default to 36mm

  for (let frame = 0; frame < frameCount; frame++) {
    const cam = interpolateCameraAtFrame(camera, keyframes, frame);

    // Focal length in pixels
    // Use the camera's focal length, accounting for zoom
    const focalLengthMM = cam.focalLength * (cam.zoom || 1);
    const fx = (focalLengthMM * width) / sensorWidth;
    const fy = fx; // Square pixels

    // Principal point (image center)
    const cx = 0.5; // Normalized to [0, 1]
    const cy = 0.5;

    // Aspect ratio
    const aspect = width / height;

    // Compute 3x4 w2c matrix
    const w2c = computeW2CMatrix(cam);

    // Flatten w2c matrix row-major: [r00, r01, r02, tx, r10, r11, r12, ty, r20, r21, r22, tz]
    const w2cFlat = [
      w2c[0][0],
      w2c[0][1],
      w2c[0][2],
      w2c[0][3],
      w2c[1][0],
      w2c[1][1],
      w2c[1][2],
      w2c[1][3],
      w2c[2][0],
      w2c[2][1],
      w2c[2][2],
      w2c[2][3],
    ];

    // Build pose entry: [time, fx, fy, cx, cy, aspect, 0, 0, w2c[0..11]]
    const poseEntry: CameraCtrlPoseEntry = [
      frame, // time (frame number)
      fx, // focal length x (pixels)
      fy, // focal length y (pixels)
      cx, // principal point x (normalized)
      cy, // principal point y (normalized)
      aspect, // aspect ratio
      0, // flag 1 (unused)
      0, // flag 2 (unused)
      ...w2cFlat, // 12 w2c matrix values
    ];

    poses.push(poseEntry);
  }

  return poses;
}

/**
 * Export CameraCtrl poses as space-separated strings
 *
 * This is the text format used by some CameraCtrl implementations
 * where each line is a space-separated list of values.
 */
export function exportAsCameraCtrlPosesText(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
  width: number,
  height: number,
): string {
  const poses = exportAsCameraCtrlPoses(
    camera,
    keyframes,
    frameCount,
    width,
    height,
  );

  return poses.map((pose) => pose.join(" ")).join("\n");
}

/**
 * Export for WanVideoFunCameraEmbeds node
 *
 * Returns the pose array ready for the CAMERACTRL_POSES input.
 */
export function exportFunCameraPackage(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
  width: number,
  height: number,
): {
  poses: CameraCtrlPoseEntry[];
  metadata: {
    frameCount: number;
    width: number;
    height: number;
    focalLength: number;
  };
} {
  return {
    poses: exportAsCameraCtrlPoses(
      camera,
      keyframes,
      frameCount,
      width,
      height,
    ),
    metadata: {
      frameCount,
      width,
      height,
      focalLength: camera.focalLength,
    },
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// Export Router
// ═══════════════════════════════════════════════════════════════════════════

import type { ExportTarget } from "@/types/export";

/**
 * Export camera data for a specific target format
 */
export function exportCameraForTarget(
  target: ExportTarget,
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
  compWidth: number = 1920,
  compHeight: number = 1080,
  fps: number = 24,
): object {
  switch (target) {
    case "motionctrl":
      return exportToMotionCtrl(camera, keyframes, frameCount);

    case "motionctrl-svd":
      return exportToMotionCtrlSVD(camera, keyframes, frameCount);

    case "wan22-fun-camera":
      return mapToWan22FunCamera(keyframes);

    case "uni3c-camera":
    case "uni3c-motion":
      return exportToUni3C(
        camera,
        keyframes,
        frameCount,
        compWidth,
        compHeight,
      );

    case "animatediff-cameractrl":
      return exportToCameraCtrl(keyframes, frameCount);

    default:
      // Full matrices for custom workflows
      return exportCameraMatrices(camera, keyframes, {
        frameCount,
        width: compWidth,
        height: compHeight,
        fps,
      });
  }
}
