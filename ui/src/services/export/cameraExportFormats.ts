/**
 * Camera Export Formats
 * Export camera animations to various AI video generation formats
 */

import type { Camera3D, CameraKeyframe } from '@/types/camera';
import type {
  MotionCtrlCameraData,
  MotionCtrlPose,
  MotionCtrlSVDCameraData,
  MotionCtrlSVDPreset,
  Wan22CameraMotion,
  Wan22FunCameraData,
  Uni3CCameraData,
  Uni3CCameraTrajectory,
  Uni3CTrajType,
  CameraCtrlPoses,
  CameraCtrlMotionType,
  FullCameraExport,
  FullCameraFrame,
} from '@/types/export';
import { focalLengthToFOV } from '@/services/math3d';

// ============================================================================
// Camera Interpolation
// ============================================================================

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
  frame: number
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
  const getPos = (kf: CameraKeyframe | null | undefined) => kf?.position ?? camera.position;
  const getOri = (kf: CameraKeyframe | null | undefined) => kf?.orientation ?? camera.orientation;
  const getFocal = (kf: CameraKeyframe | null | undefined) => kf?.focalLength ?? camera.focalLength;
  const getZoom = (kf: CameraKeyframe | null | undefined) => kf?.zoom ?? camera.zoom;
  const getFocusDist = (kf: CameraKeyframe | null | undefined) => kf?.focusDistance ?? camera.depthOfField.focusDistance;

  if (prev!.frame === next!.frame) {
    return {
      position: getPos(prev),
      rotation: getOri(prev),
      focalLength: getFocal(prev),
      zoom: getZoom(prev),
      focusDistance: getFocusDist(prev),
    };
  }

  // Interpolate
  const t = (frame - prev!.frame) / (next!.frame - prev!.frame);

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
  // Handle angle wrapping
  let diff = b - a;
  if (diff > 180) diff -= 360;
  if (diff < -180) diff += 360;
  return a + diff * t;
}

// ============================================================================
// Matrix Utilities
// ============================================================================

/**
 * Compute 4x4 view matrix from camera state
 */
export function computeViewMatrix(cam: InterpolatedCamera): number[][] {
  const { position, rotation } = cam;

  // Convert degrees to radians
  const rx = rotation.x * Math.PI / 180;
  const ry = rotation.y * Math.PI / 180;
  const rz = rotation.z * Math.PI / 180;

  // Rotation matrices
  const cosX = Math.cos(rx), sinX = Math.sin(rx);
  const cosY = Math.cos(ry), sinY = Math.sin(ry);
  const cosZ = Math.cos(rz), sinZ = Math.sin(rz);

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
  // Translation is -R^T * position
  const tx = -(r00 * position.x + r10 * position.y + r20 * position.z);
  const ty = -(r01 * position.x + r11 * position.y + r21 * position.z);
  const tz = -(r02 * position.x + r12 * position.y + r22 * position.z);

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
  farClip: number = 1000
): number[][] {
  const fov = focalLengthToFOV(cam.focalLength, 36); // 36mm film
  const fovRad = fov * Math.PI / 180;
  const tanHalfFov = Math.tan(fovRad / 2);

  const f = 1 / tanHalfFov;
  const nf = 1 / (nearClip - farClip);

  return [
    [f / aspectRatio, 0, 0, 0],
    [0, f, 0, 0],
    [0, 0, (farClip + nearClip) * nf, 2 * farClip * nearClip * nf],
    [0, 0, -1, 0],
  ];
}

// ============================================================================
// MotionCtrl Format Export
// ============================================================================

/**
 * Export camera animation to MotionCtrl format (4x4 RT matrices)
 */
export function exportToMotionCtrl(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number
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
  keyframes: CameraKeyframe[]
): MotionCtrlSVDPreset {
  if (!keyframes || keyframes.length < 2) return 'static';

  const first = keyframes[0];
  const last = keyframes[keyframes.length - 1];

  // Get positions and orientations with defaults
  const firstPos = first.position ?? { x: 0, y: 0, z: 0 };
  const lastPos = last.position ?? { x: 0, y: 0, z: 0 };
  const firstOri = first.orientation ?? { x: 0, y: 0, z: 0 };
  const lastOri = last.orientation ?? { x: 0, y: 0, z: 0 };

  const deltaX = lastPos.x - firstPos.x;
  const deltaY = lastPos.y - firstPos.y;
  const deltaZ = lastPos.z - firstPos.z;
  const deltaRy = lastOri.y - firstOri.y;

  const threshold = 50; // Movement threshold

  // Check for zoom (Z movement)
  if (Math.abs(deltaZ) > threshold) {
    return deltaZ < 0 ? 'zoom_in' : 'zoom_out';
  }

  // Check for rotation
  if (Math.abs(deltaRy) > 15) {
    return deltaRy > 0 ? 'rotate_cw' : 'rotate_ccw';
  }

  // Check for pan
  if (Math.abs(deltaX) > threshold) {
    return deltaX > 0 ? 'pan_right' : 'pan_left';
  }

  if (Math.abs(deltaY) > threshold) {
    return deltaY > 0 ? 'pan_down' : 'pan_up';
  }

  return 'static';
}

/**
 * Export to MotionCtrl-SVD format
 */
export function exportToMotionCtrlSVD(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number
): MotionCtrlSVDCameraData {
  const preset = detectMotionCtrlSVDPreset(keyframes);

  if (preset !== 'static' && keyframes.length <= 2) {
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

// ============================================================================
// Wan 2.2 Fun Camera Format
// ============================================================================

interface CameraMotionAnalysis {
  hasPan: boolean;
  panDirection?: 'up' | 'down' | 'left' | 'right';
  panMagnitude: number;
  hasZoom: boolean;
  zoomDirection?: 'in' | 'out';
  zoomMagnitude: number;
  hasOrbit: boolean;
  orbitDirection?: 'left' | 'right';
  orbitMagnitude: number;
  hasRotation: boolean;
  rotationMagnitude: number;
}

/**
 * Analyze camera motion pattern from keyframes
 */
export function analyzeCameraMotion(keyframes: CameraKeyframe[]): CameraMotionAnalysis {
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
  const firstPos = first.position ?? { x: 0, y: 0, z: 0 };
  const lastPos = last.position ?? { x: 0, y: 0, z: 0 };
  const firstOri = first.orientation ?? { x: 0, y: 0, z: 0 };
  const lastOri = last.orientation ?? { x: 0, y: 0, z: 0 };

  const deltaX = lastPos.x - firstPos.x;
  const deltaY = lastPos.y - firstPos.y;
  const deltaZ = lastPos.z - firstPos.z;
  const deltaRy = lastOri.y - firstOri.y;

  // Thresholds
  const panThreshold = 30;
  const zoomThreshold = 50;
  const orbitThreshold = 20;

  // Determine pan
  let panDirection: 'up' | 'down' | 'left' | 'right' | undefined;
  const panX = Math.abs(deltaX);
  const panY = Math.abs(deltaY);

  if (panX > panThreshold || panY > panThreshold) {
    if (panX > panY) {
      panDirection = deltaX > 0 ? 'right' : 'left';
    } else {
      panDirection = deltaY > 0 ? 'down' : 'up';
    }
  }

  // Determine zoom
  let zoomDirection: 'in' | 'out' | undefined;
  if (Math.abs(deltaZ) > zoomThreshold) {
    zoomDirection = deltaZ < 0 ? 'in' : 'out';
  }

  // Determine orbit (rotation around Y with position change)
  let orbitDirection: 'left' | 'right' | undefined;
  if (Math.abs(deltaRy) > orbitThreshold && Math.abs(deltaX) > panThreshold) {
    orbitDirection = deltaRy > 0 ? 'right' : 'left';
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
export function mapToWan22FunCamera(keyframes: CameraKeyframe[]): Wan22FunCameraData {
  const motion = analyzeCameraMotion(keyframes);

  let preset: Wan22CameraMotion = 'Static';

  // Priority: Orbit > Zoom+Pan > Zoom > Pan
  if (motion.hasOrbit) {
    preset = motion.orbitDirection === 'left' ? 'Orbital Left' : 'Orbital Right';
  } else if (motion.hasZoom && motion.hasPan) {
    const panDir = capitalize(motion.panDirection || 'up');
    const zoomDir = motion.zoomDirection === 'in' ? 'Zoom In' : 'Zoom Out';
    preset = `Pan ${panDir} + ${zoomDir}` as Wan22CameraMotion;
  } else if (motion.hasZoom) {
    preset = motion.zoomDirection === 'in' ? 'Zoom In' : 'Zoom Out';
  } else if (motion.hasPan) {
    preset = `Pan ${capitalize(motion.panDirection || 'up')}` as Wan22CameraMotion;
  }

  return { camera_motion: preset };
}

function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1);
}

// ============================================================================
// Uni3C Camera Format
// ============================================================================

/**
 * Detect Uni3C trajectory type from keyframes
 */
export function detectUni3CTrajectoryType(keyframes: CameraKeyframe[]): Uni3CTrajType {
  const motion = analyzeCameraMotion(keyframes);

  if (motion.hasOrbit && motion.orbitMagnitude > 45) {
    return 'orbit';
  }

  if (motion.hasPan && motion.hasZoom) {
    // Complex motion -> custom
    return 'custom';
  }

  // Simple motions might match presets
  if (!motion.hasPan && !motion.hasZoom && !motion.hasOrbit) {
    return 'free1'; // Minimal motion
  }

  return 'custom';
}

/**
 * Export camera animation to Uni3C format
 */
export function exportToUni3C(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frameCount: number,
  compWidth: number,
  compHeight: number
): Uni3CCameraData {
  const detectedType = detectUni3CTrajectoryType(keyframes);

  if (detectedType !== 'custom') {
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
    traj_type: 'custom',
    custom_trajectory: trajectory,
  };
}

// ============================================================================
// AnimateDiff CameraCtrl Format
// ============================================================================

/**
 * Detect AnimateDiff CameraCtrl motion type
 */
export function detectCameraCtrlMotionType(keyframes: CameraKeyframe[]): CameraCtrlMotionType {
  const motion = analyzeCameraMotion(keyframes);

  if (!motion.hasPan && !motion.hasZoom && !motion.hasRotation) {
    return 'Static';
  }

  // Check zoom
  if (motion.hasZoom) {
    return motion.zoomDirection === 'in' ? 'Move Forward' : 'Move Backward';
  }

  // Check pan
  if (motion.hasPan) {
    switch (motion.panDirection) {
      case 'left': return 'Move Left';
      case 'right': return 'Move Right';
      case 'up': return 'Move Up';
      case 'down': return 'Move Down';
    }
  }

  // Check rotation
  if (motion.hasRotation) {
    const first = keyframes[0];
    const last = keyframes[keyframes.length - 1];

    const firstOri = first.orientation ?? { x: 0, y: 0, z: 0 };
    const lastOri = last.orientation ?? { x: 0, y: 0, z: 0 };

    const deltaRx = lastOri.x - firstOri.x;
    const deltaRy = lastOri.y - firstOri.y;
    const deltaRz = lastOri.z - firstOri.z;

    if (Math.abs(deltaRy) > Math.abs(deltaRx) && Math.abs(deltaRy) > Math.abs(deltaRz)) {
      return deltaRy > 0 ? 'Rotate Right' : 'Rotate Left';
    }
    if (Math.abs(deltaRx) > Math.abs(deltaRz)) {
      return deltaRx > 0 ? 'Rotate Down' : 'Rotate Up';
    }
    return deltaRz > 0 ? 'Roll Right' : 'Roll Left';
  }

  return 'Static';
}

/**
 * Export to AnimateDiff CameraCtrl format
 */
export function exportToCameraCtrl(
  keyframes: CameraKeyframe[],
  frameCount: number
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

// ============================================================================
// Full Camera Export (Generic Format)
// ============================================================================

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
  }
): FullCameraExport {
  const frames: FullCameraFrame[] = [];
  const aspectRatio = options.width / options.height;

  for (let frame = 0; frame < options.frameCount; frame++) {
    const cam = interpolateCameraAtFrame(camera, keyframes, frame);

    const viewMatrix = computeViewMatrix(cam);
    const projMatrix = computeProjectionMatrix(cam, aspectRatio);

    frames.push({
      frame,
      timestamp: frame / options.fps,
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
      width: options.width,
      height: options.height,
      fps: options.fps,
      total_frames: options.frameCount,
      camera_type: camera.type,
      film_size: camera.filmSize,
    },
  };
}

// ============================================================================
// Export Router
// ============================================================================

import type { ExportTarget } from '@/types/export';

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
  fps: number = 24
): object {
  switch (target) {
    case 'motionctrl':
      return exportToMotionCtrl(camera, keyframes, frameCount);

    case 'motionctrl-svd':
      return exportToMotionCtrlSVD(camera, keyframes, frameCount);

    case 'wan22-fun-camera':
      return mapToWan22FunCamera(keyframes);

    case 'uni3c-camera':
    case 'uni3c-motion':
      return exportToUni3C(camera, keyframes, frameCount, compWidth, compHeight);

    case 'animatediff-cameractrl':
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
