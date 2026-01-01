/**
 * Camera Export Service
 * Exports camera data to various formats including Uni3C
 */

import type { Camera3D, CameraKeyframe } from '../types/camera';
import { focalLengthToFOV } from './math3d';

/**
 * Uni3C Camera Track Format
 * Used for camera motion transfer in video generation
 */
export interface Uni3CTrack {
  version: string;
  fps: number;
  frames: Uni3CFrame[];
  metadata: {
    source: string;
    exportDate: string;
    cameraName: string;
    compWidth: number;
    compHeight: number;
  };
}

export interface Uni3CFrame {
  frame: number;
  timestamp: number;
  camera: {
    position: { x: number; y: number; z: number };
    rotation: { x: number; y: number; z: number };  // Euler angles in degrees
    fov: number;  // Vertical FOV in degrees
    aspectRatio: number;
    nearClip: number;
    farClip: number;
  };
  dof?: {
    enabled: boolean;
    focusDistance: number;
    aperture: number;
  };
}

/**
 * Export camera data to Uni3C format
 */
export function exportToUni3C(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  fps: number,
  compWidth: number,
  compHeight: number,
  startFrame: number = 0,
  endFrame: number = 100
): Uni3CTrack {
  const frames: Uni3CFrame[] = [];
  const aspectRatio = compWidth / compHeight;

  for (let frame = startFrame; frame <= endFrame; frame++) {
    const interpolated = interpolateCamera(camera, keyframes, frame);
    const timestamp = frame / fps;

    // Calculate rotation from camera orientation and individual rotations
    const rotation = {
      x: interpolated.orientation.x + interpolated.xRotation,
      y: interpolated.orientation.y + interpolated.yRotation,
      z: interpolated.orientation.z + interpolated.zRotation
    };

    // For two-node camera, calculate rotation from position and POI
    if (camera.type === 'two-node') {
      const dir = {
        x: interpolated.pointOfInterest.x - interpolated.position.x,
        y: interpolated.pointOfInterest.y - interpolated.position.y,
        z: interpolated.pointOfInterest.z - interpolated.position.z
      };

      // Calculate yaw (Y rotation) and pitch (X rotation) from direction
      const horizontalDist = Math.sqrt(dir.x * dir.x + dir.z * dir.z);
      rotation.y = Math.atan2(dir.x, dir.z) * 180 / Math.PI;
      rotation.x = -Math.atan2(dir.y, horizontalDist) * 180 / Math.PI;
    }

    const fov = focalLengthToFOV(interpolated.focalLength, interpolated.filmSize);

    frames.push({
      frame,
      timestamp,
      camera: {
        position: { ...interpolated.position },
        rotation,
        fov,
        aspectRatio,
        nearClip: interpolated.nearClip,
        farClip: interpolated.farClip
      },
      dof: interpolated.depthOfField.enabled ? {
        enabled: true,
        focusDistance: interpolated.depthOfField.focusDistance,
        aperture: interpolated.depthOfField.aperture
      } : undefined
    });
  }

  return {
    version: '1.0',
    fps,
    frames,
    metadata: {
      source: 'Lattice Compositor',
      exportDate: new Date().toISOString(),
      cameraName: camera.name,
      compWidth,
      compHeight
    }
  };
}

/**
 * Interpolate camera properties at a given frame
 */
function interpolateCamera(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  frame: number
): Camera3D {
  if (keyframes.length === 0) {
    return camera;
  }

  // Sort keyframes by frame number
  const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);

  // Find surrounding keyframes
  let prevKeyframe: CameraKeyframe | null = null;
  let nextKeyframe: CameraKeyframe | null = null;

  for (let i = 0; i < sorted.length; i++) {
    if (sorted[i].frame <= frame) {
      prevKeyframe = sorted[i];
    }
    if (sorted[i].frame >= frame && !nextKeyframe) {
      nextKeyframe = sorted[i];
    }
  }

  // If no keyframes found, return base camera
  if (!prevKeyframe && !nextKeyframe) {
    return camera;
  }

  // If only one keyframe or exact match
  if (!prevKeyframe) {
    return applyKeyframe(camera, nextKeyframe!);
  }
  if (!nextKeyframe || prevKeyframe.frame === nextKeyframe.frame) {
    return applyKeyframe(camera, prevKeyframe);
  }

  // Interpolate between keyframes
  const t = (frame - prevKeyframe.frame) / (nextKeyframe.frame - prevKeyframe.frame);
  const eased = getEasedT(t, prevKeyframe, nextKeyframe);

  return interpolateBetweenKeyframes(camera, prevKeyframe, nextKeyframe, eased);
}

/**
 * Apply keyframe values to camera
 */
function applyKeyframe(camera: Camera3D, keyframe: CameraKeyframe): Camera3D {
  return {
    ...camera,
    position: keyframe.position ?? camera.position,
    pointOfInterest: keyframe.pointOfInterest ?? camera.pointOfInterest,
    orientation: keyframe.orientation ?? camera.orientation,
    xRotation: keyframe.xRotation ?? camera.xRotation,
    yRotation: keyframe.yRotation ?? camera.yRotation,
    zRotation: keyframe.zRotation ?? camera.zRotation,
    zoom: keyframe.zoom ?? camera.zoom,
    focalLength: keyframe.focalLength ?? camera.focalLength,
    depthOfField: {
      ...camera.depthOfField,
      focusDistance: keyframe.focusDistance ?? camera.depthOfField.focusDistance,
      aperture: keyframe.aperture ?? camera.depthOfField.aperture
    }
  };
}

/**
 * Calculate eased t value based on temporal interpolation
 */
function getEasedT(
  t: number,
  prevKeyframe: CameraKeyframe,
  nextKeyframe: CameraKeyframe
): number {
  const interpolation = prevKeyframe.temporalInterpolation ?? 'linear';

  switch (interpolation) {
    case 'hold':
      return 0;
    case 'bezier':
      // Use bezier handles if available
      if (prevKeyframe.outHandle && nextKeyframe.inHandle) {
        return cubicBezier(
          t,
          0, 0,
          prevKeyframe.outHandle.x, prevKeyframe.outHandle.y,
          nextKeyframe.inHandle.x, nextKeyframe.inHandle.y,
          1, 1
        );
      }
      // Default ease
      return easeInOut(t);
    case 'linear':
    default:
      return t;
  }
}

/**
 * Interpolate between two keyframes
 */
function interpolateBetweenKeyframes(
  camera: Camera3D,
  prev: CameraKeyframe,
  next: CameraKeyframe,
  t: number
): Camera3D {
  const lerp = (a: number, b: number) => a + (b - a) * t;
  const lerpVec3 = (
    a: { x: number; y: number; z: number } | undefined,
    b: { x: number; y: number; z: number } | undefined,
    def: { x: number; y: number; z: number }
  ) => {
    const from = a ?? def;
    const to = b ?? def;
    return {
      x: lerp(from.x, to.x),
      y: lerp(from.y, to.y),
      z: lerp(from.z, to.z)
    };
  };

  return {
    ...camera,
    position: lerpVec3(prev.position, next.position, camera.position),
    pointOfInterest: lerpVec3(prev.pointOfInterest, next.pointOfInterest, camera.pointOfInterest),
    orientation: lerpVec3(prev.orientation, next.orientation, camera.orientation),
    xRotation: lerp(prev.xRotation ?? camera.xRotation, next.xRotation ?? camera.xRotation),
    yRotation: lerp(prev.yRotation ?? camera.yRotation, next.yRotation ?? camera.yRotation),
    zRotation: lerp(prev.zRotation ?? camera.zRotation, next.zRotation ?? camera.zRotation),
    zoom: lerp(prev.zoom ?? camera.zoom, next.zoom ?? camera.zoom),
    focalLength: lerp(prev.focalLength ?? camera.focalLength, next.focalLength ?? camera.focalLength),
    depthOfField: {
      ...camera.depthOfField,
      focusDistance: lerp(
        prev.focusDistance ?? camera.depthOfField.focusDistance,
        next.focusDistance ?? camera.depthOfField.focusDistance
      ),
      aperture: lerp(
        prev.aperture ?? camera.depthOfField.aperture,
        next.aperture ?? camera.depthOfField.aperture
      )
    }
  };
}

/**
 * Cubic bezier evaluation
 */
function cubicBezier(
  t: number,
  x0: number, y0: number,
  x1: number, y1: number,
  x2: number, y2: number,
  x3: number, y3: number
): number {
  // Simple approximation - find t for x, return y
  const mt = 1 - t;
  const mt2 = mt * mt;
  const mt3 = mt2 * mt;
  const t2 = t * t;
  const t3 = t2 * t;

  return mt3 * y0 + 3 * mt2 * t * y1 + 3 * mt * t2 * y2 + t3 * y3;
}

/**
 * Simple ease in-out
 */
function easeInOut(t: number): number {
  return t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
}

/**
 * Export camera to JSON file
 */
export function exportCameraJSON(
  camera: Camera3D,
  keyframes: CameraKeyframe[]
): string {
  return JSON.stringify({
    camera,
    keyframes,
    exportedAt: new Date().toISOString(),
    version: '1.0'
  }, null, 2);
}

/**
 * Import camera from JSON
 */
export function importCameraJSON(json: string): { camera: Camera3D; keyframes: CameraKeyframe[] } | null {
  try {
    const data = JSON.parse(json);
    if (data.camera && data.keyframes) {
      return {
        camera: data.camera,
        keyframes: data.keyframes
      };
    }
    return null;
  } catch {
    return null;
  }
}

/**
 * Export to After Effects camera format (ExtendScript compatible)
 */
export function exportToAEScript(
  camera: Camera3D,
  keyframes: CameraKeyframe[],
  compName: string
): string {
  let script = `// After Effects Camera Import Script
// Generated by Lattice Compositor
// Camera: ${camera.name}

(function() {
  var comp = app.project.activeItem;
  if (!(comp instanceof CompItem)) {
    alert("Please select a composition first.");
    return;
  }

  var camera = comp.layers.addCamera("${camera.name}", [comp.width/2, comp.height/2]);
  var cameraOptions = camera.property("ADBE Camera Options Group");

  // Set camera type
  camera.property("ADBE Camera Options Group").property("ADBE Camera Type").setValue(${camera.type === 'two-node' ? 2 : 1});

  // Set initial position
  camera.position.setValue([${camera.position.x}, ${camera.position.y}, ${camera.position.z}]);

`;

  if (camera.type === 'two-node') {
    script += `  // Set point of interest
  camera.pointOfInterest.setValue([${camera.pointOfInterest.x}, ${camera.pointOfInterest.y}, ${camera.pointOfInterest.z}]);

`;
  }

  script += `  // Set zoom (focal length)
  cameraOptions.property("ADBE Camera Zoom").setValue(${camera.zoom});

  // Set depth of field
  cameraOptions.property("ADBE Camera Depth of Field").setValue(${camera.depthOfField.enabled ? 1 : 0});
  cameraOptions.property("ADBE Camera Focus Distance").setValue(${camera.depthOfField.focusDistance});
  cameraOptions.property("ADBE Camera Aperture").setValue(${camera.depthOfField.aperture});
  cameraOptions.property("ADBE Camera Blur Level").setValue(${camera.depthOfField.blurLevel * 100});

`;

  // Add keyframes if present
  if (keyframes.length > 0) {
    script += `  // Add keyframes
`;
    for (const kf of keyframes) {
      const frameTime = kf.frame / 30; // Assuming 30fps
      if (kf.position) {
        script += `  camera.position.setValueAtTime(${frameTime}, [${kf.position.x}, ${kf.position.y}, ${kf.position.z}]);
`;
      }
      if (kf.pointOfInterest) {
        script += `  camera.pointOfInterest.setValueAtTime(${frameTime}, [${kf.pointOfInterest.x}, ${kf.pointOfInterest.y}, ${kf.pointOfInterest.z}]);
`;
      }
      if (kf.zoom !== undefined) {
        script += `  cameraOptions.property("ADBE Camera Zoom").setValueAtTime(${frameTime}, ${kf.zoom});
`;
      }
    }
  }

  script += `
  alert("Camera '${camera.name}' created successfully!");
})();
`;

  return script;
}

/**
 * Download file helper
 */
export function downloadFile(content: string, filename: string, mimeType: string = 'application/json') {
  const blob = new Blob([content], { type: mimeType });
  const url = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
  URL.revokeObjectURL(url);
}
