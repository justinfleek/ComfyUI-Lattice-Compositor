/**
 * Camera Tracking Import Service
 *
 * Imports camera tracking data from external tools and creates
 * camera layers with keyframed animation.
 *
 * Supported formats:
 * - Weyl JSON (native format)
 * - COLMAP (popular open-source SfM)
 * - Blender Motion Tracking export
 * - Generic JSON with poses
 */

import type {
  CameraTrackingSolve,
  CameraTrackingImportOptions,
  CameraTrackingImportResult,
  CameraPose,
  TrackPoint3D,
  CameraIntrinsics,
  COLMAPFormat,
  BlenderFormat,
} from '@/types/cameraTracking';
import { useCompositorStore } from '@/stores/compositorStore';
import type { AnimatableProperty, Keyframe } from '@/types/project';

/**
 * Parse Weyl native JSON format
 */
export function parseWeylTrackingJSON(json: string): CameraTrackingSolve {
  const data = JSON.parse(json);

  if (!data.version || !data.poses) {
    throw new Error('Invalid Weyl tracking format: missing version or poses');
  }

  return data as CameraTrackingSolve;
}

/**
 * Parse COLMAP output files
 * Expects an object with cameras, images, and points3D text content
 */
export function parseCOLMAPOutput(files: {
  cameras: string;
  images: string;
  points3D?: string;
}): CameraTrackingSolve {
  // Parse cameras.txt
  const cameras = parseCOLMAPCameras(files.cameras);

  // Parse images.txt
  const images = parseCOLMAPImages(files.images);

  // Parse points3D.txt if provided
  const points3D = files.points3D ? parseCOLMAPPoints3D(files.points3D) : [];

  // Get first camera for intrinsics
  const firstCamera = cameras[0];
  if (!firstCamera) {
    throw new Error('No cameras found in COLMAP output');
  }

  // Convert to our format
  const intrinsics: CameraIntrinsics = {
    focalLength: firstCamera.params[0], // fx
    principalPoint: {
      x: firstCamera.params.length > 1 ? firstCamera.params[1] : firstCamera.width / 2,
      y: firstCamera.params.length > 2 ? firstCamera.params[2] : firstCamera.height / 2,
    },
    width: firstCamera.width,
    height: firstCamera.height,
    model: 'pinhole',
  };

  // Convert images to poses
  const poses: CameraPose[] = images.map((img, index) => {
    // COLMAP stores camera-to-world inverse, need to invert
    // Quaternion is already world-to-camera, position needs adjustment
    const qw = img.qw, qx = img.qx, qy = img.qy, qz = img.qz;

    // Camera position in world = -R^T * t
    const rotMatrix = quaternionToMatrix(qw, qx, qy, qz);
    const worldPos = {
      x: -(rotMatrix[0] * img.tx + rotMatrix[1] * img.ty + rotMatrix[2] * img.tz),
      y: -(rotMatrix[3] * img.tx + rotMatrix[4] * img.ty + rotMatrix[5] * img.tz),
      z: -(rotMatrix[6] * img.tx + rotMatrix[7] * img.ty + rotMatrix[8] * img.tz),
    };

    return {
      frame: index, // COLMAP doesn't store frame numbers, use index
      position: worldPos,
      rotation: { w: qw, x: qx, y: qy, z: qz },
    };
  });

  // Convert 3D points
  const trackPoints3D: TrackPoint3D[] = points3D.map(pt => ({
    id: `pt_${pt.id}`,
    position: { x: pt.x, y: pt.y, z: pt.z },
    color: { r: pt.r, g: pt.g, b: pt.b },
    track2DIDs: pt.trackIds.map(id => `track_${id}`),
    error: pt.error,
  }));

  return {
    version: '1.0',
    source: 'colmap',
    metadata: {
      sourceWidth: firstCamera.width,
      sourceHeight: firstCamera.height,
      frameRate: 24, // Default, COLMAP doesn't store this
      frameCount: images.length,
    },
    intrinsics,
    poses,
    trackPoints3D,
  };
}

/**
 * Parse COLMAP cameras.txt
 */
function parseCOLMAPCameras(content: string): COLMAPFormat.Camera[] {
  const cameras: COLMAPFormat.Camera[] = [];
  const lines = content.split('\n');

  for (const line of lines) {
    if (line.startsWith('#') || !line.trim()) continue;

    const parts = line.trim().split(/\s+/);
    if (parts.length < 5) continue;

    cameras.push({
      id: parseInt(parts[0]),
      model: parts[1],
      width: parseInt(parts[2]),
      height: parseInt(parts[3]),
      params: parts.slice(4).map(parseFloat),
    });
  }

  return cameras;
}

/**
 * Parse COLMAP images.txt
 */
function parseCOLMAPImages(content: string): COLMAPFormat.Image[] {
  const images: COLMAPFormat.Image[] = [];
  const lines = content.split('\n');
  let i = 0;

  while (i < lines.length) {
    const line = lines[i];
    if (line.startsWith('#') || !line.trim()) {
      i++;
      continue;
    }

    // Image line: IMAGE_ID, QW, QX, QY, QZ, TX, TY, TZ, CAMERA_ID, NAME
    const parts = line.trim().split(/\s+/);
    if (parts.length >= 10) {
      const image: COLMAPFormat.Image = {
        id: parseInt(parts[0]),
        qw: parseFloat(parts[1]),
        qx: parseFloat(parts[2]),
        qy: parseFloat(parts[3]),
        qz: parseFloat(parts[4]),
        tx: parseFloat(parts[5]),
        ty: parseFloat(parts[6]),
        tz: parseFloat(parts[7]),
        cameraId: parseInt(parts[8]),
        name: parts[9],
        points2D: [],
      };

      // Next line contains 2D points
      i++;
      if (i < lines.length && !lines[i].startsWith('#')) {
        const pointLine = lines[i].trim();
        if (pointLine) {
          const pointParts = pointLine.split(/\s+/);
          for (let j = 0; j < pointParts.length; j += 3) {
            if (j + 2 < pointParts.length) {
              image.points2D.push({
                x: parseFloat(pointParts[j]),
                y: parseFloat(pointParts[j + 1]),
                point3DId: parseInt(pointParts[j + 2]),
              });
            }
          }
        }
      }

      images.push(image);
    }
    i++;
  }

  return images;
}

/**
 * Parse COLMAP points3D.txt
 */
function parseCOLMAPPoints3D(content: string): COLMAPFormat.Point3D[] {
  const points: COLMAPFormat.Point3D[] = [];
  const lines = content.split('\n');

  for (const line of lines) {
    if (line.startsWith('#') || !line.trim()) continue;

    const parts = line.trim().split(/\s+/);
    if (parts.length >= 8) {
      points.push({
        id: parseInt(parts[0]),
        x: parseFloat(parts[1]),
        y: parseFloat(parts[2]),
        z: parseFloat(parts[3]),
        r: parseInt(parts[4]),
        g: parseInt(parts[5]),
        b: parseInt(parts[6]),
        error: parseFloat(parts[7]),
        trackIds: parts.slice(8).filter((_, i) => i % 2 === 0).map(n => parseInt(n)),
      });
    }
  }

  return points;
}

/**
 * Parse Blender motion tracking JSON export
 */
export function parseBlenderTrackingJSON(json: string): CameraTrackingSolve {
  const data: BlenderFormat.MotionTrackingData = JSON.parse(json);

  const intrinsics: CameraIntrinsics = {
    focalLength: (data.camera.focal_length / data.camera.sensor_width) * data.clip_width,
    principalPoint: {
      x: data.clip_width / 2,
      y: data.clip_height / 2,
    },
    width: data.clip_width,
    height: data.clip_height,
    model: 'pinhole',
  };

  // Convert poses if reconstruction exists
  const poses: CameraPose[] = data.reconstruction?.camera_poses?.map(pose => ({
    frame: pose.frame,
    position: {
      x: pose.location[0],
      y: pose.location[1],
      z: pose.location[2],
    },
    rotation: {
      w: pose.rotation[0],
      x: pose.rotation[1],
      y: pose.rotation[2],
      z: pose.rotation[3],
    },
  })) || [];

  // Convert 3D points
  const trackPoints3D: TrackPoint3D[] = data.reconstruction?.points?.map((pt, i) => ({
    id: `pt_${i}`,
    position: { x: pt.co[0], y: pt.co[1], z: pt.co[2] },
    color: pt.color ? { r: pt.color[0] * 255, g: pt.color[1] * 255, b: pt.color[2] * 255 } : undefined,
    track2DIDs: [],
  })) || [];

  // Get frame count from tracks
  let maxFrame = 0;
  for (const track of data.tracks) {
    for (const marker of track.markers) {
      maxFrame = Math.max(maxFrame, marker.frame);
    }
  }

  return {
    version: '1.0',
    source: 'blender',
    metadata: {
      sourceWidth: data.clip_width,
      sourceHeight: data.clip_height,
      frameRate: data.fps,
      frameCount: maxFrame + 1,
    },
    intrinsics,
    poses,
    trackPoints3D,
  };
}

/**
 * Detect format from file content
 */
export function detectTrackingFormat(content: string): 'weyl' | 'blender' | 'colmap' | 'unknown' {
  try {
    const json = JSON.parse(content);

    if (json.version && json.source && json.poses) {
      return 'weyl';
    }

    if (json.fps && json.tracks && json.clip_width) {
      return 'blender';
    }
  } catch {
    // Not JSON, check for COLMAP text format
    if (content.includes('# Camera list') || content.includes('CAMERA_ID')) {
      return 'colmap';
    }
  }

  return 'unknown';
}

/**
 * Import camera tracking data and create layers
 */
export async function importCameraTracking(
  solve: CameraTrackingSolve,
  options: CameraTrackingImportOptions = {}
): Promise<CameraTrackingImportResult> {
  const store = useCompositorStore();
  const result: CameraTrackingImportResult = {
    success: false,
    warnings: [],
  };

  try {
    const scale = options.scale ?? 1;
    const offset = options.offset ?? { x: 0, y: 0, z: 0 };
    const frameOffset = options.frameOffset ?? 0;

    // Apply coordinate transformations to poses
    const transformedPoses = solve.poses.map(pose => ({
      ...pose,
      frame: pose.frame + frameOffset,
      position: {
        x: pose.position.x * scale + offset.x,
        y: (options.flipY ? -pose.position.y : pose.position.y) * scale + offset.y,
        z: (options.flipZ ? -pose.position.z : pose.position.z) * scale + offset.z,
      },
    }));

    // Create camera layer if requested
    if (options.createCamera !== false) {
      // Get intrinsics
      const intrinsics = Array.isArray(solve.intrinsics)
        ? solve.intrinsics[0]
        : solve.intrinsics;

      // Calculate FOV from focal length
      const fov = 2 * Math.atan(intrinsics.height / (2 * intrinsics.focalLength)) * (180 / Math.PI);

      // Create position keyframes
      const positionKeyframes: Keyframe<{ x: number; y: number; z: number }>[] =
        transformedPoses.map(pose => ({
          frame: pose.frame,
          value: pose.position,
          interpolation: 'linear' as const,
        }));

      // Create rotation keyframes (convert quaternion to euler)
      const rotationKeyframes: Keyframe<{ x: number; y: number; z: number }>[] =
        transformedPoses.map(pose => {
          const euler = quaternionToEuler(
            pose.rotation.w,
            pose.rotation.x,
            pose.rotation.y,
            pose.rotation.z
          );
          return {
            frame: pose.frame,
            value: euler,
            interpolation: 'linear' as const,
          };
        });

      // Create camera layer
      const cameraLayer = store.addLayer({
        type: 'camera',
        name: `Tracked Camera (${solve.source})`,
        data: {
          cameraType: 'perspective',
          fov: { defaultValue: fov, animated: false, keyframes: [] },
          near: 0.1,
          far: 10000,
          dof: { enabled: false, focusDistance: 100, aperture: 2.8, blurLevel: 1 },
        },
      });

      if (cameraLayer) {
        // Apply keyframed transform
        const positionProp: AnimatableProperty<{ x: number; y: number; z: number }> = {
          defaultValue: transformedPoses[0]?.position ?? { x: 0, y: 0, z: 0 },
          animated: true,
          keyframes: positionKeyframes,
        };

        const rotationProp: AnimatableProperty<{ x: number; y: number; z: number }> = {
          defaultValue: rotationKeyframes[0]?.value ?? { x: 0, y: 0, z: 0 },
          animated: true,
          keyframes: rotationKeyframes,
        };

        store.updateLayer(cameraLayer.id, {
          threeD: true,
          transform: {
            ...cameraLayer.transform,
            position: positionProp,
            rotation: rotationProp,
          },
        });

        result.cameraLayerId = cameraLayer.id;
        result.keyframeCount = positionKeyframes.length;
      }
    }

    // Create null objects at track points if requested
    if (options.createNulls && solve.trackPoints3D && solve.trackPoints3D.length > 0) {
      result.nullLayerIds = [];
      const maxNulls = 100; // Limit to avoid creating thousands

      const pointsToCreate = solve.trackPoints3D.slice(0, maxNulls);

      for (const point of pointsToCreate) {
        const pos = {
          x: point.position.x * scale + offset.x,
          y: (options.flipY ? -point.position.y : point.position.y) * scale + offset.y,
          z: (options.flipZ ? -point.position.z : point.position.z) * scale + offset.z,
        };

        const nullLayer = store.addLayer({
          type: 'control',
          name: `Track Point ${point.id}`,
          data: {
            iconSize: 10,
            iconShape: 'crosshair',
            iconColor: point.color
              ? `rgb(${point.color.r}, ${point.color.g}, ${point.color.b})`
              : '#FFFF00',
          },
        });

        if (nullLayer) {
          store.updateLayer(nullLayer.id, {
            threeD: true,
            transform: {
              ...nullLayer.transform,
              position: {
                defaultValue: pos,
                animated: false,
                keyframes: [],
              },
            },
          });

          result.nullLayerIds.push(nullLayer.id);
        }
      }

      if (solve.trackPoints3D.length > maxNulls) {
        result.warnings?.push(
          `Only created ${maxNulls} null objects out of ${solve.trackPoints3D.length} track points`
        );
      }
    }

    // Create point cloud layer if requested
    if (options.pointCloud?.create && solve.trackPoints3D && solve.trackPoints3D.length > 0) {
      const maxPoints = options.pointCloud.maxPoints ?? 50000;
      const pointSize = options.pointCloud.pointSize ?? 2;

      const positions: number[] = [];
      const colors: number[] = [];

      for (let i = 0; i < Math.min(solve.trackPoints3D.length, maxPoints); i++) {
        const pt = solve.trackPoints3D[i];
        positions.push(
          pt.position.x * scale + offset.x,
          (options.flipY ? -pt.position.y : pt.position.y) * scale + offset.y,
          (options.flipZ ? -pt.position.z : pt.position.z) * scale + offset.z
        );

        if (pt.color) {
          colors.push(pt.color.r / 255, pt.color.g / 255, pt.color.b / 255);
        } else {
          colors.push(1, 1, 0); // Yellow default
        }
      }

      const pointCloudLayer = store.addLayer({
        type: 'point_cloud',
        name: `Track Points (${solve.source})`,
        data: {
          positions: new Float32Array(positions),
          colors: new Float32Array(colors),
          pointSize,
          format: 'xyz_rgb',
        },
      });

      if (pointCloudLayer) {
        result.pointCloudLayerId = pointCloudLayer.id;
      }
    }

    result.success = true;
  } catch (error) {
    result.error = error instanceof Error ? error.message : 'Unknown error';
    result.success = false;
  }

  return result;
}

/**
 * Convert quaternion to rotation matrix (row-major)
 */
function quaternionToMatrix(w: number, x: number, y: number, z: number): number[] {
  const xx = x * x, yy = y * y, zz = z * z;
  const xy = x * y, xz = x * z, yz = y * z;
  const wx = w * x, wy = w * y, wz = w * z;

  return [
    1 - 2 * (yy + zz), 2 * (xy - wz), 2 * (xz + wy),
    2 * (xy + wz), 1 - 2 * (xx + zz), 2 * (yz - wx),
    2 * (xz - wy), 2 * (yz + wx), 1 - 2 * (xx + yy),
  ];
}

/**
 * Convert quaternion to Euler angles (degrees, XYZ order)
 */
function quaternionToEuler(
  w: number,
  x: number,
  y: number,
  z: number
): { x: number; y: number; z: number } {
  // Roll (X-axis rotation)
  const sinr_cosp = 2 * (w * x + y * z);
  const cosr_cosp = 1 - 2 * (x * x + y * y);
  const roll = Math.atan2(sinr_cosp, cosr_cosp);

  // Pitch (Y-axis rotation)
  const sinp = 2 * (w * y - z * x);
  let pitch: number;
  if (Math.abs(sinp) >= 1) {
    pitch = Math.sign(sinp) * Math.PI / 2; // Clamp to ±90°
  } else {
    pitch = Math.asin(sinp);
  }

  // Yaw (Z-axis rotation)
  const siny_cosp = 2 * (w * z + x * y);
  const cosy_cosp = 1 - 2 * (y * y + z * z);
  const yaw = Math.atan2(siny_cosp, cosy_cosp);

  // Convert to degrees
  const toDeg = 180 / Math.PI;
  return {
    x: roll * toDeg,
    y: pitch * toDeg,
    z: yaw * toDeg,
  };
}

/**
 * Export current camera animation to Weyl tracking format
 */
export function exportCameraToTrackingFormat(
  layerId: string
): CameraTrackingSolve | null {
  const store = useCompositorStore();
  const layer = store.layers.find(l => l.id === layerId);

  if (!layer || layer.type !== 'camera') {
    return null;
  }

  const comp = store.activeComposition;
  if (!comp) return null;

  const poses: CameraPose[] = [];

  // Get position and rotation keyframes
  const positionProp = layer.transform?.position;
  const rotationProp = layer.transform?.rotation;

  // Generate poses for each frame with keyframes
  const allFrames = new Set<number>();

  if (positionProp?.keyframes) {
    positionProp.keyframes.forEach(kf => allFrames.add(kf.frame));
  }
  if (rotationProp?.keyframes) {
    rotationProp.keyframes.forEach(kf => allFrames.add(kf.frame));
  }

  // If no keyframes, just export default pose
  if (allFrames.size === 0) {
    const pos = positionProp?.defaultValue ?? { x: 0, y: 0, z: 0 };
    const rot = rotationProp?.defaultValue ?? { x: 0, y: 0, z: 0 };

    poses.push({
      frame: 0,
      position: pos,
      rotation: eulerToQuaternion(rot.x, rot.y, rot.z),
      eulerAngles: rot,
    });
  } else {
    // Sort frames
    const sortedFrames = Array.from(allFrames).sort((a, b) => a - b);

    for (const frame of sortedFrames) {
      // Interpolate position
      const pos = interpolateProperty(positionProp, frame);
      const rot = interpolateProperty(rotationProp, frame);

      poses.push({
        frame,
        position: pos,
        rotation: eulerToQuaternion(rot.x, rot.y, rot.z),
        eulerAngles: rot,
      });
    }
  }

  // Get camera data for intrinsics
  const cameraData = layer.data as {
    fov?: { defaultValue?: number };
  };

  const fov = cameraData?.fov?.defaultValue ?? 50;
  const focalLength = comp.height / (2 * Math.tan((fov * Math.PI / 180) / 2));

  return {
    version: '1.0',
    source: 'custom',
    metadata: {
      sourceWidth: comp.width,
      sourceHeight: comp.height,
      frameRate: comp.frameRate,
      frameCount: comp.frameCount,
    },
    intrinsics: {
      focalLength,
      principalPoint: { x: comp.width / 2, y: comp.height / 2 },
      width: comp.width,
      height: comp.height,
      model: 'pinhole',
    },
    poses,
  };
}

/**
 * Convert Euler angles (degrees) to quaternion
 */
function eulerToQuaternion(
  x: number,
  y: number,
  z: number
): { w: number; x: number; y: number; z: number } {
  const toRad = Math.PI / 180;
  const cx = Math.cos(x * toRad / 2);
  const sx = Math.sin(x * toRad / 2);
  const cy = Math.cos(y * toRad / 2);
  const sy = Math.sin(y * toRad / 2);
  const cz = Math.cos(z * toRad / 2);
  const sz = Math.sin(z * toRad / 2);

  return {
    w: cx * cy * cz + sx * sy * sz,
    x: sx * cy * cz - cx * sy * sz,
    y: cx * sy * cz + sx * cy * sz,
    z: cx * cy * sz - sx * sy * cz,
  };
}

/**
 * Simple linear interpolation for properties
 */
function interpolateProperty<T extends { x: number; y: number; z: number }>(
  prop: AnimatableProperty<T> | undefined,
  frame: number
): T {
  if (!prop) {
    return { x: 0, y: 0, z: 0 } as T;
  }

  if (!prop.animated || !prop.keyframes || prop.keyframes.length === 0) {
    return prop.defaultValue;
  }

  // Find surrounding keyframes
  let prev = prop.keyframes[0];
  let next = prop.keyframes[0];

  for (const kf of prop.keyframes) {
    if (kf.frame <= frame) {
      prev = kf;
    }
    if (kf.frame >= frame && next.frame < frame) {
      next = kf;
      break;
    }
    next = kf;
  }

  if (prev.frame === next.frame) {
    return prev.value;
  }

  // Linear interpolation
  const t = (frame - prev.frame) / (next.frame - prev.frame);
  return {
    x: prev.value.x + (next.value.x - prev.value.x) * t,
    y: prev.value.y + (next.value.y - prev.value.y) * t,
    z: prev.value.z + (next.value.z - prev.value.z) * t,
  } as T;
}
