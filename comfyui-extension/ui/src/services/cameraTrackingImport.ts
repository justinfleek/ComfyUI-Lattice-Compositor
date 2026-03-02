/**
 * Camera Tracking Import Service
 *
 * Imports camera tracking data from external tools and creates
 * camera layers with keyframed animation.
 *
 * Supported formats:
 * - Lattice JSON (native format)
 * - COLMAP (popular open-source SfM)
 * - Blender Motion Tracking export
 * - Generic JSON with camera path
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import { parseAndSanitize } from "@/services/security/jsonSanitizer";
import { useLayerStore } from "@/stores/layerStore";
import { useCameraStore } from "@/stores/cameraStore";
import { useProjectStore } from "@/stores/projectStore";
import {
  CameraTrackingSolveSchema,
  BlenderMotionTrackingDataSchema,
  LatticeFormatDetectionSchema,
  BlenderFormatDetectionSchema,
} from "@/schemas/imports/cameraTracking-schema";
import type { AnimatableProperty } from "@/types/animation";
import { createAnimatableProperty, createKeyframe } from "@/types/animation";
import type { Layer, PointCloudLayerData } from "@/types/project";
import type {
  CameraIntrinsics,
  CameraPose,
  CameraTrackingImportOptions,
  CameraTrackingImportResult,
  CameraTrackingSolve,
  COLMAPFormat,
  TrackPoint3D,
} from "@/types/cameraTracking";

/**
 * Parse Lattice native JSON format
 */
export function parseLatticeTrackingJSON(json: string): CameraTrackingSolve {
  const sanitizeResult = parseAndSanitize(json);
  if (!sanitizeResult.valid) {
    throw new Error(`Invalid JSON in Lattice tracking: ${sanitizeResult.error}`);
  }

  const parseResult = CameraTrackingSolveSchema.safeParse(sanitizeResult.data);
  if (!parseResult.success) {
    const issues = parseResult.error.issues
      .map((i) => `${i.path.join(".")}: ${i.message}`)
      .join("; ");
    throw new Error(`Invalid Lattice tracking data: ${issues}`);
  }

  return parseResult.data;
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
    throw new Error("No cameras found in COLMAP output");
  }

  // Convert to our format
  const intrinsics: CameraIntrinsics = {
    focalLength: firstCamera.params[0], // fx
    principalPoint: {
      x:
        firstCamera.params.length > 1
          ? firstCamera.params[1]
          : firstCamera.width / 2,
      y:
        firstCamera.params.length > 2
          ? firstCamera.params[2]
          : firstCamera.height / 2,
    },
    width: firstCamera.width,
    height: firstCamera.height,
    model: "pinhole",
  };

  // Convert images to camera path
  const cameraPath: CameraPose[] = images.map((img, index) => {
    // COLMAP stores camera-to-world inverse, need to invert
    // Quaternion is already world-to-camera, position needs adjustment
    const qw = img.qw,
      qx = img.qx,
      qy = img.qy,
      qz = img.qz;

    // Camera position in world = -R^T * t
    const rotMatrix = quaternionToMatrix(qw, qx, qy, qz);
    const worldPos = {
      x: -(
        rotMatrix[0] * img.tx +
        rotMatrix[1] * img.ty +
        rotMatrix[2] * img.tz
      ),
      y: -(
        rotMatrix[3] * img.tx +
        rotMatrix[4] * img.ty +
        rotMatrix[5] * img.tz
      ),
      z: -(
        rotMatrix[6] * img.tx +
        rotMatrix[7] * img.ty +
        rotMatrix[8] * img.tz
      ),
    };

    return {
      frame: index, // COLMAP doesn't store frame numbers, use index
      position: worldPos,
      rotation: { w: qw, x: qx, y: qy, z: qz },
    };
  });

  // Convert 3D points
  const trackPoints3D: TrackPoint3D[] = points3D.map((pt) => ({
    id: `pt_${pt.id}`,
    position: { x: pt.x, y: pt.y, z: pt.z },
    color: { r: pt.r, g: pt.g, b: pt.b },
    track2DIDs: pt.trackIds.map((id) => `track_${id}`),
    error: pt.error,
  }));

  return {
    version: "1.0",
    source: "colmap",
    metadata: {
      sourceWidth: firstCamera.width,
      sourceHeight: firstCamera.height,
      frameRate: 24, // Default, COLMAP doesn't store this
      frameCount: images.length,
    },
    intrinsics,
    cameraPath,
    trackPoints3D,
  };
}

/**
 * Parse COLMAP cameras.txt
 */
function parseCOLMAPCameras(content: string): COLMAPFormat.Camera[] {
  const cameras: COLMAPFormat.Camera[] = [];
  const lines = content.split("\n");

  for (const line of lines) {
    if (line.startsWith("#") || !line.trim()) continue;

    const parts = line.trim().split(/\s+/);
    if (parts.length < 5) continue;

    cameras.push({
      id: parseInt(parts[0], 10),
      model: parts[1],
      width: parseInt(parts[2], 10),
      height: parseInt(parts[3], 10),
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
  const lines = content.split("\n");
  let i = 0;

  while (i < lines.length) {
    const line = lines[i];
    if (line.startsWith("#") || !line.trim()) {
      i++;
      continue;
    }

    // Image line: IMAGE_ID, QW, QX, QY, QZ, TX, TY, TZ, CAMERA_ID, NAME
    const parts = line.trim().split(/\s+/);
    if (parts.length >= 10) {
      const image: COLMAPFormat.Image = {
        id: parseInt(parts[0], 10),
        qw: parseFloat(parts[1]),
        qx: parseFloat(parts[2]),
        qy: parseFloat(parts[3]),
        qz: parseFloat(parts[4]),
        tx: parseFloat(parts[5]),
        ty: parseFloat(parts[6]),
        tz: parseFloat(parts[7]),
        cameraId: parseInt(parts[8], 10),
        name: parts[9],
        points2D: [],
      };

      // Next line contains 2D points
      i++;
      if (i < lines.length && !lines[i].startsWith("#")) {
        const pointLine = lines[i].trim();
        if (pointLine) {
          const pointParts = pointLine.split(/\s+/);
          for (let j = 0; j < pointParts.length; j += 3) {
            if (j + 2 < pointParts.length) {
              image.points2D.push({
                x: parseFloat(pointParts[j]),
                y: parseFloat(pointParts[j + 1]),
                point3DId: parseInt(pointParts[j + 2], 10),
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
  const lines = content.split("\n");

  for (const line of lines) {
    if (line.startsWith("#") || !line.trim()) continue;

    const parts = line.trim().split(/\s+/);
    if (parts.length >= 8) {
      points.push({
        id: parseInt(parts[0], 10),
        x: parseFloat(parts[1]),
        y: parseFloat(parts[2]),
        z: parseFloat(parts[3]),
        r: parseInt(parts[4], 10),
        g: parseInt(parts[5], 10),
        b: parseInt(parts[6], 10),
        error: parseFloat(parts[7]),
        trackIds: parts
          .slice(8)
          .filter((_, i) => i % 2 === 0)
          .map((n) => parseInt(n, 10)),
      });
    }
  }

  return points;
}

/**
 * Parse Blender motion tracking JSON export
 */
export function parseBlenderTrackingJSON(json: string): CameraTrackingSolve {
  const sanitizeResult = parseAndSanitize(json);
  if (!sanitizeResult.valid) {
    throw new Error(`Invalid JSON in Blender tracking: ${sanitizeResult.error}`);
  }

  const parseResult = BlenderMotionTrackingDataSchema.safeParse(
    sanitizeResult.data,
  );
  if (!parseResult.success) {
    const issues = parseResult.error.issues
      .map((i) => `${i.path.join(".")}: ${i.message}`)
      .join("; ");
    throw new Error(`Invalid Blender tracking data: ${issues}`);
  }

  const data = parseResult.data;

  const intrinsics: CameraIntrinsics = {
    focalLength:
      (data.camera.focal_length / data.camera.sensor_width) * data.clip_width,
    principalPoint: {
      x: data.clip_width / 2,
      y: data.clip_height / 2,
    },
    width: data.clip_width,
    height: data.clip_height,
    model: "pinhole",
  };

  // Convert camera path if reconstruction exists
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const reconstruction = (typeof data.reconstruction === "object" && data.reconstruction !== null && "camera_poses" in data.reconstruction && Array.isArray(data.reconstruction.camera_poses))
    ? data.reconstruction.camera_poses
    : [];
  const cameraPath: CameraPose[] = reconstruction.map((pose) => ({
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
    }));

  // Convert 3D points
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const reconstructionPoints = (typeof data.reconstruction === "object" && data.reconstruction !== null && "points" in data.reconstruction && Array.isArray(data.reconstruction.points))
    ? data.reconstruction.points
    : [];
  const trackPoints3D: TrackPoint3D[] = reconstructionPoints.map((pt, i) => ({
      id: `pt_${i}`,
      position: { x: pt.co[0], y: pt.co[1], z: pt.co[2] },
      color: pt.color
        ? {
            r: Math.round(pt.color[0] * 255),
            g: Math.round(pt.color[1] * 255),
            b: Math.round(pt.color[2] * 255),
          }
        : undefined,
      track2DIDs: [],
    }));
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
  // Note: map() always returns an array, so this is defensive programming
  const trackPoints3DFinal: TrackPoint3D[] = (Array.isArray(trackPoints3D)) ? trackPoints3D : [];

  // Get frame count from tracks
  let maxFrame = 0;
  for (const track of data.tracks) {
    for (const marker of track.markers) {
      maxFrame = Math.max(maxFrame, marker.frame);
    }
  }

  return {
    version: "1.0",
    source: "blender",
    metadata: {
      sourceWidth: data.clip_width,
      sourceHeight: data.clip_height,
      frameRate: data.fps,
      frameCount: maxFrame + 1,
    },
    intrinsics,
    cameraPath,
    trackPoints3D: trackPoints3DFinal,
  };
}

/**
 * Detect format from file content
 */
export function detectTrackingFormat(
  content: string,
): "lattice" | "blender" | "colmap" | "unknown" {
  const sanitizeResult = parseAndSanitize(content);
  if (sanitizeResult.valid) {
    // Use loose detection schemas to check for format signatures
    if (LatticeFormatDetectionSchema.safeParse(sanitizeResult.data).success) {
      return "lattice";
    }

    if (BlenderFormatDetectionSchema.safeParse(sanitizeResult.data).success) {
      return "blender";
    }
  } else {
    // Not JSON, check for COLMAP text format
    if (content.includes("# Camera list") || content.includes("CAMERA_ID")) {
      return "colmap";
    }
  }

  return "unknown";
}

/**
 * Import camera tracking data and create layers
 */
export async function importCameraTracking(
  solve: CameraTrackingSolve,
  options: CameraTrackingImportOptions = {},
): Promise<CameraTrackingImportResult> {
  const layerStore = useLayerStore();
  const cameraStore = useCameraStore();
  const projectStore = useProjectStore();
  const warnings: string[] = [];
  let cameraLayerId: string | undefined = undefined;
  let nullLayerIds: string[] | undefined = undefined;
  let keyframeCount: number | undefined = undefined;

  try {
    // Type proof: scale ∈ ℝ ∪ {undefined} → ℝ
    const scaleValue = options.scale;
    const scale = isFiniteNumber(scaleValue) && scaleValue > 0 ? scaleValue : 1;
    // Type proof: offset ∈ {x, y, z} | undefined → {x, y, z}
    const offsetValue = options.offset;
    const offset = (() => {
      if (offsetValue && typeof offsetValue === "object" && "x" in offsetValue && "y" in offsetValue) {
        const zValue = "z" in offsetValue ? offsetValue.z : undefined;
        const z = isFiniteNumber(zValue) ? zValue : 0;
        return {
          x: isFiniteNumber(offsetValue.x) ? offsetValue.x : 0,
          y: isFiniteNumber(offsetValue.y) ? offsetValue.y : 0,
          z: z,
        };
      }
      return { x: 0, y: 0, z: 0 };
    })();
    // Type proof: frameOffset ∈ ℕ ∪ {undefined} → ℕ
    const frameOffsetValue = options.frameOffset;
    const frameOffset = isFiniteNumber(frameOffsetValue) && Number.isInteger(frameOffsetValue) && frameOffsetValue >= 0 ? frameOffsetValue : 0;

    // Apply coordinate transformations to camera path
    const transformedPath = solve.cameraPath.map((pose) => ({
      ...pose,
      frame: pose.frame + frameOffset,
      position: {
        x: pose.position.x * scale + offset.x,
        y:
          (options.flipY ? -pose.position.y : pose.position.y) * scale +
          offset.y,
        z:
          (options.flipZ ? -pose.position.z : pose.position.z) * scale +
          offset.z,
      },
    }));

    // Create camera layer if requested
    if (options.createCamera !== false) {
      // Get intrinsics
      const intrinsics = Array.isArray(solve.intrinsics)
        ? solve.intrinsics[0]
        : solve.intrinsics;

      // Calculate FOV from focal length
      const _fov =
        2 *
        Math.atan(intrinsics.height / (2 * intrinsics.focalLength)) *
        (180 / Math.PI);

      // Create camera layer first (needed for deterministic keyframe IDs)
      const { layer: cameraLayer } = cameraStore.createCameraLayer();
      cameraLayer.name = `Tracked Camera (${solve.source})`;

      // Create position keyframes with deterministic IDs
      const positionKeyframes = transformedPath.map((pose) =>
        createKeyframe(cameraLayer.id, "transform.position", pose.frame, pose.position, "linear"),
      );

      // Create rotation keyframes (convert quaternion to euler) with deterministic IDs
      const rotationKeyframes = transformedPath.map((pose) => {
        const euler = quaternionToEuler(
          pose.rotation.w,
          pose.rotation.x,
          pose.rotation.y,
          pose.rotation.z,
        );
        return createKeyframe(cameraLayer.id, "transform.rotation", pose.frame, euler, "linear");
      });

      // Apply keyframed transform
      // Position uses { x, y, z? } - z is optional but we include it for 3D
      const positionProp = createAnimatableProperty(
        "position",
        (() => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
          const posValue = (transformedPath.length > 0 && typeof transformedPath[0] === "object" && transformedPath[0] !== null && "position" in transformedPath[0] && typeof transformedPath[0].position === "object" && transformedPath[0].position !== null)
            ? transformedPath[0].position
            : null;
          if (posValue !== null && typeof posValue === "object" && "x" in posValue && "y" in posValue) {
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
            const zValue = ("z" in posValue && typeof posValue.z === "number") ? posValue.z : 0;
            const z = isFiniteNumber(zValue) ? zValue : 0;
            return {
              x: isFiniteNumber(posValue.x) ? posValue.x : 0,
              y: isFiniteNumber(posValue.y) ? posValue.y : 0,
              z: z,
            };
          }
          return { x: 0, y: 0, z: 0 };
        })(),
        "position",
        "Transform",
      );
      positionProp.animated = true;
      // Keyframe values include z which satisfies the z? optional type
      (positionProp as AnimatableProperty<{ x: number; y: number; z: number }>).keyframes = positionKeyframes;

      // Use orientation for 3D rotation (vector3), rotation is for 2D (number)
      const orientationProp = createAnimatableProperty(
        "orientation",
        (() => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
          const rotValue = (rotationKeyframes.length > 0 && typeof rotationKeyframes[0] === "object" && rotationKeyframes[0] !== null && "value" in rotationKeyframes[0] && typeof rotationKeyframes[0].value === "object" && rotationKeyframes[0].value !== null)
            ? rotationKeyframes[0].value
            : null;
          if (rotValue && typeof rotValue === "object" && "x" in rotValue && "y" in rotValue) {
            const zValue = "z" in rotValue ? rotValue.z : undefined;
            const z = isFiniteNumber(zValue) ? zValue : 0;
            return {
              x: isFiniteNumber(rotValue.x) ? rotValue.x : 0,
              y: isFiniteNumber(rotValue.y) ? rotValue.y : 0,
              z: z,
            };
          }
          return { x: 0, y: 0, z: 0 };
        })(),
        "vector3",
        "Transform",
      );
      orientationProp.animated = true;
      (orientationProp as AnimatableProperty<{ x: number; y: number; z: number }>).keyframes = rotationKeyframes;

      // Update the camera layer with camera-specific data and transform
      layerStore.updateLayer(cameraLayer.id, {
        threeD: true,
        transform: {
          ...cameraLayer.transform,
          position: positionProp as AnimatableProperty<{ x: number; y: number; z?: number }>,
          orientation: orientationProp,
        },
      });

      cameraLayerId = cameraLayer.id;
      keyframeCount = positionKeyframes.length;
    }

    // Create null objects at track points if requested
    if (
      options.createNulls &&
      solve.trackPoints3D &&
      solve.trackPoints3D.length > 0
    ) {
      nullLayerIds = [];
      const maxNulls = 100; // Limit to avoid creating thousands

      const pointsToCreate = solve.trackPoints3D.slice(0, maxNulls);

      for (const point of pointsToCreate) {
        const pos = {
          x: point.position.x * scale + offset.x,
          y:
            (options.flipY ? -point.position.y : point.position.y) * scale +
            offset.y,
          z:
            (options.flipZ ? -point.position.z : point.position.z) * scale +
            offset.z,
        };

        const nullLayer = layerStore.createLayer("control", `Track Point ${point.id}`);

        layerStore.updateLayer(nullLayer.id, {
          threeD: true,
          transform: {
            ...nullLayer.transform,
            position: createAnimatableProperty(
              "position",
              pos,
              "position",
              "Transform",
            ) as AnimatableProperty<{ x: number; y: number; z?: number }>,
          },
        });

        if (nullLayerIds === undefined) {
          nullLayerIds = [];
        }
        nullLayerIds.push(nullLayer.id);
      }

      if (solve.trackPoints3D.length > maxNulls) {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        warnings.push(
          `Only created ${maxNulls} null objects out of ${solve.trackPoints3D.length} track points`,
        );
      }
    }

    // Create point cloud layer if requested
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    if (
      typeof options.pointCloud === "object" && options.pointCloud !== null && "create" in options.pointCloud && options.pointCloud.create === true &&
      solve.trackPoints3D &&
      solve.trackPoints3D.length > 0
    ) {
      // Type proof: maxPoints ∈ ℕ ∪ {undefined} → ℕ
      const maxPointsValue = options.pointCloud.maxPoints;
      const maxPoints = isFiniteNumber(maxPointsValue) && Number.isInteger(maxPointsValue) && maxPointsValue > 0 ? maxPointsValue : 50000;
      // Type proof: pointSize ∈ ℝ ∪ {undefined} → ℝ
      const pointSizeValue = options.pointCloud.pointSize;
      const pointSize = isFiniteNumber(pointSizeValue) && pointSizeValue > 0 ? pointSizeValue : 2;

      const positions: number[] = [];
      const colors: number[] = [];

      for (
        let i = 0;
        i < Math.min(solve.trackPoints3D.length, maxPoints);
        i++
      ) {
        const pt = solve.trackPoints3D[i];
        positions.push(
          pt.position.x * scale + offset.x,
          (options.flipY ? -pt.position.y : pt.position.y) * scale + offset.y,
          (options.flipZ ? -pt.position.z : pt.position.z) * scale + offset.z,
        );

        if (pt.color) {
          colors.push(pt.color.r / 255, pt.color.g / 255, pt.color.b / 255);
        } else {
          colors.push(1, 1, 0); // Yellow default
        }
      }

      const pointCloudLayer = layerStore.createLayer("pointcloud", `Track Points (${solve.source})`);

      // Point cloud data structure - runtime data stored in positions/colors arrays
      // Note: This creates a minimal point cloud layer with runtime data
      // The actual PointCloudLayerData type expects assetId, but we're creating from tracking data
      const pointCloudData = {
        assetId: "", // Runtime-generated, no asset file
        format: "xyz" as const,
        pointCount: positions.length / 3,
        pointSize: createAnimatableProperty("pointSize", pointSize, "number"),
        sizeAttenuation: true,
        minPointSize: 1,
        maxPointSize: 10,
        colorMode: "rgb" as const,
        uniformColor: "#ffffff",
        // Runtime-specific data stored in these properties (not in type definition)
        positions: new Float32Array(positions),
        colors: new Float32Array(colors),
      };
      // Runtime-specific data stored separately (positions/colors not in type definition)
      // Use intersection type to include runtime properties
      const runtimeData: PointCloudLayerData & {
        positions: Float32Array;
        colors: Float32Array;
      } = pointCloudData as PointCloudLayerData & {
        positions: Float32Array;
        colors: Float32Array;
      };
      layerStore.updateLayer(pointCloudLayer.id, {
        data: runtimeData,
      });
      // Point cloud layer ID can be added to result if needed
      // For now, just create the layer - caller can access it via layerStore
    }

    return {
      success: true,
      warnings,
      cameraLayerId,
      nullLayerIds,
      keyframeCount,
    };
  } catch (error) {
    // Re-throw with context - don't silently fail
    const errorMessage = error instanceof Error ? error.message : String(error);
    throw new Error(`[CameraTrackingImport] Failed to import camera tracking data: ${errorMessage}. Check solve data format and layer creation.`);
  }
}

/**
 * Convert quaternion to rotation matrix (row-major)
 */
function quaternionToMatrix(
  w: number,
  x: number,
  y: number,
  z: number,
): number[] {
  const xx = x * x,
    yy = y * y,
    zz = z * z;
  const xy = x * y,
    xz = x * z,
    yz = y * z;
  const wx = w * x,
    wy = w * y,
    wz = w * z;

  return [
    1 - 2 * (yy + zz),
    2 * (xy - wz),
    2 * (xz + wy),
    2 * (xy + wz),
    1 - 2 * (xx + zz),
    2 * (yz - wx),
    2 * (xz - wy),
    2 * (yz + wx),
    1 - 2 * (xx + yy),
  ];
}

/**
 * Convert quaternion to Euler angles (degrees, XYZ order)
 */
function quaternionToEuler(
  w: number,
  x: number,
  y: number,
  z: number,
): { x: number; y: number; z: number } {
  // Roll (X-axis rotation)
  const sinr_cosp = 2 * (w * x + y * z);
  const cosr_cosp = 1 - 2 * (x * x + y * y);
  const roll = Math.atan2(sinr_cosp, cosr_cosp);

  // Pitch (Y-axis rotation)
  const sinp = 2 * (w * y - z * x);
  let pitch: number;
  if (Math.abs(sinp) >= 1) {
    pitch = (Math.sign(sinp) * Math.PI) / 2; // Clamp to ±90°
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
 * Export current camera animation to Lattice tracking format
 */
export function exportCameraToTrackingFormat(
  layerId: string,
): CameraTrackingSolve | null {
  const projectStore = useProjectStore();
  const layerStore = useLayerStore();
  const layer = layerStore.getLayerById(layerId);

  if (!layer || layer.type !== "camera") {
    throw new Error(`[CameraTrackingImport] Layer "${layerId}" not found or is not a camera layer`);
  }

  const comp = projectStore.getActiveComp();
  if (!comp) {
    throw new Error("[CameraTrackingImport] No active composition found");
  }

  const cameraPath: CameraPose[] = [];

  // Get position and orientation (3D rotation) properties
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const positionProp = (typeof layer.transform === "object" && layer.transform !== null && "position" in layer.transform && typeof layer.transform.position === "object" && layer.transform.position !== null)
    ? layer.transform.position
    : null;
  // Use orientation for 3D rotation, fall back to individual rotationX/Y/Z
  const orientationProp = (typeof layer.transform === "object" && layer.transform !== null && "orientation" in layer.transform && typeof layer.transform.orientation === "object" && layer.transform.orientation !== null)
    ? layer.transform.orientation
    : null;

  // Generate camera path for each frame with keyframes
  const allFrames = new Set<number>();

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (positionProp !== null && typeof positionProp === "object" && "keyframes" in positionProp && Array.isArray(positionProp.keyframes)) {
    positionProp.keyframes.forEach((kf) => allFrames.add(kf.frame));
  }
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  if (orientationProp !== null && typeof orientationProp === "object" && "keyframes" in orientationProp && Array.isArray(orientationProp.keyframes)) {
    orientationProp.keyframes.forEach((kf) => allFrames.add(kf.frame));
  }

  // Helper to ensure z is defined
  // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
  const ensureZ = (v: {
    x: number;
    y: number;
    z?: number;
  }): { x: number; y: number; z: number } => {
    const zValue = v.z;
    const z = isFiniteNumber(zValue) ? zValue : 0;
    return {
      x: v.x,
      y: v.y,
      z: z,
    };
  };

  // If no keyframes, just export default pose
  if (allFrames.size === 0) {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    const posValue = (positionProp !== null && typeof positionProp === "object" && "value" in positionProp && typeof positionProp.value === "object" && positionProp.value !== null)
      ? positionProp.value
      : null;
    const pos = ensureZ(posValue !== null && typeof posValue === "object" && "x" in posValue && "y" in posValue ? posValue : { x: 0, y: 0 });
    const rotValue = (orientationProp !== null && typeof orientationProp === "object" && "value" in orientationProp && typeof orientationProp.value === "object" && orientationProp.value !== null)
      ? orientationProp.value
      : null;
    const rot = (() => {
      if (rotValue && typeof rotValue === "object" && "x" in rotValue && "y" in rotValue) {
        const zValue = "z" in rotValue ? rotValue.z : undefined;
        const z = isFiniteNumber(zValue) ? zValue : 0;
        return {
          x: isFiniteNumber(rotValue.x) ? rotValue.x : 0,
          y: isFiniteNumber(rotValue.y) ? rotValue.y : 0,
          z: z,
        };
      }
      return { x: 0, y: 0, z: 0 };
    })();

    cameraPath.push({
      frame: 0,
      position: pos,
      rotation: eulerToQuaternion(rot.x, rot.y, rot.z),
      eulerAngles: rot,
    });
  } else {
    // Sort frames
    const sortedFrames = Array.from(allFrames).sort((a, b) => a - b);

    for (const frame of sortedFrames) {
      // Interpolate position - handle z being optional
      // System F/Omega: Convert null to undefined for function calls
      // Type proof: positionProp ∈ AnimatableProperty | null → AnimatableProperty | undefined
      const positionPropValue = positionProp !== null ? positionProp : undefined;
      const posValue = interpolatePositionProperty(positionPropValue, frame);
      const pos = ensureZ(posValue);
      // Type proof: orientationProp ∈ AnimatableProperty | null → AnimatableProperty | undefined
      const orientationPropValue = orientationProp !== null ? orientationProp : undefined;
      const rot = interpolateOrientationProperty(orientationPropValue, frame);

      cameraPath.push({
        frame,
        position: pos,
        rotation: eulerToQuaternion(rot.x, rot.y, rot.z),
        eulerAngles: rot,
      });
    }
  }

  // Get camera data for intrinsics
  const cameraData = layer.data as {
    fov?: { value?: number };
  };

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
  const cameraFov = (typeof cameraData === "object" && cameraData !== null && "fov" in cameraData && typeof cameraData.fov === "object" && cameraData.fov !== null && "value" in cameraData.fov && typeof cameraData.fov.value === "number")
    ? cameraData.fov.value
    : 50;
  const fovValue = cameraFov;
  const fov = isFiniteNumber(fovValue) && fovValue > 0 && fovValue <= 180 ? fovValue : 50;
  const focalLength =
    comp.settings.height / (2 * Math.tan((fov * Math.PI) / 180 / 2));

  return {
    version: "1.0",
    source: "custom",
    metadata: {
      sourceWidth: comp.settings.width,
      sourceHeight: comp.settings.height,
      frameRate: comp.settings.fps,
      frameCount: comp.settings.frameCount,
    },
    intrinsics: {
      focalLength,
      principalPoint: {
        x: comp.settings.width / 2,
        y: comp.settings.height / 2,
      },
      width: comp.settings.width,
      height: comp.settings.height,
      model: "pinhole",
    },
    cameraPath,
  };
}

/**
 * Convert Euler angles (degrees) to quaternion
 */
function eulerToQuaternion(
  x: number,
  y: number,
  z: number,
): { w: number; x: number; y: number; z: number } {
  const toRad = Math.PI / 180;
  const cx = Math.cos((x * toRad) / 2);
  const sx = Math.sin((x * toRad) / 2);
  const cy = Math.cos((y * toRad) / 2);
  const sy = Math.sin((y * toRad) / 2);
  const cz = Math.cos((z * toRad) / 2);
  const sz = Math.sin((z * toRad) / 2);

  return {
    w: cx * cy * cz + sx * sy * sz,
    x: sx * cy * cz - cx * sy * sz,
    y: cx * sy * cz + sx * cy * sz,
    z: cx * cy * sz - sx * sy * cz,
  };
}

/**
 * Simple linear interpolation for position properties (z is optional)
 */
function interpolatePositionProperty(
  prop: AnimatableProperty<{ x: number; y: number; z?: number }> | undefined,
  frame: number,
): { x: number; y: number; z?: number } {
  if (!prop) {
    return { x: 0, y: 0, z: 0 };
  }

  if (!prop.animated || !prop.keyframes || prop.keyframes.length === 0) {
    return prop.value;
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
  // Type proof: z ∈ ℝ ∪ {undefined} → z ∈ ℝ
  const prevZValue = prev.value.z;
  const prevZ = isFiniteNumber(prevZValue) ? prevZValue : 0;
  const nextZValue = next.value.z;
  const nextZ = isFiniteNumber(nextZValue) ? nextZValue : 0;
  return {
    x: prev.value.x + (next.value.x - prev.value.x) * t,
    y: prev.value.y + (next.value.y - prev.value.y) * t,
    z: prevZ + (nextZ - prevZ) * t,
  };
}

/**
 * Simple linear interpolation for orientation properties (all components required)
 */
function interpolateOrientationProperty(
  prop: AnimatableProperty<{ x: number; y: number; z: number }> | undefined,
  frame: number,
): { x: number; y: number; z: number } {
  if (!prop) {
    return { x: 0, y: 0, z: 0 };
  }

  if (!prop.animated || !prop.keyframes || prop.keyframes.length === 0) {
    return prop.value;
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
  };
}
