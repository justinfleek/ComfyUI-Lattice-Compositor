/**
 * Camera Tracking Types
 *
 * Defines types for importing camera tracking data from external tools
 * like COLMAP, OpenSfM, Blender, or custom JSON exports.
 */

/**
 * A 2D track point detected in footage
 */
export interface TrackPoint2D {
  /** Unique identifier for this track */
  id: string;

  /** Frame number this point was detected on */
  frame: number;

  /** X position in normalized coordinates (0-1) */
  x: number;

  /** Y position in normalized coordinates (0-1) */
  y: number;

  /** Tracking confidence (0-1) */
  confidence: number;

  /** Color of the point for visualization (optional) */
  color?: string;
}

/**
 * A 3D point reconstructed from track points
 */
export interface TrackPoint3D {
  /** Unique identifier */
  id: string;

  /** 3D position in world coordinates */
  position: { x: number; y: number; z: number };

  /** Color from texture (RGB 0-255) */
  color?: { r: number; g: number; b: number };

  /** List of 2D track point IDs that contributed to this 3D point */
  track2DIDs: string[];

  /** Reprojection error in pixels */
  error?: number;
}

/**
 * Camera intrinsics (lens parameters)
 */
export interface CameraIntrinsics {
  /** Focal length in pixels */
  focalLength: number;

  /** Principal point (optical center) */
  principalPoint: { x: number; y: number };

  /** Image dimensions */
  width: number;
  height: number;

  /** Radial distortion coefficients (k1, k2, k3) */
  distortion?: {
    k1?: number;
    k2?: number;
    k3?: number;
    p1?: number;  // Tangential
    p2?: number;
  };

  /** Camera model type */
  model?: 'pinhole' | 'radial' | 'brown' | 'fisheye';
}

/**
 * Camera pose at a specific frame
 */
export interface CameraPose {
  /** Frame number */
  frame: number;

  /** Camera position in world coordinates */
  position: { x: number; y: number; z: number };

  /** Camera rotation as quaternion (w, x, y, z) */
  rotation: { w: number; x: number; y: number; z: number };

  /** Or as Euler angles in degrees (optional alternative to quaternion) */
  eulerAngles?: { x: number; y: number; z: number };

  /** Field of view in degrees (if varying) */
  fov?: number;
}

/**
 * Ground plane definition for 3D alignment
 */
export interface GroundPlane {
  /** Normal vector of the plane */
  normal: { x: number; y: number; z: number };

  /** Point on the plane (origin) */
  origin: { x: number; y: number; z: number };

  /** Up direction */
  up: { x: number; y: number; z: number };

  /** Scale factor (units per pixel or world scale) */
  scale?: number;
}

/**
 * Complete camera tracking solve result
 */
export interface CameraTrackingSolve {
  /** Format version */
  version: string;

  /** Source application/tool */
  source: 'colmap' | 'opensfm' | 'blender' | 'nuke' | 'custom' | string;

  /** Solve metadata */
  metadata: {
    /** Original footage dimensions */
    sourceWidth: number;
    sourceHeight: number;

    /** Frame rate */
    frameRate: number;

    /** Total frames */
    frameCount: number;

    /** Average reprojection error */
    averageError?: number;

    /** Solve method used */
    solveMethod?: string;

    /** Date of solve */
    solveDate?: string;
  };

  /** Camera intrinsics (may vary per frame for zoom shots) */
  intrinsics: CameraIntrinsics | CameraIntrinsics[];

  /** Camera path - position and rotation per frame */
  cameraPath: CameraPose[];

  /** 3D track points (point cloud) */
  trackPoints3D?: TrackPoint3D[];

  /** 2D track points per frame (for visualization) */
  trackPoints2D?: TrackPoint2D[];

  /** Ground plane if defined */
  groundPlane?: GroundPlane;
}

/**
 * Import options for camera tracking data
 */
export interface CameraTrackingImportOptions {
  /** Scale factor to apply to positions */
  scale?: number;

  /** Offset to apply to positions */
  offset?: { x: number; y: number; z: number };

  /** Frame offset (add to all frame numbers) */
  frameOffset?: number;

  /** Flip Y axis (common for coordinate system differences) */
  flipY?: boolean;

  /** Flip Z axis */
  flipZ?: boolean;

  /** Import only camera path (skip point cloud) */
  cameraPathOnly?: boolean;

  /** Create camera layer automatically */
  createCamera?: boolean;

  /** Create null objects at track points */
  createNulls?: boolean;

  /** Point cloud layer settings */
  pointCloud?: {
    create: boolean;
    maxPoints?: number;
    pointSize?: number;
  };
}

/**
 * Result of importing camera tracking data
 */
export interface CameraTrackingImportResult {
  success: boolean;

  /** Created camera layer ID */
  cameraLayerId?: string;

  /** Created null layer IDs (for track points) */
  nullLayerIds?: string[];

  /** Created point cloud layer ID */
  pointCloudLayerId?: string;

  /** Number of keyframes added to camera */
  keyframeCount?: number;

  /** Warnings during import */
  warnings?: string[];

  /** Error message if failed */
  error?: string;
}

/**
 * COLMAP-specific types for parsing its output format
 */
export namespace COLMAPFormat {
  /** cameras.txt line format */
  export interface Camera {
    id: number;
    model: string;
    width: number;
    height: number;
    params: number[]; // Focal, cx, cy, distortion...
  }

  /** images.txt line format */
  export interface Image {
    id: number;
    qw: number;
    qx: number;
    qy: number;
    qz: number;
    tx: number;
    ty: number;
    tz: number;
    cameraId: number;
    name: string;
    points2D: { x: number; y: number; point3DId: number }[];
  }

  /** points3D.txt line format */
  export interface Point3D {
    id: number;
    x: number;
    y: number;
    z: number;
    r: number;
    g: number;
    b: number;
    error: number;
    trackIds: number[];
  }
}

/**
 * Blender motion tracking export format
 */
export namespace BlenderFormat {
  export interface MotionTrackingData {
    fps: number;
    clip_width: number;
    clip_height: number;
    camera: {
      focal_length: number;
      sensor_width: number;
    };
    tracks: Array<{
      name: string;
      markers: Array<{
        frame: number;
        co: [number, number]; // Normalized coordinates
      }>;
    }>;
    reconstruction?: {
      camera_poses: Array<{
        frame: number;
        location: [number, number, number];
        rotation: [number, number, number, number]; // Quaternion wxyz
      }>;
      points: Array<{
        co: [number, number, number];
        color?: [number, number, number];
      }>;
    };
  }
}
