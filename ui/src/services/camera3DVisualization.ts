/**
 * Camera 3D Visualization Service
 * Generates geometry for camera wireframes, frustums, and guides
 */

import type { Camera3D, CustomViewState, ViewType } from "../types/camera";
import {
  addVec3,
  crossVec3,
  focalLengthToFOV,
  lookAtMat4,
  type Mat4,
  normalizeVec3,
  orthographicMat4,
  perspectiveMat4,
  scaleVec3,
  subVec3,
  transformPoint,
  type Vec3,
  vec3,
} from "./math3d";

export interface LineSegment {
  start: Vec3;
  end: Vec3;
  color: string;
}

export interface CameraVisualization {
  body: LineSegment[]; // Camera body wireframe
  frustum: LineSegment[]; // View frustum cone
  compositionBounds: LineSegment[]; // Comp as 3D rectangle
  poiLine: LineSegment | null; // Point of Interest connection
  focalPlane: LineSegment[]; // DOF focus plane indicator
  motionPath: Vec3[]; // Camera motion path points
}

export interface ViewMatrices {
  view: Mat4;
  projection: Mat4;
  viewProjection: Mat4;
}

// Camera body dimensions (in world units)
const CAMERA_BODY_SIZE = 40;
const CAMERA_LENS_LENGTH = 30;
const _CAMERA_LENS_RADIUS = 15;

/**
 * Generate camera body wireframe geometry
 */
export function generateCameraBody(camera: Camera3D): LineSegment[] {
  const lines: LineSegment[] = [];
  const color = "#ffcc00"; // Yellow for camera

  // Camera is at position, looking towards POI (two-node) or along orientation (one-node)
  const pos = camera.position;

  // Get camera forward direction
  let forward: Vec3;
  if (camera.type === "two-node") {
    forward = normalizeVec3(subVec3(camera.pointOfInterest, pos));
  } else {
    // One-node: use orientation to determine forward
    const radX = (camera.orientation.x * Math.PI) / 180;
    const radY = (camera.orientation.y * Math.PI) / 180;
    forward = vec3(
      Math.sin(radY) * Math.cos(radX),
      -Math.sin(radX),
      Math.cos(radY) * Math.cos(radX),
    );
  }

  // Get right and up vectors
  const worldUp = vec3(0, -1, 0); // Y-down in AE coordinate system
  let right = normalizeVec3(crossVec3(forward, worldUp));
  if (Number.isNaN(right.x)) {
    right = vec3(1, 0, 0);
  }
  const up = normalizeVec3(crossVec3(right, forward));

  // Camera body - box behind the position
  const halfSize = CAMERA_BODY_SIZE / 2;
  const bodyBack = addVec3(pos, scaleVec3(forward, -CAMERA_BODY_SIZE));

  // 8 corners of the body box
  const corners: Vec3[] = [];
  for (let z = 0; z < 2; z++) {
    const zOffset = z === 0 ? pos : bodyBack;
    for (let x = -1; x <= 1; x += 2) {
      for (let y = -1; y <= 1; y += 2) {
        corners.push(
          addVec3(
            addVec3(zOffset, scaleVec3(right, x * halfSize)),
            scaleVec3(up, y * halfSize),
          ),
        );
      }
    }
  }

  // Connect corners to form box
  // Front face
  lines.push({ start: corners[0], end: corners[1], color });
  lines.push({ start: corners[1], end: corners[3], color });
  lines.push({ start: corners[3], end: corners[2], color });
  lines.push({ start: corners[2], end: corners[0], color });

  // Back face
  lines.push({ start: corners[4], end: corners[5], color });
  lines.push({ start: corners[5], end: corners[7], color });
  lines.push({ start: corners[7], end: corners[6], color });
  lines.push({ start: corners[6], end: corners[4], color });

  // Connecting edges
  lines.push({ start: corners[0], end: corners[4], color });
  lines.push({ start: corners[1], end: corners[5], color });
  lines.push({ start: corners[2], end: corners[6], color });
  lines.push({ start: corners[3], end: corners[7], color });

  // Lens cone at front
  const lensEnd = addVec3(pos, scaleVec3(forward, CAMERA_LENS_LENGTH));
  const lensPoints = 8;
  for (let i = 0; i < lensPoints; i++) {
    const angle = (i / lensPoints) * Math.PI * 2;
    const nextAngle = ((i + 1) / lensPoints) * Math.PI * 2;

    const p1 = addVec3(
      addVec3(pos, scaleVec3(right, Math.cos(angle) * halfSize * 0.5)),
      scaleVec3(up, Math.sin(angle) * halfSize * 0.5),
    );
    const p2 = addVec3(
      addVec3(pos, scaleVec3(right, Math.cos(nextAngle) * halfSize * 0.5)),
      scaleVec3(up, Math.sin(nextAngle) * halfSize * 0.5),
    );

    // Lens ring at camera position
    lines.push({ start: p1, end: p2, color });

    // Lines to lens tip
    lines.push({ start: p1, end: lensEnd, color });
  }

  return lines;
}

/**
 * Generate view frustum wireframe
 */
export function generateFrustum(
  camera: Camera3D,
  compWidth: number,
  compHeight: number,
  maxDistance: number = 2000,
): LineSegment[] {
  const lines: LineSegment[] = [];
  const color = "#7c9cff"; // Blue for frustum

  const fovY = focalLengthToFOV(camera.focalLength, camera.filmSize);
  const aspect = compWidth / compHeight;
  const _fovX = fovY * aspect;

  const pos = camera.position;

  // Get camera basis vectors
  let forward: Vec3;
  if (camera.type === "two-node") {
    forward = normalizeVec3(subVec3(camera.pointOfInterest, pos));
  } else {
    const radX = (camera.orientation.x * Math.PI) / 180;
    const radY = (camera.orientation.y * Math.PI) / 180;
    forward = vec3(
      Math.sin(radY) * Math.cos(radX),
      -Math.sin(radX),
      Math.cos(radY) * Math.cos(radX),
    );
  }

  const worldUp = vec3(0, -1, 0);
  let right = normalizeVec3(crossVec3(forward, worldUp));
  if (Number.isNaN(right.x)) {
    right = vec3(1, 0, 0);
  }
  const up = normalizeVec3(crossVec3(right, forward));

  // Calculate frustum corners at near and far planes
  const near = camera.nearClip;
  const far = Math.min(camera.farClip, maxDistance);

  const nearHalfHeight = near * Math.tan((fovY * Math.PI) / 360);
  const nearHalfWidth = nearHalfHeight * aspect;
  const farHalfHeight = far * Math.tan((fovY * Math.PI) / 360);
  const farHalfWidth = farHalfHeight * aspect;

  // Near plane corners
  const nearCenter = addVec3(pos, scaleVec3(forward, near));
  const nearCorners = [
    addVec3(
      addVec3(nearCenter, scaleVec3(right, -nearHalfWidth)),
      scaleVec3(up, nearHalfHeight),
    ),
    addVec3(
      addVec3(nearCenter, scaleVec3(right, nearHalfWidth)),
      scaleVec3(up, nearHalfHeight),
    ),
    addVec3(
      addVec3(nearCenter, scaleVec3(right, nearHalfWidth)),
      scaleVec3(up, -nearHalfHeight),
    ),
    addVec3(
      addVec3(nearCenter, scaleVec3(right, -nearHalfWidth)),
      scaleVec3(up, -nearHalfHeight),
    ),
  ];

  // Far plane corners
  const farCenter = addVec3(pos, scaleVec3(forward, far));
  const farCorners = [
    addVec3(
      addVec3(farCenter, scaleVec3(right, -farHalfWidth)),
      scaleVec3(up, farHalfHeight),
    ),
    addVec3(
      addVec3(farCenter, scaleVec3(right, farHalfWidth)),
      scaleVec3(up, farHalfHeight),
    ),
    addVec3(
      addVec3(farCenter, scaleVec3(right, farHalfWidth)),
      scaleVec3(up, -farHalfHeight),
    ),
    addVec3(
      addVec3(farCenter, scaleVec3(right, -farHalfWidth)),
      scaleVec3(up, -farHalfHeight),
    ),
  ];

  // Draw near plane
  for (let i = 0; i < 4; i++) {
    lines.push({ start: nearCorners[i], end: nearCorners[(i + 1) % 4], color });
  }

  // Draw far plane
  for (let i = 0; i < 4; i++) {
    lines.push({ start: farCorners[i], end: farCorners[(i + 1) % 4], color });
  }

  // Connect near to far
  for (let i = 0; i < 4; i++) {
    lines.push({ start: nearCorners[i], end: farCorners[i], color });
  }

  return lines;
}

/**
 * Generate composition bounds as 3D rectangle at Z=0
 */
export function generateCompositionBounds(
  compWidth: number,
  compHeight: number,
): LineSegment[] {
  const color = "#00ff88"; // Green for comp bounds

  const corners: Vec3[] = [
    vec3(0, 0, 0),
    vec3(compWidth, 0, 0),
    vec3(compWidth, compHeight, 0),
    vec3(0, compHeight, 0),
  ];

  const lines: LineSegment[] = [];
  for (let i = 0; i < 4; i++) {
    lines.push({ start: corners[i], end: corners[(i + 1) % 4], color });
  }

  // Cross lines for center reference
  lines.push({ start: corners[0], end: corners[2], color: "#005533" });
  lines.push({ start: corners[1], end: corners[3], color: "#005533" });

  return lines;
}

/**
 * Generate point of interest connection line
 */
export function generatePOILine(camera: Camera3D): LineSegment | null {
  if (camera.type !== "two-node") {
    return null;
  }

  return {
    start: camera.position,
    end: camera.pointOfInterest,
    color: "#ff6600", // Orange for POI connection
  };
}

/**
 * Generate focal plane indicator for DOF
 */
export function generateFocalPlane(
  camera: Camera3D,
  compWidth: number,
  compHeight: number,
): LineSegment[] {
  if (!camera.depthOfField.enabled) {
    return [];
  }

  const color = "#ff00ff"; // Magenta for focal plane
  const lines: LineSegment[] = [];

  const pos = camera.position;
  const focusDist = camera.depthOfField.focusDistance;

  // Get camera forward direction
  let forward: Vec3;
  if (camera.type === "two-node") {
    forward = normalizeVec3(subVec3(camera.pointOfInterest, pos));
  } else {
    const radX = (camera.orientation.x * Math.PI) / 180;
    const radY = (camera.orientation.y * Math.PI) / 180;
    forward = vec3(
      Math.sin(radY) * Math.cos(radX),
      -Math.sin(radX),
      Math.cos(radY) * Math.cos(radX),
    );
  }

  const worldUp = vec3(0, -1, 0);
  let right = normalizeVec3(crossVec3(forward, worldUp));
  if (Number.isNaN(right.x)) {
    right = vec3(1, 0, 0);
  }
  const up = normalizeVec3(crossVec3(right, forward));

  // Focal plane center
  const center = addVec3(pos, scaleVec3(forward, focusDist));

  // Draw a rectangle representing the focal plane
  const halfWidth = compWidth / 4;
  const halfHeight = compHeight / 4;

  const corners = [
    addVec3(
      addVec3(center, scaleVec3(right, -halfWidth)),
      scaleVec3(up, halfHeight),
    ),
    addVec3(
      addVec3(center, scaleVec3(right, halfWidth)),
      scaleVec3(up, halfHeight),
    ),
    addVec3(
      addVec3(center, scaleVec3(right, halfWidth)),
      scaleVec3(up, -halfHeight),
    ),
    addVec3(
      addVec3(center, scaleVec3(right, -halfWidth)),
      scaleVec3(up, -halfHeight),
    ),
  ];

  for (let i = 0; i < 4; i++) {
    lines.push({ start: corners[i], end: corners[(i + 1) % 4], color });
  }

  return lines;
}

/**
 * Generate complete camera visualization
 */
export function generateCameraVisualization(
  camera: Camera3D,
  compWidth: number,
  compHeight: number,
  showFrustum: boolean = true,
  showBounds: boolean = true,
  showFocalPlane: boolean = false,
): CameraVisualization {
  return {
    body: generateCameraBody(camera),
    frustum: showFrustum ? generateFrustum(camera, compWidth, compHeight) : [],
    compositionBounds: showBounds
      ? generateCompositionBounds(compWidth, compHeight)
      : [],
    poiLine: generatePOILine(camera),
    focalPlane: showFocalPlane
      ? generateFocalPlane(camera, compWidth, compHeight)
      : [],
    motionPath: [], // Populated separately from keyframes
  };
}

/**
 * Calculate view matrices for a camera
 */
export function getCameraViewMatrices(
  camera: Camera3D,
  compWidth: number,
  compHeight: number,
): ViewMatrices {
  const aspect = compWidth / compHeight;
  const fovY = focalLengthToFOV(camera.focalLength, camera.filmSize);

  // View matrix
  let target: Vec3;
  if (camera.type === "two-node") {
    target = camera.pointOfInterest;
  } else {
    // One-node: calculate target from orientation
    const radX = (camera.orientation.x * Math.PI) / 180;
    const radY = (camera.orientation.y * Math.PI) / 180;
    const forward = vec3(
      Math.sin(radY) * Math.cos(radX),
      -Math.sin(radX),
      Math.cos(radY) * Math.cos(radX),
    );
    target = addVec3(camera.position, scaleVec3(forward, 1000));
  }

  const view = lookAtMat4(camera.position, target, vec3(0, -1, 0));

  // Projection matrix
  const projection = perspectiveMat4(
    fovY,
    aspect,
    camera.nearClip,
    camera.farClip,
  );

  // Combined view-projection
  const viewProjection = multiplyMat4Local(projection, view);

  return { view, projection, viewProjection };
}

/**
 * Calculate view matrices for orthographic views
 */
export function getOrthoViewMatrices(
  viewType: ViewType,
  compWidth: number,
  compHeight: number,
  customView?: CustomViewState,
): ViewMatrices {
  const aspect = compWidth / compHeight;
  let view: Mat4;
  let size = 1000; // Orthographic view size

  const centerX = compWidth / 2;
  const centerY = compHeight / 2;

  switch (viewType) {
    case "front":
      view = lookAtMat4(
        vec3(centerX, centerY, -2000),
        vec3(centerX, centerY, 0),
        vec3(0, -1, 0),
      );
      break;
    case "back":
      view = lookAtMat4(
        vec3(centerX, centerY, 2000),
        vec3(centerX, centerY, 0),
        vec3(0, -1, 0),
      );
      break;
    case "left":
      view = lookAtMat4(
        vec3(-2000, centerY, 0),
        vec3(centerX, centerY, 0),
        vec3(0, -1, 0),
      );
      break;
    case "right":
      view = lookAtMat4(
        vec3(centerX + 2000, centerY, 0),
        vec3(centerX, centerY, 0),
        vec3(0, -1, 0),
      );
      break;
    case "top":
      view = lookAtMat4(
        vec3(centerX, -2000, 0),
        vec3(centerX, centerY, 0),
        vec3(0, 0, 1),
      );
      break;
    case "bottom":
      view = lookAtMat4(
        vec3(centerX, centerY + 2000, 0),
        vec3(centerX, centerY, 0),
        vec3(0, 0, -1),
      );
      break;
    case "custom-1":
    case "custom-2":
    case "custom-3":
      if (customView) {
        const phi = (customView.orbitPhi * Math.PI) / 180;
        const theta = (customView.orbitTheta * Math.PI) / 180;
        const dist = customView.orbitDistance;

        const eye = vec3(
          customView.orbitCenter.x + dist * Math.sin(phi) * Math.sin(theta),
          customView.orbitCenter.y + dist * Math.cos(phi),
          customView.orbitCenter.z + dist * Math.sin(phi) * Math.cos(theta),
        );

        view = lookAtMat4(eye, customView.orbitCenter, vec3(0, -1, 0));
        size = 1000 / customView.orthoZoom;
      } else {
        view = lookAtMat4(
          vec3(centerX, centerY, -2000),
          vec3(centerX, centerY, 0),
          vec3(0, -1, 0),
        );
      }
      break;
    default:
      view = lookAtMat4(
        vec3(centerX, centerY, -2000),
        vec3(centerX, centerY, 0),
        vec3(0, -1, 0),
      );
  }

  const projection = orthographicMat4(
    -size * aspect,
    size * aspect,
    -size,
    size,
    1,
    10000,
  );

  const viewProjection = multiplyMat4Local(projection, view);

  return { view, projection, viewProjection };
}

// Helper function - need to add to math3d or inline
function multiplyMat4Local(a: Mat4, b: Mat4): Mat4 {
  const ae = a.elements;
  const be = b.elements;
  const result = new Float32Array(16);

  for (let row = 0; row < 4; row++) {
    for (let col = 0; col < 4; col++) {
      let sum = 0;
      for (let i = 0; i < 4; i++) {
        sum += ae[row + i * 4] * be[i + col * 4];
      }
      result[row + col * 4] = sum;
    }
  }

  return { elements: result };
}

/**
 * Project 3D point to 2D screen coordinates
 */
export function projectToScreen(
  point: Vec3,
  viewProjection: Mat4,
  screenWidth: number,
  screenHeight: number,
): { x: number; y: number; z: number; visible: boolean } {
  const transformed = transformPoint(viewProjection, point);
  const vp = viewProjection.elements;

  // Check if point is behind camera
  const w = point.x * vp[3] + point.y * vp[7] + point.z * vp[11] + vp[15];

  if (w <= 0) {
    return { x: 0, y: 0, z: transformed.z, visible: false };
  }

  // Normalize by w and convert to screen space
  const x = ((transformed.x / w) * 0.5 + 0.5) * screenWidth;
  const y = ((-transformed.y / w) * 0.5 + 0.5) * screenHeight;

  return {
    x,
    y,
    z: transformed.z / w,
    visible: true,
  };
}

/**
 * Generate 3D reference axes
 */
export function generate3DAxes(
  center: Vec3,
  length: number = 100,
): LineSegment[] {
  return [
    {
      start: center,
      end: addVec3(center, vec3(length, 0, 0)),
      color: "#ff0000",
    }, // X - Red
    {
      start: center,
      end: addVec3(center, vec3(0, length, 0)),
      color: "#00ff00",
    }, // Y - Green
    {
      start: center,
      end: addVec3(center, vec3(0, 0, length)),
      color: "#0000ff",
    }, // Z - Blue
  ];
}

/**
 * Generate grid lines on XY plane at Z=0
 */
export function generateGrid(
  compWidth: number,
  compHeight: number,
  spacing: number = 100,
): LineSegment[] {
  const lines: LineSegment[] = [];
  const color = "#333333";
  const centerColor = "#444444";

  const centerX = compWidth / 2;
  const centerY = compHeight / 2;
  const extent = Math.max(compWidth, compHeight);

  // Vertical lines
  for (let x = -extent; x <= extent + compWidth; x += spacing) {
    const isCenter = Math.abs(x - centerX) < spacing / 2;
    lines.push({
      start: vec3(x, -extent, 0),
      end: vec3(x, extent + compHeight, 0),
      color: isCenter ? centerColor : color,
    });
  }

  // Horizontal lines
  for (let y = -extent; y <= extent + compHeight; y += spacing) {
    const isCenter = Math.abs(y - centerY) < spacing / 2;
    lines.push({
      start: vec3(-extent, y, 0),
      end: vec3(extent + compWidth, y, 0),
      color: isCenter ? centerColor : color,
    });
  }

  return lines;
}
