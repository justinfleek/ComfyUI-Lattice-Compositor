/**
 * 2.5D Camera System Types
 * Professional motion graphics camera functionality
 */

export type CameraType = "one-node" | "two-node";

export type AutoOrientMode = "off" | "orient-along-path" | "orient-towards-poi";

export type MeasureFilmSize = "horizontal" | "vertical" | "diagonal";

export type WireframeVisibility = "always" | "selected" | "off";

export interface Camera3D {
  id: string;
  name: string;
  type: CameraType;

  // === TRANSFORM ===
  position: { x: number; y: number; z: number };
  pointOfInterest: { x: number; y: number; z: number }; // Two-node only

  // Orientation (combined XYZ rotation)
  orientation: { x: number; y: number; z: number };

  // Individual rotation axes (additive with orientation)
  xRotation: number;
  yRotation: number;
  zRotation: number;

  // === LENS SETTINGS ===
  zoom: number; // Pixels (AE internal)
  focalLength: number; // mm (display)
  angleOfView: number; // Degrees (computed)
  filmSize: number; // mm (default 36 = full frame)
  measureFilmSize: MeasureFilmSize;

  // === DEPTH OF FIELD ===
  depthOfField: {
    enabled: boolean;
    focusDistance: number; // Pixels
    aperture: number; // Pixels (internal)
    fStop: number; // f-stop (display)
    blurLevel: number; // 0-1 multiplier
    lockToZoom: boolean;
  };

  // === IRIS PROPERTIES ===
  iris: {
    shape: number; // 0-10 (pentagon to circle)
    rotation: number; // Degrees
    roundness: number; // 0-1
    aspectRatio: number; // 0.5-2
    diffractionFringe: number; // 0-1
  };

  // === HIGHLIGHT PROPERTIES ===
  highlight: {
    gain: number; // 0-1
    threshold: number; // 0-1
    saturation: number; // 0-1
  };

  // === AUTO-ORIENT ===
  autoOrient: AutoOrientMode;

  // === CLIPPING ===
  nearClip: number;
  farClip: number;
}

// Camera presets with standard focal lengths
export const CAMERA_PRESETS = [
  { name: "15mm", focalLength: 15, angleOfView: 100.4, zoom: 533 },
  { name: "20mm", focalLength: 20, angleOfView: 84.0, zoom: 711 },
  { name: "24mm", focalLength: 24, angleOfView: 73.7, zoom: 853 },
  { name: "28mm", focalLength: 28, angleOfView: 65.5, zoom: 996 },
  { name: "35mm", focalLength: 35, angleOfView: 54.4, zoom: 1244 },
  { name: "50mm", focalLength: 50, angleOfView: 39.6, zoom: 1778 },
  { name: "80mm", focalLength: 80, angleOfView: 25.4, zoom: 2844 },
  { name: "135mm", focalLength: 135, angleOfView: 15.2, zoom: 4800 },
] as const;

// View types for multi-view layout
export type ViewType =
  | "active-camera"
  | "custom-1"
  | "custom-2"
  | "custom-3"
  | "front"
  | "back"
  | "left"
  | "right"
  | "top"
  | "bottom";

export type ViewLayout =
  | "1-view"
  | "2-view-horizontal"
  | "2-view-vertical"
  | "4-view";

export interface CustomViewState {
  orbitCenter: { x: number; y: number; z: number };
  orbitDistance: number;
  orbitPhi: number; // Vertical angle (0=top, 90=side)
  orbitTheta: number; // Horizontal angle
  orthoZoom: number; // For orthographic views
  orthoOffset: { x: number; y: number };
}

export interface ViewportState {
  layout: ViewLayout;
  views: ViewType[]; // Which view in each panel
  customViews: {
    "custom-1": CustomViewState;
    "custom-2": CustomViewState;
    "custom-3": CustomViewState;
  };
  activeViewIndex: number;
}

export interface ViewOptions {
  cameraWireframes: WireframeVisibility;
  lightWireframes: WireframeVisibility;
  showMotionPaths: boolean;
  showLayerPaths: boolean; // Shape/mask path visibility
  showLayerHandles: boolean;
  showSafeZones: boolean;
  showGrid: boolean;
  showRulers: boolean;
  show3DReferenceAxes: boolean;
  showCompositionBounds: boolean; // Canvas as 3D plane
  showFocalPlane: boolean; // DOF focus indicator
}

// Camera keyframes for animation
export interface CameraKeyframe {
  frame: number;

  // Transform (optional - only keyframed properties)
  position?: { x: number; y: number; z: number };
  pointOfInterest?: { x: number; y: number; z: number };
  orientation?: { x: number; y: number; z: number };
  xRotation?: number;
  yRotation?: number;
  zRotation?: number;

  // Lens
  zoom?: number;
  focalLength?: number;
  focusDistance?: number;
  aperture?: number;

  // Bezier handles for curve editor
  inHandle?: { x: number; y: number };
  outHandle?: { x: number; y: number };

  // Spatial interpolation type
  spatialInterpolation?:
    | "linear"
    | "bezier"
    | "auto-bezier"
    | "continuous-bezier";

  // Temporal interpolation type
  temporalInterpolation?: "linear" | "bezier" | "hold";

  // Separate dimensions (animate X/Y/Z independently)
  separateDimensions?: boolean;
}

// Default camera factory
export function createDefaultCamera(
  id: string,
  compWidth: number,
  compHeight: number,
): Camera3D {
  const centerX = compWidth / 2;
  const centerY = compHeight / 2;

  return {
    id,
    name: "Camera 1",
    type: "two-node",

    position: { x: centerX, y: centerY, z: -1500 },
    pointOfInterest: { x: centerX, y: centerY, z: 0 },

    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,

    zoom: 1778, // 50mm equivalent
    focalLength: 50,
    angleOfView: 39.6,
    filmSize: 36,
    measureFilmSize: "horizontal",

    depthOfField: {
      enabled: false,
      focusDistance: 1500,
      aperture: 50,
      fStop: 2.8,
      blurLevel: 1,
      lockToZoom: false,
    },

    iris: {
      shape: 7, // Heptagon by default
      rotation: 0,
      roundness: 0,
      aspectRatio: 1,
      diffractionFringe: 0,
    },

    highlight: {
      gain: 0,
      threshold: 1,
      saturation: 1,
    },

    autoOrient: "off",

    nearClip: 1,
    farClip: 10000,
  };
}

// Default viewport state
export function createDefaultViewportState(): ViewportState {
  return {
    layout: "1-view",
    views: ["active-camera"],
    customViews: {
      "custom-1": {
        orbitCenter: { x: 0, y: 0, z: 0 },
        orbitDistance: 2000,
        orbitPhi: 60,
        orbitTheta: 45,
        orthoZoom: 1,
        orthoOffset: { x: 0, y: 0 },
      },
      "custom-2": {
        orbitCenter: { x: 0, y: 0, z: 0 },
        orbitDistance: 2000,
        orbitPhi: 90,
        orbitTheta: 0,
        orthoZoom: 1,
        orthoOffset: { x: 0, y: 0 },
      },
      "custom-3": {
        orbitCenter: { x: 0, y: 0, z: 0 },
        orbitDistance: 2000,
        orbitPhi: 0,
        orbitTheta: 0,
        orthoZoom: 1,
        orthoOffset: { x: 0, y: 0 },
      },
    },
    activeViewIndex: 0,
  };
}

// Default view options
export function createDefaultViewOptions(): ViewOptions {
  return {
    cameraWireframes: "selected",
    lightWireframes: "selected",
    showMotionPaths: true,
    showLayerPaths: true,
    showLayerHandles: true,
    showSafeZones: false,
    showGrid: false,
    showRulers: true,
    show3DReferenceAxes: true,
    showCompositionBounds: true,
    showFocalPlane: false,
  };
}
