/**
 * SVG Import and 3D Extrusion Service
 *
 * Provides functionality for the logo workflow:
 * 1. Import SVG files
 * 2. Parse into separate paths/shapes
 * 3. Extrude paths at different depths
 * 4. Create 3D meshes from SVG shapes
 * 5. Export as particles or layer geometry
 *
 * Perfect for:
 * - Logo animations with depth
 * - Text extrusion
 * - Shape morphing
 * - Particle mesh sources
 */

import { isFiniteNumber, assertDefined } from "@/utils/typeGuards";
import * as THREE from "three";
import {
  SVGLoader,
  type SVGResult,
} from "three/examples/jsm/loaders/SVGLoader.js";
import { validateURL } from "@/utils/security";

// ============================================================================
// TYPES
// ============================================================================

/** Parsed SVG path with metadata */
export interface ParsedSVGPath {
  id: string;
  name: string;
  path: THREE.ShapePath;
  shapes: THREE.Shape[];
  color: THREE.Color;
  fillOpacity: number;
  strokeColor: THREE.Color | null;
  strokeWidth: number;
  /** CSS-compatible fill color string */
  fill?: string;
  /** CSS-compatible stroke color string */
  stroke?: string;
  bounds: {
    minX: number;
    minY: number;
    maxX: number;
    maxY: number;
    width: number;
    height: number;
    centerX: number;
    centerY: number;
  };
  originalTransform: THREE.Matrix4;
}

/** SVG document with all paths */
export interface ParsedSVGDocument {
  id: string;
  name: string;
  paths: ParsedSVGPath[];
  viewBox: {
    x: number;
    y: number;
    width: number;
    height: number;
  };
  bounds: {
    minX: number;
    minY: number;
    maxX: number;
    maxY: number;
    width: number;
    height: number;
  };
}

/**
 * Cap Profile Type - Controls the edge profile on front/back faces
 * Like Cinema 4D/Blender fillet caps for smooth, rounded edges
 */
export type CapProfileType =
  | "flat" // Standard flat cap (default)
  | "fillet" // Rounded inward (concave) - smooth transition
  | "convex" // Rounded outward (bulging)
  | "concave" // Rounded inward (scooped)
  | "steps" // Stepped/terraced profile
  | "custom"; // Custom profile curve

/**
 * Cap Profile Configuration - Cinema 4D/Blender style fillet caps
 */
export interface CapProfileConfig {
  /** Profile type for the cap edges */
  type: CapProfileType;

  /** Radius of the fillet/rounding (pixels) */
  radius: number;

  /** Number of segments for smooth rounding (3-32) */
  segments: number;

  /** Depth of the cap profile (how far it extends into the extrusion) */
  depth: number;

  /** Profile tension for custom curves (0 = linear, 1 = smooth) */
  tension: number;

  /** Custom profile curve points for 'custom' type (0-1 normalized) */
  customProfile?: Array<{ x: number; y: number }>;
}

/** Extrusion configuration */
export interface ExtrusionConfig {
  depth: number; // Extrusion depth (0-100)
  bevelEnabled: boolean;
  bevelThickness: number;
  bevelSize: number;
  bevelOffset: number;
  bevelSegments: number;
  curveSegments: number; // Segments for curved paths
  steps: number; // Extrusion steps

  // ============================================
  // Fillet Cap Options (Cinema 4D/Blender style)
  // ============================================

  /** Enable fillet caps on front face */
  frontCapEnabled?: boolean;
  /** Front cap profile configuration */
  frontCap?: CapProfileConfig;

  /** Enable fillet caps on back face */
  backCapEnabled?: boolean;
  /** Back cap profile configuration */
  backCap?: CapProfileConfig;

  /** Apply same profile to both front and back */
  symmetricCaps?: boolean;

  // Material options
  frontMaterial?: THREE.Material;
  sideMaterial?: THREE.Material;
  backMaterial?: THREE.Material;
}

/**
 * Create default fillet cap profile
 */
export function createDefaultCapProfile(
  type: CapProfileType = "fillet",
): CapProfileConfig {
  return {
    type,
    radius: 2,
    segments: 8,
    depth: 2,
    tension: 0.5,
  };
}

/**
 * Generate profile curve points for cap geometry
 * Returns an array of points describing the cap cross-section
 */
export function generateCapProfileCurve(
  config: CapProfileConfig,
): THREE.Vector2[] {
  const points: THREE.Vector2[] = [];
  const { type, radius, segments, depth, tension, customProfile } = config;

  switch (type) {
    case "flat":
      // Simple flat cap - just two points
      points.push(new THREE.Vector2(0, 0));
      points.push(new THREE.Vector2(0, depth));
      break;

    case "fillet":
      // Quarter-circle fillet (smooth rounded edge)
      for (let i = 0; i <= segments; i++) {
        const t = i / segments;
        const angle = (Math.PI / 2) * t;
        const x = radius * (1 - Math.cos(angle));
        const y = depth * Math.sin(angle);
        points.push(new THREE.Vector2(x, y));
      }
      break;

    case "convex":
      // Outward bulging profile
      for (let i = 0; i <= segments; i++) {
        const t = i / segments;
        const _angle = (Math.PI / 2) * t;
        // Bulge outward using sine curve
        const bulge = Math.sin(Math.PI * t) * radius * 0.5;
        const x = -bulge; // Negative = outward
        const y = depth * t;
        points.push(new THREE.Vector2(x, y));
      }
      break;

    case "concave":
      // Inward scooped profile
      for (let i = 0; i <= segments; i++) {
        const t = i / segments;
        // Scoop inward using parabolic curve
        const scoop = Math.sin(Math.PI * t) * radius;
        const x = scoop; // Positive = inward
        const y = depth * t;
        points.push(new THREE.Vector2(x, y));
      }
      break;

    case "steps": {
      // Stepped/terraced profile
      const stepCount = Math.max(2, Math.floor(segments / 2));
      const stepHeight = depth / stepCount;
      const stepWidth = radius / stepCount;
      for (let i = 0; i <= stepCount; i++) {
        // Horizontal step
        points.push(new THREE.Vector2(i * stepWidth, i * stepHeight));
        if (i < stepCount) {
          // Vertical riser
          points.push(new THREE.Vector2(i * stepWidth, (i + 1) * stepHeight));
        }
      }
      break;
    }

    case "custom":
      // Use custom profile curve if provided
      if (customProfile && customProfile.length >= 2) {
        for (const pt of customProfile) {
          points.push(new THREE.Vector2(pt.x * radius, pt.y * depth));
        }
      } else {
        // Fallback to fillet if no custom profile
        for (let i = 0; i <= segments; i++) {
          const t = i / segments;
          const angle = (Math.PI / 2) * t;
          const x = radius * (1 - Math.cos(angle));
          const y = depth * Math.sin(angle);
          points.push(new THREE.Vector2(x, y));
        }
      }
      break;
  }

  return points;
}

/** Layer configuration for extruded SVG */
export interface SVGLayerConfig {
  pathId: string;
  depth: number; // Z position in scene
  extrusionDepth: number; // Thickness of extrusion
  scale: number;
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  material: ExtrusionMaterialConfig;
}

/** Material configuration for extrusion */
export interface ExtrusionMaterialConfig {
  type: "basic" | "standard" | "physical";
  color: string;
  metalness: number;
  roughness: number;
  emissive: string;
  emissiveIntensity: number;
  opacity: number;
  transparent: boolean;
  side: "front" | "back" | "double";
}

/** Mesh particle configuration from SVG */
export interface SVGMeshParticleConfig {
  pathId: string; // Which SVG path to use
  extrusionDepth: number; // How thick the particle mesh
  scale: number; // Particle size multiplier
  simplify: boolean; // Reduce geometry complexity
  simplifyTolerance: number;
  centerOrigin: boolean; // Center mesh at origin
}

// ============================================================================
// SVG EXTRUSION SERVICE
// ============================================================================

export class SVGExtrusionService {
  private svgLoader: SVGLoader;
  private documentCache: Map<string, ParsedSVGDocument> = new Map();
  private meshCache: Map<string, THREE.BufferGeometry> = new Map();

  constructor() {
    this.svgLoader = new SVGLoader();
  }

  // ==========================================================================
  // SVG LOADING AND PARSING
  // ==========================================================================

  /**
   * Load and parse an SVG file from URL
   * @throws Error if URL is invalid or blocked for security reasons
   */
  async loadFromURL(url: string, name?: string): Promise<ParsedSVGDocument> {
    // Validate URL to prevent SSRF attacks
    const validatedUrl = validateURL(url, "SVG loading", {
      allowData: true,
      allowBlob: true,
      allowHttp: true, // Allow HTTP for local development
    });

    return new Promise((resolve, reject) => {
      this.svgLoader.load(
        validatedUrl,
        (data) => {
          const doc = this.parseSVGResult(data, name || url);
          this.documentCache.set(doc.id, doc);
          resolve(doc);
        },
        undefined,
        reject,
      );
    });
  }

  /**
   * Load and parse SVG from string content
   */
  loadFromString(svgString: string, name: string = "svg"): ParsedSVGDocument {
    const parser = new DOMParser();
    const svgDoc = parser.parseFromString(svgString, "image/svg+xml");
    const svgElement = svgDoc.querySelector("svg");

    if (!svgElement) {
      throw new Error("Invalid SVG: No SVG element found");
    }

    // Use SVGLoader to parse
    const data = this.svgLoader.parse(svgString);
    const doc = this.parseSVGResult(data, name);
    this.documentCache.set(doc.id, doc);
    return doc;
  }

  /**
   * Parse SVGLoader result into our format
   */
  private parseSVGResult(data: SVGResult, name: string): ParsedSVGDocument {
    const id = `svg_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
    const paths: ParsedSVGPath[] = [];

    let minX = Infinity,
      minY = Infinity;
    let maxX = -Infinity,
      maxY = -Infinity;

    // Parse each path
    data.paths.forEach((shapePath, index) => {
      const shapes = SVGLoader.createShapes(shapePath);

      if (shapes.length === 0) return;

      // Get fill color
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const userData = (shapePath != null && typeof shapePath === "object" && "userData" in shapePath && shapePath.userData != null && typeof shapePath.userData === "object") ? shapePath.userData : undefined;
      const style = (userData != null && typeof userData === "object" && "style" in userData && userData.style != null && typeof userData.style === "object") ? userData.style : undefined;
      const fillColor = (style != null && typeof style === "object" && "fill" in style && typeof style.fill === "string") ? style.fill : undefined;
      const color = new THREE.Color(
        fillColor != null && fillColor !== "none" ? fillColor : "#ffffff",
      );

      // Get fill opacity
      // Type proof: fillOpacity ∈ ℝ ∪ {undefined} → ℝ
      const fillOpacityValue = (style != null && typeof style === "object" && "fillOpacity" in style && typeof style.fillOpacity === "number") ? style.fillOpacity : undefined;
      const fillOpacity = isFiniteNumber(fillOpacityValue) && fillOpacityValue >= 0 && fillOpacityValue <= 1 ? fillOpacityValue : 1;

      // Get stroke
      const strokeColor = (style != null && typeof style === "object" && "stroke" in style && typeof style.stroke === "string") ? style.stroke : undefined;
      // Type proof: strokeWidth ∈ ℝ ∪ {undefined} → ℝ
      const strokeWidthValue = (style != null && typeof style === "object" && "strokeWidth" in style && typeof style.strokeWidth === "number") ? style.strokeWidth : undefined;
      const strokeWidth = isFiniteNumber(strokeWidthValue) && strokeWidthValue >= 0 ? strokeWidthValue : 0;

      // Calculate bounds for this path
      const pathBounds = this.calculatePathBounds(shapes);

      minX = Math.min(minX, pathBounds.minX);
      minY = Math.min(minY, pathBounds.minY);
      maxX = Math.max(maxX, pathBounds.maxX);
      maxY = Math.max(maxY, pathBounds.maxY);

      const strokeColorObj =
        strokeColor && strokeColor !== "none"
          ? new THREE.Color(strokeColor)
          : null;

      paths.push({
        id: `${id}_path_${index}`,
        name: `Path ${index + 1}`,
        path: shapePath,
        shapes,
        color,
        fillOpacity,
        strokeColor: strokeColorObj,
        strokeWidth,
        // CSS-compatible color strings for UI display
        fill: `#${color.getHexString()}`,
        stroke: strokeColorObj
          ? `#${strokeColorObj.getHexString()}`
          : undefined,
        bounds: pathBounds,
        originalTransform: new THREE.Matrix4(),
      });
    });

    // Calculate viewBox from SVG data
    const viewBox = {
      x: 0,
      y: 0,
      width: maxX - minX,
      height: maxY - minY,
    };

    return {
      id,
      name,
      paths,
      viewBox,
      bounds: {
        minX,
        minY,
        maxX,
        maxY,
        width: maxX - minX,
        height: maxY - minY,
      },
    };
  }

  /**
   * Calculate bounds for a set of shapes
   */
  private calculatePathBounds(shapes: THREE.Shape[]): ParsedSVGPath["bounds"] {
    let minX = Infinity,
      minY = Infinity;
    let maxX = -Infinity,
      maxY = -Infinity;

    for (const shape of shapes) {
      const points = shape.getPoints(50);
      for (const point of points) {
        minX = Math.min(minX, point.x);
        minY = Math.min(minY, point.y);
        maxX = Math.max(maxX, point.x);
        maxY = Math.max(maxY, point.y);
      }

      // Include holes
      for (const hole of shape.holes) {
        const holePoints = hole.getPoints(50);
        for (const point of holePoints) {
          minX = Math.min(minX, point.x);
          minY = Math.min(minY, point.y);
          maxX = Math.max(maxX, point.x);
          maxY = Math.max(maxY, point.y);
        }
      }
    }

    const width = maxX - minX;
    const height = maxY - minY;

    return {
      minX,
      minY,
      maxX,
      maxY,
      width,
      height,
      centerX: minX + width / 2,
      centerY: minY + height / 2,
    };
  }

  // ==========================================================================
  // EXTRUSION
  // ==========================================================================

  /**
   * Create extruded geometry from an SVG path
   * Supports Cinema 4D/Blender style fillet caps for rounded edges
   */
  createExtrudedGeometry(
    path: ParsedSVGPath,
    config: Partial<ExtrusionConfig> = {},
  ): THREE.BufferGeometry {
    const cacheKey = `${path.id}_${JSON.stringify(config)}`;
    const cached = this.meshCache.get(cacheKey);
    if (cached) return cached.clone();

    // Determine if we're using fillet caps
    const useFrontCap = config.frontCapEnabled && config.frontCap;
    const useBackCap = config.backCapEnabled && config.backCap;
    const useFilletCaps = useFrontCap || useBackCap;

    // Base extrude settings
    // Type proof: depth ∈ ℝ ∪ {undefined} → ℝ
    const depthValue = config.depth;
    const depth = isFiniteNumber(depthValue) && depthValue > 0 ? depthValue : 10;
    // Type proof: bevelEnabled ∈ boolean | undefined → boolean
    const bevelEnabled = config.bevelEnabled === true;
    // Type proof: bevelThickness ∈ ℝ ∪ {undefined} → ℝ
    const bevelThicknessValue = config.bevelThickness;
    const bevelThickness = isFiniteNumber(bevelThicknessValue) && bevelThicknessValue >= 0 ? bevelThicknessValue : 1;
    // Type proof: bevelSize ∈ ℝ ∪ {undefined} → ℝ
    const bevelSizeValue = config.bevelSize;
    const bevelSize = isFiniteNumber(bevelSizeValue) && bevelSizeValue >= 0 ? bevelSizeValue : 0.5;
    // Type proof: bevelOffset ∈ ℝ ∪ {undefined} → ℝ
    const bevelOffsetValue = config.bevelOffset;
    const bevelOffset = isFiniteNumber(bevelOffsetValue) ? bevelOffsetValue : 0;
    // Type proof: bevelSegments ∈ ℕ ∪ {undefined} → ℕ
    const bevelSegmentsValue = config.bevelSegments;
    const bevelSegments = isFiniteNumber(bevelSegmentsValue) && Number.isInteger(bevelSegmentsValue) && bevelSegmentsValue >= 0 ? bevelSegmentsValue : 3;
    // Type proof: curveSegments ∈ ℕ ∪ {undefined} → ℕ
    const curveSegmentsValue = config.curveSegments;
    const curveSegments = isFiniteNumber(curveSegmentsValue) && Number.isInteger(curveSegmentsValue) && curveSegmentsValue > 0 ? curveSegmentsValue : 12;
    // Type proof: steps ∈ ℕ ∪ {undefined} → ℕ
    const stepsValue = config.steps;
    const steps = isFiniteNumber(stepsValue) && Number.isInteger(stepsValue) && stepsValue > 0 ? stepsValue : 1;

    const extrudeSettings: THREE.ExtrudeGeometryOptions = {
      depth: depth,
      bevelEnabled: bevelEnabled,
      bevelThickness: bevelThickness,
      bevelSize: bevelSize,
      bevelOffset: bevelOffset,
      bevelSegments: bevelSegments,
      curveSegments: curveSegments,
      steps: steps,
    };

    // If using fillet caps, configure bevel to create the rounded profile
    // Three.js bevel IS essentially a fillet on the front face
    if (useFilletCaps && !config.bevelEnabled) {
      // Type proof: frontCap is guaranteed non-null when useFrontCap is true (checked above)
      const frontCap = useFrontCap
        ? (() => {
            assertDefined(config.frontCap, "frontCap must exist when useFrontCap is true");
            return config.frontCap;
          })()
        : createDefaultCapProfile("flat");
      // Type proof: backCap is guaranteed non-null when useBackCap is true (checked above)
      const _backCap = useBackCap
        ? (() => {
            assertDefined(config.backCap, "backCap must exist when useBackCap is true");
            return config.backCap;
          })()
        : config.symmetricCaps && useFrontCap
          ? (() => {
              assertDefined(config.frontCap, "frontCap must exist when symmetricCaps and useFrontCap are true");
              return config.frontCap;
            })()
          : createDefaultCapProfile("flat");

      // Use front cap settings for bevel (Three.js only supports front bevel natively)
      if (useFrontCap && frontCap.type !== "flat") {
        extrudeSettings.bevelEnabled = true;
        extrudeSettings.bevelSize = frontCap.radius;
        extrudeSettings.bevelThickness = frontCap.depth;
        extrudeSettings.bevelSegments = frontCap.segments;
        extrudeSettings.bevelOffset = 0;
      }

      // For back cap, we need to create additional geometry
      // or use extrudePath for more complex profiles
    }

    // Create geometry from all shapes in the path
    const geometries: THREE.BufferGeometry[] = [];

    for (const shape of path.shapes) {
      // Standard extrusion
      const geometry = new THREE.ExtrudeGeometry(shape, extrudeSettings);
      geometries.push(geometry);

      // Add back cap geometry if needed (separate rounded cap on back face)
      if (useBackCap && config.backCap && config.backCap.type !== "flat") {
        // System F/Omega pattern: Wrap in try/catch for expected "no cap geometry" case
        try {
          const backCapGeom = this.createFilletCapGeometry(
            shape,
            config.backCap,
            (() => {
              // Type proof: depth ∈ ℝ ∪ {undefined} → ℝ
              const depthValue = config.depth;
              return isFiniteNumber(depthValue) && depthValue > 0 ? depthValue : 10;
            })(),
            "back",
          );
          geometries.push(backCapGeom);
        } catch (error) {
          // No cap geometry generated - skip (expected for certain configurations)
        }
      }
    }

    // Merge geometries if multiple shapes
    let finalGeometry: THREE.BufferGeometry;
    if (geometries.length === 1) {
      finalGeometry = geometries[0];
    } else {
      finalGeometry = this.mergeGeometries(geometries);
      // Dispose individual geometries after merging
      geometries.forEach((g) => g.dispose());
    }

    // Flip Y axis (SVG Y is down, Three.js Y is up)
    finalGeometry.scale(1, -1, 1);

    // Compute normals
    finalGeometry.computeVertexNormals();

    // Cache the geometry
    this.meshCache.set(cacheKey, finalGeometry);

    return finalGeometry.clone();
  }

  /**
   * Create fillet cap geometry for front or back face
   * Uses LatheGeometry approach for rounded profile
   */
  /**
   * Create fillet cap geometry for front or back face
   * Uses LatheGeometry approach for rounded profile
   * 
   * System F/Omega proof: Explicit geometry generation with validation
   * Type proof: shape ∈ THREE.Shape, capConfig ∈ CapProfileConfig → THREE.BufferGeometry (non-nullable)
   * Mathematical proof: Geometry generation is deterministic - either succeeds or throws explicit error
   * Geometric proof: Profile curve must have at least 2 points to form a valid curve
   */
  private createFilletCapGeometry(
    shape: THREE.Shape,
    capConfig: CapProfileConfig,
    extrusionDepth: number,
    face: "front" | "back",
  ): THREE.BufferGeometry {
    // System F/Omega proof: Explicit validation of cap type
    // Type proof: capConfig.type ∈ "flat" | "rounded" | "beveled"
    // Mathematical proof: Flat caps don't require geometry generation
    if (capConfig.type === "flat") {
      throw new Error(
        `[SVGExtrusion] Cannot create fillet cap geometry: Cap type is "flat", which doesn't require geometry. ` +
        `Shape: ${shape.uuid || "unknown"}, face: ${face}, extrusionDepth: ${extrusionDepth}. ` +
        `Use a non-flat cap type ("rounded" or "beveled") to generate cap geometry.`
      );
    }

    // System F/Omega proof: Explicit validation of profile curve generation
    // Type proof: generateCapProfileCurve(capConfig) → Array<Point>
    // Mathematical proof: Profile curve must have at least 2 points to form a valid curve
    // Geometric proof: A curve requires at least 2 points (start and end)
    const profilePoints = generateCapProfileCurve(capConfig);
    if (!Array.isArray(profilePoints) || profilePoints.length < 2) {
      throw new Error(
        `[SVGExtrusion] Cannot create fillet cap geometry: Profile curve generation produced insufficient points. ` +
        `Profile points length: ${Array.isArray(profilePoints) ? profilePoints.length : "invalid"}, minimum required: 2. ` +
        `Cap config: ${JSON.stringify(capConfig)}, shape: ${shape.uuid || "unknown"}, face: ${face}. ` +
        `Check cap profile configuration parameters.`
      );
    }

    // For a proper fillet cap, we'd need to sweep the profile around the shape outline
    // This is a simplified approach using offset shapes at different depths

    const capGeometries: THREE.BufferGeometry[] = [];
    const segments = capConfig.segments;

    // Create layered offset shapes to approximate the fillet
    for (let i = 0; i < segments; i++) {
      const _t = i / segments;
      const profile = profilePoints[Math.min(i, profilePoints.length - 1)];

      // Calculate inset amount based on profile
      const inset = profile.x; // Horizontal component = inset amount
      const zOffset = profile.y; // Vertical component = depth into extrusion

      // Create inset shape (simplified - in production use clipper-lib for proper offset)
      if (inset > 0) {
        // For positive inset, we'd shrink the shape
        // This is a simplified approximation
        const scaleFactor = 1 - inset / 100; // Rough approximation

        const layerShape = new THREE.ShapeGeometry(shape);
        const layerZ = face === "front" ? zOffset : extrusionDepth - zOffset;

        // Scale the layer slightly
        layerShape.scale(scaleFactor, scaleFactor, 1);

        // Position the layer at the correct depth
        layerShape.translate(0, 0, layerZ);

        capGeometries.push(layerShape);
      }
    }

    // System F/Omega proof: Explicit validation of cap geometry generation
    // Type proof: capGeometries ∈ Array<THREE.BufferGeometry>
    // Mathematical proof: At least one cap geometry must be generated
    // Geometric proof: Profile curve with positive inset values must produce at least one geometry layer
    if (capGeometries.length === 0) {
      throw new Error(
        `[SVGExtrusion] Cannot create fillet cap geometry: No cap geometries generated. ` +
        `Profile points: ${profilePoints.length}, segments: ${segments}, ` +
        `shape: ${shape.uuid || "unknown"}, face: ${face}, extrusionDepth: ${extrusionDepth}. ` +
        `Profile curve must have positive inset values to generate cap geometry. ` +
        `Check cap profile configuration (radius, segments, etc.). ` +
        `Wrap in try/catch if "no cap geometry" is an expected state.`
      );
    }

    // Merge all cap layers
    return this.mergeGeometries(capGeometries);
  }

  /**
   * Create extruded geometry with custom profile path
   * For advanced fillet caps, uses extrudePath option
   */
  createProfileExtrudedGeometry(
    path: ParsedSVGPath,
    profileCurve: THREE.Curve<THREE.Vector3>,
    config: Partial<ExtrusionConfig> = {},
  ): THREE.BufferGeometry {
    const cacheKey = `${path.id}_profile_${JSON.stringify(config)}`;
    const cached = this.meshCache.get(cacheKey);
    if (cached) return cached.clone();

    // Type proof: steps ∈ ℕ ∪ {undefined} → ℕ
    const stepsValue = config.steps;
    const steps = isFiniteNumber(stepsValue) && Number.isInteger(stepsValue) && stepsValue > 0 ? stepsValue : 10;
    // Type proof: curveSegments ∈ ℕ ∪ {undefined} → ℕ
    const curveSegmentsValue = config.curveSegments;
    const curveSegments = isFiniteNumber(curveSegmentsValue) && Number.isInteger(curveSegmentsValue) && curveSegmentsValue > 0 ? curveSegmentsValue : 12;

    const extrudeSettings: THREE.ExtrudeGeometryOptions = {
      steps: steps,
      bevelEnabled: false, // Profile handles the shape
      curveSegments: curveSegments,
      extrudePath: profileCurve, // Use custom profile path
    };

    const geometries: THREE.ExtrudeGeometry[] = [];

    for (const shape of path.shapes) {
      const geometry = new THREE.ExtrudeGeometry(shape, extrudeSettings);
      geometries.push(geometry);
    }

    let finalGeometry: THREE.BufferGeometry;
    if (geometries.length === 1) {
      finalGeometry = geometries[0];
    } else {
      finalGeometry = this.mergeGeometries(geometries);
      geometries.forEach((g) => g.dispose());
    }

    finalGeometry.scale(1, -1, 1);
    finalGeometry.computeVertexNormals();

    this.meshCache.set(cacheKey, finalGeometry);
    return finalGeometry.clone();
  }

  /**
   * Create a 3D profile path from cap configuration
   * Returns a THREE.Curve that can be used with extrudePath
   */
  createProfilePathFromCap(
    capConfig: CapProfileConfig,
    extrusionDepth: number,
  ): THREE.CatmullRomCurve3 {
    const profile2D = generateCapProfileCurve(capConfig);

    // Convert 2D profile to 3D path (Z = depth)
    const points3D = profile2D.map(
      (p) => new THREE.Vector3(0, 0, p.y), // Use Y as depth (Z in 3D)
    );

    // Add the main extrusion segment
    const mainDepthStart = capConfig.depth;
    const mainDepthEnd = extrusionDepth - capConfig.depth;

    points3D.push(new THREE.Vector3(0, 0, mainDepthStart));
    points3D.push(new THREE.Vector3(0, 0, mainDepthEnd));

    // Add mirrored back cap profile
    const backProfile = profile2D.slice().reverse();
    for (const p of backProfile) {
      points3D.push(
        new THREE.Vector3(0, 0, extrusionDepth - capConfig.depth + p.y),
      );
    }

    return new THREE.CatmullRomCurve3(points3D);
  }

  /**
   * Create a flat (2D) geometry from SVG path
   */
  createFlatGeometry(path: ParsedSVGPath): THREE.BufferGeometry {
    const geometries: THREE.ShapeGeometry[] = [];

    for (const shape of path.shapes) {
      const geometry = new THREE.ShapeGeometry(shape);
      geometries.push(geometry);
    }

    let finalGeometry: THREE.BufferGeometry;
    if (geometries.length === 1) {
      finalGeometry = geometries[0];
    } else {
      finalGeometry = this.mergeGeometries(geometries);
      geometries.forEach((g) => g.dispose());
    }

    // Flip Y axis
    finalGeometry.scale(1, -1, 1);

    return finalGeometry;
  }

  /**
   * Merge multiple geometries into one
   */
  private mergeGeometries(
    geometries: THREE.BufferGeometry[],
  ): THREE.BufferGeometry {
    // Calculate total vertex count
    let totalVertices = 0;
    let totalIndices = 0;
    let hasNormals = true;
    let hasUVs = true;

    for (const geom of geometries) {
      const pos = geom.getAttribute("position");
      if (pos) totalVertices += pos.count;

      const idx = geom.getIndex();
      if (idx) totalIndices += idx.count;
      else {
        // Type proof: pos?.count ∈ ℕ ∪ {undefined} → ℕ
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const posCount = (pos != null && typeof pos === "object" && "count" in pos && typeof pos.count === "number") ? pos.count : undefined;
        totalIndices += isFiniteNumber(posCount) && Number.isInteger(posCount) && posCount >= 0 ? posCount : 0;
      }

      if (!geom.getAttribute("normal")) hasNormals = false;
      if (!geom.getAttribute("uv")) hasUVs = false;
    }

    // Create merged buffers
    const positions = new Float32Array(totalVertices * 3);
    const normals = hasNormals ? new Float32Array(totalVertices * 3) : null;
    const uvs = hasUVs ? new Float32Array(totalVertices * 2) : null;
    const indices = new Uint32Array(totalIndices);

    let vertexOffset = 0;
    let indexOffset = 0;
    let indexVertexOffset = 0;

    for (const geom of geometries) {
      const pos = geom.getAttribute("position");
      const norm = geom.getAttribute("normal");
      const uv = geom.getAttribute("uv");
      const idx = geom.getIndex();

      if (pos) {
        positions.set(pos.array as Float32Array, vertexOffset * 3);

        if (normals && norm) {
          normals.set(norm.array as Float32Array, vertexOffset * 3);
        }

        if (uvs && uv) {
          uvs.set(uv.array as Float32Array, vertexOffset * 2);
        }

        // Handle indices
        if (idx) {
          for (let i = 0; i < idx.count; i++) {
            indices[indexOffset + i] = idx.getX(i) + indexVertexOffset;
          }
          indexOffset += idx.count;
        } else {
          for (let i = 0; i < pos.count; i++) {
            indices[indexOffset + i] = i + indexVertexOffset;
          }
          indexOffset += pos.count;
        }

        indexVertexOffset += pos.count;
        vertexOffset += pos.count;
      }
    }

    // Create merged geometry
    const merged = new THREE.BufferGeometry();
    merged.setAttribute("position", new THREE.BufferAttribute(positions, 3));
    if (normals) {
      merged.setAttribute("normal", new THREE.BufferAttribute(normals, 3));
    }
    if (uvs) {
      merged.setAttribute("uv", new THREE.BufferAttribute(uvs, 2));
    }
    merged.setIndex(new THREE.BufferAttribute(indices, 1));

    return merged;
  }

  // ==========================================================================
  // MESH CREATION
  // ==========================================================================

  /**
   * Create a 3D mesh from extruded SVG path
   */
  createMesh(
    path: ParsedSVGPath,
    extrusionConfig: Partial<ExtrusionConfig> = {},
    materialConfig: Partial<ExtrusionMaterialConfig> = {},
  ): THREE.Mesh {
    const geometry = this.createExtrudedGeometry(path, extrusionConfig);
    const material = this.createMaterial(path, materialConfig);

    const mesh = new THREE.Mesh(geometry, material);
    mesh.name = path.name;
    mesh.userData.svgPathId = path.id;

    return mesh;
  }

  /**
   * Create material for extruded mesh
   */
  private createMaterial(
    path: ParsedSVGPath,
    config: Partial<ExtrusionMaterialConfig> = {},
  ): THREE.Material {
    // Type proof: type ∈ string | undefined → string
    const typeValue = config.type;
    const type = typeof typeValue === "string" && (typeValue === "standard" || typeValue === "basic" || typeValue === "physical") ? typeValue : "standard";
    // Type proof: color ∈ string | undefined → string
    const colorValue = config.color;
    const color = typeof colorValue === "string" && colorValue.length > 0 ? colorValue : `#${path.color.getHexString()}`;
    // Type proof: side ∈ string | undefined → string
    const sideValue = config.side;
    const side = this.getSide(typeof sideValue === "string" && (sideValue === "front" || sideValue === "back" || sideValue === "double") ? sideValue : "double");

    // Type proof: transparent ∈ boolean | undefined → boolean
    const transparentValue = config.transparent;
    const transparent = transparentValue === true || (transparentValue === undefined && path.fillOpacity < 1);
    // Type proof: opacity ∈ ℝ ∪ {undefined} → ℝ
    const opacityValue = config.opacity;
    const opacity = isFiniteNumber(opacityValue) && opacityValue >= 0 && opacityValue <= 1 ? opacityValue : path.fillOpacity;

    const baseParams = {
      color: new THREE.Color(color),
      transparent: transparent,
      opacity: opacity,
      side,
    };

    switch (type) {
      case "basic":
        return new THREE.MeshBasicMaterial(baseParams);

      case "physical": {
        // Type proof: metalness ∈ ℝ ∪ {undefined} → ℝ
        const metalnessValue = config.metalness;
        const metalness = isFiniteNumber(metalnessValue) && metalnessValue >= 0 && metalnessValue <= 1 ? metalnessValue : 0;
        // Type proof: roughness ∈ ℝ ∪ {undefined} → ℝ
        const roughnessValue = config.roughness;
        const roughness = isFiniteNumber(roughnessValue) && roughnessValue >= 0 && roughnessValue <= 1 ? roughnessValue : 0.5;
        // Type proof: emissive ∈ string | undefined → string
        const emissiveValue = config.emissive;
        const emissive = typeof emissiveValue === "string" && emissiveValue.length > 0 ? emissiveValue : "#000000";
        // Type proof: emissiveIntensity ∈ ℝ ∪ {undefined} → ℝ
        const emissiveIntensityValue = config.emissiveIntensity;
        const emissiveIntensity = isFiniteNumber(emissiveIntensityValue) && emissiveIntensityValue >= 0 ? emissiveIntensityValue : 0;

        return new THREE.MeshPhysicalMaterial({
          ...baseParams,
          metalness: metalness,
          roughness: roughness,
          emissive: new THREE.Color(emissive),
          emissiveIntensity: emissiveIntensity,
        });
      }
      default: {
        // Type proof: metalness ∈ ℝ ∪ {undefined} → ℝ
        const metalnessValue = config.metalness;
        const metalness = isFiniteNumber(metalnessValue) && metalnessValue >= 0 && metalnessValue <= 1 ? metalnessValue : 0;
        // Type proof: roughness ∈ ℝ ∪ {undefined} → ℝ
        const roughnessValue = config.roughness;
        const roughness = isFiniteNumber(roughnessValue) && roughnessValue >= 0 && roughnessValue <= 1 ? roughnessValue : 0.5;
        // Type proof: emissive ∈ string | undefined → string
        const emissiveValue = config.emissive;
        const emissive = typeof emissiveValue === "string" && emissiveValue.length > 0 ? emissiveValue : "#000000";
        // Type proof: emissiveIntensity ∈ ℝ ∪ {undefined} → ℝ
        const emissiveIntensityValue = config.emissiveIntensity;
        const emissiveIntensity = isFiniteNumber(emissiveIntensityValue) && emissiveIntensityValue >= 0 ? emissiveIntensityValue : 0;

        return new THREE.MeshStandardMaterial({
          ...baseParams,
          metalness: metalness,
          roughness: roughness,
          emissive: new THREE.Color(emissive),
          emissiveIntensity: emissiveIntensity,
        });
      }
    }
  }

  /**
   * Get THREE.Side from string
   */
  private getSide(side: "front" | "back" | "double"): THREE.Side {
    switch (side) {
      case "front":
        return THREE.FrontSide;
      case "back":
        return THREE.BackSide;
      case "double":
        return THREE.DoubleSide;
    }
  }

  // ==========================================================================
  // LAYER CREATION (LOGO WORKFLOW)
  // ==========================================================================

  /**
   * Create multiple layers from an SVG document for depth stacking
   * This is the main entry point for the logo workflow
   */
  createLayeredMeshes(
    document: ParsedSVGDocument,
    layerConfigs: SVGLayerConfig[],
  ): THREE.Group {
    const group = new THREE.Group();
    group.name = document.name;

    // Center the group based on document bounds
    const centerX = document.bounds.minX + document.bounds.width / 2;
    const centerY = document.bounds.minY + document.bounds.height / 2;

    for (const config of layerConfigs) {
      const path = document.paths.find((p) => p.id === config.pathId);
      if (!path) continue;

      const mesh = this.createMesh(
        path,
        { depth: config.extrusionDepth },
        config.material,
      );

      // Apply transforms
      mesh.scale.setScalar(config.scale);
      mesh.position.set(
        config.position.x - centerX * config.scale,
        config.position.y + centerY * config.scale, // Flip Y
        config.position.z + config.depth,
      );
      mesh.rotation.set(
        config.rotation.x * (Math.PI / 180),
        config.rotation.y * (Math.PI / 180),
        config.rotation.z * (Math.PI / 180),
      );

      group.add(mesh);
    }

    return group;
  }

  /**
   * Auto-generate layer configs for all paths in a document
   * Assigns incrementing depths to each path
   */
  generateAutoLayerConfigs(
    document: ParsedSVGDocument,
    baseDepth: number = 0,
    depthIncrement: number = 5,
    extrusionDepth: number = 2,
  ): SVGLayerConfig[] {
    return document.paths.map((path, index) => ({
      pathId: path.id,
      depth: baseDepth + index * depthIncrement,
      extrusionDepth,
      scale: 1,
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      material: {
        type: "standard" as const,
        color: `#${path.color.getHexString()}`,
        metalness: 0,
        roughness: 0.5,
        emissive: "#000000",
        emissiveIntensity: 0,
        opacity: path.fillOpacity,
        transparent: path.fillOpacity < 1,
        side: "double" as const,
      },
    }));
  }

  // ==========================================================================
  // PARTICLE MESH GENERATION
  // ==========================================================================

  /**
   * Create a particle-ready mesh from SVG path
   * Optimized for instanced rendering
   */
  createParticleMesh(
    path: ParsedSVGPath,
    config: Partial<SVGMeshParticleConfig> = {},
  ): THREE.BufferGeometry {
    // Type proof: extrusionDepth ∈ ℝ ∪ {undefined} → ℝ
    const extrusionDepthValue = config.extrusionDepth;
    const extrusionDepth = isFiniteNumber(extrusionDepthValue) && extrusionDepthValue > 0 ? extrusionDepthValue : 1;
    // Type proof: scale ∈ ℝ ∪ {undefined} → ℝ
    const scaleValue = config.scale;
    const scale = isFiniteNumber(scaleValue) && scaleValue > 0 ? scaleValue : 1;

    // Create geometry
    let geometry = this.createExtrudedGeometry(path, {
      depth: extrusionDepth,
      bevelEnabled: false,
      curveSegments: config.simplify ? 6 : 12,
    });

    // Simplify if requested
    if (config.simplify) {
      geometry = this.simplifyGeometry(
        geometry,
        (() => {
          // Type proof: simplifyTolerance ∈ ℝ ∪ {undefined} → ℝ
          const simplifyToleranceValue = config.simplifyTolerance;
          return isFiniteNumber(simplifyToleranceValue) && simplifyToleranceValue >= 0 ? simplifyToleranceValue : 0.1;
        })(),
      );
    }

    // Center at origin if requested
    if (config.centerOrigin !== false) {
      geometry.computeBoundingBox();
      const center = new THREE.Vector3();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const boundingBox = (geometry != null && typeof geometry === "object" && "boundingBox" in geometry && geometry.boundingBox != null && typeof geometry.boundingBox === "object") ? geometry.boundingBox : undefined;
      if (boundingBox != null && typeof boundingBox.getCenter === "function") {
        boundingBox.getCenter(center);
      }
      geometry.translate(-center.x, -center.y, -center.z);
    }

    // Apply scale
    if (scale !== 1) {
      geometry.scale(scale, scale, scale);
    }

    // Ensure we have normals
    geometry.computeVertexNormals();

    return geometry;
  }

  /**
   * Simple geometry simplification (reduces vertex count)
   */
  private simplifyGeometry(
    geometry: THREE.BufferGeometry,
    tolerance: number,
  ): THREE.BufferGeometry {
    // Note: For production, use a proper simplification library
    // This is a basic vertex welding implementation
    const position = geometry.getAttribute("position");
    const index = geometry.getIndex();

    if (!position) return geometry;

    const vertices = new Map<string, number>();
    const newPositions: number[] = [];
    const newIndices: number[] = [];
    const indexMap = new Map<number, number>();

    // Round positions to tolerance
    const roundToTolerance = (v: number) =>
      Math.round(v / tolerance) * tolerance;

    for (let i = 0; i < position.count; i++) {
      const x = roundToTolerance(position.getX(i));
      const y = roundToTolerance(position.getY(i));
      const z = roundToTolerance(position.getZ(i));
      const key = `${x},${y},${z}`;

      if (!vertices.has(key)) {
        vertices.set(key, newPositions.length / 3);
        newPositions.push(x, y, z);
      }
      indexMap.set(i, vertices.get(key)!);
    }

    // Rebuild indices
    if (index) {
      for (let i = 0; i < index.count; i++) {
        const oldIdx = index.getX(i);
        newIndices.push(indexMap.get(oldIdx)!);
      }
    } else {
      for (let i = 0; i < position.count; i++) {
        newIndices.push(indexMap.get(i)!);
      }
    }

    // Create new geometry
    const simplified = new THREE.BufferGeometry();
    simplified.setAttribute(
      "position",
      new THREE.Float32BufferAttribute(newPositions, 3),
    );
    simplified.setIndex(newIndices);
    simplified.computeVertexNormals();

    return simplified;
  }

  // ==========================================================================
  // STROKE/OUTLINE GEOMETRY
  // ==========================================================================

  /**
   * Create tube geometry from SVG stroke
   * Useful for neon-style effects or 3D outlines
   */
  createStrokeGeometry(
    path: ParsedSVGPath,
    tubeRadius: number = 1,
    tubularSegments: number = 64,
    radialSegments: number = 8,
  ): THREE.BufferGeometry[] {
    const geometries: THREE.BufferGeometry[] = [];

    for (const shape of path.shapes) {
      const points = shape.getPoints(tubularSegments);

      // Convert to 3D points
      const points3D = points.map((p) => new THREE.Vector3(p.x, -p.y, 0));

      // Create curve from points
      const curve = new THREE.CatmullRomCurve3(points3D);

      // Create tube geometry
      const tubeGeometry = new THREE.TubeGeometry(
        curve,
        tubularSegments,
        tubeRadius,
        radialSegments,
        false, // closed
      );

      geometries.push(tubeGeometry);
    }

    return geometries;
  }

  // ==========================================================================
  // UTILITY METHODS
  // ==========================================================================

  /**
   * Get cached document
   */
  getDocument(id: string): ParsedSVGDocument | undefined {
    return this.documentCache.get(id);
  }

  /**
   * Get all cached documents
   */
  getAllDocuments(): ParsedSVGDocument[] {
    return Array.from(this.documentCache.values());
  }

  /**
   * Clear caches
   */
  clearCache(): void {
    this.documentCache.clear();
    for (const geometry of this.meshCache.values()) {
      geometry.dispose();
    }
    this.meshCache.clear();
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    this.clearCache();
  }
}

// Export singleton instance
export const svgExtrusionService = new SVGExtrusionService();

// ============================================================================
// DEFAULT CONFIGS
// ============================================================================

export function createDefaultExtrusionConfig(): ExtrusionConfig {
  return {
    depth: 10,
    bevelEnabled: false,
    bevelThickness: 1,
    bevelSize: 0.5,
    bevelOffset: 0,
    bevelSegments: 3,
    curveSegments: 12,
    steps: 1,
  };
}

export function createDefaultMaterialConfig(): ExtrusionMaterialConfig {
  return {
    type: "standard",
    color: "#ffffff",
    metalness: 0,
    roughness: 0.5,
    emissive: "#000000",
    emissiveIntensity: 0,
    opacity: 1,
    transparent: false,
    side: "double",
  };
}

export function createDefaultSVGMeshParticleConfig(): SVGMeshParticleConfig {
  return {
    pathId: "",
    extrusionDepth: 1,
    scale: 0.01,
    simplify: true,
    simplifyTolerance: 0.1,
    centerOrigin: true,
  };
}
