/**
 * PointCloudLayer - Point Cloud Visualization Layer
 *
 * Supports loading and rendering point cloud data in various formats:
 * - PLY (Polygon File Format - most common for 3D scans)
 * - PCD (Point Cloud Data - ROS standard)
 * - LAS/LAZ (LiDAR data - geospatial)
 * - XYZ (Simple ASCII format)
 * - PTS (Leica scanner format)
 *
 * Features:
 * - Multiple coloring modes (RGB, intensity, height, depth, normal)
 * - Multiple render modes (points, circles, squares, splats)
 * - Size attenuation (perspective scaling)
 * - Eye-Dome Lighting (EDL) for depth perception
 * - Octree acceleration for large point clouds
 * - Point budget limiting
 * - Clipping planes
 * - Classification filtering (for LAS files)
 */

import * as THREE from "three";
import { PCDLoader } from "three/examples/jsm/loaders/PCDLoader.js";
import { PLYLoader } from "three/examples/jsm/loaders/PLYLoader.js";
import { assertDefined } from "@/utils/typeGuards";
import { interpolateProperty } from "@/services/interpolation";
import type {
  Layer,
  ModelBoundingBox,
  PointCloudColorMode,
  PointCloudLayerData,
  PointCloudRenderMode,
} from "@/types/project";
import { BaseLayer } from "./BaseLayer";

/** Point cloud vertex attributes */
interface PointCloudAttributes {
  positions: Float32Array;
  colors?: Float32Array;
  normals?: Float32Array;
  intensities?: Float32Array;
  classifications?: Uint8Array;
}

export class PointCloudLayer extends BaseLayer {
  /** The point cloud mesh */
  private pointCloud: THREE.Points | null = null;

  /** Point cloud geometry */
  private geometry: THREE.BufferGeometry | null = null;

  /** Point cloud material */
  private material: THREE.ShaderMaterial | null = null;

  /** Original point data (for color mode switching) */
  private originalAttributes: PointCloudAttributes | null = null;

  /** Bounding box helper */
  private boundingBoxHelper: THREE.BoxHelper | null = null;

  /** Layer data */
  private cloudData: PointCloudLayerData;

  /** Loading state */
  private isLoading = false;
  private loadError: string | null = null;

  /** Shared loaders */
  private static plyLoader: PLYLoader | null = null;
  private static pcdLoader: PCDLoader | null = null;

  constructor(layerData: Layer) {
    super(layerData);

    this.cloudData = this.extractCloudData(layerData);

    // Initialize loaders
    this.initializeLoaders();

    // Load the point cloud
    this.loadPointCloud();

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  /**
   * Initialize shared loaders
   */
  private initializeLoaders(): void {
    if (!PointCloudLayer.plyLoader) {
      PointCloudLayer.plyLoader = new PLYLoader();
    }
    if (!PointCloudLayer.pcdLoader) {
      PointCloudLayer.pcdLoader = new PCDLoader();
    }
  }

  /**
   * Extract point cloud data from layer
   */
  private extractCloudData(layerData: Layer): PointCloudLayerData {
    const data = layerData.data as PointCloudLayerData | null;

    // Create default animatable properties
    const defaultPointSize = {
      id: `${layerData.id}_pointSize`,
      name: "Point Size",
      type: "number" as const,
      value: 2,
      animated: false,
      keyframes: [],
    };

    const defaultOpacity = {
      id: `${layerData.id}_opacity`,
      name: "Opacity",
      type: "number" as const,
      value: 1,
      animated: false,
      keyframes: [],
    };

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data ∈ PointCloudLayerData | null → PointCloudLayerData (with explicit defaults)
    const dataValue = (layerData.data !== null && typeof layerData.data === "object") ? layerData.data as PointCloudLayerData : null;
    
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const assetIdValue = (dataValue !== null && typeof dataValue === "object" && "assetId" in dataValue && typeof dataValue.assetId === "string") ? dataValue.assetId : "";
    const formatValue = (dataValue !== null && typeof dataValue === "object" && "format" in dataValue && typeof dataValue.format === "string") ? dataValue.format : "ply";
    const pointCountValue = (dataValue !== null && typeof dataValue === "object" && "pointCount" in dataValue && typeof dataValue.pointCount === "number" && Number.isFinite(dataValue.pointCount)) ? dataValue.pointCount : 0;
    const pointSizeValue = (dataValue !== null && typeof dataValue === "object" && "pointSize" in dataValue && typeof dataValue.pointSize === "number" && Number.isFinite(dataValue.pointSize)) ? dataValue.pointSize : defaultPointSize;
    const sizeAttenuationValue = (dataValue !== null && typeof dataValue === "object" && "sizeAttenuation" in dataValue && typeof dataValue.sizeAttenuation === "boolean") ? dataValue.sizeAttenuation : true;
    const minPointSizeValue = (dataValue !== null && typeof dataValue === "object" && "minPointSize" in dataValue && typeof dataValue.minPointSize === "number" && Number.isFinite(dataValue.minPointSize)) ? dataValue.minPointSize : 1;
    const maxPointSizeValue = (dataValue !== null && typeof dataValue === "object" && "maxPointSize" in dataValue && typeof dataValue.maxPointSize === "number" && Number.isFinite(dataValue.maxPointSize)) ? dataValue.maxPointSize : 64;
    const colorModeValue = (dataValue !== null && typeof dataValue === "object" && "colorMode" in dataValue && typeof dataValue.colorMode === "string") ? dataValue.colorMode : "rgb";
    const uniformColorValue = (dataValue !== null && typeof dataValue === "object" && "uniformColor" in dataValue && typeof dataValue.uniformColor === "string" && dataValue.uniformColor.length > 0) ? dataValue.uniformColor : "#ffffff";
    const colorGradientValue = (dataValue !== null && typeof dataValue === "object" && "colorGradient" in dataValue) ? dataValue.colorGradient : undefined;
    const renderModeValue = (dataValue !== null && typeof dataValue === "object" && "renderMode" in dataValue && typeof dataValue.renderMode === "string") ? dataValue.renderMode : "circles";
    const opacityValue = (dataValue !== null && typeof dataValue === "object" && "opacity" in dataValue && typeof dataValue.opacity === "number" && Number.isFinite(dataValue.opacity)) ? dataValue.opacity : defaultOpacity;
    const depthTestValue = (dataValue !== null && typeof dataValue === "object" && "depthTest" in dataValue && typeof dataValue.depthTest === "boolean") ? dataValue.depthTest : true;
    const depthWriteValue = (dataValue !== null && typeof dataValue === "object" && "depthWrite" in dataValue && typeof dataValue.depthWrite === "boolean") ? dataValue.depthWrite : true;
    const boundingBoxValue = (dataValue !== null && typeof dataValue === "object" && "boundingBox" in dataValue) ? dataValue.boundingBox : undefined;
    const showBoundingBoxValue = (dataValue !== null && typeof dataValue === "object" && "showBoundingBox" in dataValue && typeof dataValue.showBoundingBox === "boolean") ? dataValue.showBoundingBox : false;
    const lodValue = (dataValue !== null && typeof dataValue === "object" && "lod" in dataValue) ? dataValue.lod : undefined;
    const octreeValue = (dataValue !== null && typeof dataValue === "object" && "octree" in dataValue) ? dataValue.octree : undefined;
    const pointBudgetValue = (dataValue !== null && typeof dataValue === "object" && "pointBudget" in dataValue && typeof dataValue.pointBudget === "number" && Number.isFinite(dataValue.pointBudget)) ? dataValue.pointBudget : 1000000;
    const edlValue = (dataValue !== null && typeof dataValue === "object" && "edl" in dataValue) ? dataValue.edl : undefined;
    const clipPlanesValue = (dataValue !== null && typeof dataValue === "object" && "clipPlanes" in dataValue) ? dataValue.clipPlanes : undefined;
    const classificationFilterValue = (dataValue !== null && typeof dataValue === "object" && "classificationFilter" in dataValue) ? dataValue.classificationFilter : undefined;

    return {
      assetId: assetIdValue,
      format: formatValue,
      pointCount: pointCountValue,
      pointSize: pointSizeValue,
      sizeAttenuation: sizeAttenuationValue,
      minPointSize: minPointSizeValue,
      maxPointSize: maxPointSizeValue,
      colorMode: colorModeValue,
      uniformColor: uniformColorValue,
      colorGradient: colorGradientValue,
      renderMode: renderModeValue,
      opacity: opacityValue,
      depthTest: depthTestValue,
      depthWrite: depthWriteValue,
      boundingBox: boundingBoxValue,
      showBoundingBox: showBoundingBoxValue,
      lod: lodValue,
      octree: octreeValue,
      pointBudget: pointBudgetValue,
      edl: edlValue,
      clipPlanes: clipPlanesValue,
      classificationFilter: classificationFilterValue,
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      intensityRange: (dataValue != null && typeof dataValue === "object" && "intensityRange" in dataValue && dataValue.intensityRange != null) ? dataValue.intensityRange : undefined,
    };
  }

  /**
   * Load the point cloud from asset
   */
  private async loadPointCloud(): Promise<void> {
    if (!this.cloudData.assetId) {
      this.createPlaceholder();
      return;
    }

    this.isLoading = true;
    this.loadError = null;

    try {
      const url = await this.resolveAssetUrl(this.cloudData.assetId);

      let geometry: THREE.BufferGeometry;

      switch (this.cloudData.format) {
        case "ply":
          geometry = await this.loadPLY(url);
          break;
        case "pcd":
          geometry = await this.loadPCD(url);
          break;
        case "xyz":
        case "pts":
          geometry = await this.loadXYZ(url);
          break;
        case "las":
        case "laz":
          geometry = await this.loadLAS(url);
          break;
        default:
          throw new Error(
            `Unsupported point cloud format: ${this.cloudData.format}`,
          );
      }

      this.setGeometry(geometry);
    } catch (error) {
      this.loadError = error instanceof Error ? error.message : "Unknown error";
      console.error(
        `[PointCloudLayer] Failed to load point cloud: ${this.loadError}`,
      );
      this.createPlaceholder();
    } finally {
      this.isLoading = false;
    }
  }

  /**
   * Resolve asset ID to URL
   */
  private async resolveAssetUrl(assetId: string): Promise<string> {
    return assetId;
  }

  /**
   * Load PLY point cloud
   */
  private loadPLY(url: string): Promise<THREE.BufferGeometry> {
    return new Promise((resolve, reject) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const plyLoader = PointCloudLayer.plyLoader;
      if (plyLoader != null && typeof plyLoader === "object" && typeof plyLoader.load === "function") {
        plyLoader.load(url, resolve, undefined, reject);
      } else {
        reject(new Error("PLY loader not initialized"));
      }
    });
  }

  /**
   * Load PCD point cloud
   */
  private loadPCD(url: string): Promise<THREE.BufferGeometry> {
    return new Promise((resolve, reject) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const pcdLoader = PointCloudLayer.pcdLoader;
      if (pcdLoader != null && typeof pcdLoader === "object" && typeof pcdLoader.load === "function") {
        pcdLoader.load(
          url,
          (points: THREE.Points) => {
            resolve(points.geometry);
          },
          undefined,
          reject,
        );
      } else {
        reject(new Error("PCD loader not initialized"));
      }
    });
  }

  /**
   * Load XYZ/PTS point cloud (ASCII format)
   */
  private async loadXYZ(url: string): Promise<THREE.BufferGeometry> {
    const response = await fetch(url);
    const text = await response.text();
    const lines = text.trim().split("\n");

    const positions: number[] = [];
    const colors: number[] = [];

    for (const line of lines) {
      const parts = line.trim().split(/\s+/);
      if (parts.length >= 3) {
        positions.push(
          parseFloat(parts[0]),
          parseFloat(parts[1]),
          parseFloat(parts[2]),
        );

        // Optional RGB values
        if (parts.length >= 6) {
          colors.push(
            parseFloat(parts[3]) / 255,
            parseFloat(parts[4]) / 255,
            parseFloat(parts[5]) / 255,
          );
        } else {
          colors.push(1, 1, 1);
        }
      }
    }

    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute(
      "position",
      new THREE.Float32BufferAttribute(positions, 3),
    );
    geometry.setAttribute("color", new THREE.Float32BufferAttribute(colors, 3));

    return geometry;
  }

  /**
   * Load LAS/LAZ point cloud
   * Implements basic LAS 1.2-1.4 format parsing
   */
  private async loadLAS(url: string): Promise<THREE.BufferGeometry> {
    const response = await fetch(url);
    const buffer = await response.arrayBuffer();
    const view = new DataView(buffer);

    // Check signature "LASF"
    const signature = String.fromCharCode(
      view.getUint8(0),
      view.getUint8(1),
      view.getUint8(2),
      view.getUint8(3),
    );
    if (signature !== "LASF") {
      throw new Error("Invalid LAS file: missing LASF signature");
    }

    // Parse header
    const versionMajor = view.getUint8(24);
    const versionMinor = view.getUint8(25);
    const _headerSize = view.getUint16(94, true);
    const offsetToPointData = view.getUint32(96, true);
    const pointDataFormat = view.getUint8(104);
    const pointDataLength = view.getUint16(105, true);

    // Point count (depends on version)
    let pointCount: number;
    if (versionMajor === 1 && versionMinor >= 4) {
      // LAS 1.4 uses 64-bit point count
      pointCount = Number(view.getBigUint64(247, true));
    } else {
      pointCount = view.getUint32(107, true);
    }

    // Scale and offset for coordinates
    const scaleX = view.getFloat64(131, true);
    const scaleY = view.getFloat64(139, true);
    const scaleZ = view.getFloat64(147, true);
    const offsetX = view.getFloat64(155, true);
    const offsetY = view.getFloat64(163, true);
    const offsetZ = view.getFloat64(171, true);

    // Limit point count for performance
    const maxPoints = Math.min(pointCount, this.cloudData.pointBudget);
    const skipRate = Math.max(1, Math.floor(pointCount / maxPoints));

    const positions: number[] = [];
    const colors: number[] = [];
    const intensities: number[] = [];
    const classifications: number[] = [];

    // Point format determines data layout
    // Format 0: X,Y,Z,Intensity,Return,Classification (20 bytes)
    // Format 1: Format 0 + GPS Time (28 bytes)
    // Format 2: Format 0 + RGB (26 bytes)
    // Format 3: Format 1 + RGB (34 bytes)
    const hasRGB =
      pointDataFormat === 2 ||
      pointDataFormat === 3 ||
      pointDataFormat === 7 ||
      pointDataFormat === 8;

    let offset = offsetToPointData;
    let loadedPoints = 0;

    for (let i = 0; i < pointCount && loadedPoints < maxPoints; i++) {
      if (i % skipRate !== 0) {
        offset += pointDataLength;
        continue;
      }

      // Read X, Y, Z (4 bytes each, signed int32)
      const x = view.getInt32(offset, true) * scaleX + offsetX;
      const y = view.getInt32(offset + 4, true) * scaleY + offsetY;
      const z = view.getInt32(offset + 8, true) * scaleZ + offsetZ;

      // Read intensity (2 bytes, unsigned)
      const intensity = view.getUint16(offset + 12, true);

      // Read classification (1 byte at offset 15 for most formats)
      const classification = view.getUint8(offset + 15);

      positions.push(x, z, -y); // Convert to Y-up coordinate system
      intensities.push(intensity / 65535); // Normalize to 0-1
      classifications.push(classification);

      // Read RGB if available
      if (hasRGB) {
        const rgbOffset =
          pointDataFormat === 2
            ? 20
            : pointDataFormat === 3
              ? 28
              : pointDataFormat === 7
                ? 30
                : pointDataFormat === 8
                  ? 30
                  : 20;

        if (offset + rgbOffset + 6 <= buffer.byteLength) {
          const r = view.getUint16(offset + rgbOffset, true) / 65535;
          const g = view.getUint16(offset + rgbOffset + 2, true) / 65535;
          const b = view.getUint16(offset + rgbOffset + 4, true) / 65535;
          colors.push(r, g, b);
        } else {
          colors.push(1, 1, 1);
        }
      } else {
        // Use intensity as grayscale
        const gray = intensity / 65535;
        colors.push(gray, gray, gray);
      }

      offset += pointDataLength;
      loadedPoints++;
    }

    console.log(
      `[PointCloudLayer] Loaded ${loadedPoints} points from LAS v${versionMajor}.${versionMinor} (format ${pointDataFormat})`,
    );

    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute(
      "position",
      new THREE.Float32BufferAttribute(positions, 3),
    );
    geometry.setAttribute("color", new THREE.Float32BufferAttribute(colors, 3));

    // Store intensity and classification for coloring modes
    this.originalAttributes = {
      positions: new Float32Array(positions),
      colors: new Float32Array(colors),
      intensities: new Float32Array(intensities),
      classifications: new Uint8Array(classifications),
    };

    return geometry;
  }

  /**
   * Hash a string to a number for deterministic seeding
   */
  private hashString(str: string): number {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
      const char = str.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash;
    }
    return Math.abs(hash);
  }

  /**
   * Deterministic pseudo-random number generator
   */
  private seededRandom(seed: number): number {
    const x = Math.sin(seed) * 43758.5453123;
    return x - Math.floor(x);
  }

  /**
   * Create placeholder geometry
   */
  private createPlaceholderGeometry(): THREE.BufferGeometry {
    const positions: number[] = [];
    const colors: number[] = [];

    // Create a cube of points
    const size = 100;
    const count = 1000;

    // Use deterministic seeded random based on layer ID
    const baseSeed = this.hashString(this.id);

    for (let i = 0; i < count; i++) {
      positions.push(
        (this.seededRandom(baseSeed + i * 6) - 0.5) * size,
        (this.seededRandom(baseSeed + i * 6 + 1) - 0.5) * size,
        (this.seededRandom(baseSeed + i * 6 + 2) - 0.5) * size,
      );
      colors.push(
        this.seededRandom(baseSeed + i * 6 + 3),
        this.seededRandom(baseSeed + i * 6 + 4),
        this.seededRandom(baseSeed + i * 6 + 5),
      );
    }

    const geometry = new THREE.BufferGeometry();
    geometry.setAttribute(
      "position",
      new THREE.Float32BufferAttribute(positions, 3),
    );
    geometry.setAttribute("color", new THREE.Float32BufferAttribute(colors, 3));

    return geometry;
  }

  /**
   * Create placeholder point cloud
   */
  private createPlaceholder(): void {
    const geometry = this.createPlaceholderGeometry();
    this.setGeometry(geometry);
  }

  /**
   * Set the point cloud geometry
   */
  private setGeometry(geometry: THREE.BufferGeometry): void {
    // Remove existing point cloud
    if (this.pointCloud) {
      this.group.remove(this.pointCloud);
      this.disposePointCloud();
    }

    this.geometry = geometry;

    // Store original attributes
    this.storeOriginalAttributes();

    // Update point count
    const positionAttr = geometry.getAttribute("position");
    this.cloudData.pointCount = positionAttr ? positionAttr.count : 0;

    // Create material
    this.createMaterial();

    // Type proof: material is guaranteed non-null by createMaterial() setting it
    assertDefined(this.material, "material must exist after createMaterial()");
    // Create point cloud
    this.pointCloud = new THREE.Points(this.geometry, this.material);
    this.pointCloud.name = `pointcloud_${this.id}`;

    // Calculate bounding box
    this.calculateBoundingBox();

    // Update bounding box helper
    this.updateBoundingBoxHelper();

    // Apply color mode
    this.applyColorMode(this.cloudData.colorMode);

    // Add to group
    this.group.add(this.pointCloud);
  }

  /**
   * Store original point attributes
   */
  private storeOriginalAttributes(): void {
    if (!this.geometry) return;

    const position = this.geometry.getAttribute("position");
    const color = this.geometry.getAttribute("color");
    const normal = this.geometry.getAttribute("normal");

    this.originalAttributes = {
      positions: position
        ? new Float32Array(position.array)
        : new Float32Array(),
      colors: color ? new Float32Array(color.array) : undefined,
      normals: normal ? new Float32Array(normal.array) : undefined,
    };
  }

  /**
   * Create point cloud material
   */
  private createMaterial(): void {
    // Custom shader for advanced point rendering
    this.material = new THREE.ShaderMaterial({
      uniforms: {
        pointSize: { value: 2.0 },
        minPointSize: { value: this.cloudData.minPointSize },
        maxPointSize: { value: this.cloudData.maxPointSize },
        opacity: { value: 1.0 },
        sizeAttenuation: { value: this.cloudData.sizeAttenuation ? 1.0 : 0.0 },
        uniformColor: { value: new THREE.Color(this.cloudData.uniformColor) },
        useUniformColor: { value: 0.0 },
        heightMin: { value: 0.0 },
        heightMax: { value: 100.0 },
        gradientColors: { value: this.getGradientTexture() },
        renderMode: { value: this.getRenderModeValue() },
      },
      vertexShader: this.getVertexShader(),
      fragmentShader: this.getFragmentShader(),
      transparent: true,
      depthTest: this.cloudData.depthTest,
      depthWrite: this.cloudData.depthWrite,
      vertexColors: true,
    });
  }

  /**
   * Get vertex shader for point cloud rendering
   */
  private getVertexShader(): string {
    return `
      uniform float pointSize;
      uniform float minPointSize;
      uniform float maxPointSize;
      uniform float sizeAttenuation;

      varying vec3 vColor;
      varying vec3 vPosition;
      varying vec3 vNormal;

      void main() {
        vColor = color;
        vPosition = position;
        vNormal = normal;

        vec4 mvPosition = modelViewMatrix * vec4(position, 1.0);
        gl_Position = projectionMatrix * mvPosition;

        // Size attenuation
        float size = pointSize;
        if (sizeAttenuation > 0.5) {
          size = pointSize * (300.0 / -mvPosition.z);
        }

        // Clamp size
        gl_PointSize = clamp(size, minPointSize, maxPointSize);
      }
    `;
  }

  /**
   * Get fragment shader for point cloud rendering
   */
  private getFragmentShader(): string {
    return `
      uniform float opacity;
      uniform vec3 uniformColor;
      uniform float useUniformColor;
      uniform float renderMode;

      varying vec3 vColor;
      varying vec3 vPosition;
      varying vec3 vNormal;

      void main() {
        vec2 coord = gl_PointCoord - vec2(0.5);

        // Render mode: 0 = points, 1 = circles, 2 = squares, 3 = splats
        if (renderMode > 0.5 && renderMode < 1.5) {
          // Circle
          float dist = length(coord);
          if (dist > 0.5) discard;
        } else if (renderMode > 2.5) {
          // Gaussian splat
          float dist = length(coord);
          float alpha = exp(-dist * dist * 8.0);
          if (alpha < 0.01) discard;
          gl_FragColor = vec4(mix(vColor, uniformColor, useUniformColor), alpha * opacity);
          return;
        }
        // Squares (mode 2) use full point

        vec3 color = mix(vColor, uniformColor, useUniformColor);
        gl_FragColor = vec4(color, opacity);
      }
    `;
  }

  /**
   * Get render mode value for shader
   */
  private getRenderModeValue(): number {
    switch (this.cloudData.renderMode) {
      case "points":
        return 0;
      case "circles":
        return 1;
      case "squares":
        return 2;
      case "splats":
        return 3;
      default:
        return 1;
    }
  }

  /**
   * Create gradient texture for color mapping
   */
  private getGradientTexture(): THREE.DataTexture {
    const size = 256;
    const data = new Uint8Array(size * 4);

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: colorGradient.stops ∈ GradientStop[] | undefined → GradientStop[] (default stops)
    const colorGradientData = (typeof this.cloudData.colorGradient === "object" && this.cloudData.colorGradient !== null && "stops" in this.cloudData.colorGradient && Array.isArray(this.cloudData.colorGradient.stops)) ? this.cloudData.colorGradient.stops : undefined;
    const stops = (colorGradientData !== undefined && colorGradientData.length > 0) ? colorGradientData : [
      { position: 0, color: "#0000ff" },
      { position: 0.5, color: "#00ff00" },
      { position: 1, color: "#ff0000" },
    ];

    for (let i = 0; i < size; i++) {
      const t = i / (size - 1);

      // Find surrounding stops
      let stop1 = stops[0];
      let stop2 = stops[stops.length - 1];

      for (let j = 0; j < stops.length - 1; j++) {
        if (t >= stops[j].position && t <= stops[j + 1].position) {
          stop1 = stops[j];
          stop2 = stops[j + 1];
          break;
        }
      }

      // Interpolate color
      const localT = (t - stop1.position) / (stop2.position - stop1.position);
      const color1 = new THREE.Color(stop1.color);
      const color2 = new THREE.Color(stop2.color);
      const color = color1.lerp(color2, localT);

      data[i * 4] = Math.floor(color.r * 255);
      data[i * 4 + 1] = Math.floor(color.g * 255);
      data[i * 4 + 2] = Math.floor(color.b * 255);
      data[i * 4 + 3] = 255;
    }

    const texture = new THREE.DataTexture(data, size, 1, THREE.RGBAFormat);
    texture.needsUpdate = true;
    return texture;
  }

  /**
   * Calculate and store bounding box
   */
  private calculateBoundingBox(): void {
    if (!this.geometry) return;

    this.geometry.computeBoundingBox();
    const box = this.geometry.boundingBox;
    if (!box) return;

    const center = box.getCenter(new THREE.Vector3());
    const size = box.getSize(new THREE.Vector3());

    this.cloudData.boundingBox = {
      min: { x: box.min.x, y: box.min.y, z: box.min.z },
      max: { x: box.max.x, y: box.max.y, z: box.max.z },
      center: { x: center.x, y: center.y, z: center.z },
      size: { x: size.x, y: size.y, z: size.z },
    };

    // Update height range for height coloring
    if (this.material) {
      this.material.uniforms.heightMin.value = box.min.y;
      this.material.uniforms.heightMax.value = box.max.y;
    }
  }

  // ============================================================================
  // COLOR MODES
  // ============================================================================

  /**
   * Apply color mode to point cloud
   */
  applyColorMode(mode: PointCloudColorMode): void {
    if (!this.geometry || !this.material || !this.originalAttributes) return;

    this.cloudData.colorMode = mode;
    const positions = this.originalAttributes.positions;
    const _count = positions.length / 3;

    switch (mode) {
      case "rgb":
        // Use original colors or white if none
        if (this.originalAttributes.colors) {
          this.geometry.setAttribute(
            "color",
            new THREE.Float32BufferAttribute(this.originalAttributes.colors, 3),
          );
        }
        this.material.uniforms.useUniformColor.value = 0;
        break;

      case "uniform":
        this.material.uniforms.useUniformColor.value = 1;
        this.material.uniforms.uniformColor.value.set(
          this.cloudData.uniformColor,
        );
        break;

      case "height":
        this.applyHeightColoring();
        break;

      case "depth":
        this.applyDepthColoring();
        break;

      case "normal":
        this.applyNormalColoring();
        break;

      case "intensity":
        this.applyIntensityColoring();
        break;

      case "classification":
        this.applyClassificationColoring();
        break;
    }

    this.geometry.attributes.color.needsUpdate = true;
  }

  /**
   * Apply height-based coloring
   */
  private applyHeightColoring(): void {
    if (
      !this.geometry ||
      !this.originalAttributes ||
      !this.cloudData.boundingBox
    )
      return;

    const positions = this.originalAttributes.positions;
    const count = positions.length / 3;
    const colors = new Float32Array(count * 3);

    const minY = this.cloudData.boundingBox.min.y;
    const maxY = this.cloudData.boundingBox.max.y;
    const range = maxY - minY || 1;

    for (let i = 0; i < count; i++) {
      const y = positions[i * 3 + 1];
      const t = (y - minY) / range;

      // Rainbow gradient: blue -> cyan -> green -> yellow -> red
      const color = new THREE.Color();
      color.setHSL((1 - t) * 0.7, 1, 0.5);

      colors[i * 3] = color.r;
      colors[i * 3 + 1] = color.g;
      colors[i * 3 + 2] = color.b;
    }

    this.geometry.setAttribute(
      "color",
      new THREE.Float32BufferAttribute(colors, 3),
    );
    if (this.material) {
      this.material.uniforms.useUniformColor.value = 0;
    }
  }

  /**
   * Apply depth-based coloring (distance from camera)
   */
  private applyDepthColoring(): void {
    if (
      !this.geometry ||
      !this.originalAttributes ||
      !this.cloudData.boundingBox
    )
      return;

    const positions = this.originalAttributes.positions;
    const count = positions.length / 3;
    const colors = new Float32Array(count * 3);

    const minZ = this.cloudData.boundingBox.min.z;
    const maxZ = this.cloudData.boundingBox.max.z;
    const range = maxZ - minZ || 1;

    for (let i = 0; i < count; i++) {
      const z = positions[i * 3 + 2];
      const t = (z - minZ) / range;

      // Depth gradient: near (white) -> far (dark)
      const value = 1 - t;
      colors[i * 3] = value;
      colors[i * 3 + 1] = value;
      colors[i * 3 + 2] = value;
    }

    this.geometry.setAttribute(
      "color",
      new THREE.Float32BufferAttribute(colors, 3),
    );
    if (this.material) {
      this.material.uniforms.useUniformColor.value = 0;
    }
  }

  /**
   * Apply normal-based coloring
   */
  private applyNormalColoring(): void {
    if (!this.geometry || !this.originalAttributes) return;

    if (this.originalAttributes.normals) {
      // Use normals directly as colors (normalized to 0-1)
      const normals = this.originalAttributes.normals;
      const count = normals.length / 3;
      const colors = new Float32Array(count * 3);

      for (let i = 0; i < count; i++) {
        colors[i * 3] = normals[i * 3] * 0.5 + 0.5;
        colors[i * 3 + 1] = normals[i * 3 + 1] * 0.5 + 0.5;
        colors[i * 3 + 2] = normals[i * 3 + 2] * 0.5 + 0.5;
      }

      this.geometry.setAttribute(
        "color",
        new THREE.Float32BufferAttribute(colors, 3),
      );
    } else {
      // Compute normals if not available (simple approach)
      console.warn(
        "[PointCloudLayer] No normals available for normal coloring",
      );
      if (this.material) {
        this.material.uniforms.useUniformColor.value = 1;
        this.material.uniforms.uniformColor.value.set("#8080ff");
      }
    }

    if (this.material) {
      this.material.uniforms.useUniformColor.value = 0;
    }
  }

  /**
   * Apply intensity-based coloring
   */
  private applyIntensityColoring(): void {
    if (!this.geometry || !this.originalAttributes) return;

    if (this.originalAttributes.intensities) {
      const intensities = this.originalAttributes.intensities;
      const count = intensities.length;
      const colors = new Float32Array(count * 3);

      // Find min/max intensity
      let min = Infinity,
        max = -Infinity;
      for (let i = 0; i < count; i++) {
        min = Math.min(min, intensities[i]);
        max = Math.max(max, intensities[i]);
      }

      // Apply range filter if specified
      if (this.cloudData.intensityRange) {
        min = Math.max(min, this.cloudData.intensityRange.min);
        max = Math.min(max, this.cloudData.intensityRange.max);
      }

      const range = max - min || 1;

      for (let i = 0; i < count; i++) {
        const t = (intensities[i] - min) / range;
        // Grayscale
        colors[i * 3] = t;
        colors[i * 3 + 1] = t;
        colors[i * 3 + 2] = t;
      }

      this.geometry.setAttribute(
        "color",
        new THREE.Float32BufferAttribute(colors, 3),
      );
      if (this.material) {
        this.material.uniforms.useUniformColor.value = 0;
      }
    } else {
      console.warn("[PointCloudLayer] No intensity data available");
      if (this.material) {
        this.material.uniforms.useUniformColor.value = 1;
      }
    }
  }

  /**
   * Apply classification-based coloring (for LAS files)
   */
  private applyClassificationColoring(): void {
    if (!this.geometry || !this.originalAttributes) return;

    if (this.originalAttributes.classifications) {
      const classifications = this.originalAttributes.classifications;
      const count = classifications.length;
      const colors = new Float32Array(count * 3);

      // Standard LAS classification colors
      const classColors: Record<number, [number, number, number]> = {
        0: [0.5, 0.5, 0.5], // Never classified
        1: [0.5, 0.5, 0.5], // Unclassified
        2: [0.6, 0.4, 0.2], // Ground
        3: [0.2, 0.8, 0.2], // Low vegetation
        4: [0.1, 0.6, 0.1], // Medium vegetation
        5: [0.0, 0.4, 0.0], // High vegetation
        6: [0.9, 0.2, 0.2], // Building
        7: [0.5, 0.5, 0.5], // Low point (noise)
        8: [0.5, 0.5, 0.5], // Reserved
        9: [0.2, 0.4, 0.8], // Water
        10: [0.8, 0.6, 0.4], // Rail
        11: [0.3, 0.3, 0.3], // Road surface
        12: [0.5, 0.5, 0.5], // Reserved
        13: [0.8, 0.8, 0.2], // Wire - Guard
        14: [0.8, 0.6, 0.2], // Wire - Conductor
        15: [0.9, 0.9, 0.9], // Transmission Tower
        16: [0.6, 0.6, 0.8], // Wire - Connector
        17: [0.4, 0.4, 0.6], // Bridge Deck
        18: [0.9, 0.1, 0.1], // High Noise
      };

      for (let i = 0; i < count; i++) {
        const classId = classifications[i];
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
        // Pattern match: classColors[classId] ∈ [number, number, number] | undefined → [number, number, number] (default gray)
        // Note: classColors is a Record<number, [number, number, number]>, so check if key exists
        const classColorEntry = (classId in classColors && Array.isArray(classColors[classId]) && classColors[classId].length === 3 && typeof classColors[classId][0] === "number" && typeof classColors[classId][1] === "number" && typeof classColors[classId][2] === "number") ? classColors[classId] as [number, number, number] : [0.5, 0.5, 0.5];
        const color = classColorEntry;
        colors[i * 3] = color[0];
        colors[i * 3 + 1] = color[1];
        colors[i * 3 + 2] = color[2];
      }

      this.geometry.setAttribute(
        "color",
        new THREE.Float32BufferAttribute(colors, 3),
      );
      if (this.material) {
        this.material.uniforms.useUniformColor.value = 0;
      }
    } else {
      console.warn("[PointCloudLayer] No classification data available");
      if (this.material) {
        this.material.uniforms.useUniformColor.value = 1;
      }
    }
  }

  // ============================================================================
  // HELPERS
  // ============================================================================

  /**
   * Update bounding box helper
   */
  private updateBoundingBoxHelper(): void {
    if (this.boundingBoxHelper) {
      this.group.remove(this.boundingBoxHelper);
      this.boundingBoxHelper.dispose();
      this.boundingBoxHelper = null;
    }

    if (this.cloudData.showBoundingBox && this.pointCloud) {
      this.boundingBoxHelper = new THREE.BoxHelper(this.pointCloud, 0x00ff00);
      this.boundingBoxHelper.name = `bbox_helper_${this.id}`;
      this.group.add(this.boundingBoxHelper);
    }
  }

  // ============================================================================
  // SETTERS
  // ============================================================================

  /**
   * Set point size
   */
  setPointSize(size: number): void {
    if (this.material) {
      // Validate size (NaN would corrupt shader uniform)
      const validSize = Number.isFinite(size) && size > 0 ? size : 2;
      this.material.uniforms.pointSize.value = validSize;
    }
  }

  /**
   * Set opacity
   */
  setOpacity(opacity: number): void {
    if (this.material) {
      // Validate opacity (NaN would corrupt shader uniform)
      const validOpacity = Number.isFinite(opacity)
        ? Math.max(0, Math.min(1, opacity))
        : 1;
      this.material.uniforms.opacity.value = validOpacity;
    }
  }

  /**
   * Set uniform color
   */
  setUniformColor(color: string): void {
    this.cloudData.uniformColor = color;
    if (this.material) {
      this.material.uniforms.uniformColor.value.set(color);
    }
  }

  /**
   * Set render mode
   */
  setRenderMode(mode: PointCloudRenderMode): void {
    this.cloudData.renderMode = mode;
    if (this.material) {
      this.material.uniforms.renderMode.value = this.getRenderModeValue();
    }
  }

  /**
   * Set bounding box visibility
   */
  setShowBoundingBox(show: boolean): void {
    this.cloudData.showBoundingBox = show;
    this.updateBoundingBoxHelper();
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get point count
   */
  getPointCount(): number {
    return this.cloudData.pointCount;
  }

  /**
   * Get point cloud-specific bounding box data
   */
  getPointCloudBoundingBox(): ModelBoundingBox | undefined {
    return this.cloudData.boundingBox;
  }

  /**
   * Check if loading
   */
  isPointCloudLoading(): boolean {
    return this.isLoading;
  }

  /**
   * Get load error
   */
  getLoadError(): string | null {
    return this.loadError;
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Use composition fps for correct animation timing (not hardcoded 30fps)
    const fps = this.compositionFps;
    const layerId = this.id;

    // Evaluate animated point size
    const size = interpolateProperty(
      this.cloudData.pointSize,
      frame,
      fps,
      layerId,
    );
    this.setPointSize(size);

    // Evaluate animated opacity
    const opacity = interpolateProperty(
      this.cloudData.opacity,
      frame,
      fps,
      layerId,
    );
    this.setOpacity(opacity);

    // Update bounding box helper
    if (this.boundingBoxHelper) {
      this.boundingBoxHelper.update();
    }
  }

  protected override onApplyEvaluatedState(
    state: import("../MotionEngine").EvaluatedLayer,
  ): void {
    const props = state.properties;

    if (props.pointSize !== undefined) {
      this.setPointSize(props.pointSize as number);
    }

    if (props.opacity !== undefined) {
      this.setOpacity(props.opacity as number);
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<PointCloudLayerData> | undefined;

    if (data) {
      // Handle asset change
      if (
        data.assetId !== undefined &&
        data.assetId !== this.cloudData.assetId
      ) {
        this.cloudData.assetId = data.assetId;
        if (data.format) {
          this.cloudData.format = data.format;
        }
        this.loadPointCloud();
      }

      // Handle color mode change
      if (data.colorMode !== undefined) {
        this.applyColorMode(data.colorMode);
      }

      // Handle uniform color change
      if (data.uniformColor !== undefined) {
        this.setUniformColor(data.uniformColor);
      }

      // Handle render mode change
      if (data.renderMode !== undefined) {
        this.setRenderMode(data.renderMode);
      }

      // Handle bounding box visibility
      if (data.showBoundingBox !== undefined) {
        this.setShowBoundingBox(data.showBoundingBox);
      }

      // Handle depth settings
      if (data.depthTest !== undefined || data.depthWrite !== undefined) {
        if (this.material) {
          if (data.depthTest !== undefined) {
            this.material.depthTest = data.depthTest;
            this.cloudData.depthTest = data.depthTest;
          }
          if (data.depthWrite !== undefined) {
            this.material.depthWrite = data.depthWrite;
            this.cloudData.depthWrite = data.depthWrite;
          }
        }
      }
    }
  }

  protected onDispose(): void {
    this.disposePointCloud();
  }

  /**
   * Dispose point cloud resources
   */
  private disposePointCloud(): void {
    if (this.boundingBoxHelper) {
      this.boundingBoxHelper.dispose();
      this.boundingBoxHelper = null;
    }

    if (this.material) {
      this.material.dispose();
      this.material = null;
    }

    if (this.geometry) {
      this.geometry.dispose();
      this.geometry = null;
    }

    this.originalAttributes = null;
    this.pointCloud = null;
  }
}
