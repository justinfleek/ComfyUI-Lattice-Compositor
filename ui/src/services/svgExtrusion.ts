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

import * as THREE from 'three';
import { SVGLoader, SVGResult } from 'three/examples/jsm/loaders/SVGLoader.js';

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

/** Extrusion configuration */
export interface ExtrusionConfig {
  depth: number;           // Extrusion depth (0-100)
  bevelEnabled: boolean;
  bevelThickness: number;
  bevelSize: number;
  bevelOffset: number;
  bevelSegments: number;
  curveSegments: number;   // Segments for curved paths
  steps: number;           // Extrusion steps
  // Material options
  frontMaterial?: THREE.Material;
  sideMaterial?: THREE.Material;
  backMaterial?: THREE.Material;
}

/** Layer configuration for extruded SVG */
export interface SVGLayerConfig {
  pathId: string;
  depth: number;           // Z position in scene
  extrusionDepth: number;  // Thickness of extrusion
  scale: number;
  position: { x: number; y: number; z: number };
  rotation: { x: number; y: number; z: number };
  material: ExtrusionMaterialConfig;
}

/** Material configuration for extrusion */
export interface ExtrusionMaterialConfig {
  type: 'basic' | 'standard' | 'physical';
  color: string;
  metalness: number;
  roughness: number;
  emissive: string;
  emissiveIntensity: number;
  opacity: number;
  transparent: boolean;
  side: 'front' | 'back' | 'double';
}

/** Mesh particle configuration from SVG */
export interface SVGMeshParticleConfig {
  pathId: string;          // Which SVG path to use
  extrusionDepth: number;  // How thick the particle mesh
  scale: number;           // Particle size multiplier
  simplify: boolean;       // Reduce geometry complexity
  simplifyTolerance: number;
  centerOrigin: boolean;   // Center mesh at origin
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
   */
  async loadFromURL(url: string, name?: string): Promise<ParsedSVGDocument> {
    return new Promise((resolve, reject) => {
      this.svgLoader.load(
        url,
        (data) => {
          const doc = this.parseSVGResult(data, name || url);
          this.documentCache.set(doc.id, doc);
          resolve(doc);
        },
        undefined,
        reject
      );
    });
  }

  /**
   * Load and parse SVG from string content
   */
  loadFromString(svgString: string, name: string = 'svg'): ParsedSVGDocument {
    const parser = new DOMParser();
    const svgDoc = parser.parseFromString(svgString, 'image/svg+xml');
    const svgElement = svgDoc.querySelector('svg');

    if (!svgElement) {
      throw new Error('Invalid SVG: No SVG element found');
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
    const id = `svg_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    const paths: ParsedSVGPath[] = [];

    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;

    // Parse each path
    data.paths.forEach((shapePath, index) => {
      const shapes = SVGLoader.createShapes(shapePath);

      if (shapes.length === 0) return;

      // Get fill color
      const fillColor = shapePath.userData?.style?.fill;
      const color = new THREE.Color(
        fillColor && fillColor !== 'none' ? fillColor : '#ffffff'
      );

      // Get fill opacity
      const fillOpacity = shapePath.userData?.style?.fillOpacity ?? 1;

      // Get stroke
      const strokeColor = shapePath.userData?.style?.stroke;
      const strokeWidth = shapePath.userData?.style?.strokeWidth ?? 0;

      // Calculate bounds for this path
      const pathBounds = this.calculatePathBounds(shapes);

      minX = Math.min(minX, pathBounds.minX);
      minY = Math.min(minY, pathBounds.minY);
      maxX = Math.max(maxX, pathBounds.maxX);
      maxY = Math.max(maxY, pathBounds.maxY);

      paths.push({
        id: `${id}_path_${index}`,
        name: `Path ${index + 1}`,
        path: shapePath,
        shapes,
        color,
        fillOpacity,
        strokeColor: strokeColor && strokeColor !== 'none'
          ? new THREE.Color(strokeColor)
          : null,
        strokeWidth,
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
  private calculatePathBounds(shapes: THREE.Shape[]): ParsedSVGPath['bounds'] {
    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;

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
   */
  createExtrudedGeometry(
    path: ParsedSVGPath,
    config: Partial<ExtrusionConfig> = {}
  ): THREE.BufferGeometry {
    const cacheKey = `${path.id}_${JSON.stringify(config)}`;
    const cached = this.meshCache.get(cacheKey);
    if (cached) return cached.clone();

    const extrudeSettings: THREE.ExtrudeGeometryOptions = {
      depth: config.depth ?? 10,
      bevelEnabled: config.bevelEnabled ?? false,
      bevelThickness: config.bevelThickness ?? 1,
      bevelSize: config.bevelSize ?? 0.5,
      bevelOffset: config.bevelOffset ?? 0,
      bevelSegments: config.bevelSegments ?? 3,
      curveSegments: config.curveSegments ?? 12,
      steps: config.steps ?? 1,
    };

    // Create geometry from all shapes in the path
    const geometries: THREE.ExtrudeGeometry[] = [];

    for (const shape of path.shapes) {
      const geometry = new THREE.ExtrudeGeometry(shape, extrudeSettings);
      geometries.push(geometry);
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
  private mergeGeometries(geometries: THREE.BufferGeometry[]): THREE.BufferGeometry {
    // Calculate total vertex count
    let totalVertices = 0;
    let totalIndices = 0;
    let hasNormals = true;
    let hasUVs = true;

    for (const geom of geometries) {
      const pos = geom.getAttribute('position');
      if (pos) totalVertices += pos.count;

      const idx = geom.getIndex();
      if (idx) totalIndices += idx.count;
      else totalIndices += pos?.count ?? 0;

      if (!geom.getAttribute('normal')) hasNormals = false;
      if (!geom.getAttribute('uv')) hasUVs = false;
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
      const pos = geom.getAttribute('position');
      const norm = geom.getAttribute('normal');
      const uv = geom.getAttribute('uv');
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
    merged.setAttribute('position', new THREE.BufferAttribute(positions, 3));
    if (normals) {
      merged.setAttribute('normal', new THREE.BufferAttribute(normals, 3));
    }
    if (uvs) {
      merged.setAttribute('uv', new THREE.BufferAttribute(uvs, 2));
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
    materialConfig: Partial<ExtrusionMaterialConfig> = {}
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
    config: Partial<ExtrusionMaterialConfig> = {}
  ): THREE.Material {
    const type = config.type ?? 'standard';
    const color = config.color ?? `#${path.color.getHexString()}`;
    const side = this.getSide(config.side ?? 'double');

    const baseParams = {
      color: new THREE.Color(color),
      transparent: config.transparent ?? path.fillOpacity < 1,
      opacity: config.opacity ?? path.fillOpacity,
      side,
    };

    switch (type) {
      case 'basic':
        return new THREE.MeshBasicMaterial(baseParams);

      case 'physical':
        return new THREE.MeshPhysicalMaterial({
          ...baseParams,
          metalness: config.metalness ?? 0,
          roughness: config.roughness ?? 0.5,
          emissive: new THREE.Color(config.emissive ?? '#000000'),
          emissiveIntensity: config.emissiveIntensity ?? 0,
        });

      case 'standard':
      default:
        return new THREE.MeshStandardMaterial({
          ...baseParams,
          metalness: config.metalness ?? 0,
          roughness: config.roughness ?? 0.5,
          emissive: new THREE.Color(config.emissive ?? '#000000'),
          emissiveIntensity: config.emissiveIntensity ?? 0,
        });
    }
  }

  /**
   * Get THREE.Side from string
   */
  private getSide(side: 'front' | 'back' | 'double'): THREE.Side {
    switch (side) {
      case 'front': return THREE.FrontSide;
      case 'back': return THREE.BackSide;
      case 'double': return THREE.DoubleSide;
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
    layerConfigs: SVGLayerConfig[]
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
        config.material
      );

      // Apply transforms
      mesh.scale.setScalar(config.scale);
      mesh.position.set(
        config.position.x - centerX * config.scale,
        config.position.y + centerY * config.scale, // Flip Y
        config.position.z + config.depth
      );
      mesh.rotation.set(
        config.rotation.x * (Math.PI / 180),
        config.rotation.y * (Math.PI / 180),
        config.rotation.z * (Math.PI / 180)
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
    extrusionDepth: number = 2
  ): SVGLayerConfig[] {
    return document.paths.map((path, index) => ({
      pathId: path.id,
      depth: baseDepth + index * depthIncrement,
      extrusionDepth,
      scale: 1,
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      material: {
        type: 'standard' as const,
        color: `#${path.color.getHexString()}`,
        metalness: 0,
        roughness: 0.5,
        emissive: '#000000',
        emissiveIntensity: 0,
        opacity: path.fillOpacity,
        transparent: path.fillOpacity < 1,
        side: 'double' as const,
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
    config: Partial<SVGMeshParticleConfig> = {}
  ): THREE.BufferGeometry {
    const extrusionDepth = config.extrusionDepth ?? 1;
    const scale = config.scale ?? 1;

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
        config.simplifyTolerance ?? 0.1
      );
    }

    // Center at origin if requested
    if (config.centerOrigin !== false) {
      geometry.computeBoundingBox();
      const center = new THREE.Vector3();
      geometry.boundingBox!.getCenter(center);
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
    tolerance: number
  ): THREE.BufferGeometry {
    // Note: For production, use a proper simplification library
    // This is a basic vertex welding implementation
    const position = geometry.getAttribute('position');
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
      'position',
      new THREE.Float32BufferAttribute(newPositions, 3)
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
    radialSegments: number = 8
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
        false // closed
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
    type: 'standard',
    color: '#ffffff',
    metalness: 0,
    roughness: 0.5,
    emissive: '#000000',
    emissiveIntensity: 0,
    opacity: 1,
    transparent: false,
    side: 'double',
  };
}

export function createDefaultSVGMeshParticleConfig(): SVGMeshParticleConfig {
  return {
    pathId: '',
    extrusionDepth: 1,
    scale: 0.01,
    simplify: true,
    simplifyTolerance: 0.1,
    centerOrigin: true,
  };
}
