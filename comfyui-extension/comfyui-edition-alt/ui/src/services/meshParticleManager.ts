/**
 * Mesh Particle Manager
 *
 * Manages custom 3D mesh geometries for use as particles.
 * Integrates with:
 * - SVG Extrusion (logo workflow)
 * - 3D Model Import (GLTF, OBJ, etc.)
 * - Procedural Geometry
 *
 * Provides:
 * - Mesh registration and caching
 * - Instanced mesh rendering for particles
 * - LOD support for performance
 * - Mesh atlas for GPU texture-based instancing
 */

import { isFiniteNumber } from "@/utils/typeGuards";
import * as THREE from "three";
import type {
  EmitterShapeConfig,
  RenderConfig,
} from "../engine/particles/types";
import {
  type ParsedSVGPath,
  type SVGMeshParticleConfig,
  svgExtrusionService,
} from "./svgExtrusion";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/** Mesh particle source type */
export type MeshParticleSource =
  | "svg" // From SVG extrusion
  | "model" // From 3D model file
  | "primitive" // Built-in primitive shapes
  | "custom"; // User-provided geometry

/** Registered mesh particle definition */
export interface RegisteredMeshParticle {
  id: string;
  name: string;
  source: MeshParticleSource;
  geometry: THREE.BufferGeometry;
  boundingBox: THREE.Box3;
  boundingSphere: THREE.Sphere;
  vertexCount: number;
  faceCount: number;

  // Metadata
  sourceId?: string; // SVG path ID or model asset ID
  thumbnail?: string; // Base64 preview image

  //                                                                       // lod
  lodGeometries?: THREE.BufferGeometry[];
  lodDistances?: number[];

  // Original configuration
  config?: MeshParticleConfig;
}

/** Mesh particle configuration */
export interface MeshParticleConfig {
  source: MeshParticleSource;

  //                                                                       // svg
  svgDocumentId?: string;
  svgPathId?: string;
  svgExtrusionDepth?: number;

  // Model source options
  modelAssetId?: string;
  modelSubmeshIndex?: number;

  // Primitive options
  primitiveType?:
    | "cube"
    | "sphere"
    | "cone"
    | "cylinder"
    | "torus"
    | "tetrahedron"
    | "octahedron"
    | "icosahedron";
  primitiveSize?: number;
  primitiveDetail?: number;

  // Common options
  scale: number;
  centerOrigin: boolean;
  simplify: boolean;
  simplifyTolerance: number;

  // Material options (for rendering)
  materialId?: string; // Reference to MaterialSystem material
  color?: string;
  metalness?: number;
  roughness?: number;
  emissive?: string;
  emissiveIntensity?: number;
}

/** Instanced mesh particle renderer */
export interface InstancedMeshParticles {
  mesh: THREE.InstancedMesh;
  maxInstances: number;
  activeInstances: number;
  geometry: THREE.BufferGeometry;
  material: THREE.Material;
}

// ════════════════════════════════════════════════════════════════════════════
//                                               // mesh // particle // manager
// ════════════════════════════════════════════════════════════════════════════

export class MeshParticleManager {
  /** Registered mesh particles */
  private meshRegistry: Map<string, RegisteredMeshParticle> = new Map();

  /** Instanced mesh renderers */
  private instancedMeshes: Map<string, InstancedMeshParticles> = new Map();

  /** Default material for mesh particles */
  private defaultMaterial: THREE.MeshStandardMaterial;

  /** Texture loader for particle textures */
  private textureLoader: THREE.TextureLoader;

  constructor() {
    this.defaultMaterial = new THREE.MeshStandardMaterial({
      color: 0xffffff,
      metalness: 0,
      roughness: 0.5,
      side: THREE.DoubleSide,
    });
    this.textureLoader = new THREE.TextureLoader();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // mesh // registration
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Register a mesh for use as particles
   */
  registerMesh(
    id: string,
    name: string,
    geometry: THREE.BufferGeometry,
    source: MeshParticleSource,
    config?: MeshParticleConfig,
  ): RegisteredMeshParticle {
    // Ensure geometry has proper bounding info
    geometry.computeBoundingBox();
    geometry.computeBoundingSphere();

    const registration: RegisteredMeshParticle = {
      id,
      name,
      source,
      geometry,
      // Type proof: boundingBox ∈ Box3 | undefined → Box3
      boundingBox: (() => {
        const boundingBox = geometry.boundingBox;
        return boundingBox !== null && boundingBox !== undefined ? boundingBox.clone() : new THREE.Box3();
      })(),
      // Type proof: boundingSphere ∈ Sphere | undefined → Sphere
      boundingSphere: (() => {
        const boundingSphere = geometry.boundingSphere;
        return boundingSphere !== null && boundingSphere !== undefined ? boundingSphere.clone() : new THREE.Sphere();
      })(),
      // Type proof: vertexCount ∈ ℕ ∪ {undefined} → ℕ
      vertexCount: (() => {
        const positionAttr = geometry.getAttribute("position");
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const count = (positionAttr != null && typeof positionAttr === "object" && "count" in positionAttr && typeof positionAttr.count === "number") ? positionAttr.count : undefined;
        return isFiniteNumber(count) && Number.isInteger(count) && count >= 0 ? count : 0;
      })(),
      // Type proof: faceCount ∈ ℕ (computed from index or vertexCount)
      faceCount: geometry.index
        ? geometry.index.count / 3
        : (() => {
            const positionAttr = geometry.getAttribute("position");
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const count = (positionAttr != null && typeof positionAttr === "object" && "count" in positionAttr && typeof positionAttr.count === "number") ? positionAttr.count : undefined;
            const vertexCount = isFiniteNumber(count) && Number.isInteger(count) && count >= 0 ? count : 0;
            return vertexCount / 3;
          })(),
      config,
    };

    this.meshRegistry.set(id, registration);
    return registration;
  }

  /**
   * Register mesh from SVG path
   */
  registerFromSVG(
    svgDocumentId: string,
    svgPathId: string,
    name: string,
    options: Partial<SVGMeshParticleConfig> = {},
  ): RegisteredMeshParticle {
    const document = svgExtrusionService.getDocument(svgDocumentId);
    if (!document) {
      throw new Error(`[MeshParticleManager] Cannot register mesh from SVG: SVG document "${svgDocumentId}" not found`);
    }

    const path = document.paths.find((p) => p.id === svgPathId);
    if (!path) {
      throw new Error(`[MeshParticleManager] Cannot register mesh from SVG: SVG path "${svgPathId}" not found in document "${svgDocumentId}"`);
    }

    // Create particle mesh from SVG
    const geometry = svgExtrusionService.createParticleMesh(path, {
      ...options,
      pathId: svgPathId,
    });

    const id = `svg_particle_${svgDocumentId}_${svgPathId}`;
    return this.registerMesh(id, name, geometry, "svg", {
      source: "svg",
      svgDocumentId,
      svgPathId,
      // Type proof: svgExtrusionDepth ∈ ℝ ∪ {undefined} → ℝ
      svgExtrusionDepth: (() => {
        const extrusionDepthValue = options.extrusionDepth;
        return isFiniteNumber(extrusionDepthValue) && extrusionDepthValue > 0 ? extrusionDepthValue : 1;
      })(),
      // Type proof: scale ∈ ℝ ∪ {undefined} → ℝ
      scale: (() => {
        const scaleValue = options.scale;
        return isFiniteNumber(scaleValue) && scaleValue > 0 ? scaleValue : 0.01;
      })(),
      // Type proof: centerOrigin ∈ boolean | undefined → boolean
      centerOrigin: options.centerOrigin === true,
      // Type proof: simplify ∈ boolean | undefined → boolean
      simplify: options.simplify === true,
      // Type proof: simplifyTolerance ∈ ℝ ∪ {undefined} → ℝ
      simplifyTolerance: (() => {
        const simplifyToleranceValue = options.simplifyTolerance;
        return isFiniteNumber(simplifyToleranceValue) && simplifyToleranceValue >= 0 ? simplifyToleranceValue : 0.1;
      })(),
    });
  }

  /**
   * Register mesh from parsed SVG path directly
   */
  registerFromSVGPath(
    path: ParsedSVGPath,
    name: string,
    options: Partial<SVGMeshParticleConfig> = {},
  ): RegisteredMeshParticle {
    const geometry = svgExtrusionService.createParticleMesh(path, {
      ...options,
      pathId: path.id,
    });

    const id = `svg_particle_${path.id}`;
    return this.registerMesh(id, name, geometry, "svg", {
      source: "svg",
      svgPathId: path.id,
      // Type proof: svgExtrusionDepth ∈ ℝ ∪ {undefined} → ℝ
      svgExtrusionDepth: (() => {
        const extrusionDepthValue = options.extrusionDepth;
        return isFiniteNumber(extrusionDepthValue) && extrusionDepthValue > 0 ? extrusionDepthValue : 1;
      })(),
      // Type proof: scale ∈ ℝ ∪ {undefined} → ℝ
      scale: (() => {
        const scaleValue = options.scale;
        return isFiniteNumber(scaleValue) && scaleValue > 0 ? scaleValue : 0.01;
      })(),
      // Type proof: centerOrigin ∈ boolean | undefined → boolean
      centerOrigin: options.centerOrigin === true,
      // Type proof: simplify ∈ boolean | undefined → boolean
      simplify: options.simplify === true,
      // Type proof: simplifyTolerance ∈ ℝ ∪ {undefined} → ℝ
      simplifyTolerance: (() => {
        const simplifyToleranceValue = options.simplifyTolerance;
        return isFiniteNumber(simplifyToleranceValue) && simplifyToleranceValue >= 0 ? simplifyToleranceValue : 0.1;
      })(),
    });
  }

  /**
   * Register a primitive shape as mesh particle
   */
  registerPrimitive(
    type: MeshParticleConfig["primitiveType"],
    name?: string,
    size: number = 1,
    detail: number = 1,
  ): RegisteredMeshParticle {
    let geometry: THREE.BufferGeometry;

    switch (type) {
      case "cube":
        geometry = new THREE.BoxGeometry(size, size, size);
        break;
      case "sphere":
        geometry = new THREE.SphereGeometry(size / 2, 8 * detail, 6 * detail);
        break;
      case "cone":
        geometry = new THREE.ConeGeometry(size / 2, size, 8 * detail);
        break;
      case "cylinder":
        geometry = new THREE.CylinderGeometry(
          size / 2,
          size / 2,
          size,
          8 * detail,
        );
        break;
      case "torus":
        geometry = new THREE.TorusGeometry(
          size / 2,
          size / 6,
          8 * detail,
          12 * detail,
        );
        break;
      case "tetrahedron":
        geometry = new THREE.TetrahedronGeometry(size / 2, detail - 1);
        break;
      case "octahedron":
        geometry = new THREE.OctahedronGeometry(size / 2, detail - 1);
        break;
      case "icosahedron":
        geometry = new THREE.IcosahedronGeometry(size / 2, detail - 1);
        break;
      default:
        geometry = new THREE.BoxGeometry(size, size, size);
    }

    const id = `primitive_${type}_${size}_${detail}`;
    const displayName =
      (() => {
        // Type proof: name ∈ string | undefined → string
        const nameValue = name;
        if (typeof nameValue === "string" && nameValue.length > 0) {
          return nameValue;
        }
        // Type proof: type ∈ string | undefined → string
        const typeValue = type;
        if (typeof typeValue === "string" && typeValue.length > 0) {
          return `${typeValue.charAt(0).toUpperCase()}${typeValue.slice(1)}`;
        }
        return "Primitive";
      })();

    return this.registerMesh(id, displayName, geometry, "primitive", {
      source: "primitive",
      primitiveType: type,
      primitiveSize: size,
      primitiveDetail: detail,
      scale: 1,
      centerOrigin: true,
      simplify: false,
      simplifyTolerance: 0,
    });
  }

  /**
   * Register a custom geometry
   */
  registerCustom(
    id: string,
    name: string,
    geometry: THREE.BufferGeometry,
    config?: Partial<MeshParticleConfig>,
  ): RegisteredMeshParticle {
    return this.registerMesh(id, name, geometry, "custom", {
      source: "custom",
      scale: 1,
      centerOrigin: true,
      simplify: false,
      simplifyTolerance: 0,
      ...config,
    });
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                            // instanced // mesh // rendering
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Create an instanced mesh for particle rendering
   */
  createInstancedMesh(
    meshId: string,
    maxInstances: number,
    material?: THREE.Material,
  ): InstancedMeshParticles {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) {
      throw new Error(`[MeshParticleManager] Cannot create instanced mesh: Mesh "${meshId}" not found`);
    }

    // Type proof: material ∈ Material | undefined → Material
    const mat = material !== undefined && material !== null ? material : this.createMaterialForMesh(registration);
    const instancedMesh = new THREE.InstancedMesh(
      registration.geometry,
      mat,
      maxInstances,
    );

    instancedMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
    instancedMesh.count = 0; // Start with no visible instances
    instancedMesh.frustumCulled = false; // Let particle system handle culling

    const instance: InstancedMeshParticles = {
      mesh: instancedMesh,
      maxInstances,
      activeInstances: 0,
      geometry: registration.geometry,
      material: mat,
    };

    this.instancedMeshes.set(meshId, instance);
    return instance;
  }

  /**
   * Update instanced mesh with particle data
   * @param meshId - Registered mesh ID
   * @param particles - Array of particle transforms
   */
  updateInstancedMesh(
    meshId: string,
    particles: Array<{
      position: THREE.Vector3;
      rotation: THREE.Quaternion | THREE.Euler;
      scale: THREE.Vector3 | number;
      color?: THREE.Color;
    }>,
  ): void {
    const instance = this.instancedMeshes.get(meshId);
    if (!instance) return;

    const matrix = new THREE.Matrix4();
    const quaternion = new THREE.Quaternion();
    const scaleVec = new THREE.Vector3();

    const count = Math.min(particles.length, instance.maxInstances);
    instance.mesh.count = count;
    instance.activeInstances = count;

    for (let i = 0; i < count; i++) {
      const p = particles[i];

      // Handle rotation
      if (p.rotation instanceof THREE.Euler) {
        quaternion.setFromEuler(p.rotation);
      } else {
        quaternion.copy(p.rotation);
      }

      // Handle scale
      if (typeof p.scale === "number") {
        scaleVec.set(p.scale, p.scale, p.scale);
      } else {
        scaleVec.copy(p.scale);
      }

      // Compose matrix
      matrix.compose(p.position, quaternion, scaleVec);
      instance.mesh.setMatrixAt(i, matrix);

      // Set color if supported and provided
      if (p.color && instance.mesh.instanceColor) {
        instance.mesh.setColorAt(i, p.color);
      }
    }

    instance.mesh.instanceMatrix.needsUpdate = true;
    if (instance.mesh.instanceColor) {
      instance.mesh.instanceColor.needsUpdate = true;
    }
  }

  /**
   * Create default material for a mesh
   */
  private createMaterialForMesh(
    registration: RegisteredMeshParticle,
  ): THREE.Material {
    const config = registration.config;

    if (!config) {
      return this.defaultMaterial.clone();
    }

    // Type proof: color ∈ string | undefined → string
    const colorValue = config.color;
    const color = typeof colorValue === "string" && colorValue.length > 0 ? colorValue : "#ffffff";
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
      color: new THREE.Color(color),
      metalness: metalness,
      roughness: roughness,
      emissive: new THREE.Color(emissive),
      emissiveIntensity: emissiveIntensity,
      side: THREE.DoubleSide,
    });
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                    // emitter // integration
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get EmitterShapeConfig for mesh emission
   * Particles emit from mesh vertices
   */
  getEmitterShapeConfig(meshId: string): EmitterShapeConfig {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) {
      throw new Error(`[MeshParticleManager] Cannot get emitter shape config: Mesh "${meshId}" not found`);
    }

    const position = registration.geometry.getAttribute("position");
    const normal = registration.geometry.getAttribute("normal");

    if (!position) {
      throw new Error(`[MeshParticleManager] Cannot get emitter shape config: Mesh "${meshId}" has no position attribute`);
    }

    // Extract vertex positions and normals as Float32Arrays
    const vertices = new Float32Array(position.array);
    const normals = normal ? new Float32Array(normal.array) : undefined;

    return {
      type: "mesh",
      meshVertices: vertices,
      meshNormals: normals,
    };
  }

  /**
   * Get RenderConfig for mesh particle rendering
   */
  getRenderConfig(meshId: string): Partial<RenderConfig> {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) {
      throw new Error(`[MeshParticleManager] Cannot get render config: Mesh "${meshId}" not found`);
    }

    return {
      mode: "mesh",
      meshGeometry: "custom",
    };
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // lod // management
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Add LOD levels to a registered mesh
   */
  addLODLevels(
    meshId: string,
    lodGeometries: THREE.BufferGeometry[],
    lodDistances: number[],
  ): void {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) return;

    registration.lodGeometries = lodGeometries;
    registration.lodDistances = lodDistances;
  }

  /**
   * Get appropriate LOD geometry for distance
   */
  getLODGeometry(
    meshId: string,
    distance: number,
  ): THREE.BufferGeometry {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) {
      throw new Error(`[MeshParticleManager] Cannot get LOD geometry: Mesh "${meshId}" not found`);
    }

    if (!registration.lodGeometries || !registration.lodDistances) {
      return registration.geometry;
    }

    for (let i = registration.lodDistances.length - 1; i >= 0; i--) {
      if (distance >= registration.lodDistances[i]) {
        return registration.lodGeometries[i];
      }
    }

    return registration.geometry;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // thumbnail // generation
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Generate a thumbnail preview for a mesh
   */
  async generateThumbnail(
    meshId: string,
    size: number = 128,
  ): Promise<string> {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) {
      throw new Error(`[MeshParticleManager] Cannot generate thumbnail: Mesh "${meshId}" not found`);
    }

    // Create a small scene for rendering
    const scene = new THREE.Scene();
    scene.background = new THREE.Color(0x1a1a1a);

    // Add mesh
    const mesh = new THREE.Mesh(
      registration.geometry,
      new THREE.MeshStandardMaterial({
        color: 0xffffff,
        metalness: 0.3,
        roughness: 0.6,
      }),
    );
    scene.add(mesh);

    // Fit camera to bounding sphere
    const camera = new THREE.PerspectiveCamera(50, 1, 0.1, 1000);
    const radius = registration.boundingSphere.radius;
    const distance = radius / Math.sin((camera.fov * Math.PI) / 360);
    camera.position.set(distance * 0.8, distance * 0.5, distance * 0.8);
    camera.lookAt(registration.boundingSphere.center);

    // Add lights
    const ambient = new THREE.AmbientLight(0xffffff, 0.5);
    const directional = new THREE.DirectionalLight(0xffffff, 1);
    directional.position.set(5, 10, 5);
    scene.add(ambient, directional);

    // Render to canvas
    const canvas = document.createElement("canvas");
    canvas.width = size;
    canvas.height = size;

    const renderer = new THREE.WebGLRenderer({
      canvas,
      antialias: true,
      preserveDrawingBuffer: true,
    });
    renderer.setSize(size, size);
    renderer.render(scene, camera);

    // Get data URL
    const dataUrl = canvas.toDataURL("image/png");

    // Cleanup
    renderer.dispose();
    mesh.geometry.dispose();
    (mesh.material as THREE.Material).dispose();

    // Store thumbnail
    registration.thumbnail = dataUrl;

    return dataUrl;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // accessors
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get a registered mesh
   */
  getMesh(id: string): RegisteredMeshParticle | undefined {
    return this.meshRegistry.get(id);
  }

  /**
   * Get all registered meshes
   */
  getAllMeshes(): RegisteredMeshParticle[] {
    return Array.from(this.meshRegistry.values());
  }

  /**
   * Get meshes by source type
   */
  getMeshesBySource(source: MeshParticleSource): RegisteredMeshParticle[] {
    return Array.from(this.meshRegistry.values()).filter(
      (m) => m.source === source,
    );
  }

  /**
   * Get instanced mesh renderer
   */
  getInstancedMesh(meshId: string): InstancedMeshParticles | undefined {
    return this.instancedMeshes.get(meshId);
  }

  /**
   * Check if a mesh is registered
   */
  hasMesh(id: string): boolean {
    return this.meshRegistry.has(id);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // cleanup
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Unregister a mesh
   */
  unregisterMesh(id: string): void {
    const registration = this.meshRegistry.get(id);
    if (registration) {
      registration.geometry.dispose();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const lodGeometries = (registration != null && typeof registration === "object" && "lodGeometries" in registration && registration.lodGeometries != null && Array.isArray(registration.lodGeometries)) ? registration.lodGeometries : undefined;
      if (lodGeometries != null) {
        lodGeometries.forEach((g) => g.dispose());
      }
    }
    this.meshRegistry.delete(id);

    // Also remove instanced mesh if exists
    const instance = this.instancedMeshes.get(id);
    if (instance) {
      instance.mesh.dispose();
      instance.material.dispose();
    }
    this.instancedMeshes.delete(id);
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    // Dispose all geometries
    for (const registration of this.meshRegistry.values()) {
      registration.geometry.dispose();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const lodGeometries = (registration != null && typeof registration === "object" && "lodGeometries" in registration && registration.lodGeometries != null && Array.isArray(registration.lodGeometries)) ? registration.lodGeometries : undefined;
      if (lodGeometries != null) {
        lodGeometries.forEach((g) => g.dispose());
      }
    }
    this.meshRegistry.clear();

    // Dispose all instanced meshes
    for (const instance of this.instancedMeshes.values()) {
      instance.mesh.dispose();
      instance.material.dispose();
    }
    this.instancedMeshes.clear();

    // Dispose default material
    this.defaultMaterial.dispose();
  }
}

// Export singleton instance
export const meshParticleManager = new MeshParticleManager();

// ════════════════════════════════════════════════════════════════════════════
//                                                        // default // configs
// ════════════════════════════════════════════════════════════════════════════

export function createDefaultMeshParticleConfig(): MeshParticleConfig {
  return {
    source: "primitive",
    primitiveType: "sphere",
    primitiveSize: 1,
    primitiveDetail: 1,
    scale: 1,
    centerOrigin: true,
    simplify: false,
    simplifyTolerance: 0.1,
  };
}
