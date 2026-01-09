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

// ============================================================================
// TYPES
// ============================================================================

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

  // LOD levels (optional)
  lodGeometries?: THREE.BufferGeometry[];
  lodDistances?: number[];

  // Original configuration
  config?: MeshParticleConfig;
}

/** Mesh particle configuration */
export interface MeshParticleConfig {
  source: MeshParticleSource;

  // SVG source options
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

// ============================================================================
// MESH PARTICLE MANAGER
// ============================================================================

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

  // ==========================================================================
  // MESH REGISTRATION
  // ==========================================================================

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
      boundingBox: geometry.boundingBox?.clone() ?? new THREE.Box3(),
      boundingSphere: geometry.boundingSphere?.clone() ?? new THREE.Sphere(),
      vertexCount: geometry.getAttribute("position")?.count ?? 0,
      faceCount: geometry.index
        ? geometry.index.count / 3
        : (geometry.getAttribute("position")?.count ?? 0) / 3,
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
  ): RegisteredMeshParticle | null {
    const document = svgExtrusionService.getDocument(svgDocumentId);
    if (!document) {
      console.warn(`SVG document not found: ${svgDocumentId}`);
      return null;
    }

    const path = document.paths.find((p) => p.id === svgPathId);
    if (!path) {
      console.warn(`SVG path not found: ${svgPathId}`);
      return null;
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
      svgExtrusionDepth: options.extrusionDepth ?? 1,
      scale: options.scale ?? 0.01,
      centerOrigin: options.centerOrigin ?? true,
      simplify: options.simplify ?? true,
      simplifyTolerance: options.simplifyTolerance ?? 0.1,
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
      svgExtrusionDepth: options.extrusionDepth ?? 1,
      scale: options.scale ?? 0.01,
      centerOrigin: options.centerOrigin ?? true,
      simplify: options.simplify ?? true,
      simplifyTolerance: options.simplifyTolerance ?? 0.1,
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
      name ?? `${type?.charAt(0).toUpperCase()}${type?.slice(1)}`;

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

  // ==========================================================================
  // INSTANCED MESH RENDERING
  // ==========================================================================

  /**
   * Create an instanced mesh for particle rendering
   */
  createInstancedMesh(
    meshId: string,
    maxInstances: number,
    material?: THREE.Material,
  ): InstancedMeshParticles | null {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) {
      console.warn(`Mesh not found: ${meshId}`);
      return null;
    }

    const mat = material ?? this.createMaterialForMesh(registration);
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

    return new THREE.MeshStandardMaterial({
      color: new THREE.Color(config.color ?? "#ffffff"),
      metalness: config.metalness ?? 0,
      roughness: config.roughness ?? 0.5,
      emissive: new THREE.Color(config.emissive ?? "#000000"),
      emissiveIntensity: config.emissiveIntensity ?? 0,
      side: THREE.DoubleSide,
    });
  }

  // ==========================================================================
  // EMITTER INTEGRATION
  // ==========================================================================

  /**
   * Get EmitterShapeConfig for mesh emission
   * Particles emit from mesh vertices
   */
  getEmitterShapeConfig(meshId: string): EmitterShapeConfig | null {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) return null;

    const position = registration.geometry.getAttribute("position");
    const normal = registration.geometry.getAttribute("normal");

    if (!position) return null;

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
  getRenderConfig(meshId: string): Partial<RenderConfig> | null {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) return null;

    return {
      mode: "mesh",
      meshGeometry: "custom",
    };
  }

  // ==========================================================================
  // LOD MANAGEMENT
  // ==========================================================================

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
  ): THREE.BufferGeometry | null {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) return null;

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

  // ==========================================================================
  // THUMBNAIL GENERATION
  // ==========================================================================

  /**
   * Generate a thumbnail preview for a mesh
   */
  async generateThumbnail(
    meshId: string,
    size: number = 128,
  ): Promise<string | null> {
    const registration = this.meshRegistry.get(meshId);
    if (!registration) return null;

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

  // ==========================================================================
  // ACCESSORS
  // ==========================================================================

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

  // ==========================================================================
  // CLEANUP
  // ==========================================================================

  /**
   * Unregister a mesh
   */
  unregisterMesh(id: string): void {
    const registration = this.meshRegistry.get(id);
    if (registration) {
      registration.geometry.dispose();
      registration.lodGeometries?.forEach((g) => g.dispose());
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
      registration.lodGeometries?.forEach((g) => g.dispose());
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

// ============================================================================
// DEFAULT CONFIGS
// ============================================================================

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
