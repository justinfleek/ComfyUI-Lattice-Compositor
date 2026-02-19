/**
 * GPU Particle Renderer
 *
 * High-performance particle rendering using Three.js InstancedMesh.
 * Offloads particle rendering to GPU while keeping simulation on CPU.
 *
 * Performance targets:
 * - 100,000+ particles at 60fps
 * - Minimal CPU-GPU data transfer
 * - Efficient attribute updates via BufferGeometry
 *
 * Features:
 * - Instanced rendering for millions of particles
 * - Custom shaders for particle effects
 * - Soft particles (depth fade)
 * - Motion blur via velocity stretching
 * - Emissive/bloom support
 * - Sprite sheet animation
 */

import * as THREE from "three";
import type { Particle, RenderOptions } from "./particleSystem";
import { isFiniteNumber } from "@/utils/typeGuards";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export interface GPUParticleRendererConfig {
  /** Maximum particles to render (pre-allocates buffers) */
  maxParticles: number;
  /** Enable soft particles (depth-based fading) */
  softParticles: boolean;
  /** Soft particle fade distance */
  softParticleDistance: number;
  /** Enable velocity-based motion blur */
  velocityMotionBlur: boolean;
  /** Motion blur stretch amount */
  motionBlurStrength: number;
  /** Enable emissive rendering for bloom */
  emissive: boolean;
  /** Emissive intensity */
  emissiveIntensity: number;
}

export interface GPUParticleData {
  /** Position array (x, y, z per particle) */
  positions: Float32Array;
  /** Velocity array for motion blur (vx, vy, vz per particle) */
  velocities: Float32Array;
  /** Color array (r, g, b, a per particle) */
  colors: Float32Array;
  /** Size array (size per particle) */
  sizes: Float32Array;
  /** Age/lifetime array (age, lifetime per particle) for shader effects */
  ages: Float32Array;
  /** Rotation array (rotation per particle) */
  rotations: Float32Array;
  /** Active particle count */
  count: number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                                  // shaders
// ═══════════════════════════════════════════════════════════════════════════

const PARTICLE_VERTEX_SHADER = `
  attribute float size;
  attribute vec4 particleColor;
  attribute vec2 ageLifetime;
  attribute vec3 velocity;
  attribute float rotation;

  uniform float uTime;
  uniform float uMotionBlurStrength;
  uniform bool uMotionBlur;
  uniform float uSizeScale;

  varying vec4 vColor;
  varying vec2 vUv;
  varying float vAge;
  varying float vLifetimeRatio;
  varying float vRotation;

  void main() {
    vColor = particleColor;
    vUv = uv;
    vAge = ageLifetime.x;
    vLifetimeRatio = ageLifetime.x / max(ageLifetime.y, 0.001);
    vRotation = rotation;

    // Apply motion blur stretch
    vec3 pos = position;
    if (uMotionBlur && length(velocity) > 0.001) {
      // Stretch along velocity direction
      float stretch = length(velocity) * uMotionBlurStrength * 10.0;
      pos += normalize(velocity) * stretch * 0.5;
    }

    vec4 mvPosition = modelViewMatrix * vec4(pos, 1.0);

    // Point size with perspective
    gl_PointSize = size * uSizeScale * (300.0 / -mvPosition.z);
    gl_PointSize = clamp(gl_PointSize, 1.0, 256.0);

    gl_Position = projectionMatrix * mvPosition;
  }
`;

const PARTICLE_FRAGMENT_SHADER = `
  uniform sampler2D uSprite;
  uniform bool uUseSprite;
  uniform bool uSoftParticles;
  uniform float uSoftDistance;
  uniform sampler2D uDepthTexture;
  uniform vec2 uResolution;
  uniform float uNear;
  uniform float uFar;
  uniform bool uEmissive;
  uniform float uEmissiveIntensity;

  varying vec4 vColor;
  varying vec2 vUv;
  varying float vAge;
  varying float vLifetimeRatio;
  varying float vRotation;

  float linearizeDepth(float depth) {
    return (2.0 * uNear * uFar) / (uFar + uNear - depth * (uFar - uNear));
  }

  void main() {
    vec2 uv = gl_PointCoord;

    // Apply rotation
    if (abs(vRotation) > 0.001) {
      float c = cos(vRotation);
      float s = sin(vRotation);
      uv = uv - 0.5;
      uv = vec2(c * uv.x - s * uv.y, s * uv.x + c * uv.y);
      uv = uv + 0.5;
    }

    vec4 color = vColor;

    if (uUseSprite) {
      vec4 spriteColor = texture2D(uSprite, uv);
      color *= spriteColor;
    } else {
      // Default circular particle
      float dist = length(uv - 0.5) * 2.0;
      if (dist > 1.0) discard;

      // Smooth circle falloff
      float alpha = 1.0 - smoothstep(0.5, 1.0, dist);
      color.a *= alpha;
    }

    // Soft particles (depth fade)
    if (uSoftParticles) {
      vec2 screenUV = gl_FragCoord.xy / uResolution;
      float sceneDepth = texture2D(uDepthTexture, screenUV).r;
      sceneDepth = linearizeDepth(sceneDepth);

      float particleDepth = linearizeDepth(gl_FragCoord.z);
      float depthDiff = sceneDepth - particleDepth;

      float fade = smoothstep(0.0, uSoftDistance, depthDiff);
      color.a *= fade;
    }

    // Fade out at end of life
    if (vLifetimeRatio > 0.8) {
      color.a *= 1.0 - (vLifetimeRatio - 0.8) / 0.2;
    }

    // Emissive output for bloom
    if (uEmissive) {
      color.rgb *= uEmissiveIntensity;
    }

    if (color.a < 0.01) discard;

    gl_FragColor = color;
  }
`;

// ═══════════════════════════════════════════════════════════════════════════
//                                     // gpu // particle // renderer // class
// ═══════════════════════════════════════════════════════════════════════════

export class GPUParticleRenderer {
  private readonly geometry: THREE.BufferGeometry;
  private readonly material: THREE.ShaderMaterial;
  private readonly points: THREE.Points;
  private readonly config: GPUParticleRendererConfig;
  private depthTexture: THREE.DepthTexture | null = null;

  // Attribute buffers
  private positionAttr: THREE.BufferAttribute;
  private colorAttr: THREE.BufferAttribute;
  private sizeAttr: THREE.BufferAttribute;
  private velocityAttr: THREE.BufferAttribute;
  private ageAttr: THREE.BufferAttribute;
  private rotationAttr: THREE.BufferAttribute;

  // Sprite texture
  private spriteTexture: THREE.Texture | null = null;

  // Current particle count
  private activeCount: number = 0;

  constructor(config: Partial<GPUParticleRendererConfig> = {}) {
    // Type proof: maxParticles ∈ number | undefined → number
    const maxParticles = isFiniteNumber(config.maxParticles) &&
      config.maxParticles > 0
      ? Math.floor(config.maxParticles)
      : 100000;
    // Type proof: softParticles ∈ boolean | undefined → boolean
    const softParticles =
      typeof config.softParticles === "boolean" ? config.softParticles : false;
    // Type proof: softParticleDistance ∈ number | undefined → number
    const softParticleDistance = isFiniteNumber(config.softParticleDistance) &&
      config.softParticleDistance > 0
      ? config.softParticleDistance
      : 50;
    // Type proof: velocityMotionBlur ∈ boolean | undefined → boolean
    const velocityMotionBlur =
      typeof config.velocityMotionBlur === "boolean"
        ? config.velocityMotionBlur
        : true;
    // Type proof: motionBlurStrength ∈ number | undefined → number
    const motionBlurStrength = isFiniteNumber(config.motionBlurStrength)
      ? Math.max(0, config.motionBlurStrength)
      : 0.5;
    // Type proof: emissive ∈ boolean | undefined → boolean
    const emissive =
      typeof config.emissive === "boolean" ? config.emissive : false;
    // Type proof: emissiveIntensity ∈ number | undefined → number
    const emissiveIntensity = isFiniteNumber(config.emissiveIntensity) &&
      config.emissiveIntensity > 0
      ? config.emissiveIntensity
      : 2.0;

    this.config = {
      maxParticles,
      softParticles,
      softParticleDistance,
      velocityMotionBlur,
      motionBlurStrength,
      emissive,
      emissiveIntensity,
    };

    // Create geometry with pre-allocated buffers
    this.geometry = new THREE.BufferGeometry();

    // Position (x, y, z)
    const positions = new Float32Array(this.config.maxParticles * 3);
    this.positionAttr = new THREE.BufferAttribute(positions, 3);
    this.positionAttr.setUsage(THREE.DynamicDrawUsage);
    this.geometry.setAttribute("position", this.positionAttr);

    // Color (r, g, b, a)
    const colors = new Float32Array(this.config.maxParticles * 4);
    this.colorAttr = new THREE.BufferAttribute(colors, 4);
    this.colorAttr.setUsage(THREE.DynamicDrawUsage);
    this.geometry.setAttribute("particleColor", this.colorAttr);

    // Size
    const sizes = new Float32Array(this.config.maxParticles);
    this.sizeAttr = new THREE.BufferAttribute(sizes, 1);
    this.sizeAttr.setUsage(THREE.DynamicDrawUsage);
    this.geometry.setAttribute("size", this.sizeAttr);

    // Velocity (for motion blur)
    const velocities = new Float32Array(this.config.maxParticles * 3);
    this.velocityAttr = new THREE.BufferAttribute(velocities, 3);
    this.velocityAttr.setUsage(THREE.DynamicDrawUsage);
    this.geometry.setAttribute("velocity", this.velocityAttr);

    // Age and lifetime
    const ages = new Float32Array(this.config.maxParticles * 2);
    this.ageAttr = new THREE.BufferAttribute(ages, 2);
    this.ageAttr.setUsage(THREE.DynamicDrawUsage);
    this.geometry.setAttribute("ageLifetime", this.ageAttr);

    // Rotation
    const rotations = new Float32Array(this.config.maxParticles);
    this.rotationAttr = new THREE.BufferAttribute(rotations, 1);
    this.rotationAttr.setUsage(THREE.DynamicDrawUsage);
    this.geometry.setAttribute("rotation", this.rotationAttr);

    // Create shader material
    this.material = new THREE.ShaderMaterial({
      vertexShader: PARTICLE_VERTEX_SHADER,
      fragmentShader: PARTICLE_FRAGMENT_SHADER,
      uniforms: {
        uTime: { value: 0 },
        uSprite: { value: null },
        uUseSprite: { value: false },
        uSoftParticles: { value: this.config.softParticles },
        uSoftDistance: { value: this.config.softParticleDistance },
        uDepthTexture: { value: null },
        uResolution: { value: new THREE.Vector2(1920, 1080) },
        uNear: { value: 0.1 },
        uFar: { value: 10000 },
        uMotionBlur: { value: this.config.velocityMotionBlur },
        uMotionBlurStrength: { value: this.config.motionBlurStrength },
        uSizeScale: { value: 1.0 },
        uEmissive: { value: this.config.emissive },
        uEmissiveIntensity: { value: this.config.emissiveIntensity },
      },
      transparent: true,
      depthWrite: false,
      blending: THREE.AdditiveBlending,
    });

    // Create points mesh
    this.points = new THREE.Points(this.geometry, this.material);
    this.points.frustumCulled = false; // Particles often extend outside bounding box

    // Initialize draw range to 0
    this.geometry.setDrawRange(0, 0);
  }

  /**
   * Get the Three.js object for adding to scene
   */
  getObject(): THREE.Points {
    return this.points;
  }

  /**
   * Update particle data from CPU simulation
   * Efficient bulk update of all attributes
   */
  updateParticles(
    particles: readonly Particle[],
    canvasWidth: number,
    canvasHeight: number,
  ): void {
    const count = Math.min(particles.length, this.config.maxParticles);
    this.activeCount = count;

    const positions = this.positionAttr.array as Float32Array;
    const colors = this.colorAttr.array as Float32Array;
    const sizes = this.sizeAttr.array as Float32Array;
    const velocities = this.velocityAttr.array as Float32Array;
    const ages = this.ageAttr.array as Float32Array;
    const rotations = this.rotationAttr.array as Float32Array;

    for (let i = 0; i < count; i++) {
      const p = particles[i];
      const i3 = i * 3;
      const i4 = i * 4;
      const i2 = i * 2;

      // Position (convert from normalized 0-1 to world coordinates)
      positions[i3] = p.x * canvasWidth;
      positions[i3 + 1] = p.y * canvasHeight;
      positions[i3 + 2] = 0; // Z for layering

      // Color (RGBA normalized)
      colors[i4] = p.color[0] / 255;
      colors[i4 + 1] = p.color[1] / 255;
      colors[i4 + 2] = p.color[2] / 255;
      colors[i4 + 3] = p.color[3] / 255;

      // Size
      sizes[i] = p.size;

      // Velocity (convert from normalized to world)
      velocities[i3] = p.vx * canvasWidth;
      velocities[i3 + 1] = p.vy * canvasHeight;
      velocities[i3 + 2] = 0;

      // Age and lifetime
      ages[i2] = p.age;
      ages[i2 + 1] = p.lifetime;

      // Rotation
      rotations[i] = p.rotation;
    }

    // Mark attributes as needing update
    this.positionAttr.needsUpdate = true;
    this.colorAttr.needsUpdate = true;
    this.sizeAttr.needsUpdate = true;
    this.velocityAttr.needsUpdate = true;
    this.ageAttr.needsUpdate = true;
    this.rotationAttr.needsUpdate = true;

    // Update draw range
    this.geometry.setDrawRange(0, count);
  }

  /**
   * Set sprite texture for particle rendering
   */
  setSpriteTexture(texture: THREE.Texture | null): void {
    this.spriteTexture = texture;
    this.material.uniforms.uSprite.value = texture;
    this.material.uniforms.uUseSprite.value = texture !== null;
  }

  /**
   * Load sprite from URL
   */
  async loadSprite(url: string): Promise<void> {
    const loader = new THREE.TextureLoader();
    const texture = await loader.loadAsync(url);
    this.setSpriteTexture(texture);
  }

  /**
   * Set depth texture for soft particles
   */
  setDepthTexture(texture: THREE.DepthTexture): void {
    this.depthTexture = texture;
    this.material.uniforms.uDepthTexture.value = texture;
  }

  /**
   * Update resolution for soft particles
   */
  setResolution(width: number, height: number): void {
    this.material.uniforms.uResolution.value.set(width, height);
  }

  /**
   * Update camera near/far for soft particles
   */
  setCameraClipPlanes(near: number, far: number): void {
    this.material.uniforms.uNear.value = near;
    this.material.uniforms.uFar.value = far;
  }

  /**
   * Set blend mode
   */
  setBlendMode(mode: RenderOptions["blendMode"]): void {
    switch (mode) {
      case "additive":
        this.material.blending = THREE.AdditiveBlending;
        break;
      case "multiply":
        this.material.blending = THREE.MultiplyBlending;
        break;
      case "screen":
        // Three.js doesn't have screen blending, use custom
        this.material.blending = THREE.CustomBlending;
        this.material.blendSrc = THREE.OneFactor;
        this.material.blendDst = THREE.OneMinusSrcColorFactor;
        break;
      default:
        this.material.blending = THREE.NormalBlending;
        break;
    }
  }

  /**
   * Set motion blur enabled/strength
   */
  setMotionBlur(enabled: boolean, strength?: number): void {
    this.material.uniforms.uMotionBlur.value = enabled;
    if (strength !== undefined) {
      this.material.uniforms.uMotionBlurStrength.value = strength;
    }
  }

  /**
   * Set soft particles enabled
   */
  setSoftParticles(enabled: boolean, distance?: number): void {
    this.material.uniforms.uSoftParticles.value = enabled;
    if (distance !== undefined) {
      this.material.uniforms.uSoftDistance.value = distance;
    }
  }

  /**
   * Set emissive rendering for bloom
   */
  setEmissive(enabled: boolean, intensity?: number): void {
    this.material.uniforms.uEmissive.value = enabled;
    if (intensity !== undefined) {
      this.material.uniforms.uEmissiveIntensity.value = intensity;
    }
  }

  /**
   * Set size scale
   */
  setSizeScale(scale: number): void {
    this.material.uniforms.uSizeScale.value = scale;
  }

  /**
   * Update time uniform
   */
  setTime(time: number): void {
    this.material.uniforms.uTime.value = time;
  }

  /**
   * Get current particle count
   */
  getParticleCount(): number {
    return this.activeCount;
  }

  /**
   * Get configuration
   */
  getConfig(): GPUParticleRendererConfig {
    return { ...this.config };
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    this.geometry.dispose();
    this.material.dispose();
    if (this.spriteTexture) {
      this.spriteTexture.dispose();
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// INSTANCED MESH RENDERER (for complex particle shapes)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Instanced particle renderer for complex particle shapes
 * Uses InstancedMesh for shapes beyond simple points
 */
export class InstancedParticleRenderer {
  private readonly mesh: THREE.InstancedMesh;
  private readonly maxInstances: number;
  private activeCount: number = 0;

  // Instance attributes
  private readonly colorArray: Float32Array;
  private readonly colorAttr: THREE.InstancedBufferAttribute;

  constructor(
    geometry: THREE.BufferGeometry,
    material: THREE.Material,
    maxInstances: number = 100000,
  ) {
    this.maxInstances = maxInstances;

    // Create instanced mesh
    this.mesh = new THREE.InstancedMesh(geometry, material, maxInstances);
    this.mesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
    this.mesh.frustumCulled = false;

    // Add instance color attribute
    this.colorArray = new Float32Array(maxInstances * 4);
    this.colorAttr = new THREE.InstancedBufferAttribute(this.colorArray, 4);
    this.colorAttr.setUsage(THREE.DynamicDrawUsage);
    this.mesh.geometry.setAttribute("instanceColor", this.colorAttr);

    // Start with 0 visible
    this.mesh.count = 0;
  }

  /**
   * Get the Three.js object
   */
  getObject(): THREE.InstancedMesh {
    return this.mesh;
  }

  /**
   * Update instances from particle data
   */
  updateInstances(
    particles: readonly Particle[],
    canvasWidth: number,
    canvasHeight: number,
  ): void {
    const count = Math.min(particles.length, this.maxInstances);
    this.activeCount = count;

    const matrix = new THREE.Matrix4();
    const position = new THREE.Vector3();
    const quaternion = new THREE.Quaternion();
    const scale = new THREE.Vector3();

    for (let i = 0; i < count; i++) {
      const p = particles[i];

      // Position
      position.set(p.x * canvasWidth, p.y * canvasHeight, 0);

      // Rotation (around Z axis)
      quaternion.setFromEuler(new THREE.Euler(0, 0, p.rotation));

      // Scale based on particle size
      const s = p.size / 10; // Normalize size
      scale.set(s, s, s);

      // Compose matrix
      matrix.compose(position, quaternion, scale);
      this.mesh.setMatrixAt(i, matrix);

      // Color
      const i4 = i * 4;
      this.colorArray[i4] = p.color[0] / 255;
      this.colorArray[i4 + 1] = p.color[1] / 255;
      this.colorArray[i4 + 2] = p.color[2] / 255;
      this.colorArray[i4 + 3] = p.color[3] / 255;
    }

    this.mesh.instanceMatrix.needsUpdate = true;
    this.colorAttr.needsUpdate = true;
    this.mesh.count = count;
  }

  /**
   * Get instance count
   */
  getInstanceCount(): number {
    return this.activeCount;
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    this.mesh.geometry.dispose();
    if (this.mesh.material instanceof THREE.Material) {
      this.mesh.material.dispose();
    }
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                     // factory // functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Create a GPU particle renderer with default settings
 */
export function createGPUParticleRenderer(
  config?: Partial<GPUParticleRendererConfig>,
): GPUParticleRenderer {
  return new GPUParticleRenderer(config);
}

/**
 * Create an instanced renderer for a specific shape
 */
export function createInstancedParticleRenderer(
  shape: "circle" | "square" | "triangle" | "star",
  maxInstances?: number,
): InstancedParticleRenderer {
  let geometry: THREE.BufferGeometry;

  switch (shape) {
    case "circle":
      geometry = new THREE.CircleGeometry(0.5, 16);
      break;
    case "square":
      geometry = new THREE.PlaneGeometry(1, 1);
      break;
    case "triangle": {
      geometry = new THREE.BufferGeometry();
      const vertices = new Float32Array([
        0, 0.5, 0, -0.5, -0.5, 0, 0.5, -0.5, 0,
      ]);
      geometry.setAttribute("position", new THREE.BufferAttribute(vertices, 3));
      break;
    }
    case "star":
      geometry = createStarGeometry(5, 0.5, 0.25);
      break;
    default:
      geometry = new THREE.CircleGeometry(0.5, 16);
  }

  const material = new THREE.MeshBasicMaterial({
    transparent: true,
    side: THREE.DoubleSide,
  });

  return new InstancedParticleRenderer(geometry, material, maxInstances);
}

/**
 * Create star geometry helper
 */
function createStarGeometry(
  points: number,
  outerRadius: number,
  innerRadius: number,
): THREE.BufferGeometry {
  const geometry = new THREE.BufferGeometry();
  const vertices: number[] = [];

  for (let i = 0; i < points * 2; i++) {
    const radius = i % 2 === 0 ? outerRadius : innerRadius;
    const angle = (i / (points * 2)) * Math.PI * 2 - Math.PI / 2;
    vertices.push(Math.cos(angle) * radius, Math.sin(angle) * radius, 0);
  }

  // Create triangles from center
  const indices: number[] = [];
  for (let i = 0; i < points * 2; i++) {
    // Center triangle
    indices.push(points * 2, i, (i + 1) % (points * 2));
  }

  // Add center vertex
  vertices.push(0, 0, 0);

  geometry.setAttribute(
    "position",
    new THREE.Float32BufferAttribute(vertices, 3),
  );
  geometry.setIndex(indices);
  geometry.computeVertexNormals();

  return geometry;
}

export default GPUParticleRenderer;
