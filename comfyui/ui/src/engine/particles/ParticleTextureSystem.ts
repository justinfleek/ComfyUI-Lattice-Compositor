/**
 * Particle Texture System
 *
 * Handles particle textures, sprite sheets, procedural shapes,
 * motion blur, and glow effects.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from "three";
import {
  PARTICLE_GLOW_FRAGMENT_SHADER,
  PARTICLE_GLOW_VERTEX_SHADER,
} from "./particleShaders";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

export interface SpriteSheetConfig {
  columns: number;
  rows: number;
  animate: boolean;
  frameRate: number;
  randomStart: boolean;
}

export interface GlowConfig {
  enabled: boolean;
  radius: number;
  intensity: number;
}

export interface MotionBlurConfig {
  enabled: boolean;
  strength: number;
  minStretch: number;
  maxStretch: number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                   // particle // texture // system // class
// ═══════════════════════════════════════════════════════════════════════════

export class ParticleTextureSystem {
  private particleTexture: THREE.Texture | null = null;
  private spriteSheetConfig: SpriteSheetConfig | null = null;
  private glowConfig: GlowConfig | null = null;
  private glowMaterial: THREE.ShaderMaterial | null = null;
  private glowMesh: THREE.Mesh | null = null;
  private material: THREE.ShaderMaterial | null = null;
  private instancedGeometry: THREE.InstancedBufferGeometry | null = null;

  /**
   * Set the material and geometry references
   */
  setRenderTargets(
    material: THREE.ShaderMaterial | null,
    instancedGeometry: THREE.InstancedBufferGeometry | null,
  ): void {
    this.material = material;
    this.instancedGeometry = instancedGeometry;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                       // texture // loading
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Load a particle texture from URL or data URI
   */
  loadTexture(
    url: string,
    spriteSheet?: {
      columns?: number;
      rows?: number;
      animate?: boolean;
      frameRate?: number;
      randomStart?: boolean;
    },
  ): Promise<void> {
    return new Promise((resolve, reject) => {
      const loader = new THREE.TextureLoader();

      loader.load(
        url,
        (texture) => {
          this.particleTexture = texture;
          texture.minFilter = THREE.LinearMipMapLinearFilter;
          texture.magFilter = THREE.LinearFilter;
          texture.wrapS = THREE.ClampToEdgeWrapping;
          texture.wrapT = THREE.ClampToEdgeWrapping;

          // Update material uniforms
          if (this.material) {
            this.material.uniforms.diffuseMap.value = texture;
            this.material.uniforms.hasDiffuseMap.value = 1;
            this.material.uniforms.proceduralShape.value = 0;

            // Sprite sheet configuration
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
            if (spriteSheet && (spriteSheet.columns || spriteSheet.rows)) {
              // Validate cols/rows - explicit pattern matching first, then validate
              const rawCols = (typeof spriteSheet.columns === "number" && Number.isFinite(spriteSheet.columns) && spriteSheet.columns > 0) ? spriteSheet.columns : 1;
              const cols = (Number.isFinite(rawCols) && rawCols > 0)
                ? Math.floor(rawCols)
                : 1;
              const rawRows = (typeof spriteSheet.rows === "number" && Number.isFinite(spriteSheet.rows) && spriteSheet.rows > 0) ? spriteSheet.rows : 1;
              const rows = (Number.isFinite(rawRows) && rawRows > 0)
                ? Math.floor(rawRows)
                : 1;
              // Validate frameRate
              const rawFrameRate = (typeof spriteSheet.frameRate === "number" && Number.isFinite(spriteSheet.frameRate) && spriteSheet.frameRate > 0) ? spriteSheet.frameRate : 10;
              const frameRate = (Number.isFinite(rawFrameRate) && rawFrameRate > 0)
                ? rawFrameRate
                : 10;

              const animate = (typeof spriteSheet.animate === "boolean") ? spriteSheet.animate : false;
              const randomStart = (typeof spriteSheet.randomStart === "boolean") ? spriteSheet.randomStart : false;
              this.spriteSheetConfig = {
                columns: cols,
                rows: rows,
                animate,
                frameRate: frameRate,
                randomStart,
              };

              this.material.uniforms.spriteSheetSize.value.set(cols, rows);
              this.material.uniforms.spriteFrameCount.value = cols * rows;
              this.material.uniforms.animateSprite.value = spriteSheet.animate
                ? 1
                : 0;
              this.material.uniforms.spriteFrameRate.value = frameRate;
              // Enable per-particle random start frame for sprite sheet variation
              this.material.uniforms.randomStartFrame.value =
                spriteSheet.randomStart ? 1 : 0;
            }

            this.material.needsUpdate = true;
          }

          resolve();
        },
        undefined,
        (error) => {
          console.error("Failed to load particle texture:", error);
          reject(error);
        },
      );
    });
  }

  /**
   * Get the current texture
   */
  getTexture(): THREE.Texture | null {
    return this.particleTexture;
  }

  /**
   * Get sprite sheet config
   */
  getSpriteSheetConfig(): SpriteSheetConfig | null {
    return this.spriteSheetConfig;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                     // procedural // shapes
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Set procedural shape (no texture).
   * Supports all 9 shapes: 0=none, 1=circle, 2=ring, 3=square, 4=star, 5=noise, 6=line, 7=triangle, 8=shadedSphere, 9=fadedSphere
   */
  setProceduralShape(
    shape:
      | "none"
      | "circle"
      | "ring"
      | "square"
      | "star"
      | "noise"
      | "line"
      | "triangle"
      | "shadedSphere"
      | "fadedSphere",
  ): void {
    const shapeMap: Record<string, number> = {
      none: 0,
      circle: 1,
      ring: 2,
      square: 3,
      star: 4,
      noise: 5,
      line: 6,
      triangle: 7,
      shadedSphere: 8,
      fadedSphere: 9,
    };
    if (this.material) {
      this.material.uniforms.hasDiffuseMap.value = 0;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
      const shapeValue = shapeMap[shape];
      this.material.uniforms.proceduralShape.value = (shapeValue !== null && shapeValue !== undefined && typeof shapeValue === "number" && Number.isFinite(shapeValue)) ? shapeValue : 1;
      this.material.needsUpdate = true;
    }
    this.particleTexture = null;
    this.spriteSheetConfig = null;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                      // sprite // animation
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Update time uniform for sprite animation
   */
  updateSpriteAnimation(time: number): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const spriteSheetConfig = this.spriteSheetConfig;
    const spriteSheetAnimate = (spriteSheetConfig != null && typeof spriteSheetConfig === "object" && "animate" in spriteSheetConfig && typeof spriteSheetConfig.animate === "boolean" && spriteSheetConfig.animate) ? true : false;
    if (this.material != null && spriteSheetAnimate) {
      this.material.uniforms.time.value = time;
    }
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                           // motion // blur
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Configure motion blur effect
   * Stretches particles along their velocity direction
   */
  setMotionBlur(
    config: MotionBlurConfig,
    renderConfig: {
      motionBlur?: boolean;
      motionBlurStrength?: number;
      minStretch?: number;
      maxStretch?: number;
    },
  ): void {
    if (!this.material) return;

    this.material.uniforms.motionBlurEnabled.value = config.enabled ? 1 : 0;

    // Validate motion blur values
    if (config.strength !== undefined && Number.isFinite(config.strength)) {
      this.material.uniforms.motionBlurStrength.value = Math.max(0, config.strength);
    }
    if (config.minStretch !== undefined && Number.isFinite(config.minStretch)) {
      this.material.uniforms.minStretch.value = Math.max(0, config.minStretch);
    }
    if (config.maxStretch !== undefined && Number.isFinite(config.maxStretch)) {
      this.material.uniforms.maxStretch.value = Math.max(0, config.maxStretch);
    }

    // Update config
    renderConfig.motionBlur = config.enabled;
    if (config.strength !== undefined) {
      renderConfig.motionBlurStrength = config.strength;
    }
    if (config.minStretch !== undefined) {
      renderConfig.minStretch = config.minStretch;
    }
    if (config.maxStretch !== undefined) {
      renderConfig.maxStretch = config.maxStretch;
    }
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                          // glow // effects
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Initialize glow effect rendering
   * Creates a separate mesh that renders an expanded soft glow behind particles
   */
  initializeGlow(config: GlowConfig): void {
    this.glowConfig = config;

    if (!config.enabled || !this.instancedGeometry) return;

    // Validate glow config
    const safeRadius = Number.isFinite(config.radius) && config.radius > 0 ? config.radius : 10;
    const safeIntensity = Number.isFinite(config.intensity) && config.intensity >= 0 ? config.intensity : 0.5;
    
    // Create glow material with custom shaders
    this.glowMaterial = new THREE.ShaderMaterial({
      vertexShader: PARTICLE_GLOW_VERTEX_SHADER,
      fragmentShader: PARTICLE_GLOW_FRAGMENT_SHADER,
      uniforms: {
        glowRadius: { value: safeRadius / 10 }, // Normalize to 0-1 range
        glowIntensity: { value: safeIntensity },
      },
      transparent: true,
      depthWrite: false,
      depthTest: true,
      blending: THREE.AdditiveBlending,
    });

    // Clone instanced geometry for glow pass
    this.glowMesh = new THREE.Mesh(this.instancedGeometry, this.glowMaterial);
    this.glowMesh.frustumCulled = false;
    this.glowMesh.renderOrder = -1; // Render glow behind particles
  }

  /**
   * Update glow configuration
   */
  setGlow(config: {
    enabled?: boolean;
    radius?: number;
    intensity?: number;
  }): void {
    if (!this.glowConfig) {
      this.glowConfig = { enabled: false, radius: 10, intensity: 0.5 };
    }

    if (config.enabled !== undefined) {
      this.glowConfig.enabled = config.enabled;
      if (this.glowMesh) {
        this.glowMesh.visible = config.enabled;
      }
    }

    if (this.glowMaterial) {
      // Validate glow values
      if (config.radius !== undefined && Number.isFinite(config.radius)) {
        const safeRadius = Math.max(0, config.radius);
        this.glowMaterial.uniforms.glowRadius.value = safeRadius / 10;
        this.glowConfig.radius = safeRadius;
      }
      if (config.intensity !== undefined && Number.isFinite(config.intensity)) {
        const safeIntensity = Math.max(0, config.intensity);
        this.glowMaterial.uniforms.glowIntensity.value = safeIntensity;
        this.glowConfig.intensity = safeIntensity;
      }
    }
  }

  /**
   * Get the glow mesh for adding to scene
   */
  getGlowMesh(): THREE.Mesh | null {
    return this.glowMesh;
  }

  /**
   * Get glow configuration
   */
  getGlowConfig(): GlowConfig | null {
    return this.glowConfig;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                                  // cleanup
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Dispose all texture resources
   */
  dispose(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const particleTexture = this.particleTexture;
    if (particleTexture != null && typeof particleTexture === "object" && typeof particleTexture.dispose === "function") {
      particleTexture.dispose();
    }
    this.particleTexture = null;
    this.spriteSheetConfig = null;

    const glowMaterial = this.glowMaterial;
    if (glowMaterial != null && typeof glowMaterial === "object" && typeof glowMaterial.dispose === "function") {
      glowMaterial.dispose();
    }
    this.glowMaterial = null;
    this.glowMesh = null;
    this.glowConfig = null;
  }
}
