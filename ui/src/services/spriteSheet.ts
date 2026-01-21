/**
 * Sprite Sheet Service
 *
 * Manages sprite sheet textures for particle systems and 2D animations.
 * Features:
 * - Load sprite sheets from images or URLs
 * - Automatic frame detection (grid-based or JSON metadata)
 * - Frame animation playback
 * - Integration with GPU particle system
 * - Sprite atlas generation
 */

import * as THREE from "three";
import { isFiniteNumber } from "@/utils/typeGuards";

// ============================================================================
// TYPES
// ============================================================================

/** Individual frame in a sprite sheet */
export interface SpriteFrame {
  /** Frame index (0-based) */
  index: number;
  /** Frame name/label (optional) */
  name?: string;
  /** UV coordinates (0-1 range) */
  uv: {
    u: number; // Left
    v: number; // Bottom (Three.js UV origin is bottom-left)
    w: number; // Width
    h: number; // Height
  };
  /** Pixel coordinates in source image */
  source: {
    x: number;
    y: number;
    width: number;
    height: number;
  };
  /** Duration in ms (for variable frame timing) */
  duration?: number;
  /** Anchor point for this frame (0-1, default 0.5, 0.5) */
  anchor?: { x: number; y: number };
}

/** Animation sequence definition */
export interface SpriteAnimation {
  name: string;
  frames: number[]; // Frame indices
  frameRate: number; // FPS
  loop: boolean;
  pingPong: boolean; // Play forward then backward
}

/** Sprite sheet configuration */
export interface SpriteSheetConfig {
  id: string;
  name: string;
  url?: string;
  texture?: THREE.Texture;

  // Grid layout (simple mode)
  columns: number;
  rows: number;

  // Frame info (computed or from metadata)
  frames: SpriteFrame[];
  totalFrames: number;
  frameWidth: number;
  frameHeight: number;

  // Source image dimensions
  imageWidth: number;
  imageHeight: number;

  // Animations
  animations: Map<string, SpriteAnimation>;

  // Timing
  defaultFrameRate: number;
  defaultLoop: boolean;
}

/** JSON metadata format (Aseprite/TexturePacker compatible) */
export interface SpriteSheetMetadata {
  frames: Record<
    string,
    {
      frame: { x: number; y: number; w: number; h: number };
      rotated?: boolean;
      trimmed?: boolean;
      spriteSourceSize?: { x: number; y: number; w: number; h: number };
      sourceSize?: { w: number; h: number };
      duration?: number;
    }
  >;
  meta?: {
    app?: string;
    version?: string;
    image?: string;
    size?: { w: number; h: number };
    scale?: string;
    frameTags?: Array<{
      name: string;
      from: number;
      to: number;
      direction?: "forward" | "reverse" | "pingpong";
    }>;
  };
}

/** Particle texture config for sprite sheets */
export interface ParticleSpriteConfig {
  spriteSheetId: string;
  animationName?: string; // Specific animation to play
  startFrame?: number; // Starting frame (random if not set)
  randomStartFrame: boolean;
  playAnimation: boolean; // Animate through frames
  frameRate?: number; // Override default frame rate
  loop: boolean;
}

// ============================================================================
// SPRITE SHEET SERVICE
// ============================================================================

export class SpriteSheetService {
  private sheets: Map<string, SpriteSheetConfig> = new Map();
  private textureLoader: THREE.TextureLoader;

  constructor() {
    this.textureLoader = new THREE.TextureLoader();
  }

  // ==========================================================================
  // LOADING
  // ==========================================================================

  /**
   * Load a sprite sheet from URL with grid-based layout
   */
  async loadFromGrid(
    url: string,
    columns: number,
    rows: number,
    options: {
      name?: string;
      frameRate?: number;
      loop?: boolean;
    } = {},
  ): Promise<SpriteSheetConfig> {
    const texture = await this.loadTexture(url);
    const id = `spritesheet_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

    const imageWidth = texture.image.width;
    const imageHeight = texture.image.height;
    const frameWidth = imageWidth / columns;
    const frameHeight = imageHeight / rows;
    const totalFrames = columns * rows;

    // Generate frames
    const frames: SpriteFrame[] = [];
    for (let row = 0; row < rows; row++) {
      for (let col = 0; col < columns; col++) {
        const index = row * columns + col;
        const x = col * frameWidth;
        const y = row * frameHeight;

        frames.push({
          index,
          uv: {
            u: x / imageWidth,
            v: 1 - (y + frameHeight) / imageHeight, // Flip Y for Three.js
            w: frameWidth / imageWidth,
            h: frameHeight / imageHeight,
          },
          source: {
            x,
            y,
            width: frameWidth,
            height: frameHeight,
          },
        });
      }
    }

    const config: SpriteSheetConfig = {
      id,
      name: options.name || url,
      url,
      texture,
      columns,
      rows,
      frames,
      totalFrames,
      frameWidth,
      frameHeight,
      imageWidth,
      imageHeight,
      animations: new Map(),
      // Type proof: defaultFrameRate ∈ number | undefined → number
      defaultFrameRate: isFiniteNumber(options.frameRate) && options.frameRate > 0
        ? Math.max(1, Math.min(120, Math.floor(options.frameRate)))
        : 12,
      // Type proof: defaultLoop ∈ boolean | undefined → boolean
      defaultLoop:
        typeof options.loop === "boolean" ? options.loop : true,
    };

    // Create default animation with all frames
    config.animations.set("all", {
      name: "all",
      frames: frames.map((f) => f.index),
      frameRate: config.defaultFrameRate,
      loop: config.defaultLoop,
      pingPong: false,
    });

    this.sheets.set(id, config);
    return config;
  }

  /**
   * Load a sprite sheet from URL with JSON metadata
   */
  async loadFromMetadata(
    imageUrl: string,
    metadataUrl: string,
    options: {
      name?: string;
      frameRate?: number;
    } = {},
  ): Promise<SpriteSheetConfig> {
    // Load image and metadata in parallel
    const [texture, metadataResponse] = await Promise.all([
      this.loadTexture(imageUrl),
      fetch(metadataUrl),
    ]);

    const metadata: SpriteSheetMetadata = await metadataResponse.json();

    const id = `spritesheet_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
    const imageWidth = texture.image.width;
    const imageHeight = texture.image.height;

    // Parse frames
    const frames: SpriteFrame[] = [];
    const frameEntries = Object.entries(metadata.frames);

    frameEntries.forEach(([name, frameData], index) => {
      const f = frameData.frame;
      frames.push({
        index,
        name,
        uv: {
          u: f.x / imageWidth,
          v: 1 - (f.y + f.h) / imageHeight,
          w: f.w / imageWidth,
          h: f.h / imageHeight,
        },
        source: {
          x: f.x,
          y: f.y,
          width: f.w,
          height: f.h,
        },
        duration: frameData.duration,
      });
    });

    // Determine grid size from frames
    const columns = Math.ceil(Math.sqrt(frames.length));
    const rows = Math.ceil(frames.length / columns);

    const config: SpriteSheetConfig = {
      id,
      name: options.name || imageUrl,
      url: imageUrl,
      texture,
      columns,
      rows,
      frames,
      totalFrames: frames.length,
      // Type proof: frameWidth ∈ number | undefined → number
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      frameWidth: (() => {
        if (frames.length > 0) {
          const firstFrame = frames[0];
          const source = (firstFrame != null && typeof firstFrame === "object" && "source" in firstFrame && firstFrame.source != null && typeof firstFrame.source === "object") ? firstFrame.source : undefined;
          const width = (source != null && typeof source === "object" && "width" in source && typeof source.width === "number") ? source.width : undefined;
          return isFiniteNumber(width) ? Math.max(1, Math.floor(width)) : 0;
        }
        return 0;
      })(),
      // Type proof: frameHeight ∈ number | undefined → number
      frameHeight: (() => {
        if (frames.length > 0) {
          const firstFrame = frames[0];
          const source = (firstFrame != null && typeof firstFrame === "object" && "source" in firstFrame && firstFrame.source != null && typeof firstFrame.source === "object") ? firstFrame.source : undefined;
          const height = (source != null && typeof source === "object" && "height" in source && typeof source.height === "number") ? source.height : undefined;
          return isFiniteNumber(height) ? Math.max(1, Math.floor(height)) : 0;
        }
        return 0;
      })(),
      imageWidth,
      imageHeight,
      animations: new Map(),
      // Type proof: defaultFrameRate ∈ number | undefined → number
      defaultFrameRate: isFiniteNumber(options.frameRate) && options.frameRate > 0
        ? Math.max(1, Math.min(120, Math.floor(options.frameRate)))
        : 12,
      defaultLoop: true,
    };

    // Parse animations from frame tags
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const meta = (metadata != null && typeof metadata === "object" && "meta" in metadata && metadata.meta != null && typeof metadata.meta === "object") ? metadata.meta : undefined;
    const frameTags = (meta != null && typeof meta === "object" && "frameTags" in meta && Array.isArray(meta.frameTags)) ? meta.frameTags : undefined;
    if (frameTags != null) {
      for (const tag of frameTags) {
        const animFrames: number[] = [];
        for (let i = tag.from; i <= tag.to; i++) {
          animFrames.push(i);
        }

        config.animations.set(tag.name, {
          name: tag.name,
          frames: animFrames,
          frameRate: config.defaultFrameRate,
          loop: true,
          pingPong: tag.direction === "pingpong",
        });
      }
    }

    // Create default animation with all frames
    config.animations.set("all", {
      name: "all",
      frames: frames.map((f) => f.index),
      frameRate: config.defaultFrameRate,
      loop: config.defaultLoop,
      pingPong: false,
    });

    this.sheets.set(id, config);
    return config;
  }

  /**
   * Load texture from URL
   */
  private loadTexture(url: string): Promise<THREE.Texture> {
    return new Promise((resolve, reject) => {
      this.textureLoader.load(
        url,
        (texture) => {
          // Configure for pixel-perfect rendering
          texture.magFilter = THREE.NearestFilter;
          texture.minFilter = THREE.NearestFilter;
          texture.generateMipmaps = false;
          texture.colorSpace = THREE.SRGBColorSpace;
          resolve(texture);
        },
        undefined,
        reject,
      );
    });
  }

  /**
   * Create a sprite sheet from an existing texture
   */
  createFromTexture(
    texture: THREE.Texture,
    columns: number,
    rows: number,
    options: {
      id?: string;
      name?: string;
      frameRate?: number;
      loop?: boolean;
    } = {},
  ): SpriteSheetConfig {
    const id = options.id || `spritesheet_${Date.now()}`;
    const imageWidth = texture.image.width;
    const imageHeight = texture.image.height;
    const frameWidth = imageWidth / columns;
    const frameHeight = imageHeight / rows;
    const totalFrames = columns * rows;

    const frames: SpriteFrame[] = [];
    for (let row = 0; row < rows; row++) {
      for (let col = 0; col < columns; col++) {
        const index = row * columns + col;
        const x = col * frameWidth;
        const y = row * frameHeight;

        frames.push({
          index,
          uv: {
            u: x / imageWidth,
            v: 1 - (y + frameHeight) / imageHeight,
            w: frameWidth / imageWidth,
            h: frameHeight / imageHeight,
          },
          source: { x, y, width: frameWidth, height: frameHeight },
        });
      }
    }

    const config: SpriteSheetConfig = {
      id,
      name: options.name || id,
      texture,
      columns,
      rows,
      frames,
      totalFrames,
      frameWidth,
      frameHeight,
      imageWidth,
      imageHeight,
      animations: new Map(),
      // Type proof: defaultFrameRate ∈ number | undefined → number
      defaultFrameRate: isFiniteNumber(options.frameRate) && options.frameRate > 0
        ? Math.max(1, Math.min(120, Math.floor(options.frameRate)))
        : 12,
      // Type proof: defaultLoop ∈ boolean | undefined → boolean
      defaultLoop:
        typeof options.loop === "boolean" ? options.loop : true,
    };

    config.animations.set("all", {
      name: "all",
      frames: frames.map((f) => f.index),
      frameRate: config.defaultFrameRate,
      loop: config.defaultLoop,
      pingPong: false,
    });

    this.sheets.set(id, config);
    return config;
  }

  // ==========================================================================
  // ANIMATION MANAGEMENT
  // ==========================================================================

  /**
   * Add a custom animation to a sprite sheet
   */
  addAnimation(sheetId: string, animation: SpriteAnimation): void {
    const sheet = this.sheets.get(sheetId);
    if (!sheet) {
      console.warn(`Sprite sheet not found: ${sheetId}`);
      return;
    }
    sheet.animations.set(animation.name, animation);
  }

  /**
   * Get frame index for a specific time in an animation
   */
  getFrameAtTime(
    sheetId: string,
    animationName: string,
    timeMs: number,
  ): number {
    const sheet = this.sheets.get(sheetId);
    if (!sheet) return 0;

    const animation = sheet.animations.get(animationName);
    if (!animation || animation.frames.length === 0) return 0;

    const frameDuration = 1000 / animation.frameRate;
    const totalDuration = animation.frames.length * frameDuration;

    let t = timeMs;

    if (animation.loop) {
      if (animation.pingPong) {
        // Ping-pong: 0->N->0->N->...
        const fullCycle = totalDuration * 2 - frameDuration * 2;
        t = t % fullCycle;
        if (t > totalDuration - frameDuration) {
          t = fullCycle - t;
        }
      } else {
        t = t % totalDuration;
      }
    } else {
      t = Math.min(t, totalDuration - frameDuration);
    }

    const frameIndex = Math.floor(t / frameDuration);
    return animation.frames[Math.min(frameIndex, animation.frames.length - 1)];
  }

  /**
   * Get UV coordinates for a specific frame
   */
  /**
   * Get UV coordinates for a specific frame in a sprite sheet
   * 
   * System F/Omega proof: Frame UV coordinate retrieval
   * Type proof: sheetId ∈ string, frameIndex ∈ ℕ → SpriteFrame["uv"]
   * Mathematical proof: Frame index must be within valid range [0, frames.length)
   * Geometric proof: UV coordinates are well-defined for valid frame indices
   * 
   * @param sheetId - Sprite sheet ID (must exist)
   * @param frameIndex - Frame index (0-based, must be within sheet frame count)
   * @returns UV coordinates for the frame
   * @throws Error if sheet not found or frame index is invalid
   */
  getFrameUV(sheetId: string, frameIndex: number): SpriteFrame["uv"] {
    // System F/Omega proof: Explicit validation of sheet existence
    // Type proof: sheetId ∈ string → sheet ∈ SpriteSheet | undefined
    // Mathematical proof: Sheet must exist to retrieve frame UV
    const sheet = this.sheets.get(sheetId);
    
    if (!sheet) {
      throw new Error(`[SpriteSheet] Cannot get frame UV: Sprite sheet "${sheetId}" not found. Sheet must be registered before retrieving frame UV coordinates. Available sheets: ${Array.from(this.sheets.keys()).join(", ") || "none"}.`);
    }
    
    // System F/Omega proof: Explicit validation of frame index
    // Type proof: frameIndex ∈ ℕ → must be finite non-negative integer
    // Mathematical proof: Frame index must be within valid range [0, frames.length)
    if (!Number.isFinite(frameIndex) || !Number.isInteger(frameIndex) || frameIndex < 0) {
      throw new Error(`[SpriteSheet] Cannot get frame UV: Invalid frame index (frameIndex: ${frameIndex}). Frame index must be a finite non-negative integer. Sheet ID: ${sheetId}, sheet frame count: ${sheet.frames.length}.`);
    }
    
    if (frameIndex >= sheet.frames.length) {
      throw new Error(`[SpriteSheet] Cannot get frame UV: Frame index out of range (frameIndex: ${frameIndex}, sheet frame count: ${sheet.frames.length}). Frame index must be in range [0, ${sheet.frames.length}). Sheet ID: ${sheetId}.`);
    }
    
    return sheet.frames[frameIndex].uv;
  }

  // ==========================================================================
  // PARTICLE SYSTEM INTEGRATION
  // ==========================================================================

  /**
   * Get texture config for GPU particle system
   */
  /**
   * Get texture configuration for GPU particle system
   * 
   * System F/Omega proof: Sprite sheet texture configuration retrieval
   * Type proof: sheetId ∈ string → texture config object (non-nullable)
   * Mathematical proof: Texture config is well-defined for valid sprite sheets with URLs
   * 
   * @param sheetId - Sprite sheet ID (must exist and have URL)
   * @param animationName - Optional animation name (defaults to "all")
   * @returns Texture configuration object
   * @throws Error if sheet not found or URL is missing
   */
  getParticleTextureConfig(
    sheetId: string,
    animationName?: string,
  ): {
    diffuseMap: string;
    spriteSheetColumns: number;
    spriteSheetRows: number;
    animateSprite: boolean;
    spriteFrameRate: number;
    randomStartFrame: boolean;
  } {
    // System F/Omega proof: Explicit validation of sheet existence
    // Type proof: sheetId ∈ string → sheet ∈ SpriteSheet | undefined
    // Mathematical proof: Sheet must exist to retrieve texture config
    const sheet = this.sheets.get(sheetId);
    
    if (!sheet) {
      throw new Error(`[SpriteSheet] Cannot get particle texture config: Sprite sheet "${sheetId}" not found. Sheet must be registered before retrieving texture configuration. Available sheets: ${Array.from(this.sheets.keys()).join(", ") || "none"}.`);
    }
    
    // System F/Omega proof: Explicit validation of sheet URL
    // Type proof: sheet.url ∈ string | undefined → must be non-empty string
    // Mathematical proof: Texture config requires valid URL for texture loading
    if (!sheet.url || typeof sheet.url !== "string" || sheet.url.length === 0) {
      throw new Error(`[SpriteSheet] Cannot get particle texture config: Sprite sheet "${sheetId}" has no URL. Sheet must have a valid URL to create texture configuration. Sheet columns: ${sheet.columns}, rows: ${sheet.rows}, frames: ${sheet.frames.length}.`);
    }

    const animation = animationName
      ? sheet.animations.get(animationName)
      : sheet.animations.get("all");

    // Type proof: spriteFrameRate ∈ number | undefined → number
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const animationFrameRate = (animation != null && typeof animation === "object" && "frameRate" in animation && typeof animation.frameRate === "number") ? animation.frameRate : undefined;
    const spriteFrameRate = isFiniteNumber(animationFrameRate) &&
      animationFrameRate > 0
      ? Math.max(1, Math.min(120, Math.floor(animationFrameRate)))
      : sheet.defaultFrameRate;

    return {
      diffuseMap: sheet.url,
      spriteSheetColumns: sheet.columns,
      spriteSheetRows: sheet.rows,
      animateSprite: true,
      spriteFrameRate,
      randomStartFrame: true,
    };
  }

  /**
   * Create a Three.js SpriteMaterial for a specific frame
   */
  /**
   * Create a Three.js SpriteMaterial for a specific frame
   * 
   * System F/Omega proof: Sprite material creation from sprite sheet frame
   * Type proof: sheetId ∈ string, frameIndex ∈ ℕ → THREE.SpriteMaterial
   * Mathematical proof: Material creation requires valid sheet, texture, and frame
   * Geometric proof: UV coordinates must be valid for texture mapping
   * 
   * @param sheetId - Sprite sheet ID (must exist and have loaded texture)
   * @param frameIndex - Frame index (0-based, must be within sheet frame count)
   * @returns THREE.SpriteMaterial configured for the frame
   * @throws Error if sheet/texture/frame not found or invalid
   */
  createSpriteMaterial(
    sheetId: string,
    frameIndex: number,
  ): THREE.SpriteMaterial {
    // System F/Omega proof: Explicit validation of sheet existence
    // Type proof: sheetId ∈ string → sheet ∈ SpriteSheet | undefined
    // Mathematical proof: Sheet must exist to create material
    const sheet = this.sheets.get(sheetId);
    
    if (!sheet) {
      throw new Error(`[SpriteSheet] Cannot create sprite material: Sprite sheet "${sheetId}" not found. Sheet must be registered and texture loaded before creating materials. Available sheets: ${Array.from(this.sheets.keys()).join(", ") || "none"}.`);
    }
    
    // System F/Omega proof: Explicit validation of texture
    // Type proof: sheet.texture ∈ THREE.Texture | undefined → must be valid texture
    // Mathematical proof: Material creation requires loaded texture
    if (!sheet.texture || typeof sheet.texture !== "object") {
      throw new Error(`[SpriteSheet] Cannot create sprite material: Sprite sheet "${sheetId}" has no loaded texture. Texture must be loaded before creating materials. Sheet URL: ${sheet.url || "none"}, columns: ${sheet.columns}, rows: ${sheet.rows}.`);
    }
    
    // System F/Omega proof: Explicit validation of frame index
    // Type proof: frameIndex ∈ ℕ → must be finite non-negative integer
    // Mathematical proof: Frame index must be within valid range [0, frames.length)
    if (!Number.isFinite(frameIndex) || !Number.isInteger(frameIndex) || frameIndex < 0) {
      throw new Error(`[SpriteSheet] Cannot create sprite material: Invalid frame index (frameIndex: ${frameIndex}). Frame index must be a finite non-negative integer. Sheet ID: ${sheetId}, sheet frame count: ${sheet.frames.length}.`);
    }
    
    const frame = sheet.frames[frameIndex];
    
    if (!frame || typeof frame !== "object") {
      throw new Error(`[SpriteSheet] Cannot create sprite material: Frame not found (frameIndex: ${frameIndex}, sheet frame count: ${sheet.frames.length}). Frame index must be in range [0, ${sheet.frames.length}). Sheet ID: ${sheetId}.`);
    }

    // Clone texture and set UV offset/repeat for this frame
    const texture = sheet.texture.clone();
    texture.offset.set(frame.uv.u, frame.uv.v);
    texture.repeat.set(frame.uv.w, frame.uv.h);
    texture.needsUpdate = true;

    return new THREE.SpriteMaterial({
      map: texture,
      transparent: true,
    });
  }

  /**
   * Update a SpriteMaterial to show a specific frame
   */
  updateSpriteMaterialFrame(
    material: THREE.SpriteMaterial,
    sheetId: string,
    frameIndex: number,
  ): void {
    const sheet = this.sheets.get(sheetId);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const sheetTexture = (sheet != null && typeof sheet === "object" && "texture" in sheet && sheet.texture != null) ? sheet.texture : undefined;
    if (!sheetTexture || !material.map) return;

    const frame = sheet.frames[frameIndex];
    if (!frame) return;

    material.map.offset.set(frame.uv.u, frame.uv.v);
    material.map.repeat.set(frame.uv.w, frame.uv.h);
    material.map.needsUpdate = true;
  }

  // ==========================================================================
  // ACCESSORS
  // ==========================================================================

  /**
   * Get a sprite sheet by ID
   */
  getSheet(id: string): SpriteSheetConfig | undefined {
    return this.sheets.get(id);
  }

  /**
   * Get all sprite sheets
   */
  getAllSheets(): SpriteSheetConfig[] {
    return Array.from(this.sheets.values());
  }

  /**
   * Check if a sprite sheet exists
   */
  hasSheet(id: string): boolean {
    return this.sheets.has(id);
  }

  /**
   * Get texture for a sprite sheet
   */
  getTexture(sheetId: string): THREE.Texture | undefined {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const sheet = this.sheets.get(sheetId);
    return (sheet != null && typeof sheet === "object" && "texture" in sheet && sheet.texture != null) ? sheet.texture : undefined;
  }

  // ==========================================================================
  // CLEANUP
  // ==========================================================================

  /**
   * Remove a sprite sheet
   */
  removeSheet(id: string): void {
    const sheet = this.sheets.get(id);
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const sheetTexture = (sheet != null && typeof sheet === "object" && "texture" in sheet && sheet.texture != null) ? sheet.texture : undefined;
    if (sheetTexture != null) {
      sheetTexture.dispose();
    }
    this.sheets.delete(id);
  }

  /**
   * Dispose all resources
   */
  dispose(): void {
    for (const sheet of this.sheets.values()) {
      if (sheet.texture) {
        sheet.texture.dispose();
      }
    }
    this.sheets.clear();
  }
}

// Export singleton instance
export const spriteSheetService = new SpriteSheetService();

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Create default particle sprite config
 */
export function createDefaultParticleSpriteConfig(): ParticleSpriteConfig {
  return {
    spriteSheetId: "",
    randomStartFrame: true,
    playAnimation: true,
    loop: true,
  };
}
