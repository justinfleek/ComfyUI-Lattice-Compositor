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

import * as THREE from 'three';

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
    u: number;   // Left
    v: number;   // Bottom (Three.js UV origin is bottom-left)
    w: number;   // Width
    h: number;   // Height
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
  frames: number[];           // Frame indices
  frameRate: number;          // FPS
  loop: boolean;
  pingPong: boolean;          // Play forward then backward
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
  frames: Record<string, {
    frame: { x: number; y: number; w: number; h: number };
    rotated?: boolean;
    trimmed?: boolean;
    spriteSourceSize?: { x: number; y: number; w: number; h: number };
    sourceSize?: { w: number; h: number };
    duration?: number;
  }>;
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
      direction?: 'forward' | 'reverse' | 'pingpong';
    }>;
  };
}

/** Particle texture config for sprite sheets */
export interface ParticleSpriteConfig {
  spriteSheetId: string;
  animationName?: string;       // Specific animation to play
  startFrame?: number;          // Starting frame (random if not set)
  randomStartFrame: boolean;
  playAnimation: boolean;       // Animate through frames
  frameRate?: number;           // Override default frame rate
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
    } = {}
  ): Promise<SpriteSheetConfig> {
    const texture = await this.loadTexture(url);
    const id = `spritesheet_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

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
      defaultFrameRate: options.frameRate ?? 12,
      defaultLoop: options.loop ?? true,
    };

    // Create default animation with all frames
    config.animations.set('all', {
      name: 'all',
      frames: frames.map(f => f.index),
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
    } = {}
  ): Promise<SpriteSheetConfig> {
    // Load image and metadata in parallel
    const [texture, metadataResponse] = await Promise.all([
      this.loadTexture(imageUrl),
      fetch(metadataUrl),
    ]);

    const metadata: SpriteSheetMetadata = await metadataResponse.json();

    const id = `spritesheet_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
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
      frameWidth: frames[0]?.source.width ?? 0,
      frameHeight: frames[0]?.source.height ?? 0,
      imageWidth,
      imageHeight,
      animations: new Map(),
      defaultFrameRate: options.frameRate ?? 12,
      defaultLoop: true,
    };

    // Parse animations from frame tags
    if (metadata.meta?.frameTags) {
      for (const tag of metadata.meta.frameTags) {
        const animFrames: number[] = [];
        for (let i = tag.from; i <= tag.to; i++) {
          animFrames.push(i);
        }

        config.animations.set(tag.name, {
          name: tag.name,
          frames: animFrames,
          frameRate: config.defaultFrameRate,
          loop: true,
          pingPong: tag.direction === 'pingpong',
        });
      }
    }

    // Create default animation with all frames
    config.animations.set('all', {
      name: 'all',
      frames: frames.map(f => f.index),
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
        reject
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
    } = {}
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
      defaultFrameRate: options.frameRate ?? 12,
      defaultLoop: options.loop ?? true,
    };

    config.animations.set('all', {
      name: 'all',
      frames: frames.map(f => f.index),
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
  addAnimation(
    sheetId: string,
    animation: SpriteAnimation
  ): void {
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
    timeMs: number
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
  getFrameUV(sheetId: string, frameIndex: number): SpriteFrame['uv'] | null {
    const sheet = this.sheets.get(sheetId);
    if (!sheet || frameIndex < 0 || frameIndex >= sheet.frames.length) {
      return null;
    }
    return sheet.frames[frameIndex].uv;
  }

  // ==========================================================================
  // PARTICLE SYSTEM INTEGRATION
  // ==========================================================================

  /**
   * Get texture config for GPU particle system
   */
  getParticleTextureConfig(
    sheetId: string,
    animationName?: string
  ): {
    diffuseMap: string;
    spriteSheetColumns: number;
    spriteSheetRows: number;
    animateSprite: boolean;
    spriteFrameRate: number;
    randomStartFrame: boolean;
  } | null {
    const sheet = this.sheets.get(sheetId);
    if (!sheet || !sheet.url) return null;

    const animation = animationName
      ? sheet.animations.get(animationName)
      : sheet.animations.get('all');

    return {
      diffuseMap: sheet.url,
      spriteSheetColumns: sheet.columns,
      spriteSheetRows: sheet.rows,
      animateSprite: true,
      spriteFrameRate: animation?.frameRate ?? sheet.defaultFrameRate,
      randomStartFrame: true,
    };
  }

  /**
   * Create a Three.js SpriteMaterial for a specific frame
   */
  createSpriteMaterial(
    sheetId: string,
    frameIndex: number
  ): THREE.SpriteMaterial | null {
    const sheet = this.sheets.get(sheetId);
    if (!sheet?.texture) return null;

    const frame = sheet.frames[frameIndex];
    if (!frame) return null;

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
    frameIndex: number
  ): void {
    const sheet = this.sheets.get(sheetId);
    if (!sheet?.texture || !material.map) return;

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
    return this.sheets.get(sheetId)?.texture;
  }

  // ==========================================================================
  // CLEANUP
  // ==========================================================================

  /**
   * Remove a sprite sheet
   */
  removeSheet(id: string): void {
    const sheet = this.sheets.get(id);
    if (sheet?.texture) {
      sheet.texture.dispose();
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
    spriteSheetId: '',
    randomStartFrame: true,
    playAnimation: true,
    loop: true,
  };
}
