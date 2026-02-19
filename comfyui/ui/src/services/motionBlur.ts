/**
 * Motion Blur Service - Comprehensive Motion Blur System
 *
 * Implements multiple industry-standard motion blur types:
 * - Pixel Motion Blur (velocity-based)
 * - Directional Blur (linear direction)
 * - Radial Blur (circular/zoom)
 * - Vector Motion Blur (vector-based)
 * - Shutter Angle/Samples control
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export type MotionBlurType =
  | "none" // No motion blur
  | "standard" // Standard AE motion blur (shutter-based)
  | "pixel" // Pixel Motion Blur (analyzes frame differences)
  | "directional" // Directional Blur (single direction)
  | "radial" // Radial Blur (zoom/spin from center)
  | "vector" // Vector Motion Blur (uses velocity data)
  | "adaptive"; // Adaptive (auto-selects based on motion)

export type RadialBlurMode = "spin" | "zoom";

export interface MotionBlurSettings {
  enabled: boolean;
  type: MotionBlurType;

  // Standard/Vector blur settings
  shutterAngle: number; // 0-720 degrees (180 = standard film, 360 = full exposure)
  shutterPhase: number; // -180 to 180 degrees (timing offset)
  samplesPerFrame: number; // 2-64 (quality vs performance)

  // Pixel Motion Blur settings
  pixelBlurLength: number; // 0-100% blur intensity
  vectorDetail: number; // 1-100 motion vector precision

  // Directional Blur settings
  direction: number; // 0-360 degrees
  blurLength: number; // Pixels of blur

  // Radial Blur settings
  radialMode: RadialBlurMode; // 'spin' or 'zoom'
  radialAmount: number; // 0-100
  radialCenterX: number; // 0-1 normalized
  radialCenterY: number; // 0-1 normalized

  // Advanced settings
  adaptiveThreshold: number; // Min velocity for blur (px/frame)
  motionBlurQuality: "draft" | "normal" | "high";
  useGPU: boolean;

  // Composition fps for preset enforcement (optional)
  // When set, suggestSettings() will validate against this fps
  targetFps?: number; // Composition fps these settings were tuned for
}

export interface VelocityData {
  x: number;
  y: number;
  rotation: number;
  scale: number;
}

export interface MotionBlurFrame {
  canvas: OffscreenCanvas | HTMLCanvasElement;
  velocity: VelocityData;
  timestamp: number;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // default // settings
// ════════════════════════════════════════════════════════════════════════════

export function createDefaultMotionBlurSettings(): MotionBlurSettings {
  return {
    enabled: false,
    type: "standard",
    shutterAngle: 180,
    shutterPhase: -90,
    samplesPerFrame: 16,
    pixelBlurLength: 50,
    vectorDetail: 50,
    direction: 0,
    blurLength: 10,
    radialMode: "zoom",
    radialAmount: 50,
    radialCenterX: 0.5,
    radialCenterY: 0.5,
    adaptiveThreshold: 2,
    motionBlurQuality: "normal",
    useGPU: true,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                               // motion // blur // processor
// ════════════════════════════════════════════════════════════════════════════

export class MotionBlurProcessor {
  private settings: MotionBlurSettings;
  private frameBuffer: MotionBlurFrame[] = [];
  private maxBufferSize: number = 5;

  // Cached canvases for compositing
  private workCanvas: OffscreenCanvas;
  private workCtx: OffscreenCanvasRenderingContext2D;
  private outputCanvas: OffscreenCanvas;
  private outputCtx: OffscreenCanvasRenderingContext2D;

  constructor(
    width: number,
    height: number,
    settings?: Partial<MotionBlurSettings>,
  ) {
    this.settings = { ...createDefaultMotionBlurSettings(), ...settings };

    this.workCanvas = new OffscreenCanvas(width, height);
    this.workCtx = this.workCanvas.getContext("2d")!;
    this.outputCanvas = new OffscreenCanvas(width, height);
    this.outputCtx = this.outputCanvas.getContext("2d")!;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                  // settings
  // ════════════════════════════════════════════════════════════════════════════

  setSettings(settings: Partial<MotionBlurSettings>): void {
    this.settings = { ...this.settings, ...settings };
  }

  getSettings(): MotionBlurSettings {
    return { ...this.settings };
  }

  resize(width: number, height: number): void {
    this.workCanvas = new OffscreenCanvas(width, height);
    this.workCtx = this.workCanvas.getContext("2d")!;
    this.outputCanvas = new OffscreenCanvas(width, height);
    this.outputCtx = this.outputCanvas.getContext("2d")!;
    this.frameBuffer = [];
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // velocity // calculation
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Calculate velocity from transform changes between frames
   */
  calculateVelocity(
    prevTransform: {
      x: number;
      y: number;
      rotation: number;
      scaleX: number;
      scaleY: number;
    },
    currTransform: {
      x: number;
      y: number;
      rotation: number;
      scaleX: number;
      scaleY: number;
    },
    deltaTime: number = 1,
  ): VelocityData {
    return {
      x: (currTransform.x - prevTransform.x) / deltaTime,
      y: (currTransform.y - prevTransform.y) / deltaTime,
      rotation: (currTransform.rotation - prevTransform.rotation) / deltaTime,
      scale:
        (currTransform.scaleX -
          prevTransform.scaleX +
          (currTransform.scaleY - prevTransform.scaleY)) /
        2 /
        deltaTime,
    };
  }

  /**
   * Get velocity magnitude
   */
  getVelocityMagnitude(velocity: VelocityData): number {
    return Math.sqrt(velocity.x * velocity.x + velocity.y * velocity.y);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // blur // application
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply motion blur to a canvas based on current settings
   */
  applyMotionBlur(
    sourceCanvas: OffscreenCanvas | HTMLCanvasElement,
    velocity: VelocityData,
    frame: number,
  ): OffscreenCanvas {
    if (!this.settings.enabled || this.settings.type === "none") {
      // Return copy of source
      this.outputCtx.clearRect(
        0,
        0,
        this.outputCanvas.width,
        this.outputCanvas.height,
      );
      this.outputCtx.drawImage(sourceCanvas, 0, 0);
      return this.outputCanvas;
    }

    // Store frame in buffer for temporal effects
    this.addFrameToBuffer(sourceCanvas, velocity, frame);

    switch (this.settings.type) {
      case "standard":
        return this.applyStandardBlur(sourceCanvas, velocity);
      case "pixel":
        return this.applyPixelMotionBlur(sourceCanvas);
      case "directional":
        return this.applyDirectionalBlur(sourceCanvas);
      case "radial":
        return this.applyRadialBlur(sourceCanvas);
      case "vector":
        return this.applyVectorBlur(sourceCanvas, velocity);
      case "adaptive":
        return this.applyAdaptiveBlur(sourceCanvas, velocity);
      default:
        this.outputCtx.drawImage(sourceCanvas, 0, 0);
        return this.outputCanvas;
    }
  }

  /**
   * Add frame to circular buffer
   */
  private addFrameToBuffer(
    canvas: OffscreenCanvas | HTMLCanvasElement,
    velocity: VelocityData,
    frame: number,
  ): void {
    // Clone the canvas
    const cloned = new OffscreenCanvas(canvas.width, canvas.height);
    const ctx = cloned.getContext("2d")!;
    ctx.drawImage(canvas, 0, 0);

    this.frameBuffer.push({
      canvas: cloned,
      velocity,
      timestamp: frame,
    });

    // Keep buffer size limited
    while (this.frameBuffer.length > this.maxBufferSize) {
      this.frameBuffer.shift();
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                // standard // motion // blur
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Standard shutter-angle motion blur
   * Simulates camera shutter open during frame exposure
   */
  private applyStandardBlur(
    sourceCanvas: OffscreenCanvas | HTMLCanvasElement,
    velocity: VelocityData,
  ): OffscreenCanvas {
    const { shutterAngle, shutterPhase, samplesPerFrame } = this.settings;

    // Convert shutter angle to exposure time (360 = full frame)
    const exposureRatio = shutterAngle / 360;
    const phaseOffset = shutterPhase / 360;

    // Calculate blur distance based on velocity and shutter
    const blurDistX = velocity.x * exposureRatio;
    const blurDistY = velocity.y * exposureRatio;

    this.outputCtx.clearRect(
      0,
      0,
      this.outputCanvas.width,
      this.outputCanvas.height,
    );

    // Composite multiple samples along motion vector
    const samples = this.getSampleCount();
    const alpha = 1 / samples;

    this.outputCtx.globalAlpha = alpha;

    for (let i = 0; i < samples; i++) {
      const t = i / (samples - 1) - 0.5 + phaseOffset;
      const offsetX = blurDistX * t;
      const offsetY = blurDistY * t;

      this.outputCtx.drawImage(sourceCanvas, offsetX, offsetY);
    }

    this.outputCtx.globalAlpha = 1;
    return this.outputCanvas;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // pixel // motion // blur
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Pixel Motion Blur - analyzes motion between frames
   * Creates blur based on pixel movement vectors
   */
  private applyPixelMotionBlur(
    sourceCanvas: OffscreenCanvas | HTMLCanvasElement,
  ): OffscreenCanvas {
    if (this.frameBuffer.length < 2) {
      this.outputCtx.clearRect(
        0,
        0,
        this.outputCanvas.width,
        this.outputCanvas.height,
      );
      this.outputCtx.drawImage(sourceCanvas, 0, 0);
      return this.outputCanvas;
    }

    const { pixelBlurLength, vectorDetail } = this.settings;
    const blurStrength = pixelBlurLength / 100;

    this.outputCtx.clearRect(
      0,
      0,
      this.outputCanvas.width,
      this.outputCanvas.height,
    );

    // Blend recent frames based on motion
    const frameCount = Math.min(
      this.frameBuffer.length,
      Math.ceil(vectorDetail / 20) + 2,
    );
    const alpha = 1 / frameCount;

    this.outputCtx.globalAlpha = alpha;

    for (
      let i = this.frameBuffer.length - frameCount;
      i < this.frameBuffer.length;
      i++
    ) {
      if (i >= 0) {
        const frame = this.frameBuffer[i];
        const timeOffset = (this.frameBuffer.length - 1 - i) * blurStrength;

        // Apply slight transform based on stored velocity
        this.outputCtx.save();
        this.outputCtx.translate(
          -frame.velocity.x * timeOffset * 0.5,
          -frame.velocity.y * timeOffset * 0.5,
        );
        this.outputCtx.drawImage(frame.canvas, 0, 0);
        this.outputCtx.restore();
      }
    }

    // Draw current frame on top with higher weight
    this.outputCtx.globalAlpha = 0.5;
    this.outputCtx.drawImage(sourceCanvas, 0, 0);

    this.outputCtx.globalAlpha = 1;
    return this.outputCanvas;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // directional // blur
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Directional blur - blur in a specific direction
   * Independent of actual motion
   */
  private applyDirectionalBlur(
    sourceCanvas: OffscreenCanvas | HTMLCanvasElement,
  ): OffscreenCanvas {
    const { direction, blurLength } = this.settings;

    // Convert direction to radians
    const angleRad = (direction * Math.PI) / 180;
    const dx = Math.cos(angleRad) * blurLength;
    const dy = Math.sin(angleRad) * blurLength;

    this.outputCtx.clearRect(
      0,
      0,
      this.outputCanvas.width,
      this.outputCanvas.height,
    );

    const samples = this.getSampleCount();
    const alpha = 1 / samples;

    this.outputCtx.globalAlpha = alpha;

    for (let i = 0; i < samples; i++) {
      const t = i / (samples - 1) - 0.5;
      const offsetX = dx * t;
      const offsetY = dy * t;

      this.outputCtx.drawImage(sourceCanvas, offsetX, offsetY);
    }

    this.outputCtx.globalAlpha = 1;
    return this.outputCanvas;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // radial // blur
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Radial blur - zoom or spin blur from center point
   */
  private applyRadialBlur(
    sourceCanvas: OffscreenCanvas | HTMLCanvasElement,
  ): OffscreenCanvas {
    const { radialMode, radialAmount, radialCenterX, radialCenterY } =
      this.settings;

    const centerX = this.outputCanvas.width * radialCenterX;
    const centerY = this.outputCanvas.height * radialCenterY;

    this.outputCtx.clearRect(
      0,
      0,
      this.outputCanvas.width,
      this.outputCanvas.height,
    );

    const samples = this.getSampleCount();
    const alpha = 1 / samples;
    const amount = radialAmount / 100;

    this.outputCtx.globalAlpha = alpha;

    for (let i = 0; i < samples; i++) {
      const t = i / (samples - 1) - 0.5;

      this.outputCtx.save();
      this.outputCtx.translate(centerX, centerY);

      if (radialMode === "spin") {
        // Spin blur - rotate around center
        const angle = t * amount * 0.2; // Max ~11 degrees per sample
        this.outputCtx.rotate(angle);
      } else {
        // Zoom blur - scale from center
        const scale = 1 + t * amount * 0.1;
        this.outputCtx.scale(scale, scale);
      }

      this.outputCtx.translate(-centerX, -centerY);
      this.outputCtx.drawImage(sourceCanvas, 0, 0);
      this.outputCtx.restore();
    }

    this.outputCtx.globalAlpha = 1;
    return this.outputCanvas;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                  // vector // motion // blur
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Vector-based motion blur using velocity data
   * More accurate than pixel-based for known motion
   */
  private applyVectorBlur(
    sourceCanvas: OffscreenCanvas | HTMLCanvasElement,
    velocity: VelocityData,
  ): OffscreenCanvas {
    const { shutterAngle, vectorDetail } = this.settings;
    const exposureRatio = shutterAngle / 360;

    // Use velocity to determine blur vector
    const blurX = velocity.x * exposureRatio;
    const blurY = velocity.y * exposureRatio;
    const blurRotation = velocity.rotation * exposureRatio * 0.01;
    const blurScale = velocity.scale * exposureRatio * 0.001;

    this.outputCtx.clearRect(
      0,
      0,
      this.outputCanvas.width,
      this.outputCanvas.height,
    );

    const samples = Math.ceil((vectorDetail / 100) * this.getSampleCount());
    const alpha = 1 / samples;

    const centerX = this.outputCanvas.width / 2;
    const centerY = this.outputCanvas.height / 2;

    this.outputCtx.globalAlpha = alpha;

    for (let i = 0; i < samples; i++) {
      const t = i / (samples - 1) - 0.5;

      this.outputCtx.save();
      this.outputCtx.translate(centerX, centerY);

      // Apply all motion components
      this.outputCtx.translate(blurX * t, blurY * t);
      this.outputCtx.rotate(blurRotation * t);
      this.outputCtx.scale(1 + blurScale * t, 1 + blurScale * t);

      this.outputCtx.translate(-centerX, -centerY);
      this.outputCtx.drawImage(sourceCanvas, 0, 0);
      this.outputCtx.restore();
    }

    this.outputCtx.globalAlpha = 1;
    return this.outputCanvas;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                          // adaptive // blur
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Adaptive blur - automatically selects blur type based on motion
   */
  private applyAdaptiveBlur(
    sourceCanvas: OffscreenCanvas | HTMLCanvasElement,
    velocity: VelocityData,
  ): OffscreenCanvas {
    const magnitude = this.getVelocityMagnitude(velocity);

    // Below threshold - no blur
    if (magnitude < this.settings.adaptiveThreshold) {
      this.outputCtx.clearRect(
        0,
        0,
        this.outputCanvas.width,
        this.outputCanvas.height,
      );
      this.outputCtx.drawImage(sourceCanvas, 0, 0);
      return this.outputCanvas;
    }

    // High rotation - use radial spin
    if (Math.abs(velocity.rotation) > magnitude * 0.5) {
      const origMode = this.settings.radialMode;
      this.settings.radialMode = "spin";
      this.settings.radialAmount = Math.min(
        100,
        Math.abs(velocity.rotation) * 2,
      );
      const result = this.applyRadialBlur(sourceCanvas);
      this.settings.radialMode = origMode;
      return result;
    }

    // High scale change - use radial zoom
    if (Math.abs(velocity.scale) > 0.1) {
      const origMode = this.settings.radialMode;
      this.settings.radialMode = "zoom";
      this.settings.radialAmount = Math.min(
        100,
        Math.abs(velocity.scale) * 500,
      );
      const result = this.applyRadialBlur(sourceCanvas);
      this.settings.radialMode = origMode;
      return result;
    }

    // Default - use vector blur
    return this.applyVectorBlur(sourceCanvas, velocity);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // utilities
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get sample count based on quality setting
   */
  private getSampleCount(): number {
    const base = this.settings.samplesPerFrame;
    switch (this.settings.motionBlurQuality) {
      case "draft":
        return Math.max(4, Math.floor(base / 2));
      case "high":
        return Math.min(64, base * 2);
      default:
        return base;
    }
  }

  /**
   * Clear frame buffer (call when seeking or starting new playback)
   */
  clearBuffer(): void {
    this.frameBuffer = [];
  }

  /**
   * Get motion blur intensity suggestion based on frame rate
   */
  static suggestSettings(fps: number): Partial<MotionBlurSettings> {
    // Film standard is 180 degrees at 24fps
    // For higher frame rates, reduce shutter angle
    const baseAngle = 180;
    const fpsRatio = 24 / fps;

    return {
      shutterAngle: Math.min(360, baseAngle * fpsRatio),
      samplesPerFrame: fps >= 60 ? 8 : fps >= 30 ? 12 : 16,
    };
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                 // motion // blur // presets
// ════════════════════════════════════════════════════════════════════════════

export const MOTION_BLUR_PRESETS: Record<
  string,
  Partial<MotionBlurSettings>
> = {
  // Film Standards
  film_24fps: {
    type: "standard",
    shutterAngle: 180,
    shutterPhase: -90,
    samplesPerFrame: 16,
  },
  film_cinematic: {
    type: "standard",
    shutterAngle: 172.8, // 1/48s at 24fps
    shutterPhase: -90,
    samplesPerFrame: 16,
  },
  film_smooth: {
    type: "standard",
    shutterAngle: 270,
    shutterPhase: -90,
    samplesPerFrame: 24,
  },

  // Video Standards
  video_30fps: {
    type: "standard",
    shutterAngle: 180,
    shutterPhase: -90,
    samplesPerFrame: 12,
  },
  video_60fps: {
    type: "standard",
    shutterAngle: 180,
    shutterPhase: -90,
    samplesPerFrame: 8,
  },

  // Stylized
  action_crisp: {
    type: "standard",
    shutterAngle: 90,
    shutterPhase: -45,
    samplesPerFrame: 8,
  },
  dreamy: {
    type: "standard",
    shutterAngle: 360,
    shutterPhase: -180,
    samplesPerFrame: 32,
  },
  staccato: {
    type: "standard",
    shutterAngle: 45,
    shutterPhase: -22.5,
    samplesPerFrame: 4,
  },

  // Directional Effects
  speed_horizontal: {
    type: "directional",
    direction: 0,
    blurLength: 20,
    samplesPerFrame: 16,
  },
  speed_vertical: {
    type: "directional",
    direction: 90,
    blurLength: 20,
    samplesPerFrame: 16,
  },
  diagonal_streak: {
    type: "directional",
    direction: 45,
    blurLength: 30,
    samplesPerFrame: 24,
  },

  // Radial Effects
  zoom_impact: {
    type: "radial",
    radialMode: "zoom",
    radialAmount: 75,
    radialCenterX: 0.5,
    radialCenterY: 0.5,
    samplesPerFrame: 24,
  },
  spin_vortex: {
    type: "radial",
    radialMode: "spin",
    radialAmount: 50,
    radialCenterX: 0.5,
    radialCenterY: 0.5,
    samplesPerFrame: 24,
  },

  // Advanced
  pixel_smooth: {
    type: "pixel",
    pixelBlurLength: 60,
    vectorDetail: 70,
    samplesPerFrame: 16,
  },
  vector_accurate: {
    type: "vector",
    shutterAngle: 180,
    vectorDetail: 90,
    samplesPerFrame: 24,
  },
  adaptive_auto: {
    type: "adaptive",
    shutterAngle: 180,
    adaptiveThreshold: 3,
    samplesPerFrame: 16,
  },
};

/**
 * Get a motion blur preset by name
 */
export function getMotionBlurPreset(name: string): MotionBlurSettings {
  const preset = MOTION_BLUR_PRESETS[name];
  if (preset) {
    return { ...createDefaultMotionBlurSettings(), ...preset, enabled: true };
  }
  return createDefaultMotionBlurSettings();
}

/**
 * List all available presets
 */
export function listMotionBlurPresets(): string[] {
  return Object.keys(MOTION_BLUR_PRESETS);
}
