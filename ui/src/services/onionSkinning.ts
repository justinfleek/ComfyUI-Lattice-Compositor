/**
 * Onion Skinning Service
 *
 * Provides animation preview by showing semi-transparent overlays of
 * previous and next frames. Essential for hand-drawn animation workflows.
 *
 * Features:
 * - Configurable frames before/after current frame
 * - Opacity falloff (linear or exponential)
 * - Color tinting for past (red) vs future (green) frames
 * - Frame spacing for keyframe-only preview
 *
 * Reference: ComfyUI-TRELLIS2_Motion onion skinning patterns
 */

import { createLogger } from "@/utils/logger";

const logger = createLogger("OnionSkinning");

// ============================================================================
// TYPES
// ============================================================================

export type OpacityFalloff = "linear" | "exponential" | "constant";

export interface OnionSkinConfig {
  /** Enable onion skinning */
  enabled: boolean;
  /** Number of frames to show before current frame */
  framesBefore: number;
  /** Number of frames to show after current frame */
  framesAfter: number;
  /** How opacity decreases with distance from current frame */
  opacityFalloff: OpacityFalloff;
  /** Maximum opacity for closest onion skin frame (0-1) */
  maxOpacity: number;
  /** Minimum opacity before frame is not rendered (0-1) */
  minOpacity: number;
  /** Tint color for past frames (CSS color) */
  beforeColor: string;
  /** Tint color for future frames (CSS color) */
  afterColor: string;
  /** Tint intensity (0 = no tint, 1 = full tint) */
  tintIntensity: number;
  /** Frame spacing (1 = every frame, 2 = every other frame, etc.) */
  spacing: number;
  /** Only show keyframe positions (ignores spacing if true) */
  keyframesOnly: boolean;
  /** Blend mode for compositing */
  blendMode: "normal" | "multiply" | "screen" | "overlay";
}

export interface OnionSkinFrame {
  /** Frame number */
  frame: number;
  /** Opacity to render at */
  opacity: number;
  /** Tint color (CSS format) */
  tintColor: string;
  /** Tint intensity (0-1) */
  tintIntensity: number;
  /** Whether this is a past or future frame */
  direction: "before" | "after";
  /** Distance from current frame */
  distance: number;
}

export interface OnionSkinRenderData {
  /** Current frame (not included in frames array) */
  currentFrame: number;
  /** Frames to render as onion skins */
  frames: OnionSkinFrame[];
  /** Global config */
  config: OnionSkinConfig;
}

// ============================================================================
// DEFAULT CONFIG
// ============================================================================

export const DEFAULT_ONION_SKIN_CONFIG: OnionSkinConfig = {
  enabled: false,
  framesBefore: 3,
  framesAfter: 2,
  opacityFalloff: "exponential",
  maxOpacity: 0.5,
  minOpacity: 0.1,
  beforeColor: "#ff4444", // Red for past
  afterColor: "#44ff44", // Green for future
  tintIntensity: 0.3,
  spacing: 1,
  keyframesOnly: false,
  blendMode: "normal",
};

// ============================================================================
// PRESETS
// ============================================================================

export const ONION_SKIN_PRESETS: Record<string, Partial<OnionSkinConfig>> = {
  /** Traditional animation - focus on past frames */
  traditional: {
    framesBefore: 5,
    framesAfter: 1,
    opacityFalloff: "exponential",
    maxOpacity: 0.6,
    tintIntensity: 0.4,
  },
  /** Keyframe preview - only show keyframes */
  keyframes: {
    framesBefore: 5,
    framesAfter: 5,
    keyframesOnly: true,
    opacityFalloff: "constant",
    maxOpacity: 0.4,
    tintIntensity: 0.5,
  },
  /** Light preview - subtle overlay */
  light: {
    framesBefore: 2,
    framesAfter: 1,
    opacityFalloff: "linear",
    maxOpacity: 0.3,
    tintIntensity: 0.2,
  },
  /** Heavy preview - strong overlay for detailed work */
  heavy: {
    framesBefore: 4,
    framesAfter: 3,
    opacityFalloff: "linear",
    maxOpacity: 0.7,
    tintIntensity: 0.5,
  },
  /** Motion arc - visualize motion paths */
  motionArc: {
    framesBefore: 8,
    framesAfter: 4,
    spacing: 2,
    opacityFalloff: "exponential",
    maxOpacity: 0.4,
    tintIntensity: 0.6,
  },
  /** Cycle preview - for looping animations */
  cycle: {
    framesBefore: 3,
    framesAfter: 3,
    opacityFalloff: "constant",
    maxOpacity: 0.35,
    tintIntensity: 0.3,
  },
};

// ============================================================================
// OPACITY CALCULATION
// ============================================================================

/**
 * Calculate opacity for an onion skin frame based on distance
 */
export function calculateOpacity(
  distance: number,
  maxFrames: number,
  falloff: OpacityFalloff,
  maxOpacity: number,
  minOpacity: number,
): number {
  if (distance <= 0) return maxOpacity;
  if (distance > maxFrames) return 0;

  const normalizedDistance = distance / maxFrames;

  let opacity: number;

  switch (falloff) {
    case "linear":
      // Linear falloff: opacity decreases linearly with distance
      opacity = maxOpacity * (1 - normalizedDistance);
      break;

    case "exponential":
      // Exponential falloff: opacity decreases faster at greater distances
      // Using e^(-2*x) for a nice curve
      opacity = maxOpacity * Math.exp(-2 * normalizedDistance);
      break;

    case "constant":
      // Constant opacity for all frames
      opacity = maxOpacity;
      break;

    default:
      opacity = maxOpacity * (1 - normalizedDistance);
  }

  // Clamp to min opacity
  return Math.max(opacity, minOpacity);
}

/**
 * Parse CSS color to RGB components
 */
export function parseColor(color: string): { r: number; g: number; b: number } {
  // Handle hex colors
  if (color.startsWith("#")) {
    const hex = color.slice(1);
    if (hex.length === 3) {
      return {
        r: parseInt(hex[0] + hex[0], 16) / 255,
        g: parseInt(hex[1] + hex[1], 16) / 255,
        b: parseInt(hex[2] + hex[2], 16) / 255,
      };
    } else if (hex.length === 6) {
      return {
        r: parseInt(hex.slice(0, 2), 16) / 255,
        g: parseInt(hex.slice(2, 4), 16) / 255,
        b: parseInt(hex.slice(4, 6), 16) / 255,
      };
    }
  }

  // Handle rgb/rgba colors
  const rgbMatch = color.match(/rgba?\((\d+),\s*(\d+),\s*(\d+)/);
  if (rgbMatch) {
    return {
      r: parseInt(rgbMatch[1], 10) / 255,
      g: parseInt(rgbMatch[2], 10) / 255,
      b: parseInt(rgbMatch[3], 10) / 255,
    };
  }

  // Default to white
  return { r: 1, g: 1, b: 1 };
}

// ============================================================================
// FRAME CALCULATION
// ============================================================================

/**
 * Calculate which frames to render as onion skins
 */
export function calculateOnionSkinFrames(
  currentFrame: number,
  totalFrames: number,
  config: OnionSkinConfig,
  keyframeFrames?: number[],
): OnionSkinFrame[] {
  if (!config.enabled) return [];

  const frames: OnionSkinFrame[] = [];

  // Calculate before frames
  if (config.keyframesOnly && keyframeFrames) {
    // Only show keyframes before current
    const keyframesBefore = keyframeFrames
      .filter((f) => f < currentFrame)
      .sort((a, b) => b - a) // Sort descending (closest first)
      .slice(0, config.framesBefore);

    for (let i = 0; i < keyframesBefore.length; i++) {
      const frame = keyframesBefore[i];
      const distance = i + 1;
      const opacity = calculateOpacity(
        distance,
        config.framesBefore,
        config.opacityFalloff,
        config.maxOpacity,
        config.minOpacity,
      );

      if (opacity >= config.minOpacity) {
        frames.push({
          frame,
          opacity,
          tintColor: config.beforeColor,
          tintIntensity: config.tintIntensity,
          direction: "before",
          distance,
        });
      }
    }
  } else {
    // Regular frame spacing
    for (let i = 1; i <= config.framesBefore; i++) {
      const frameOffset = i * config.spacing;
      const frame = currentFrame - frameOffset;

      if (frame < 0) continue;

      const opacity = calculateOpacity(
        i,
        config.framesBefore,
        config.opacityFalloff,
        config.maxOpacity,
        config.minOpacity,
      );

      if (opacity >= config.minOpacity) {
        frames.push({
          frame,
          opacity,
          tintColor: config.beforeColor,
          tintIntensity: config.tintIntensity,
          direction: "before",
          distance: i,
        });
      }
    }
  }

  // Calculate after frames
  if (config.keyframesOnly && keyframeFrames) {
    // Only show keyframes after current
    const keyframesAfter = keyframeFrames
      .filter((f) => f > currentFrame)
      .sort((a, b) => a - b) // Sort ascending (closest first)
      .slice(0, config.framesAfter);

    for (let i = 0; i < keyframesAfter.length; i++) {
      const frame = keyframesAfter[i];
      const distance = i + 1;
      const opacity = calculateOpacity(
        distance,
        config.framesAfter,
        config.opacityFalloff,
        config.maxOpacity,
        config.minOpacity,
      );

      if (opacity >= config.minOpacity) {
        frames.push({
          frame,
          opacity,
          tintColor: config.afterColor,
          tintIntensity: config.tintIntensity,
          direction: "after",
          distance,
        });
      }
    }
  } else {
    // Regular frame spacing
    for (let i = 1; i <= config.framesAfter; i++) {
      const frameOffset = i * config.spacing;
      const frame = currentFrame + frameOffset;

      if (frame >= totalFrames) continue;

      const opacity = calculateOpacity(
        i,
        config.framesAfter,
        config.opacityFalloff,
        config.maxOpacity,
        config.minOpacity,
      );

      if (opacity >= config.minOpacity) {
        frames.push({
          frame,
          opacity,
          tintColor: config.afterColor,
          tintIntensity: config.tintIntensity,
          direction: "after",
          distance: i,
        });
      }
    }
  }

  // Sort by distance (furthest first so closest renders on top)
  frames.sort((a, b) => b.distance - a.distance);

  return frames;
}

// ============================================================================
// SERVICE CLASS
// ============================================================================

export class OnionSkinningService {
  private config: OnionSkinConfig = { ...DEFAULT_ONION_SKIN_CONFIG };
  private keyframeCache: Map<string, number[]> = new Map();

  /**
   * Get current configuration
   */
  getConfig(): OnionSkinConfig {
    return { ...this.config };
  }

  /**
   * Update configuration
   */
  setConfig(config: Partial<OnionSkinConfig>): void {
    this.config = { ...this.config, ...config };
    logger.debug("Onion skin config updated:", this.config);
  }

  /**
   * Apply a preset
   */
  applyPreset(presetName: string): void {
    const preset = ONION_SKIN_PRESETS[presetName];
    if (preset) {
      this.setConfig(preset);
      logger.info(`Applied onion skin preset: ${presetName}`);
    } else {
      logger.warn(`Unknown onion skin preset: ${presetName}`);
    }
  }

  /**
   * Enable/disable onion skinning
   */
  setEnabled(enabled: boolean): void {
    this.setConfig({ enabled });
  }

  /**
   * Check if enabled
   */
  isEnabled(): boolean {
    return this.config.enabled;
  }

  /**
   * Set frames before current
   */
  setFramesBefore(count: number): void {
    this.setConfig({ framesBefore: Math.max(0, Math.floor(count)) });
  }

  /**
   * Set frames after current
   */
  setFramesAfter(count: number): void {
    this.setConfig({ framesAfter: Math.max(0, Math.floor(count)) });
  }

  /**
   * Set opacity falloff mode
   */
  setOpacityFalloff(falloff: OpacityFalloff): void {
    this.setConfig({ opacityFalloff: falloff });
  }

  /**
   * Set tint colors
   */
  setTintColors(beforeColor: string, afterColor: string): void {
    this.setConfig({ beforeColor, afterColor });
  }

  /**
   * Cache keyframes for a layer
   */
  cacheKeyframes(layerId: string, keyframeFrames: number[]): void {
    this.keyframeCache.set(
      layerId,
      [...keyframeFrames].sort((a, b) => a - b),
    );
  }

  /**
   * Clear keyframe cache
   */
  clearKeyframeCache(): void {
    this.keyframeCache.clear();
  }

  /**
   * Get all unique keyframe frames across all cached layers
   */
  getAllKeyframeFrames(): number[] {
    const allFrames = new Set<number>();
    for (const frames of this.keyframeCache.values()) {
      frames.forEach((f) => allFrames.add(f));
    }
    return [...allFrames].sort((a, b) => a - b);
  }

  /**
   * Calculate render data for current frame
   */
  getRenderData(
    currentFrame: number,
    totalFrames: number,
  ): OnionSkinRenderData {
    const keyframeFrames = this.config.keyframesOnly
      ? this.getAllKeyframeFrames()
      : undefined;

    const frames = calculateOnionSkinFrames(
      currentFrame,
      totalFrames,
      this.config,
      keyframeFrames,
    );

    return {
      currentFrame,
      frames,
      config: { ...this.config },
    };
  }

  /**
   * Reset to default configuration
   */
  reset(): void {
    this.config = { ...DEFAULT_ONION_SKIN_CONFIG };
    this.keyframeCache.clear();
    logger.debug("Onion skin service reset");
  }
}

// ============================================================================
// CANVAS COMPOSITING (2D fallback)
// ============================================================================

/**
 * Composite an onion skin frame onto a canvas
 * Used for 2D canvas fallback when WebGL compositing isn't available
 */
export function compositeOnionSkinFrame(
  ctx: CanvasRenderingContext2D,
  frameImage: ImageData | HTMLCanvasElement | HTMLImageElement,
  frame: OnionSkinFrame,
  blendMode: OnionSkinConfig["blendMode"] = "normal",
): void {
  ctx.save();

  // Set blend mode
  switch (blendMode) {
    case "multiply":
      ctx.globalCompositeOperation = "multiply";
      break;
    case "screen":
      ctx.globalCompositeOperation = "screen";
      break;
    case "overlay":
      ctx.globalCompositeOperation = "overlay";
      break;
    default:
      ctx.globalCompositeOperation = "source-over";
  }

  // Set opacity
  ctx.globalAlpha = frame.opacity;

  // Draw frame
  if (frameImage instanceof ImageData) {
    ctx.putImageData(frameImage, 0, 0);
  } else {
    ctx.drawImage(frameImage, 0, 0);
  }

  // Apply tint if intensity > 0
  if (frame.tintIntensity > 0) {
    const rgb = parseColor(frame.tintColor);
    ctx.globalCompositeOperation = "multiply";
    ctx.globalAlpha = frame.tintIntensity * frame.opacity;
    ctx.fillStyle = `rgb(${Math.floor(rgb.r * 255)}, ${Math.floor(rgb.g * 255)}, ${Math.floor(rgb.b * 255)})`;
    ctx.fillRect(0, 0, ctx.canvas.width, ctx.canvas.height);
  }

  ctx.restore();
}

// ============================================================================
// SINGLETON EXPORT
// ============================================================================

export const onionSkinning = new OnionSkinningService();
export default onionSkinning;
