/**
 * Conditioning Renderer
 *
 * Generates conditioning images for AI diffusion models (Wan 2.1, etc.)
 * Optimized for DATA VOLUME over visual quality - renders millions of
 * particles as simple 2D projections.
 *
 * Output formats:
 * - Depth maps (grayscale, Z → brightness)
 * - Trajectory maps (colored spline strokes)
 * - Segmentation masks (category → color)
 * - Velocity/flow maps (optical flow style)
 * - Shape silhouettes (binary masks)
 *
 * Performance targets:
 * - 100k particles: real-time (60fps)
 * - 1M particles: ~2s per frame
 * - 10M particles: ~20s per frame (worker thread)
 */

// ============================================================================
// TYPES
// ============================================================================

export interface Vec3 {
  x: number;
  y: number;
  z: number;
}

export interface ParticleData {
  position: Vec3;
  velocity?: Vec3;
  color?: { r: number; g: number; b: number; a?: number };
  size?: number;
  age?: number;
  lifetime?: number;
  category?: string | number;
  dataValue?: number;
}

export interface TrajectoryData {
  points: Vec3[];
  color?: { r: number; g: number; b: number };
  width?: number;
  category?: string | number;
}

export interface ConditioningConfig {
  width: number;
  height: number;
  // Camera/projection
  cameraPosition?: Vec3;
  cameraTarget?: Vec3;
  fov?: number;
  near?: number;
  far?: number;
  // Depth settings
  depthNear?: number;
  depthFar?: number;
  depthInvert?: boolean;
  // Visual settings
  particleSize?: number;
  backgroundColor?: string;
  // Category color map
  categoryColors?: Record<string | number, string>;
}

export interface ConditioningResult {
  imageData: ImageData;
  canvas: OffscreenCanvas | HTMLCanvasElement;
  particleCount: number;
  renderTime: number;
}

// ============================================================================
// DEFAULT CATEGORY COLORS (Anadol-style palettes)
// ============================================================================

export const ANADOL_PALETTE = {
  // Data stream colors
  primary: "#00D4FF", // Cyan - main data flow
  secondary: "#FF006E", // Magenta - secondary streams
  tertiary: "#FFD000", // Gold - highlights
  quaternary: "#00FF88", // Green - nature/organic

  // Depth gradient
  near: "#FFFFFF",
  mid: "#888888",
  far: "#000000",

  // Category presets
  social: "#1DA1F2", // Twitter blue
  financial: "#00C853", // Money green
  weather: "#FF9800", // Weather orange
  health: "#E91E63", // Health pink
  tech: "#9C27B0", // Tech purple
};

export const DEPTH_COLORMAPS = {
  grayscale: (t: number) => {
    const v = Math.floor(t * 255);
    return { r: v, g: v, b: v };
  },
  viridis: (t: number) => {
    // Simplified viridis approximation
    const r = Math.floor(68 + t * 187);
    const g = Math.floor(1 + t * 180 + (1 - t) * 80);
    const b = Math.floor(84 + (1 - t) * 171);
    return { r, g, b };
  },
  plasma: (t: number) => {
    const r = Math.floor(13 + t * 242);
    const g = Math.floor(8 + t * 140 + (1 - t) * 40);
    const b = Math.floor(135 + (1 - t) * 100 - t * 50);
    return {
      r: Math.max(0, Math.min(255, r)),
      g: Math.max(0, Math.min(255, g)),
      b: Math.max(0, Math.min(255, b)),
    };
  },
  turbo: (t: number) => {
    // Turbo colormap (rainbow-like, better for depth)
    const r = Math.floor(Math.sin(t * Math.PI) * 255);
    const g = Math.floor(Math.sin(t * Math.PI + Math.PI / 3) * 255);
    const b = Math.floor(Math.sin(t * Math.PI + (2 * Math.PI) / 3) * 255);
    return { r: Math.abs(r), g: Math.abs(g), b: Math.abs(b) };
  },
};

// ============================================================================
// CONDITIONING RENDERER CLASS
// ============================================================================

export class ConditioningRenderer {
  private config: Required<ConditioningConfig>;
  private canvas: OffscreenCanvas | HTMLCanvasElement;
  private ctx: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D;

  constructor(config: ConditioningConfig) {
    this.config = {
      width: config.width,
      height: config.height,
      cameraPosition: config.cameraPosition ?? { x: 0, y: 0, z: 1000 },
      cameraTarget: config.cameraTarget ?? { x: 0, y: 0, z: 0 },
      fov: config.fov ?? 60,
      near: config.near ?? 0.1,
      far: config.far ?? 10000,
      depthNear: config.depthNear ?? 0,
      depthFar: config.depthFar ?? 1000,
      depthInvert: config.depthInvert ?? false,
      particleSize: config.particleSize ?? 2,
      backgroundColor: config.backgroundColor ?? "#000000",
      categoryColors: config.categoryColors ?? {},
    };

    // Create canvas (prefer OffscreenCanvas for worker support)
    if (typeof OffscreenCanvas !== "undefined") {
      this.canvas = new OffscreenCanvas(this.config.width, this.config.height);
    } else {
      this.canvas = document.createElement("canvas");
      this.canvas.width = this.config.width;
      this.canvas.height = this.config.height;
    }

    this.ctx = this.canvas.getContext("2d") as
      | CanvasRenderingContext2D
      | OffscreenCanvasRenderingContext2D;
  }

  // ==========================================================================
  // DEPTH MAP RENDERING
  // ==========================================================================

  /**
   * Render particles as a depth map (grayscale, Z → brightness)
   *
   * @param particles - Array of particle positions
   * @param colormap - Color mapping function for depth
   * @returns Conditioning result with depth map
   */
  renderDepthMap(
    particles: ParticleData[],
    colormap: keyof typeof DEPTH_COLORMAPS = "grayscale",
  ): ConditioningResult {
    const startTime = performance.now();
    const { width, height, depthNear, depthFar, depthInvert, particleSize } =
      this.config;
    const colormapFn = DEPTH_COLORMAPS[colormap];

    // Clear canvas
    this.ctx.fillStyle = this.config.backgroundColor;
    this.ctx.fillRect(0, 0, width, height);

    // Project and render each particle
    const depthRange = depthFar - depthNear;

    for (const p of particles) {
      // Project to screen coordinates (orthographic for simplicity)
      const screenX = (p.position.x / width + 0.5) * width;
      const screenY = (p.position.y / height + 0.5) * height;

      // Calculate depth (0 = near, 1 = far)
      let depth = (p.position.z - depthNear) / depthRange;
      depth = Math.max(0, Math.min(1, depth));
      if (depthInvert) depth = 1 - depth;

      // Get color from colormap
      const color = colormapFn(depth);
      const size = p.size ?? particleSize;

      // Draw particle
      this.ctx.fillStyle = `rgb(${color.r},${color.g},${color.b})`;
      this.ctx.beginPath();
      this.ctx.arc(screenX, screenY, size, 0, Math.PI * 2);
      this.ctx.fill();
    }

    return {
      imageData: this.ctx.getImageData(0, 0, width, height),
      canvas: this.canvas,
      particleCount: particles.length,
      renderTime: performance.now() - startTime,
    };
  }

  // ==========================================================================
  // TRAJECTORY MAP RENDERING
  // ==========================================================================

  /**
   * Render trajectories as colored strokes
   * Color gradient along path indicates time/progress
   *
   * @param trajectories - Array of trajectory paths
   * @returns Conditioning result with trajectory map
   */
  renderTrajectoryMap(trajectories: TrajectoryData[]): ConditioningResult {
    const startTime = performance.now();
    const { width, height } = this.config;

    // Clear canvas
    this.ctx.fillStyle = this.config.backgroundColor;
    this.ctx.fillRect(0, 0, width, height);

    let totalPoints = 0;

    for (const trajectory of trajectories) {
      if (trajectory.points.length < 2) continue;
      totalPoints += trajectory.points.length;

      const lineWidth = trajectory.width ?? 2;
      const baseColor = trajectory.color ?? { r: 0, g: 212, b: 255 };

      // Draw trajectory with gradient along path
      for (let i = 0; i < trajectory.points.length - 1; i++) {
        const p1 = trajectory.points[i];
        const p2 = trajectory.points[i + 1];

        // Progress along path (0 to 1)
        const t = i / (trajectory.points.length - 1);

        // Project to screen
        const x1 = (p1.x / width + 0.5) * width;
        const y1 = (p1.y / height + 0.5) * height;
        const x2 = (p2.x / width + 0.5) * width;
        const y2 = (p2.y / height + 0.5) * height;

        // Color gradient: base color → white as time progresses
        const r = Math.floor(baseColor.r + (255 - baseColor.r) * t);
        const g = Math.floor(baseColor.g + (255 - baseColor.g) * t);
        const b = Math.floor(baseColor.b + (255 - baseColor.b) * t);

        this.ctx.strokeStyle = `rgb(${r},${g},${b})`;
        this.ctx.lineWidth = lineWidth;
        this.ctx.lineCap = "round";
        this.ctx.beginPath();
        this.ctx.moveTo(x1, y1);
        this.ctx.lineTo(x2, y2);
        this.ctx.stroke();
      }
    }

    return {
      imageData: this.ctx.getImageData(0, 0, width, height),
      canvas: this.canvas,
      particleCount: totalPoints,
      renderTime: performance.now() - startTime,
    };
  }

  // ==========================================================================
  // SEGMENTATION MASK RENDERING
  // ==========================================================================

  /**
   * Render particles as segmentation mask (category → distinct color)
   *
   * @param particles - Array of particles with category field
   * @returns Conditioning result with segmentation mask
   */
  renderSegmentationMask(particles: ParticleData[]): ConditioningResult {
    const startTime = performance.now();
    const { width, height, particleSize, categoryColors } = this.config;

    // Clear canvas
    this.ctx.fillStyle = this.config.backgroundColor;
    this.ctx.fillRect(0, 0, width, height);

    // Default category colors
    const defaultColors = [
      "#FF0000",
      "#00FF00",
      "#0000FF",
      "#FFFF00",
      "#FF00FF",
      "#00FFFF",
      "#FF8800",
      "#88FF00",
      "#0088FF",
      "#FF0088",
      "#8800FF",
      "#00FF88",
    ];
    let colorIndex = 0;
    const categoryColorMap = new Map<string | number, string>();

    for (const p of particles) {
      // Get category color
      const category = p.category ?? "default";
      let color = categoryColorMap.get(category);

      if (!color) {
        color =
          categoryColors[category] ??
          defaultColors[colorIndex % defaultColors.length];
        categoryColorMap.set(category, color);
        colorIndex++;
      }

      // Project to screen
      const screenX = (p.position.x / width + 0.5) * width;
      const screenY = (p.position.y / height + 0.5) * height;
      const size = p.size ?? particleSize;

      // Draw particle
      this.ctx.fillStyle = color;
      this.ctx.beginPath();
      this.ctx.arc(screenX, screenY, size, 0, Math.PI * 2);
      this.ctx.fill();
    }

    return {
      imageData: this.ctx.getImageData(0, 0, width, height),
      canvas: this.canvas,
      particleCount: particles.length,
      renderTime: performance.now() - startTime,
    };
  }

  // ==========================================================================
  // VELOCITY/FLOW MAP RENDERING
  // ==========================================================================

  /**
   * Render particles with velocity as optical flow colors
   * Hue = direction, Saturation = speed
   *
   * @param particles - Array of particles with velocity
   * @returns Conditioning result with velocity map
   */
  renderVelocityMap(particles: ParticleData[]): ConditioningResult {
    const startTime = performance.now();
    const { width, height, particleSize } = this.config;

    // Clear canvas with neutral gray (zero motion)
    this.ctx.fillStyle = "#808080";
    this.ctx.fillRect(0, 0, width, height);

    // Find max velocity for normalization
    let maxSpeed = 0;
    for (const p of particles) {
      if (p.velocity) {
        const speed = Math.sqrt(p.velocity.x ** 2 + p.velocity.y ** 2);
        maxSpeed = Math.max(maxSpeed, speed);
      }
    }
    maxSpeed = maxSpeed || 1;

    for (const p of particles) {
      if (!p.velocity) continue;

      // Project to screen
      const screenX = (p.position.x / width + 0.5) * width;
      const screenY = (p.position.y / height + 0.5) * height;

      // Calculate direction (hue) and speed (saturation)
      const vx = p.velocity.x;
      const vy = p.velocity.y;
      const speed = Math.sqrt(vx ** 2 + vy ** 2);
      const direction = Math.atan2(vy, vx); // -PI to PI

      // Convert to HSL
      const hue = ((direction + Math.PI) / (2 * Math.PI)) * 360;
      const saturation = Math.min(100, (speed / maxSpeed) * 100);
      const lightness = 50;

      const size = p.size ?? particleSize;
      this.ctx.fillStyle = `hsl(${hue}, ${saturation}%, ${lightness}%)`;
      this.ctx.beginPath();
      this.ctx.arc(screenX, screenY, size, 0, Math.PI * 2);
      this.ctx.fill();
    }

    return {
      imageData: this.ctx.getImageData(0, 0, width, height),
      canvas: this.canvas,
      particleCount: particles.length,
      renderTime: performance.now() - startTime,
    };
  }

  // ==========================================================================
  // SHAPE SILHOUETTE RENDERING
  // ==========================================================================

  /**
   * Render particles as binary silhouette mask
   * White particles on black background
   *
   * @param particles - Array of particle positions
   * @param invert - If true, black particles on white background
   * @returns Conditioning result with silhouette
   */
  renderSilhouette(
    particles: ParticleData[],
    invert = false,
  ): ConditioningResult {
    const startTime = performance.now();
    const { width, height, particleSize } = this.config;

    // Clear canvas
    this.ctx.fillStyle = invert ? "#FFFFFF" : "#000000";
    this.ctx.fillRect(0, 0, width, height);

    const particleColor = invert ? "#000000" : "#FFFFFF";

    for (const p of particles) {
      // Project to screen
      const screenX = (p.position.x / width + 0.5) * width;
      const screenY = (p.position.y / height + 0.5) * height;
      const size = p.size ?? particleSize;

      this.ctx.fillStyle = particleColor;
      this.ctx.beginPath();
      this.ctx.arc(screenX, screenY, size, 0, Math.PI * 2);
      this.ctx.fill();
    }

    return {
      imageData: this.ctx.getImageData(0, 0, width, height),
      canvas: this.canvas,
      particleCount: particles.length,
      renderTime: performance.now() - startTime,
    };
  }

  // ==========================================================================
  // DATA-DRIVEN RENDERING
  // ==========================================================================

  /**
   * Render particles with data value mapped to color ramp
   *
   * @param particles - Array of particles with dataValue field
   * @param minValue - Minimum data value (maps to start of ramp)
   * @param maxValue - Maximum data value (maps to end of ramp)
   * @param colorRamp - Array of colors for gradient
   * @returns Conditioning result
   */
  renderDataValueMap(
    particles: ParticleData[],
    minValue: number,
    maxValue: number,
    colorRamp: string[] = [
      "#0000FF",
      "#00FFFF",
      "#00FF00",
      "#FFFF00",
      "#FF0000",
    ],
  ): ConditioningResult {
    const startTime = performance.now();
    const { width, height, particleSize } = this.config;

    // Clear canvas
    this.ctx.fillStyle = this.config.backgroundColor;
    this.ctx.fillRect(0, 0, width, height);

    const valueRange = maxValue - minValue || 1;

    for (const p of particles) {
      const dataValue = p.dataValue ?? 0;

      // Normalize value to 0-1
      const t = Math.max(0, Math.min(1, (dataValue - minValue) / valueRange));

      // Interpolate color from ramp
      const rampIndex = t * (colorRamp.length - 1);
      const lowerIndex = Math.floor(rampIndex);
      const upperIndex = Math.min(lowerIndex + 1, colorRamp.length - 1);
      const localT = rampIndex - lowerIndex;

      // Simple color interpolation (assumes hex colors)
      const color1 = this.hexToRgb(colorRamp[lowerIndex]);
      const color2 = this.hexToRgb(colorRamp[upperIndex]);

      const r = Math.floor(color1.r + (color2.r - color1.r) * localT);
      const g = Math.floor(color1.g + (color2.g - color1.g) * localT);
      const b = Math.floor(color1.b + (color2.b - color1.b) * localT);

      // Project to screen
      const screenX = (p.position.x / width + 0.5) * width;
      const screenY = (p.position.y / height + 0.5) * height;
      const size = p.size ?? particleSize;

      this.ctx.fillStyle = `rgb(${r},${g},${b})`;
      this.ctx.beginPath();
      this.ctx.arc(screenX, screenY, size, 0, Math.PI * 2);
      this.ctx.fill();
    }

    return {
      imageData: this.ctx.getImageData(0, 0, width, height),
      canvas: this.canvas,
      particleCount: particles.length,
      renderTime: performance.now() - startTime,
    };
  }

  // ==========================================================================
  // BATCH RENDERING (for millions of particles)
  // ==========================================================================

  /**
   * Render particles using raw pixel manipulation (faster for millions)
   * Bypasses Canvas2D API for direct ImageData access
   *
   * @param particles - Array of particle positions
   * @param mode - Rendering mode
   * @returns Conditioning result
   */
  renderBatch(
    particles: ParticleData[],
    mode: "depth" | "silhouette" | "velocity" = "depth",
  ): ConditioningResult {
    const startTime = performance.now();
    const { width, height, depthNear, depthFar, depthInvert } = this.config;
    const depthRange = depthFar - depthNear;

    // Create ImageData directly
    const imageData = this.ctx.createImageData(width, height);
    const data = imageData.data;

    // Fill background
    const bgColor = mode === "velocity" ? 128 : 0;
    for (let i = 0; i < data.length; i += 4) {
      data[i] = bgColor;
      data[i + 1] = bgColor;
      data[i + 2] = bgColor;
      data[i + 3] = 255;
    }

    // Render particles directly to pixel buffer
    for (const p of particles) {
      // Project to screen (integer coordinates)
      const screenX = Math.floor((p.position.x / width + 0.5) * width);
      const screenY = Math.floor((p.position.y / height + 0.5) * height);

      // Bounds check
      if (screenX < 0 || screenX >= width || screenY < 0 || screenY >= height)
        continue;

      const pixelIndex = (screenY * width + screenX) * 4;

      if (mode === "depth") {
        let depth = (p.position.z - depthNear) / depthRange;
        depth = Math.max(0, Math.min(1, depth));
        if (depthInvert) depth = 1 - depth;
        const v = Math.floor(depth * 255);
        data[pixelIndex] = v;
        data[pixelIndex + 1] = v;
        data[pixelIndex + 2] = v;
      } else if (mode === "silhouette") {
        data[pixelIndex] = 255;
        data[pixelIndex + 1] = 255;
        data[pixelIndex + 2] = 255;
      } else if (mode === "velocity" && p.velocity) {
        // Encode velocity as color (optical flow style)
        const maxVel = 100;
        const vx = Math.max(-1, Math.min(1, p.velocity.x / maxVel));
        const vy = Math.max(-1, Math.min(1, p.velocity.y / maxVel));
        data[pixelIndex] = Math.floor((vx + 1) * 127.5); // Red = X velocity
        data[pixelIndex + 1] = Math.floor((vy + 1) * 127.5); // Green = Y velocity
        data[pixelIndex + 2] = 128; // Blue = neutral
      }
    }

    this.ctx.putImageData(imageData, 0, 0);

    return {
      imageData,
      canvas: this.canvas,
      particleCount: particles.length,
      renderTime: performance.now() - startTime,
    };
  }

  // ==========================================================================
  // UTILITIES
  // ==========================================================================

  private hexToRgb(hex: string): { r: number; g: number; b: number } {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result
      ? {
          r: parseInt(result[1], 16),
          g: parseInt(result[2], 16),
          b: parseInt(result[3], 16),
        }
      : { r: 0, g: 0, b: 0 };
  }

  /**
   * Resize the renderer
   */
  resize(width: number, height: number): void {
    this.config.width = width;
    this.config.height = height;
    if (this.canvas instanceof OffscreenCanvas) {
      this.canvas = new OffscreenCanvas(width, height);
    } else {
      this.canvas.width = width;
      this.canvas.height = height;
    }
    this.ctx = this.canvas.getContext("2d") as
      | CanvasRenderingContext2D
      | OffscreenCanvasRenderingContext2D;
  }

  /**
   * Get the current canvas as a blob (for export)
   */
  async toBlob(type = "image/png", quality = 1.0): Promise<Blob> {
    if (this.canvas instanceof OffscreenCanvas) {
      return this.canvas.convertToBlob({ type, quality });
    } else {
      return new Promise((resolve) => {
        (this.canvas as HTMLCanvasElement).toBlob(
          (blob: Blob | null) => resolve(blob!),
          type,
          quality,
        );
      });
    }
  }
}

// ============================================================================
// FACTORY FUNCTIONS
// ============================================================================

/**
 * Create a conditioning renderer for standard video output
 */
export function createConditioningRenderer(
  width = 1280,
  height = 720,
  options: Partial<ConditioningConfig> = {},
): ConditioningRenderer {
  return new ConditioningRenderer({
    width,
    height,
    ...options,
  });
}

/**
 * Generate particles from CSV data
 * Maps CSV columns to particle positions/properties
 */
export function particlesFromCSV(
  rows: string[][],
  mapping: {
    xColumn: number;
    yColumn: number;
    zColumn?: number;
    sizeColumn?: number;
    categoryColumn?: number;
    dataValueColumn?: number;
  },
  options: {
    xScale?: number;
    yScale?: number;
    zScale?: number;
    xOffset?: number;
    yOffset?: number;
    zOffset?: number;
  } = {},
): ParticleData[] {
  const {
    xScale = 1,
    yScale = 1,
    zScale = 1,
    xOffset = 0,
    yOffset = 0,
    zOffset = 0,
  } = options;

  return rows.map((row) => {
    const x = (parseFloat(row[mapping.xColumn]) || 0) * xScale + xOffset;
    const y = (parseFloat(row[mapping.yColumn]) || 0) * yScale + yOffset;
    const z =
      mapping.zColumn !== undefined
        ? (parseFloat(row[mapping.zColumn]) || 0) * zScale + zOffset
        : 0;

    const particle: ParticleData = {
      position: { x, y, z },
    };

    if (mapping.sizeColumn !== undefined) {
      particle.size = parseFloat(row[mapping.sizeColumn]) || 2;
    }

    if (mapping.categoryColumn !== undefined) {
      particle.category = row[mapping.categoryColumn];
    }

    if (mapping.dataValueColumn !== undefined) {
      particle.dataValue = parseFloat(row[mapping.dataValueColumn]) || 0;
    }

    return particle;
  });
}

/**
 * Generate trajectory from spline points
 */
export function trajectoryFromSpline(
  points: Vec3[],
  subdivisions = 10,
): TrajectoryData {
  // Simple linear interpolation (would use bezier for smooth curves)
  const interpolated: Vec3[] = [];

  for (let i = 0; i < points.length - 1; i++) {
    const p1 = points[i];
    const p2 = points[i + 1];

    for (let j = 0; j <= subdivisions; j++) {
      const t = j / subdivisions;
      interpolated.push({
        x: p1.x + (p2.x - p1.x) * t,
        y: p1.y + (p2.y - p1.y) * t,
        z: p1.z + (p2.z - p1.z) * t,
      });
    }
  }

  return { points: interpolated };
}

/**
 * Generate particles along a spline path
 */
export function particlesAlongSpline(
  splinePoints: Vec3[],
  count: number,
  spread = 10,
): ParticleData[] {
  const trajectory = trajectoryFromSpline(splinePoints);
  const particles: ParticleData[] = [];

  for (let i = 0; i < count; i++) {
    // Random position along trajectory
    const pathIndex = Math.floor(Math.random() * trajectory.points.length);
    const basePoint = trajectory.points[pathIndex];

    // Add some spread
    particles.push({
      position: {
        x: basePoint.x + (Math.random() - 0.5) * spread,
        y: basePoint.y + (Math.random() - 0.5) * spread,
        z: basePoint.z + (Math.random() - 0.5) * spread,
      },
    });
  }

  return particles;
}

// ============================================================================
// EXPORTS
// ============================================================================

export default {
  ConditioningRenderer,
  createConditioningRenderer,
  particlesFromCSV,
  trajectoryFromSpline,
  particlesAlongSpline,
  ANADOL_PALETTE,
  DEPTH_COLORMAPS,
};
