/**
 * Distort Effect Renderers
 *
 * Implements distortion effects: Transform, Warp, Displacement Map, Turbulent Displace
 * These effects manipulate pixel positions rather than colors.
 */
import {
  registerEffectRenderer,
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams
} from '../effectProcessor';

// ============================================================================
// SIMPLEX NOISE IMPLEMENTATION
// For Turbulent Displace effect - deterministic, seeded noise
// ============================================================================

/**
 * Seeded Simplex Noise implementation for turbulent displacement
 * Based on Stefan Gustavson's implementation, adapted for deterministic behavior
 */
class SimplexNoise {
  private perm: number[] = [];
  private permMod12: number[] = [];

  private static readonly grad3: number[][] = [
    [1, 1, 0], [-1, 1, 0], [1, -1, 0], [-1, -1, 0],
    [1, 0, 1], [-1, 0, 1], [1, 0, -1], [-1, 0, -1],
    [0, 1, 1], [0, -1, 1], [0, 1, -1], [0, -1, -1]
  ];

  constructor(seed: number) {
    this.initializePermutationTable(seed);
  }

  private initializePermutationTable(seed: number): void {
    // Mulberry32 seeded random
    const mulberry32 = (s: number) => {
      return () => {
        let t = (s += 0x6D2B79F5);
        t = Math.imul(t ^ (t >>> 15), t | 1);
        t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
      };
    };

    const random = mulberry32(seed);

    // Generate permutation table
    const p: number[] = [];
    for (let i = 0; i < 256; i++) {
      p[i] = i;
    }

    // Fisher-Yates shuffle with seeded random
    for (let i = 255; i > 0; i--) {
      const j = Math.floor(random() * (i + 1));
      [p[i], p[j]] = [p[j], p[i]];
    }

    // Duplicate for wrapping
    for (let i = 0; i < 512; i++) {
      this.perm[i] = p[i & 255];
      this.permMod12[i] = this.perm[i] % 12;
    }
  }

  /**
   * 2D Simplex noise
   * Returns value in range [-1, 1]
   */
  noise2D(xin: number, yin: number): number {
    const F2 = 0.5 * (Math.sqrt(3) - 1);
    const G2 = (3 - Math.sqrt(3)) / 6;

    // Skew input space to determine which simplex cell we're in
    const s = (xin + yin) * F2;
    const i = Math.floor(xin + s);
    const j = Math.floor(yin + s);
    const t = (i + j) * G2;

    // Unskew cell origin back to (x,y) space
    const X0 = i - t;
    const Y0 = j - t;

    // The x,y distances from the cell origin
    const x0 = xin - X0;
    const y0 = yin - Y0;

    // Determine which simplex we're in
    let i1: number, j1: number;
    if (x0 > y0) {
      i1 = 1; j1 = 0;
    } else {
      i1 = 0; j1 = 1;
    }

    // Offsets for middle corner
    const x1 = x0 - i1 + G2;
    const y1 = y0 - j1 + G2;

    // Offsets for last corner
    const x2 = x0 - 1 + 2 * G2;
    const y2 = y0 - 1 + 2 * G2;

    // Hash coordinates of the three simplex corners
    const ii = i & 255;
    const jj = j & 255;
    const gi0 = this.permMod12[ii + this.perm[jj]];
    const gi1 = this.permMod12[ii + i1 + this.perm[jj + j1]];
    const gi2 = this.permMod12[ii + 1 + this.perm[jj + 1]];

    // Calculate contribution from the three corners
    let n0 = 0, n1 = 0, n2 = 0;

    let t0 = 0.5 - x0 * x0 - y0 * y0;
    if (t0 >= 0) {
      t0 *= t0;
      n0 = t0 * t0 * this.dot2D(SimplexNoise.grad3[gi0], x0, y0);
    }

    let t1 = 0.5 - x1 * x1 - y1 * y1;
    if (t1 >= 0) {
      t1 *= t1;
      n1 = t1 * t1 * this.dot2D(SimplexNoise.grad3[gi1], x1, y1);
    }

    let t2 = 0.5 - x2 * x2 - y2 * y2;
    if (t2 >= 0) {
      t2 *= t2;
      n2 = t2 * t2 * this.dot2D(SimplexNoise.grad3[gi2], x2, y2);
    }

    // Scale result to [-1, 1]
    return 70 * (n0 + n1 + n2);
  }

  private dot2D(g: number[], x: number, y: number): number {
    return g[0] * x + g[1] * y;
  }
}

// ============================================================================
// HELPER: NaN-safe number extraction
// ============================================================================

/**
 * Safely extract a numeric value, returning default if NaN/undefined/null
 * Optionally clamps to min/max bounds
 *
 * BUG-025/026/027/028 FIX: NaN values bypass Math.max/min clamps
 */
function safeNum(val: unknown, def: number, min?: number, max?: number): number {
  const num = typeof val === 'number' && Number.isFinite(val) ? val : def;
  if (min !== undefined && max !== undefined) {
    return Math.max(min, Math.min(max, num));
  }
  if (min !== undefined) return Math.max(min, num);
  if (max !== undefined) return Math.min(max, num);
  return num;
}

// ============================================================================
// TRANSFORM EFFECT
// ============================================================================

/**
 * Transform effect renderer
 * Applies anchor point, position, scale, skew, rotation, and opacity
 *
 * Parameters:
 * - anchor_point: { x, y } normalized (0-1)
 * - position: { x, y } normalized (0-1)
 * - scale_width: percentage
 * - scale_height: percentage
 * - skew: degrees (-85 to 85)
 * - skew_axis: degrees
 * - rotation: degrees
 * - opacity: percentage (0-100)
 */
export function transformRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // BUG-025 FIX: Validate all numeric params to prevent NaN propagation
  const anchorPoint = params.anchor_point ?? { x: 0.5, y: 0.5 };
  const position = params.position ?? { x: 0.5, y: 0.5 };

  // Validate anchor and position coordinates
  const anchorX_norm = safeNum(anchorPoint.x, 0.5, 0, 1);
  const anchorY_norm = safeNum(anchorPoint.y, 0.5, 0, 1);
  const posX_norm = safeNum(position.x, 0.5, 0, 1);
  const posY_norm = safeNum(position.y, 0.5, 0, 1);

  const scaleWidth = safeNum(params.scale_width, 100, 0.01, 10000) / 100;
  const scaleHeight = safeNum(params.scale_height, 100, 0.01, 10000) / 100;
  const skew = safeNum(params.skew, 0, -85, 85) * Math.PI / 180;
  const skewAxis = safeNum(params.skew_axis, 0, -360, 360) * Math.PI / 180;
  const rotation = safeNum(params.rotation, 0) * Math.PI / 180;
  const opacity = safeNum(params.opacity, 100, 0, 100) / 100;

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Calculate pixel positions (using validated coordinates)
  const anchorX = anchorX_norm * width;
  const anchorY = anchorY_norm * height;
  const posX = posX_norm * width;
  const posY = posY_norm * height;

  // Apply transform
  output.ctx.globalAlpha = opacity;
  output.ctx.translate(posX, posY);
  output.ctx.rotate(rotation);

  // Apply skew
  if (skew !== 0) {
    const skewX = Math.tan(skew) * Math.cos(skewAxis);
    const skewY = Math.tan(skew) * Math.sin(skewAxis);
    output.ctx.transform(1, skewY, skewX, 1, 0, 0);
  }

  output.ctx.scale(scaleWidth, scaleHeight);
  output.ctx.translate(-anchorX, -anchorY);

  output.ctx.drawImage(input.canvas, 0, 0);
  output.ctx.setTransform(1, 0, 0, 1, 0, 0);
  output.ctx.globalAlpha = 1;

  return output;
}

// ============================================================================
// WARP EFFECT
// ============================================================================

/**
 * Warp effect renderer
 * Applies various warp distortions
 *
 * Parameters:
 * - warp_style: 'arc' | 'bulge' | 'wave' | 'fisheye' | 'twist' | etc.
 * - bend: -100 to 100
 * - horizontal_distortion: -100 to 100
 * - vertical_distortion: -100 to 100
 */
export function warpRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const warpStyle = params.warp_style ?? 'arc';
  // BUG-026 FIX: Validate numeric params to prevent NaN bypass of === 0 check
  const bend = safeNum(params.bend, 0, -100, 100) / 100;
  const hDistort = safeNum(params.horizontal_distortion, 0, -100, 100) / 100;
  const vDistort = safeNum(params.vertical_distortion, 0, -100, 100) / 100;

  // No warp needed (NaN params now safely default to 0)
  if (bend === 0 && hDistort === 0 && vDistort === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;

  const centerX = width / 2;
  const centerY = height / 2;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      // Normalize coordinates to -1 to 1
      const nx = (x - centerX) / centerX;
      const ny = (y - centerY) / centerY;

      let srcX = x;
      let srcY = y;

      // Apply warp based on style
      switch (warpStyle) {
        case 'arc': {
          const arcBend = bend * ny * ny;
          srcX = x + arcBend * centerX * nx;
          break;
        }
        case 'bulge': {
          const r = Math.sqrt(nx * nx + ny * ny);
          if (r < 1) {
            const factor = 1 + bend * (1 - r * r);
            srcX = centerX + (x - centerX) / factor;
            srcY = centerY + (y - centerY) / factor;
          }
          break;
        }
        case 'wave': {
          srcX = x + Math.sin(ny * Math.PI * 2) * bend * width * 0.1;
          srcY = y + Math.sin(nx * Math.PI * 2) * bend * height * 0.1;
          break;
        }
        case 'fisheye': {
          const r = Math.sqrt(nx * nx + ny * ny);
          if (r > 0 && r < 1) {
            const theta = Math.atan2(ny, nx);
            const newR = Math.pow(r, 1 + bend);
            srcX = centerX + newR * Math.cos(theta) * centerX;
            srcY = centerY + newR * Math.sin(theta) * centerY;
          }
          break;
        }
        case 'twist': {
          const r = Math.sqrt(nx * nx + ny * ny);
          const angle = bend * Math.PI * (1 - r);
          const cos = Math.cos(angle);
          const sin = Math.sin(angle);
          srcX = centerX + (nx * cos - ny * sin) * centerX;
          srcY = centerY + (nx * sin + ny * cos) * centerY;
          break;
        }
        default:
          // Pass through for unimplemented styles
          break;
      }

      // Apply horizontal and vertical distortion
      srcX += hDistort * centerX * (1 - ny * ny);
      srcY += vDistort * centerY * (1 - nx * nx);

      // Clamp to bounds
      srcX = Math.max(0, Math.min(width - 1, srcX));
      srcY = Math.max(0, Math.min(height - 1, srcY));

      // Bilinear interpolation
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;

      const idx00 = (y0 * width + x0) * 4;
      const idx01 = (y0 * width + x1) * 4;
      const idx10 = (y1 * width + x0) * 4;
      const idx11 = (y1 * width + x1) * 4;
      const outIdx = (y * width + x) * 4;

      for (let c = 0; c < 4; c++) {
        const v00 = src[idx00 + c];
        const v01 = src[idx01 + c];
        const v10 = src[idx10 + c];
        const v11 = src[idx11 + c];

        dst[outIdx + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) +
          v01 * fx * (1 - fy) +
          v10 * (1 - fx) * fy +
          v11 * fx * fy
        );
      }
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// DISPLACEMENT MAP EFFECT
// ============================================================================

/**
 * Extract channel value from pixel based on channel type
 */
function getChannelValue(
  r: number, g: number, b: number, a: number,
  channel: string
): number {
  switch (channel) {
    case 'red': return r;
    case 'green': return g;
    case 'blue': return b;
    case 'alpha': return a;
    case 'luminance':
    default:
      return 0.299 * r + 0.587 * g + 0.114 * b;
  }
}

/**
 * Generate procedural displacement map (noise-based)
 * Uses seeded random for deterministic noise
 */
function generateProceduralMap(
  width: number,
  height: number,
  mapType: string,
  scale: number,
  seed: number = 12345
): ImageData {
  const canvas = document.createElement('canvas');
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext('2d')!;
  const imageData = ctx.createImageData(width, height);
  const data = imageData.data;

  // Seeded random for deterministic noise
  const mulberry32 = (s: number) => {
    return () => {
      let t = (s += 0x6D2B79F5);
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  };
  const random = mulberry32(seed);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      let value = 128; // Neutral (no displacement)

      switch (mapType) {
        case 'noise':
          // Seeded pseudo-random noise (deterministic)
          value = Math.floor(random() * 256);
          break;
        case 'gradient-h':
          // Horizontal gradient
          value = Math.floor((x / width) * 255);
          break;
        case 'gradient-v':
          // Vertical gradient
          value = Math.floor((y / height) * 255);
          break;
        case 'radial':
          // Radial gradient from center
          const cx = width / 2;
          const cy = height / 2;
          const dist = Math.sqrt((x - cx) ** 2 + (y - cy) ** 2);
          const maxDist = Math.sqrt(cx ** 2 + cy ** 2);
          value = Math.floor((1 - dist / maxDist) * 255);
          break;
        case 'sine-h':
          // Horizontal sine wave
          value = Math.floor(128 + 127 * Math.sin((x / width) * Math.PI * 2 * scale));
          break;
        case 'sine-v':
          // Vertical sine wave
          value = Math.floor(128 + 127 * Math.sin((y / height) * Math.PI * 2 * scale));
          break;
        case 'checker':
          // Checkerboard pattern
          const tileSize = Math.max(1, Math.floor(width / (scale * 10)));
          const checkX = Math.floor(x / tileSize) % 2;
          const checkY = Math.floor(y / tileSize) % 2;
          value = (checkX + checkY) % 2 === 0 ? 255 : 0;
          break;
        default:
          value = 128;
      }

      data[i] = value;     // R
      data[i + 1] = value; // G
      data[i + 2] = value; // B
      data[i + 3] = 255;   // A
    }
  }

  return imageData;
}

/**
 * Map behavior types for layer displacement maps
 */
type MapBehavior = 'center' | 'stretch' | 'tile';

/**
 * Apply map behavior transformation to get pixel coordinates
 * @param x - Output X coordinate
 * @param y - Output Y coordinate
 * @param targetWidth - Target (output) width
 * @param targetHeight - Target (output) height
 * @param mapWidth - Displacement map width
 * @param mapHeight - Displacement map height
 * @param behavior - Map behavior mode
 * @returns Pixel coordinates in the displacement map
 */
function applyMapBehavior(
  x: number,
  y: number,
  targetWidth: number,
  targetHeight: number,
  mapWidth: number,
  mapHeight: number,
  behavior: MapBehavior
): { mapX: number; mapY: number } {
  switch (behavior) {
    case 'center': {
      // Center the map over the target layer
      const offsetX = (targetWidth - mapWidth) / 2;
      const offsetY = (targetHeight - mapHeight) / 2;
      let mapX = x - offsetX;
      let mapY = y - offsetY;
      // Return -1 if outside map bounds (no displacement)
      if (mapX < 0 || mapX >= mapWidth || mapY < 0 || mapY >= mapHeight) {
        return { mapX: -1, mapY: -1 };
      }
      return { mapX, mapY };
    }

    case 'stretch': {
      // Stretch/shrink map to fit target dimensions
      const mapX = (x / targetWidth) * mapWidth;
      const mapY = (y / targetHeight) * mapHeight;
      return { mapX, mapY };
    }

    case 'tile': {
      // Tile the map across the target
      const mapX = ((x % mapWidth) + mapWidth) % mapWidth;
      const mapY = ((y % mapHeight) + mapHeight) % mapHeight;
      return { mapX, mapY };
    }

    default:
      // Default to stretch
      return {
        mapX: (x / targetWidth) * mapWidth,
        mapY: (y / targetHeight) * mapHeight
      };
  }
}

/**
 * Displacement Map effect renderer
 * Displaces pixels based on a displacement map (layer or procedural)
 *
 * Parameters:
 * - displacement_map_layer: layer ID (when map_type='layer')
 * - map_type: 'layer' | 'noise' | 'gradient-h' | 'gradient-v' | 'radial' | 'sine-h' | 'sine-v' | 'checker'
 * - displacement_map_behavior: 'center' | 'stretch' | 'tile'
 * - use_for_horizontal: 'red' | 'green' | 'blue' | 'alpha' | 'luminance' | 'off'
 * - max_horizontal: pixels (-4000 to 4000)
 * - use_for_vertical: 'red' | 'green' | 'blue' | 'alpha' | 'luminance' | 'off'
 * - max_vertical: pixels (-4000 to 4000)
 * - edge_behavior: 'off' | 'tiles' | 'mirror'
 * - map_scale: scale factor for procedural maps (0.1-10)
 *
 * Special params (injected by render pipeline):
 * - _mapLayerCanvas: HTMLCanvasElement - Pre-rendered layer to use as displacement map
 */
export function displacementMapRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const mapType = params.map_type ?? 'layer';
  const mapBehavior = (params.displacement_map_behavior ?? 'stretch') as MapBehavior;
  const useHorizontal = params.use_for_horizontal ?? 'red';
  const useVertical = params.use_for_vertical ?? 'green';
  // BUG-027 FIX: Validate numeric params to prevent NaN propagation
  const maxHorizontal = safeNum(params.max_horizontal, 0, -4000, 4000);
  const maxVertical = safeNum(params.max_vertical, 0, -4000, 4000);
  const wrapMode = params.edge_behavior ?? 'off';
  const mapScale = safeNum(params.map_scale, 1, 0.1, 10);

  // Check for pre-rendered layer canvas (injected by render pipeline)
  const mapLayerCanvas = params._mapLayerCanvas as HTMLCanvasElement | undefined;

  // No displacement if both are off or zero
  if ((useHorizontal === 'off' || maxHorizontal === 0) &&
      (useVertical === 'off' || maxVertical === 0)) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Get input pixels
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;

  // Get displacement map data
  let mapData: Uint8ClampedArray;
  let mapWidth: number;
  let mapHeight: number;

  if (mapType === 'layer' && mapLayerCanvas) {
    // Use pre-rendered layer as displacement map
    const mapCtx = mapLayerCanvas.getContext('2d');
    if (mapCtx) {
      mapWidth = mapLayerCanvas.width;
      mapHeight = mapLayerCanvas.height;
      const mapImageData = mapCtx.getImageData(0, 0, mapWidth, mapHeight);
      mapData = mapImageData.data;
    } else {
      // Fallback to procedural if layer context unavailable
      const dispMap = generateProceduralMap(width, height, 'noise', mapScale);
      mapData = dispMap.data;
      mapWidth = width;
      mapHeight = height;
    }
  } else if (mapType !== 'layer') {
    // Generate procedural displacement map
    const dispMap = generateProceduralMap(width, height, mapType, mapScale);
    mapData = dispMap.data;
    mapWidth = width;
    mapHeight = height;
  } else {
    // Layer mode but no canvas provided - use neutral map (no displacement)
    // This allows the effect to be configured before a layer is selected
    const dispMap = generateProceduralMap(width, height, 'radial', mapScale);
    mapData = dispMap.data;
    mapWidth = width;
    mapHeight = height;
  }

  // Create output
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;

      // Apply map behavior to get displacement map coordinates
      const { mapX, mapY } = applyMapBehavior(
        x, y, width, height, mapWidth, mapHeight, mapBehavior
      );

      // If outside map bounds (center mode), no displacement
      if (mapX < 0 || mapY < 0) {
        dst[i] = src[i];
        dst[i + 1] = src[i + 1];
        dst[i + 2] = src[i + 2];
        dst[i + 3] = src[i + 3];
        continue;
      }

      // Bilinear sample the displacement map for smooth results
      const mx0 = Math.floor(mapX);
      const my0 = Math.floor(mapY);
      const mx1 = Math.min(mx0 + 1, mapWidth - 1);
      const my1 = Math.min(my0 + 1, mapHeight - 1);
      const mfx = mapX - mx0;
      const mfy = mapY - my0;

      const mi00 = (my0 * mapWidth + mx0) * 4;
      const mi10 = (my0 * mapWidth + mx1) * 4;
      const mi01 = (my1 * mapWidth + mx0) * 4;
      const mi11 = (my1 * mapWidth + mx1) * 4;

      // Interpolate map values for each channel
      const interpChannel = (channel: number): number => {
        return Math.round(
          mapData[mi00 + channel] * (1 - mfx) * (1 - mfy) +
          mapData[mi10 + channel] * mfx * (1 - mfy) +
          mapData[mi01 + channel] * (1 - mfx) * mfy +
          mapData[mi11 + channel] * mfx * mfy
        );
      };

      const mapR = interpChannel(0);
      const mapG = interpChannel(1);
      const mapB = interpChannel(2);
      const mapA = interpChannel(3);

      // Calculate displacement amounts (map value 128 = no displacement)
      let dx = 0;
      let dy = 0;

      if (useHorizontal !== 'off' && maxHorizontal !== 0) {
        const hValue = getChannelValue(mapR, mapG, mapB, mapA, useHorizontal);
        dx = ((hValue - 128) / 128) * maxHorizontal;
      }

      if (useVertical !== 'off' && maxVertical !== 0) {
        const vValue = getChannelValue(mapR, mapG, mapB, mapA, useVertical);
        dy = ((vValue - 128) / 128) * maxVertical;
      }

      // Calculate source coordinates
      let srcX = x - dx;
      let srcY = y - dy;

      // Handle edge wrapping
      if (wrapMode === 'tiles') {
        srcX = ((srcX % width) + width) % width;
        srcY = ((srcY % height) + height) % height;
      } else if (wrapMode === 'mirror') {
        srcX = Math.abs(srcX);
        srcY = Math.abs(srcY);
        if (Math.floor(srcX / width) % 2 === 1) srcX = width - 1 - (srcX % width);
        else srcX = srcX % width;
        if (Math.floor(srcY / height) % 2 === 1) srcY = height - 1 - (srcY % height);
        else srcY = srcY % height;
      } else {
        // Clamp to edges
        srcX = Math.max(0, Math.min(width - 1, srcX));
        srcY = Math.max(0, Math.min(height - 1, srcY));
      }

      // Bilinear interpolation for smooth results
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;

      const i00 = (y0 * width + x0) * 4;
      const i10 = (y0 * width + x1) * 4;
      const i01 = (y1 * width + x0) * 4;
      const i11 = (y1 * width + x1) * 4;

      // Interpolate each channel
      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];

        dst[i + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) +
          v10 * fx * (1 - fy) +
          v01 * (1 - fx) * fy +
          v11 * fx * fy
        );
      }
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// TURBULENT DISPLACE EFFECT
// Procedural noise-based displacement with multiple displacement types
// ============================================================================

/**
 * Displacement types for Turbulent Displace
 */
type TurbulentDisplaceType =
  | 'turbulent'        // Random organic distortion (default)
  | 'bulge'            // Inflating/deflating effect
  | 'twist'            // Rotational distortion
  | 'turbulent-smoother' // Smoother turbulence
  | 'horizontal'       // X-axis only
  | 'vertical'         // Y-axis only
  | 'cross';           // X and Y linked

/**
 * Pinning options for edge handling
 */
type PinningType = 'none' | 'all' | 'horizontal' | 'vertical';

/**
 * Turbulent Displace effect renderer
 * Generates procedural organic distortion without needing a separate map
 *
 * Parameters:
 * - displacement: TurbulentDisplaceType
 * - amount: 0-1000 (distortion intensity)
 * - size: 1-1000 (scale of turbulence pattern)
 * - complexity: 1-10 (octaves/detail levels)
 * - evolution: angle (0-360°, animatable for motion)
 * - cycle_evolution: boolean (enable seamless looping)
 * - cycle_revolutions: 1-100 (number of revolutions before cycle repeats)
 * - random_seed: 0-99999 (base pattern variation)
 * - offset: { x, y } (turbulence pattern offset)
 * - pinning: PinningType (edge handling)
 */
export function turbulentDisplaceRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  const displacementType = (params.displacement ?? 'turbulent') as TurbulentDisplaceType;
  // BUG-027 FIX: Validate all numeric params to prevent NaN propagation
  const amount = safeNum(params.amount, 50, 0, 1000);
  const size = safeNum(params.size, 100, 1, 1000);
  // Complexity must be integer 1-10, NaN would bypass Math.max/min
  const complexityRaw = safeNum(params.complexity, 3, 1, 10);
  const complexity = Math.floor(complexityRaw);
  const evolutionDeg = safeNum(params.evolution, 0);
  const cycleEvolution = params.cycle_evolution ?? false;
  const cycleRevolutions = safeNum(params.cycle_revolutions, 1, 1, 100);
  const randomSeed = safeNum(params.random_seed, 0, 0, 99999);
  const offsetRaw = params.offset ?? { x: 0, y: 0 };
  const offset = {
    x: safeNum(offsetRaw.x, 0),
    y: safeNum(offsetRaw.y, 0)
  };
  const pinning = (params.pinning ?? 'none') as PinningType;

  // No displacement if amount is 0 (NaN params now safely default)
  if (amount === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  // Get input pixels
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;

  // Calculate evolution phase for animation
  let evolutionPhase = evolutionDeg * Math.PI / 180;
  if (cycleEvolution && cycleRevolutions > 0) {
    // Normalize evolution to [0, 2π * cycleRevolutions] and wrap
    evolutionPhase = (evolutionPhase % (2 * Math.PI * cycleRevolutions));
  }

  // Create noise generator with combined seed
  const effectiveSeed = randomSeed + Math.floor(evolutionPhase * 1000);
  const noise = new SimplexNoise(effectiveSeed);

  // Second noise for evolution animation (different pattern)
  const evolutionNoise = new SimplexNoise(randomSeed + 12345);

  // Precompute center
  const centerX = width / 2;
  const centerY = height / 2;

  // Process each pixel
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      // Calculate pinning factors (1 = full displacement, 0 = pinned)
      let pinFactorH = 1;
      let pinFactorV = 1;

      if (pinning === 'all' || pinning === 'horizontal') {
        // Pin top and bottom edges
        const edgeDist = Math.min(y, height - 1 - y);
        const edgeThreshold = height * 0.1; // 10% from edge
        pinFactorV = Math.min(1, edgeDist / edgeThreshold);
      }

      if (pinning === 'all' || pinning === 'vertical') {
        // Pin left and right edges
        const edgeDist = Math.min(x, width - 1 - x);
        const edgeThreshold = width * 0.1; // 10% from edge
        pinFactorH = Math.min(1, edgeDist / edgeThreshold);
      }

      // Calculate normalized coordinates
      const nx = (x + offset.x) / size;
      const ny = (y + offset.y) / size;

      // Calculate displacement based on type
      let dx = 0;
      let dy = 0;

      switch (displacementType) {
        case 'turbulent': {
          // Multi-octave turbulent noise
          let noiseX = 0;
          let noiseY = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;

          for (let octave = 0; octave < complexity; octave++) {
            // Use evolution phase for time-based variation
            const timeOffset = evolutionPhase * 0.1;
            noiseX += noise.noise2D(nx * frequency + timeOffset, ny * frequency) * amplitude;
            noiseY += noise.noise2D(nx * frequency + 100, ny * frequency + timeOffset) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }

          dx = (noiseX / maxAmp) * amount * pinFactorH;
          dy = (noiseY / maxAmp) * amount * pinFactorV;
          break;
        }

        case 'turbulent-smoother': {
          // Smoother turbulence with fewer octaves and more smoothing
          let noiseX = 0;
          let noiseY = 0;
          let amplitude = 1;
          let frequency = 0.5; // Lower frequency for smoother
          let maxAmp = 0;

          const smoothComplexity = Math.max(1, complexity - 2);
          for (let octave = 0; octave < smoothComplexity; octave++) {
            const timeOffset = evolutionPhase * 0.05;
            noiseX += noise.noise2D(nx * frequency + timeOffset, ny * frequency) * amplitude;
            noiseY += noise.noise2D(nx * frequency + 100, ny * frequency + timeOffset) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.6;
            frequency *= 1.5;
          }

          dx = (noiseX / maxAmp) * amount * pinFactorH;
          dy = (noiseY / maxAmp) * amount * pinFactorV;
          break;
        }

        case 'bulge': {
          // Bulge effect: inflate/deflate based on noise
          const noiseVal = noise.noise2D(nx + evolutionPhase * 0.1, ny);

          // Calculate direction from center
          const fromCenterX = x - centerX;
          const fromCenterY = y - centerY;
          const dist = Math.sqrt(fromCenterX * fromCenterX + fromCenterY * fromCenterY);

          if (dist > 0) {
            const bulgeFactor = noiseVal * (amount / 100) * (1 - dist / Math.max(centerX, centerY));
            dx = (fromCenterX / dist) * bulgeFactor * amount * 0.5 * pinFactorH;
            dy = (fromCenterY / dist) * bulgeFactor * amount * 0.5 * pinFactorV;
          }
          break;
        }

        case 'twist': {
          // Rotational swirl distortion
          const fromCenterX = x - centerX;
          const fromCenterY = y - centerY;
          const dist = Math.sqrt(fromCenterX * fromCenterX + fromCenterY * fromCenterY);
          const maxDist = Math.sqrt(centerX * centerX + centerY * centerY);

          // Noise-based twist angle
          const noiseVal = noise.noise2D(nx + evolutionPhase * 0.1, ny);
          const twistAngle = noiseVal * (amount / 50) * Math.PI * (1 - dist / maxDist);

          const cos = Math.cos(twistAngle);
          const sin = Math.sin(twistAngle);

          dx = ((fromCenterX * cos - fromCenterY * sin) - fromCenterX) * pinFactorH;
          dy = ((fromCenterX * sin + fromCenterY * cos) - fromCenterY) * pinFactorV;
          break;
        }

        case 'horizontal': {
          // Horizontal displacement only
          let noiseX = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;

          for (let octave = 0; octave < complexity; octave++) {
            noiseX += noise.noise2D(nx * frequency + evolutionPhase * 0.1, ny * frequency) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }

          dx = (noiseX / maxAmp) * amount * pinFactorH;
          dy = 0;
          break;
        }

        case 'vertical': {
          // Vertical displacement only
          let noiseY = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;

          for (let octave = 0; octave < complexity; octave++) {
            noiseY += noise.noise2D(nx * frequency + 100, ny * frequency + evolutionPhase * 0.1) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }

          dx = 0;
          dy = (noiseY / maxAmp) * amount * pinFactorV;
          break;
        }

        case 'cross': {
          // Cross displacement: X and Y are linked (same noise value)
          let noiseVal = 0;
          let amplitude = 1;
          let frequency = 1;
          let maxAmp = 0;

          for (let octave = 0; octave < complexity; octave++) {
            noiseVal += noise.noise2D(nx * frequency + evolutionPhase * 0.1, ny * frequency) * amplitude;
            maxAmp += amplitude;
            amplitude *= 0.5;
            frequency *= 2;
          }

          const normalized = noiseVal / maxAmp;
          dx = normalized * amount * pinFactorH;
          dy = normalized * amount * pinFactorV;
          break;
        }
      }

      // Calculate source coordinates
      let srcX = x - dx;
      let srcY = y - dy;

      // Clamp to bounds
      srcX = Math.max(0, Math.min(width - 1, srcX));
      srcY = Math.max(0, Math.min(height - 1, srcY));

      // Bilinear interpolation for smooth results
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;

      const i00 = (y0 * width + x0) * 4;
      const i10 = (y0 * width + x1) * 4;
      const i01 = (y1 * width + x0) * 4;
      const i11 = (y1 * width + x1) * 4;
      const outIdx = (y * width + x) * 4;

      // Interpolate each channel
      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];

        dst[outIdx + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) +
          v10 * fx * (1 - fy) +
          v01 * (1 - fx) * fy +
          v11 * fx * fy
        );
      }
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// RIPPLE DISTORT EFFECT
// Creates expanding ripple distortion from a center point
// ============================================================================

/**
 * Ripple effect renderer
 * Creates concentric wave distortion emanating from a center point
 *
 * Parameters:
 * - center: { x, y } normalized (0-1)
 * - radius: pixels (max radius of effect)
 * - wavelength: pixels (distance between wave peaks)
 * - amplitude: pixels (max displacement)
 * - phase: angle (for animation, 0-360°)
 * - decay: 0-100 (falloff from center)
 */
export function rippleDistortRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams
): EffectStackResult {
  // BUG-028 FIX: Validate all numeric params to prevent NaN propagation
  const centerRaw = params.center ?? { x: 0.5, y: 0.5 };
  const center = {
    x: safeNum(centerRaw.x, 0.5, 0, 1),
    y: safeNum(centerRaw.y, 0.5, 0, 1)
  };
  const radius = safeNum(params.radius, 200, 0, 10000);
  const wavelength = safeNum(params.wavelength, 50, 1, 1000);
  const amplitude = safeNum(params.amplitude, 20, 0, 1000);
  const phaseDeg = safeNum(params.phase, 0);
  const decay = safeNum(params.decay, 50, 0, 100) / 100;

  // No effect if amplitude is 0 (NaN params now safely default)
  if (amplitude === 0) {
    return input;
  }

  const { width, height } = input.canvas;
  const output = createMatchingCanvas(input.canvas);

  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;
  const outputData = output.ctx.createImageData(width, height);
  const dst = outputData.data;

  const centerX = center.x * width;
  const centerY = center.y * height;
  const phase = phaseDeg * Math.PI / 180;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dx = x - centerX;
      const dy = y - centerY;
      const dist = Math.sqrt(dx * dx + dy * dy);

      let srcX = x;
      let srcY = y;

      if (dist > 0 && dist < radius) {
        // Calculate ripple displacement
        const ripple = Math.sin((dist / wavelength) * 2 * Math.PI + phase);

        // Apply decay from center
        const falloff = Math.pow(1 - dist / radius, decay);
        const displacement = ripple * amplitude * falloff;

        // Displace radially
        const nx = dx / dist;
        const ny = dy / dist;
        srcX = x - nx * displacement;
        srcY = y - ny * displacement;
      }

      // Clamp to bounds
      srcX = Math.max(0, Math.min(width - 1, srcX));
      srcY = Math.max(0, Math.min(height - 1, srcY));

      // Bilinear interpolation
      const x0 = Math.floor(srcX);
      const y0 = Math.floor(srcY);
      const x1 = Math.min(x0 + 1, width - 1);
      const y1 = Math.min(y0 + 1, height - 1);
      const fx = srcX - x0;
      const fy = srcY - y0;

      const i00 = (y0 * width + x0) * 4;
      const i10 = (y0 * width + x1) * 4;
      const i01 = (y1 * width + x0) * 4;
      const i11 = (y1 * width + x1) * 4;
      const outIdx = (y * width + x) * 4;

      for (let c = 0; c < 4; c++) {
        const v00 = src[i00 + c];
        const v10 = src[i10 + c];
        const v01 = src[i01 + c];
        const v11 = src[i11 + c];

        dst[outIdx + c] = Math.round(
          v00 * (1 - fx) * (1 - fy) +
          v10 * fx * (1 - fy) +
          v01 * (1 - fx) * fy +
          v11 * fx * fy
        );
      }
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register all distort effect renderers
 */
export function registerDistortEffects(): void {
  registerEffectRenderer('transform', transformRenderer);
  registerEffectRenderer('warp', warpRenderer);
  registerEffectRenderer('displacement-map', displacementMapRenderer);
  registerEffectRenderer('turbulent-displace', turbulentDisplaceRenderer);
  registerEffectRenderer('ripple-distort', rippleDistortRenderer);
}

export default {
  transformRenderer,
  warpRenderer,
  displacementMapRenderer,
  turbulentDisplaceRenderer,
  rippleDistortRenderer,
  registerDistortEffects
};
