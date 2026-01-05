/**
 * Procedural Mask Generator
 *
 * Generates binary masks with various geometric shapes for compositing workflows.
 * Ported from Saber (https://github.com/franciszzj/Saber) mask_generator_and_augmentation.py
 *
 * Shape families:
 * - ellipse: Standard rounded shapes
 * - superellipse: Lamé curves / squircle (rounded rectangles)
 * - fourier: Organic, often-concave blobs via radial Fourier decomposition
 * - concavePolygon: Irregular shapes with uneven angles and local dents
 * - centeredRectangle: Axis-aligned boxes with rough edges
 */

export type MaskShapeType =
  | "ellipse"
  | "superellipse"
  | "fourier"
  | "concavePolygon"
  | "centeredRectangle";

export interface MaskGeneratorOptions {
  width: number;
  height: number;
  areaRatioRange?: [number, number];
  shapeTypes?: MaskShapeType[];
  seed?: number;
}

export interface AffineTransformParams {
  hflip: boolean;
  angle: number;
  scale: number;
  shear: [number, number];
  translate: [number, number];
  center: [number, number];
}

// Seeded random number generator (Mulberry32)
function createRng(seed: number) {
  let state = seed;
  return {
    random(): number {
      state |= 0;
      state = (state + 0x6d2b79f5) | 0;
      let t = Math.imul(state ^ (state >>> 15), 1 | state);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    },
    uniform(min: number, max: number): number {
      return min + this.random() * (max - min);
    },
    integers(min: number, max: number): number {
      return Math.floor(this.uniform(min, max));
    },
    normal(mean: number = 0, std: number = 1): number {
      // Box-Muller transform
      const u1 = this.random();
      const u2 = this.random();
      const z = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
      return mean + std * z;
    },
    gamma(shape: number, scale: number = 1): number {
      // Marsaglia and Tsang's method for shape >= 1
      if (shape < 1) {
        return this.gamma(shape + 1, scale) * this.random() ** (1 / shape);
      }
      const d = shape - 1 / 3;
      const c = 1 / Math.sqrt(9 * d);
      while (true) {
        let x: number, v: number;
        do {
          x = this.normal();
          v = 1 + c * x;
        } while (v <= 0);
        v = v * v * v;
        const u = this.random();
        if (u < 1 - 0.0331 * (x * x) * (x * x)) return d * v * scale;
        if (Math.log(u) < 0.5 * x * x + d * (1 - v + Math.log(v)))
          return d * v * scale;
      }
    },
    choice<T>(arr: T[]): T {
      return arr[Math.floor(this.random() * arr.length)];
    },
    choiceMultiple<T>(arr: T[], count: number): T[] {
      const result: T[] = [];
      const copy = [...arr];
      for (let i = 0; i < count && copy.length > 0; i++) {
        const idx = Math.floor(this.random() * copy.length);
        result.push(copy.splice(idx, 1)[0]);
      }
      return result;
    },
  };
}

/**
 * Generate a binary mask with a single connected component
 */
export function generateMask(options: MaskGeneratorOptions): Uint8Array {
  const {
    width,
    height,
    areaRatioRange = [0.1, 0.5],
    shapeTypes,
    seed = Date.now(),
  } = options;

  const rng = createRng(seed);
  const N = width * height;

  // Sanitize area range
  let [lo, hi] = areaRatioRange;
  lo = Math.max(0, Math.min(1, lo));
  hi = Math.max(lo, Math.min(1, hi));
  let A_lo = Math.ceil(lo * N);
  let A_hi = Math.floor(hi * N);
  if (A_lo > A_hi) {
    A_lo = Math.min(A_lo, N);
    A_hi = Math.max(A_lo, A_lo);
  }

  const families: MaskShapeType[] = [
    "ellipse",
    "superellipse",
    "fourier",
    "concavePolygon",
    "centeredRectangle",
  ];
  const family = shapeTypes
    ? rng.choice(shapeTypes.filter((s) => families.includes(s)) || families)
    : rng.choice(families);

  const minDim = Math.min(width, height);
  const MIN_R = Math.max(2, 0.01 * minDim);

  function sampleCenter(marginScale = 0.1): [number, number] {
    const my = Math.max(1, Math.round(marginScale * height));
    const mx = Math.max(1, Math.round(marginScale * width));
    const cy = rng.integers(my, Math.max(my + 1, height - my));
    const cx = rng.integers(mx, Math.max(mx + 1, width - mx));
    return [cy, cx];
  }

  // Create mask array
  function createMaskArray(): Uint8Array {
    return new Uint8Array(width * height);
  }

  // Get pixel at (y, x)
  function getPixel(mask: Uint8Array, y: number, x: number): number {
    if (y < 0 || y >= height || x < 0 || x >= width) return 0;
    return mask[y * width + x];
  }

  // Set pixel at (y, x)
  function setPixel(
    mask: Uint8Array,
    y: number,
    x: number,
    value: number,
  ): void {
    if (y >= 0 && y < height && x >= 0 && x < width) {
      mask[y * width + x] = value;
    }
  }

  // Count mask area
  function countArea(mask: Uint8Array): number {
    let count = 0;
    for (let i = 0; i < mask.length; i++) {
      if (mask[i]) count++;
    }
    return count;
  }

  // Get 8-neighbor count
  function neighborCount(mask: Uint8Array, y: number, x: number): number {
    let count = 0;
    for (let dy = -1; dy <= 1; dy++) {
      for (let dx = -1; dx <= 1; dx++) {
        if (dy === 0 && dx === 0) continue;
        if (getPixel(mask, y + dy, x + dx)) count++;
      }
    }
    return count;
  }

  // Check if a pixel is a simple point (can be removed without breaking connectivity)
  function isSimplePoint(mask: Uint8Array, y: number, x: number): boolean {
    if (!getPixel(mask, y, x)) return false;

    const ncnt = neighborCount(mask, y, x);
    if (ncnt < 2 || ncnt > 6) return false;

    // Get 8-neighbors in clockwise order
    const neighbors = [
      getPixel(mask, y - 1, x), // N
      getPixel(mask, y - 1, x + 1), // NE
      getPixel(mask, y, x + 1), // E
      getPixel(mask, y + 1, x + 1), // SE
      getPixel(mask, y + 1, x), // S
      getPixel(mask, y + 1, x - 1), // SW
      getPixel(mask, y, x - 1), // W
      getPixel(mask, y - 1, x - 1), // NW
    ];

    // Count 0->1 transitions
    let transitions = 0;
    for (let i = 0; i < 8; i++) {
      if (!neighbors[i] && neighbors[(i + 1) % 8]) transitions++;
    }

    return transitions === 1;
  }

  // Grow mask to target area
  function growTo(mask: Uint8Array, targetArea: number): Uint8Array {
    const result = new Uint8Array(mask);
    let current = countArea(result);

    while (current < targetArea) {
      const candidates: number[] = [];
      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          if (!getPixel(result, y, x) && neighborCount(result, y, x) > 0) {
            candidates.push(y * width + x);
          }
        }
      }

      if (candidates.length === 0) break;

      const need = targetArea - current;
      const take =
        candidates.length <= need
          ? candidates
          : rng.choiceMultiple(candidates, need);

      for (const idx of take) {
        result[idx] = 1;
      }
      current += take.length;
    }

    return result;
  }

  // Shrink mask to target area
  function shrinkTo(mask: Uint8Array, targetArea: number): Uint8Array {
    const result = new Uint8Array(mask);
    let current = countArea(result);

    while (current > targetArea) {
      const simplePoints: number[] = [];
      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          if (isSimplePoint(result, y, x)) {
            simplePoints.push(y * width + x);
          }
        }
      }

      if (simplePoints.length === 0) break;

      const need = current - targetArea;
      const takeCount = Math.min(
        need,
        Math.max(32, Math.floor(simplePoints.length / 2)),
      );
      const take = rng.choiceMultiple(simplePoints, takeCount);

      for (const idx of take) {
        result[idx] = 0;
      }
      current -= take.length;
    }

    return result;
  }

  // Shape generators
  function ellipseMaskFn(): (scale: number) => Uint8Array {
    const [cy, cx] = sampleCenter(0.1);
    const ar = rng.uniform(0.5, 2.0);
    const ry0 = Math.max(MIN_R, rng.uniform(0.15, 0.35) * height);
    const rx0 = Math.max(MIN_R, ar * ry0);

    return (scale: number) => {
      const ry = Math.max(MIN_R, ry0 * scale);
      const rx = Math.max(MIN_R, rx0 * scale);
      const mask = createMaskArray();

      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const v = ((y - cy) / ry) ** 2 + ((x - cx) / rx) ** 2;
          if (v <= 1.0) setPixel(mask, y, x, 1);
        }
      }
      return mask;
    };
  }

  function superellipseMaskFn(): (scale: number) => Uint8Array {
    const [cy, cx] = sampleCenter(0.12);
    const n = rng.uniform(2.2, 6.0);
    const ar = rng.uniform(0.6, 1.7);
    const b0 = Math.max(MIN_R, rng.uniform(0.12, 0.3) * height);
    const a0 = Math.max(MIN_R, ar * b0);

    return (scale: number) => {
      const a = Math.max(MIN_R, a0 * scale);
      const b = Math.max(MIN_R, b0 * scale);
      const mask = createMaskArray();

      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const v = Math.abs((x - cx) / a) ** n + Math.abs((y - cy) / b) ** n;
          if (v <= 1.0) setPixel(mask, y, x, 1);
        }
      }
      return mask;
    };
  }

  function fourierMaskFn(): (scale: number) => Uint8Array {
    const [cy, cx] = sampleCenter(0.12);
    const K = rng.integers(3, 7);

    // Precompute coefficients
    const a: number[] = [];
    const b: number[] = [];
    for (let k = 0; k < K; k++) {
      const decay = 1.0 / (1.0 + k + 1);
      a.push(rng.normal(0, 0.25) * decay);
      b.push(rng.normal(0, 0.25) * decay);
    }
    const c0 = 1.0 + Math.abs(rng.normal(0, 0.15));

    // Precompute R0 for each pixel
    const R0 = new Float32Array(width * height);
    let minR0 = Infinity;

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const dy = y - cy;
        const dx = x - cx;
        const theta = Math.atan2(dy, dx);

        let r = c0;
        for (let k = 1; k <= K; k++) {
          r += a[k - 1] * Math.cos(k * theta) + b[k - 1] * Math.sin(k * theta);
        }
        R0[y * width + x] = r;
        if (r < minR0) minR0 = r;
      }
    }

    // Normalize R0
    const baseSize = Math.sqrt((height * width) / Math.PI) * 0.25;
    for (let i = 0; i < R0.length; i++) {
      R0[i] = (R0[i] - minR0 + 0.2) * baseSize;
    }

    return (scale: number) => {
      const mask = createMaskArray();

      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const dy = y - cy;
          const dx = x - cx;
          const rho = Math.sqrt(dy * dy + dx * dx);
          const R = R0[y * width + x] * scale;
          if (rho <= R) setPixel(mask, y, x, 1);
        }
      }
      return mask;
    };
  }

  function concavePolygonMaskFn(): (scale: number) => Uint8Array {
    const [cy, cx] = sampleCenter(0.12);
    const Nv = rng.integers(28, 64);

    // Uneven angles via random gaps
    const gaps: number[] = [];
    let gapSum = 0;
    for (let i = 0; i < Nv; i++) {
      const g = rng.gamma(1.4, 1.0);
      gaps.push(g);
      gapSum += g;
    }

    let angles: number[] = [];
    let cumSum = 0;
    for (let i = 0; i < Nv; i++) {
      cumSum += gaps[i];
      angles.push(
        (2 * Math.PI * cumSum) / gapSum + rng.uniform(0, 2 * Math.PI),
      );
    }
    angles = angles.map(
      (a) => ((a % (2 * Math.PI)) + 2 * Math.PI) % (2 * Math.PI),
    );
    angles.sort((a, b) => a - b);

    // Base radius
    const baseR = Math.sqrt(Math.max((A_lo + A_hi) / 2, 1) / Math.PI);

    // Smooth random variation
    let noise = angles.map(() => rng.normal(0, 0.18));
    for (let iter = 0; iter < 2; iter++) {
      const smoothed = noise.map((n, i) => {
        const prev = noise[(i - 1 + Nv) % Nv];
        const next = noise[(i + 1) % Nv];
        return 0.25 * prev + 0.5 * n + 0.25 * next;
      });
      noise = smoothed;
    }

    // Localized dents
    const M = rng.integers(2, 5);
    const dentCenters = Array.from({ length: M }, () =>
      rng.uniform(0, 2 * Math.PI),
    );
    const dentWidths = Array.from({ length: M }, () => rng.uniform(0.1, 0.35));
    const dentDepths = Array.from({ length: M }, () => rng.uniform(0.18, 0.42));

    const dentFactor = angles.map((angle, _i) => {
      let dent = 0;
      for (let m = 0; m < M; m++) {
        let dtheta = angle - dentCenters[m];
        dtheta = Math.atan2(Math.sin(dtheta), Math.cos(dtheta));
        dent += Math.exp(-0.5 * (dtheta / dentWidths[m]) ** 2) * dentDepths[m];
      }
      return Math.max(0.25, Math.min(1.6, 1.0 - dent));
    });

    const radii0 = angles.map((_, i) => {
      return Math.max(MIN_R + 1, baseR * (1.0 + noise[i]) * dentFactor[i]);
    });

    return (scale: number) => {
      const mask = createMaskArray();

      // Generate polygon vertices
      const pts: [number, number][] = radii0.map((r, i) => {
        const scaledR = r * scale;
        const px = Math.round(cx + scaledR * Math.cos(angles[i]));
        const py = Math.round(cy + scaledR * Math.sin(angles[i]));
        return [
          Math.max(1, Math.min(width - 2, px)),
          Math.max(1, Math.min(height - 2, py)),
        ];
      });

      // Fill polygon using scanline algorithm
      fillPolygon(mask, pts, width, height);
      return mask;
    };
  }

  function centeredRectangleMaskFn(): (scale: number) => Uint8Array {
    const cy = Math.floor(height / 2);
    const cx = Math.floor(width / 2);
    const ar = rng.uniform(0.6, 1.7);
    const sy0 = Math.max(MIN_R, rng.uniform(0.12, 0.3) * height);
    const sx0 = Math.max(MIN_R, ar * sy0);

    const roughAmpX = rng.uniform(0.5, 3.0);
    const roughAmpY = rng.uniform(0.5, 3.0);

    // Generate smooth 1D noise
    function smoothNoise1D(n: number, amp: number): Float32Array {
      const v = new Float32Array(n);
      for (let i = 0; i < n; i++) v[i] = rng.normal();

      // Simple smoothing
      for (let iter = 0; iter < 2; iter++) {
        const smoothed = new Float32Array(n);
        for (let i = 0; i < n; i++) {
          const prev = v[(i - 1 + n) % n];
          const curr = v[i];
          const next = v[(i + 1) % n];
          smoothed[i] = 0.25 * prev + 0.5 * curr + 0.25 * next;
        }
        for (let i = 0; i < n; i++) v[i] = smoothed[i];
      }

      // Normalize and scale
      let std = 0;
      for (let i = 0; i < n; i++) std += v[i] * v[i];
      std = Math.sqrt(std / n) + 1e-6;
      for (let i = 0; i < n; i++) v[i] = (v[i] / std) * amp;

      return v;
    }

    const jitterTop = smoothNoise1D(width, roughAmpY);
    const jitterBot = smoothNoise1D(width, roughAmpY);
    const jitterLeft = smoothNoise1D(height, roughAmpX);
    const jitterRight = smoothNoise1D(height, roughAmpX);

    return (scale: number) => {
      const mask = createMaskArray();
      const sy = Math.max(MIN_R, sy0 * scale);
      const sx = Math.max(MIN_R, sx0 * scale);

      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          const yTop = Math.floor(cy - sy + jitterTop[x]);
          const yBot = Math.ceil(cy + sy + jitterBot[x]);
          const xLeft = Math.floor(cx - sx + jitterLeft[y]);
          const xRight = Math.ceil(cx + sx + jitterRight[y]);

          if (y >= yTop && y <= yBot && x >= xLeft && x <= xRight) {
            setPixel(mask, y, x, 1);
          }
        }
      }
      return mask;
    };
  }

  // Polygon fill helper (scanline algorithm)
  function fillPolygon(
    mask: Uint8Array,
    vertices: [number, number][],
    w: number,
    h: number,
  ): void {
    if (vertices.length < 3) return;

    // Find bounding box
    let minY = h,
      maxY = 0;
    for (const [_x, y] of vertices) {
      if (y < minY) minY = y;
      if (y > maxY) maxY = y;
    }
    minY = Math.max(0, minY);
    maxY = Math.min(h - 1, maxY);

    // Scanline fill
    for (let y = minY; y <= maxY; y++) {
      const intersections: number[] = [];

      for (let i = 0; i < vertices.length; i++) {
        const [x1, y1] = vertices[i];
        const [x2, y2] = vertices[(i + 1) % vertices.length];

        if ((y1 <= y && y2 > y) || (y2 <= y && y1 > y)) {
          const x = x1 + ((y - y1) / (y2 - y1)) * (x2 - x1);
          intersections.push(x);
        }
      }

      intersections.sort((a, b) => a - b);

      for (let i = 0; i < intersections.length - 1; i += 2) {
        const xStart = Math.max(0, Math.ceil(intersections[i]));
        const xEnd = Math.min(w - 1, Math.floor(intersections[i + 1]));
        for (let x = xStart; x <= xEnd; x++) {
          mask[y * w + x] = 1;
        }
      }
    }
  }

  // Binary search for scale
  function findScaleInRange(maskFn: (scale: number) => Uint8Array): {
    mask: Uint8Array;
    area: number;
    hit: boolean;
  } {
    let sLo = 0,
      aLo = 0;
    let sHi = 1.0;
    let mHi = maskFn(sHi);
    let aHi = countArea(mHi);

    // Expand upper bound if needed
    let tries = 0;
    while (aHi < A_lo && tries < 32) {
      sLo = sHi;
      aLo = aHi;
      sHi *= 2.0;
      mHi = maskFn(sHi);
      aHi = countArea(mHi);
      tries++;
    }

    if (A_lo <= aHi && aHi <= A_hi) {
      return { mask: mHi, area: aHi, hit: true };
    }

    // Bisection
    for (let iter = 0; iter < 48; iter++) {
      const sMid = 0.5 * (sLo + sHi);
      const mMid = maskFn(sMid);
      const aMid = countArea(mMid);

      if (A_lo <= aMid && aMid <= A_hi) {
        return { mask: mMid, area: aMid, hit: true };
      }

      if (aMid < A_lo) {
        sLo = sMid;
        aLo = aMid;
      } else {
        sHi = sMid;
        mHi = mMid;
        aHi = aMid;
      }
    }

    // Return closest
    const distLo = Math.min(Math.abs(aLo - A_lo), Math.abs(aLo - A_hi));
    const distHi = Math.min(Math.abs(aHi - A_lo), Math.abs(aHi - A_hi));

    if (distLo < distHi) {
      return { mask: maskFn(sLo), area: aLo, hit: A_lo <= aLo && aLo <= A_hi };
    }
    return { mask: mHi, area: aHi, hit: A_lo <= aHi && aHi <= A_hi };
  }

  // Select shape family and create mask function
  let maskFn: (scale: number) => Uint8Array;
  switch (family) {
    case "ellipse":
      maskFn = ellipseMaskFn();
      break;
    case "superellipse":
      maskFn = superellipseMaskFn();
      break;
    case "fourier":
      maskFn = fourierMaskFn();
      break;
    case "centeredRectangle":
      maskFn = centeredRectangleMaskFn();
      break;
    default:
      maskFn = concavePolygonMaskFn();
      break;
  }

  // Find scale and generate mask
  let { mask, area, hit } = findScaleInRange(maskFn);

  // Adjust if needed
  if (area < A_lo) {
    mask = growTo(mask, A_lo);
  } else if (area > A_hi) {
    mask = shrinkTo(mask, A_hi);
  }

  return mask;
}

/**
 * Convert mask array to ImageData for canvas rendering
 */
export function maskToImageData(
  mask: Uint8Array,
  width: number,
  height: number,
  foregroundColor: [number, number, number, number] = [255, 255, 255, 255],
  backgroundColor: [number, number, number, number] = [0, 0, 0, 255],
): ImageData {
  const imageData = new ImageData(width, height);
  const data = imageData.data;

  for (let i = 0; i < mask.length; i++) {
    const color = mask[i] ? foregroundColor : backgroundColor;
    const idx = i * 4;
    data[idx] = color[0];
    data[idx + 1] = color[1];
    data[idx + 2] = color[2];
    data[idx + 3] = color[3];
  }

  return imageData;
}

/**
 * Convert mask to canvas for preview
 */
export function maskToCanvas(
  mask: Uint8Array,
  width: number,
  height: number,
): HTMLCanvasElement {
  const canvas = document.createElement("canvas");
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext("2d")!;
  const imageData = maskToImageData(mask, width, height);
  ctx.putImageData(imageData, 0, 0);
  return canvas;
}

/**
 * Export mask as PNG data URL
 */
export function maskToDataURL(
  mask: Uint8Array,
  width: number,
  height: number,
): string {
  return maskToCanvas(mask, width, height).toDataURL("image/png");
}

/**
 * Generate multiple masks for a frame sequence
 */
export function generateMaskSequence(
  width: number,
  height: number,
  frameCount: number,
  options?: Partial<MaskGeneratorOptions>,
): Uint8Array[] {
  const masks: Uint8Array[] = [];
  const baseSeed = options?.seed ?? Date.now();

  for (let i = 0; i < frameCount; i++) {
    masks.push(
      generateMask({
        width,
        height,
        ...options,
        seed: baseSeed + i,
      }),
    );
  }

  return masks;
}
