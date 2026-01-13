/**
 * Stylize Effect Renderers
 *
 * Implements creative/artistic effects:
 * - Pixel Sort (saturation-based sorting)
 * - Glitch (digital corruption effect)
 * - VHS (tape distortion)
 * - RGB Split (chromatic aberration)
 * - Scanlines (CRT effect)
 * - Halftone (print dot pattern)
 * - Dither (ordered/Floyd-Steinberg)
 * - Ripple (water distortion)
 * - Emboss (relief effect)
 * - Find Edges (edge detection)
 * - Mosaic (pixelation)
 *
 * Inspired by filliptm's ComfyUI_Fill-Nodes
 * Attribution: https://github.com/filliptm/ComfyUI_Fill-Nodes
 */
import {
  createMatchingCanvas,
  type EffectStackResult,
  type EvaluatedEffectParams,
  registerEffectRenderer,
} from "../effectProcessor";
import { SeededRandom } from "../particleSystem";

// ============================================================================
// PIXEL SORT
// ============================================================================

/**
 * Pixel Sort effect - sorts pixels by saturation within intervals
 *
 * Parameters:
 * - direction: 'horizontal' | 'vertical'
 * - threshold: 0-1 (edge detection threshold)
 * - smoothing: 0-1 (interval boundary smoothness)
 * - sort_by: 'saturation' | 'brightness' | 'hue'
 * - reverse: boolean
 */
export function pixelSortRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const direction = params.direction ?? "horizontal";
  // Validate numeric params (NaN causes visual corruption)
  const rawThreshold = params.threshold ?? 0.25;
  const threshold = Number.isFinite(rawThreshold) ? rawThreshold : 0.25;
  const rawSmoothing = params.smoothing ?? 0.1;
  const smoothing = Number.isFinite(rawSmoothing) ? rawSmoothing : 0.1;
  const sortBy = params.sort_by ?? "saturation";
  const reverse = params.reverse ?? false;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const imageData = input.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;

  // Helper: get pixel value for sorting
  const getSortValue = (r: number, g: number, b: number): number => {
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);

    switch (sortBy) {
      case "brightness":
        return (r + g + b) / 3;
      case "hue": {
        if (max === min) return 0;
        let h = 0;
        if (max === r) h = (g - b) / (max - min);
        else if (max === g) h = 2 + (b - r) / (max - min);
        else h = 4 + (r - g) / (max - min);
        return (h * 60 + 360) % 360;
      }
      default: {
        const l = (max + min) / 2;
        if (max === min) return 0;
        return l > 0.5
          ? (max - min) / (2 - max - min)
          : (max - min) / (max + min);
      }
    }
  };

  const isVertical = direction === "vertical";
  const outerSize = isVertical ? width : height;
  const innerSize = isVertical ? height : width;

  for (let outer = 0; outer < outerSize; outer++) {
    // Collect pixels for this row/column
    const pixels: Array<{
      r: number;
      g: number;
      b: number;
      a: number;
      sortVal: number;
    }> = [];

    for (let inner = 0; inner < innerSize; inner++) {
      const x = isVertical ? outer : inner;
      const y = isVertical ? inner : outer;
      const idx = (y * width + x) * 4;

      const r = data[idx] / 255;
      const g = data[idx + 1] / 255;
      const b = data[idx + 2] / 255;
      const a = data[idx + 3];

      pixels.push({
        r: data[idx],
        g: data[idx + 1],
        b: data[idx + 2],
        a,
        sortVal: getSortValue(r, g, b),
      });
    }

    // Find intervals based on threshold
    const intervals: Array<{ start: number; end: number }> = [];
    let intervalStart = 0;

    for (let i = 1; i < pixels.length; i++) {
      const diff = Math.abs(pixels[i].sortVal - pixels[i - 1].sortVal);
      if (diff > threshold * (1 - smoothing)) {
        if (i > intervalStart + 1) {
          intervals.push({ start: intervalStart, end: i });
        }
        intervalStart = i;
      }
    }
    if (intervalStart < pixels.length - 1) {
      intervals.push({ start: intervalStart, end: pixels.length });
    }

    // Sort each interval
    for (const interval of intervals) {
      const segment = pixels.slice(interval.start, interval.end);
      segment.sort((a, b) =>
        reverse ? b.sortVal - a.sortVal : a.sortVal - b.sortVal,
      );

      for (let i = 0; i < segment.length; i++) {
        pixels[interval.start + i] = segment[i];
      }
    }

    // Write back sorted pixels
    for (let inner = 0; inner < innerSize; inner++) {
      const x = isVertical ? outer : inner;
      const y = isVertical ? inner : outer;
      const idx = (y * width + x) * 4;

      data[idx] = pixels[inner].r;
      data[idx + 1] = pixels[inner].g;
      data[idx + 2] = pixels[inner].b;
      data[idx + 3] = pixels[inner].a;
    }
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// GLITCH
// ============================================================================

/**
 * Glitch effect - digital corruption/distortion
 *
 * Parameters:
 * - glitch_amount: 0-10 (intensity)
 * - color_offset: boolean (RGB channel displacement)
 * - block_size: 1-50 (glitch block height)
 * - seed: random seed for determinism
 * - scanlines: boolean (add scanline artifacts)
 */
export function glitchRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
  frame?: number,
): EffectStackResult {
  // Validate numeric params (NaN causes visual corruption and bypasses === 0 check)
  const rawGlitchAmount = params.glitch_amount ?? 5;
  const glitchAmount = Number.isFinite(rawGlitchAmount) ? rawGlitchAmount : 5;
  const colorOffset = params.color_offset ?? true;
  const rawBlockSize = params.block_size ?? 8;
  const blockSize = Number.isFinite(rawBlockSize)
    ? Math.max(1, rawBlockSize)
    : 8;
  const rawSeed = params.seed ?? 12345;
  const seed = Number.isFinite(rawSeed) ? rawSeed : 12345;
  const scanlines = params.scanlines ?? true;

  if (glitchAmount === 0) return input;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;

  // Start by copying original
  output.ctx.drawImage(input.canvas, 0, 0);

  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;

  const rng = new SeededRandom(seed + (frame ?? 0));

  // Horizontal block shifts
  const numBlocks = Math.floor(glitchAmount * 3);
  for (let b = 0; b < numBlocks; b++) {
    const y = Math.floor(rng.next() * height);
    const blockHeight = Math.floor(rng.next() * blockSize) + 1;
    const shift = Math.floor((rng.next() - 0.5) * glitchAmount * 20);

    for (let row = y; row < Math.min(y + blockHeight, height); row++) {
      const rowData: number[] = [];

      // Copy row
      for (let x = 0; x < width; x++) {
        const idx = (row * width + x) * 4;
        rowData.push(data[idx], data[idx + 1], data[idx + 2], data[idx + 3]);
      }

      // Shift row
      for (let x = 0; x < width; x++) {
        const srcX = (((x - shift) % width) + width) % width;
        const dstIdx = (row * width + x) * 4;
        const srcIdx = srcX * 4;

        data[dstIdx] = rowData[srcIdx];
        data[dstIdx + 1] = rowData[srcIdx + 1];
        data[dstIdx + 2] = rowData[srcIdx + 2];
        data[dstIdx + 3] = rowData[srcIdx + 3];
      }
    }
  }

  // Color channel offset (chromatic aberration style)
  if (colorOffset) {
    const offsetX = Math.floor(glitchAmount * 2);
    const outputData = new Uint8ClampedArray(data.length);

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;

        // Red channel shifted left
        const redX = Math.max(0, Math.min(width - 1, x - offsetX));
        const redIdx = (y * width + redX) * 4;
        outputData[idx] = data[redIdx];

        // Green channel stays
        outputData[idx + 1] = data[idx + 1];

        // Blue channel shifted right
        const blueX = Math.max(0, Math.min(width - 1, x + offsetX));
        const blueIdx = (y * width + blueX) * 4;
        outputData[idx + 2] = data[blueIdx + 2];

        outputData[idx + 3] = data[idx + 3];
      }
    }

    for (let i = 0; i < data.length; i++) {
      data[i] = outputData[i];
    }
  }

  // Scanline artifacts
  if (scanlines) {
    for (let y = 0; y < height; y += 2) {
      if (rng.next() > 0.7) {
        for (let x = 0; x < width; x++) {
          const idx = (y * width + x) * 4;
          data[idx] = Math.min(255, data[idx] * 1.1);
          data[idx + 1] = Math.min(255, data[idx + 1] * 1.1);
          data[idx + 2] = Math.min(255, data[idx + 2] * 1.1);
        }
      }
    }
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// VHS
// ============================================================================

/**
 * VHS effect - tape distortion simulation
 *
 * Parameters:
 * - tracking: 0-1 (horizontal jitter)
 * - noise: 0-1 (static noise amount)
 * - color_bleed: 0-20 (color bleeding/smearing)
 * - jitter: 0-5 (vertical jitter)
 * - rolling_bands: boolean (rolling horizontal bands)
 */
export function vhsRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
  frame?: number,
): EffectStackResult {
  const tracking = params.tracking ?? 0.5;
  const noise = params.noise ?? 0.3;
  const colorBleed = params.color_bleed ?? 3;
  const jitter = params.jitter ?? 0.5;
  const rollingBands = params.rolling_bands ?? true;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;

  output.ctx.drawImage(input.canvas, 0, 0);

  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;

  const rng = new SeededRandom(12345 + (frame ?? 0));

  // Color bleeding (smear horizontally)
  if (colorBleed > 0) {
    for (let y = 0; y < height; y++) {
      for (let x = colorBleed; x < width; x++) {
        const idx = (y * width + x) * 4;
        const prevIdx = (y * width + (x - colorBleed)) * 4;

        // Bleed red channel
        data[idx] = Math.floor(data[idx] * 0.7 + data[prevIdx] * 0.3);
      }
    }
  }

  // Tracking lines (horizontal displacement)
  if (tracking > 0) {
    const numLines = Math.floor(tracking * 20);
    for (let i = 0; i < numLines; i++) {
      const y = Math.floor(rng.next() * height);
      const lineHeight = Math.floor(rng.next() * 3) + 1;
      const shift = Math.floor((rng.next() - 0.5) * tracking * 30);

      for (let row = y; row < Math.min(y + lineHeight, height); row++) {
        const rowData: number[] = [];
        for (let x = 0; x < width; x++) {
          const idx = (row * width + x) * 4;
          rowData.push(data[idx], data[idx + 1], data[idx + 2], data[idx + 3]);
        }

        for (let x = 0; x < width; x++) {
          const srcX = (((x - shift) % width) + width) % width;
          const dstIdx = (row * width + x) * 4;
          const srcIdx = srcX * 4;

          data[dstIdx] = rowData[srcIdx];
          data[dstIdx + 1] = rowData[srcIdx + 1];
          data[dstIdx + 2] = rowData[srcIdx + 2];
        }
      }
    }
  }

  // Static noise
  if (noise > 0) {
    for (let i = 0; i < data.length; i += 4) {
      if (rng.next() < noise * 0.1) {
        const noiseVal = Math.floor(rng.next() * 255);
        data[i] = noiseVal;
        data[i + 1] = noiseVal;
        data[i + 2] = noiseVal;
      }
    }
  }

  // Rolling bands
  if (rollingBands && frame !== undefined) {
    const bandY = (frame * 3) % height;
    const bandHeight = 20;

    for (let y = bandY; y < Math.min(bandY + bandHeight, height); y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;
        const factor = 0.7 + ((y - bandY) / bandHeight) * 0.3;
        data[idx] = Math.floor(data[idx] * factor);
        data[idx + 1] = Math.floor(data[idx + 1] * factor);
        data[idx + 2] = Math.floor(data[idx + 2] * factor);
      }
    }
  }

  // Vertical jitter
  if (jitter > 0) {
    const jitterAmount = Math.floor(rng.next() * jitter * 2);
    if (jitterAmount !== 0) {
      const jitteredData = new Uint8ClampedArray(data.length);
      for (let y = 0; y < height; y++) {
        const srcY = Math.max(0, Math.min(height - 1, y + jitterAmount));
        for (let x = 0; x < width; x++) {
          const dstIdx = (y * width + x) * 4;
          const srcIdx = (srcY * width + x) * 4;
          jitteredData[dstIdx] = data[srcIdx];
          jitteredData[dstIdx + 1] = data[srcIdx + 1];
          jitteredData[dstIdx + 2] = data[srcIdx + 2];
          jitteredData[dstIdx + 3] = data[srcIdx + 3];
        }
      }
      for (let i = 0; i < data.length; i++) {
        data[i] = jitteredData[i];
      }
    }
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// RGB SPLIT
// ============================================================================

/**
 * RGB Split effect - chromatic aberration
 *
 * Parameters:
 * - red_offset_x, red_offset_y: -100 to 100
 * - green_offset_x, green_offset_y: -100 to 100
 * - blue_offset_x, blue_offset_y: -100 to 100
 * - blend_mode: 'screen' | 'add' | 'normal'
 */
export function rgbSplitRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const redOffsetX = params.red_offset_x ?? 5;
  const redOffsetY = params.red_offset_y ?? 0;
  const greenOffsetX = params.green_offset_x ?? 0;
  const greenOffsetY = params.green_offset_y ?? 0;
  const blueOffsetX = params.blue_offset_x ?? -5;
  const blueOffsetY = params.blue_offset_y ?? 0;
  const blendMode = params.blend_mode ?? "screen";

  // No offset = no change
  if (
    redOffsetX === 0 &&
    redOffsetY === 0 &&
    greenOffsetX === 0 &&
    greenOffsetY === 0 &&
    blueOffsetX === 0 &&
    blueOffsetY === 0
  ) {
    return input;
  }

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const data = inputData.data;
  const outputData = new Uint8ClampedArray(data.length);

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;

      // Sample each channel from offset position
      const redX = Math.max(0, Math.min(width - 1, x + redOffsetX));
      const redY = Math.max(0, Math.min(height - 1, y + redOffsetY));
      const redIdx = (redY * width + redX) * 4;

      const greenX = Math.max(0, Math.min(width - 1, x + greenOffsetX));
      const greenY = Math.max(0, Math.min(height - 1, y + greenOffsetY));
      const greenIdx = (greenY * width + greenX) * 4;

      const blueX = Math.max(0, Math.min(width - 1, x + blueOffsetX));
      const blueY = Math.max(0, Math.min(height - 1, y + blueOffsetY));
      const blueIdx = (blueY * width + blueX) * 4;

      let r = data[redIdx];
      let g = data[greenIdx + 1];
      let b = data[blueIdx + 2];

      // Apply blend mode
      if (blendMode === "screen") {
        // Screen blend tends to lighten
        r = 255 - ((255 - r) * (255 - data[idx])) / 255;
        g = 255 - ((255 - g) * (255 - data[idx + 1])) / 255;
        b = 255 - ((255 - b) * (255 - data[idx + 2])) / 255;
      } else if (blendMode === "add") {
        r = Math.min(255, r + data[idx] * 0.3);
        g = Math.min(255, g + data[idx + 1] * 0.3);
        b = Math.min(255, b + data[idx + 2] * 0.3);
      }
      // 'normal' mode just uses the offset values directly

      outputData[idx] = r;
      outputData[idx + 1] = g;
      outputData[idx + 2] = b;
      outputData[idx + 3] = data[idx + 3];
    }
  }

  const outputImageData = new ImageData(outputData, width, height);
  output.ctx.putImageData(outputImageData, 0, 0);
  return output;
}

// ============================================================================
// SCANLINES
// ============================================================================

/**
 * Scanlines effect - CRT monitor simulation
 *
 * Parameters:
 * - line_width: 1-20
 * - line_spacing: 1-20
 * - opacity: 0-1
 * - direction: 'horizontal' | 'vertical'
 * - animate: boolean (scroll scanlines)
 */
export function scanlinesRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
  frame?: number,
): EffectStackResult {
  const lineWidth = params.line_width ?? 2;
  const lineSpacing = params.line_spacing ?? 2;
  const opacity = params.opacity ?? 0.3;
  const direction = params.direction ?? "horizontal";
  const animate = params.animate ?? false;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;

  output.ctx.drawImage(input.canvas, 0, 0);

  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;

  const totalWidth = lineWidth + lineSpacing;
  const offset = animate && frame !== undefined ? frame % totalWidth : 0;

  const isHorizontal = direction === "horizontal";
  const outerSize = isHorizontal ? height : width;

  for (let outer = 0; outer < outerSize; outer++) {
    const adjustedPos = (outer + offset) % totalWidth;
    const inLine = adjustedPos < lineWidth;

    if (inLine) {
      const innerSize = isHorizontal ? width : height;
      for (let inner = 0; inner < innerSize; inner++) {
        const x = isHorizontal ? inner : outer;
        const y = isHorizontal ? outer : inner;
        const idx = (y * width + x) * 4;

        data[idx] = Math.floor(data[idx] * (1 - opacity));
        data[idx + 1] = Math.floor(data[idx + 1] * (1 - opacity));
        data[idx + 2] = Math.floor(data[idx + 2] * (1 - opacity));
      }
    }
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// HALFTONE
// ============================================================================

/**
 * Halftone effect - print-style dot pattern
 *
 * Parameters:
 * - dot_size: 2-20 (max dot diameter)
 * - angle: 0-360 (pattern rotation in degrees)
 * - color_mode: 'grayscale' | 'cmyk' | 'rgb'
 */
export function halftoneRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const dotSize = Math.max(2, params.dot_size ?? 6);
  const angle = ((params.angle ?? 45) * Math.PI) / 180;
  const colorMode = params.color_mode ?? "grayscale";

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const data = inputData.data;

  // Clear output (white background for halftone)
  output.ctx.fillStyle = "#ffffff";
  output.ctx.fillRect(0, 0, width, height);

  const cos = Math.cos(angle);
  const sin = Math.sin(angle);

  // Sample grid
  for (let gy = 0; gy < height + dotSize; gy += dotSize) {
    for (let gx = 0; gx < width + dotSize; gx += dotSize) {
      // Rotate sample point
      const cx = gx + dotSize / 2;
      const cy = gy + dotSize / 2;
      const _rx = Math.floor(
        cos * (cx - width / 2) - sin * (cy - height / 2) + width / 2,
      );
      const _ry = Math.floor(
        sin * (cx - width / 2) + cos * (cy - height / 2) + height / 2,
      );

      // Get average color in cell
      let totalR = 0,
        totalG = 0,
        totalB = 0,
        count = 0;
      for (let sy = gy; sy < Math.min(gy + dotSize, height); sy++) {
        for (let sx = gx; sx < Math.min(gx + dotSize, width); sx++) {
          const idx = (sy * width + sx) * 4;
          totalR += data[idx];
          totalG += data[idx + 1];
          totalB += data[idx + 2];
          count++;
        }
      }

      if (count === 0) continue;

      const avgR = totalR / count;
      const avgG = totalG / count;
      const avgB = totalB / count;

      if (colorMode === "grayscale") {
        const brightness = (avgR + avgG + avgB) / 3 / 255;
        const radius = ((1 - brightness) * dotSize) / 2;

        if (radius > 0.5) {
          output.ctx.beginPath();
          output.ctx.arc(cx, cy, radius, 0, Math.PI * 2);
          output.ctx.fillStyle = "#000000";
          output.ctx.fill();
        }
      } else if (colorMode === "rgb") {
        // RGB dots with slight offset
        const offsets = [
          { color: `rgb(${Math.floor(avgR)}, 0, 0)`, dx: -1, dy: 0 },
          { color: `rgb(0, ${Math.floor(avgG)}, 0)`, dx: 0, dy: 1 },
          { color: `rgb(0, 0, ${Math.floor(avgB)})`, dx: 1, dy: 0 },
        ];

        for (const { color, dx, dy } of offsets) {
          const brightness =
            color === offsets[0].color
              ? avgR
              : color === offsets[1].color
                ? avgG
                : avgB;
          const radius = ((brightness / 255) * dotSize) / 3;
          if (radius > 0.3) {
            output.ctx.beginPath();
            output.ctx.arc(cx + dx * 2, cy + dy * 2, radius, 0, Math.PI * 2);
            output.ctx.fillStyle = color;
            output.ctx.globalCompositeOperation = "multiply";
            output.ctx.fill();
            output.ctx.globalCompositeOperation = "source-over";
          }
        }
      } else if (colorMode === "cmyk") {
        // Convert to CMYK
        const r = avgR / 255,
          g = avgG / 255,
          b = avgB / 255;
        const k = 1 - Math.max(r, g, b);
        const c = k < 1 ? (1 - r - k) / (1 - k) : 0;
        const m = k < 1 ? (1 - g - k) / (1 - k) : 0;
        const y = k < 1 ? (1 - b - k) / (1 - k) : 0;

        const cmykColors = [
          { val: c, color: "cyan", angle: 15 },
          { val: m, color: "magenta", angle: 75 },
          { val: y, color: "yellow", angle: 0 },
          { val: k, color: "black", angle: 45 },
        ];

        for (const { val, color, angle: a } of cmykColors) {
          const radius = (val * dotSize) / 2;
          if (radius > 0.3) {
            const da = (a * Math.PI) / 180;
            const dcx = cx + Math.cos(da) * dotSize * 0.1;
            const dcy = cy + Math.sin(da) * dotSize * 0.1;

            output.ctx.beginPath();
            output.ctx.arc(dcx, dcy, radius, 0, Math.PI * 2);
            output.ctx.fillStyle = color;
            output.ctx.globalCompositeOperation = "multiply";
            output.ctx.fill();
            output.ctx.globalCompositeOperation = "source-over";
          }
        }
      }
    }
  }

  return output;
}

// ============================================================================
// DITHER
// ============================================================================

/**
 * Dither effect - reduces color depth with dithering
 *
 * Parameters:
 * - method: 'ordered' | 'floyd_steinberg' | 'atkinson'
 * - levels: 2-256 (color levels per channel)
 * - matrix_size: 2 | 4 | 8 (for ordered dithering)
 */
export function ditherRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const method = params.method ?? "ordered";
  const levels = Math.max(2, Math.min(256, params.levels ?? 4));
  const matrixSize = params.matrix_size ?? 4;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const imageData = input.ctx.getImageData(0, 0, width, height);
  const data = new Float32Array(imageData.data.length);

  // Convert to float for error diffusion
  for (let i = 0; i < imageData.data.length; i++) {
    data[i] = imageData.data[i];
  }

  // Bayer matrices
  const bayer2 = [
    [0, 2],
    [3, 1],
  ];

  const bayer4 = [
    [0, 8, 2, 10],
    [12, 4, 14, 6],
    [3, 11, 1, 9],
    [15, 7, 13, 5],
  ];

  const bayer8 = [
    [0, 32, 8, 40, 2, 34, 10, 42],
    [48, 16, 56, 24, 50, 18, 58, 26],
    [12, 44, 4, 36, 14, 46, 6, 38],
    [60, 28, 52, 20, 62, 30, 54, 22],
    [3, 35, 11, 43, 1, 33, 9, 41],
    [51, 19, 59, 27, 49, 17, 57, 25],
    [15, 47, 7, 39, 13, 45, 5, 37],
    [63, 31, 55, 23, 61, 29, 53, 21],
  ];

  const matrix = matrixSize === 2 ? bayer2 : matrixSize === 8 ? bayer8 : bayer4;
  const matrixMax = matrixSize * matrixSize;

  const quantize = (val: number): number => {
    const step = 255 / (levels - 1);
    return Math.round(val / step) * step;
  };

  if (method === "ordered") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;
        const threshold =
          (matrix[y % matrix.length][x % matrix[0].length] / matrixMax - 0.5) *
          (256 / levels);

        for (let c = 0; c < 3; c++) {
          data[idx + c] = quantize(
            Math.max(0, Math.min(255, data[idx + c] + threshold)),
          );
        }
      }
    }
  } else if (method === "floyd_steinberg") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;

        for (let c = 0; c < 3; c++) {
          const oldVal = data[idx + c];
          const newVal = quantize(oldVal);
          data[idx + c] = newVal;

          const error = oldVal - newVal;

          // Distribute error
          if (x + 1 < width) {
            data[(y * width + x + 1) * 4 + c] += (error * 7) / 16;
          }
          if (y + 1 < height) {
            if (x > 0) {
              data[((y + 1) * width + x - 1) * 4 + c] += (error * 3) / 16;
            }
            data[((y + 1) * width + x) * 4 + c] += (error * 5) / 16;
            if (x + 1 < width) {
              data[((y + 1) * width + x + 1) * 4 + c] += (error * 1) / 16;
            }
          }
        }
      }
    }
  } else if (method === "atkinson") {
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = (y * width + x) * 4;

        for (let c = 0; c < 3; c++) {
          const oldVal = data[idx + c];
          const newVal = quantize(oldVal);
          data[idx + c] = newVal;

          const error = (oldVal - newVal) / 8;

          // Atkinson distribution (only 6/8 of error)
          const offsets = [
            [1, 0],
            [2, 0],
            [-1, 1],
            [0, 1],
            [1, 1],
            [0, 2],
          ];

          for (const [dx, dy] of offsets) {
            const nx = x + dx;
            const ny = y + dy;
            if (nx >= 0 && nx < width && ny < height) {
              data[(ny * width + nx) * 4 + c] += error;
            }
          }
        }
      }
    }
  }

  // Convert back to uint8
  for (let i = 0; i < data.length; i++) {
    imageData.data[i] = Math.max(0, Math.min(255, Math.round(data[i])));
  }

  output.ctx.putImageData(imageData, 0, 0);
  return output;
}

// ============================================================================
// RIPPLE
// ============================================================================

/**
 * Ripple effect - water distortion
 *
 * Parameters:
 * - amplitude: 0-50 (wave height)
 * - wavelength: 10-200 (distance between waves)
 * - phase: 0-360 (wave phase, animate for motion)
 * - center_x, center_y: 0-100 (ripple center as percentage)
 * - decay: 0-1 (how quickly ripples fade from center)
 */
export function rippleRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
  frame?: number,
): EffectStackResult {
  const amplitude = params.amplitude ?? 10;
  const wavelength = params.wavelength ?? 50;
  let phase = params.phase ?? 0;
  const centerX = (params.center_x ?? 50) / 100;
  const centerY = (params.center_y ?? 50) / 100;
  const decay = params.decay ?? 0.5;

  // Animate phase if frame is provided
  if (frame !== undefined && params.animate !== false) {
    phase = (phase + frame * 5) % 360;
  }

  const phaseRad = (phase * Math.PI) / 180;

  if (amplitude === 0) return input;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const srcData = inputData.data;
  const dstData = outputData.data;

  const cx = centerX * width;
  const cy = centerY * height;
  const maxDist = Math.sqrt(width * width + height * height) / 2;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const dx = x - cx;
      const dy = y - cy;
      const dist = Math.sqrt(dx * dx + dy * dy);

      // Calculate displacement
      const decayFactor =
        decay > 0 ? Math.exp((-dist / maxDist) * decay * 5) : 1;
      const wave =
        Math.sin((dist / wavelength) * Math.PI * 2 + phaseRad) *
        amplitude *
        decayFactor;

      // Displace perpendicular to radius (radial ripple)
      const angle = Math.atan2(dy, dx);
      const srcX = Math.round(x + Math.cos(angle) * wave);
      const srcY = Math.round(y + Math.sin(angle) * wave);

      // Clamp to bounds
      const sx = Math.max(0, Math.min(width - 1, srcX));
      const sy = Math.max(0, Math.min(height - 1, srcY));

      const srcIdx = (sy * width + sx) * 4;
      const dstIdx = (y * width + x) * 4;

      dstData[dstIdx] = srcData[srcIdx];
      dstData[dstIdx + 1] = srcData[srcIdx + 1];
      dstData[dstIdx + 2] = srcData[srcIdx + 2];
      dstData[dstIdx + 3] = srcData[srcIdx + 3];
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// EMBOSS
// ============================================================================

/**
 * Emboss effect - relief/raised appearance
 *
 * Parameters:
 * - direction: 0-360 (light direction)
 * - height: 1-10 (emboss depth)
 * - amount: 1-500 (intensity)
 */
export function embossRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const direction = ((params.direction ?? 135) * Math.PI) / 180;
  const height = Math.max(1, params.height ?? 3);
  const amount = params.amount ?? 100;

  const output = createMatchingCanvas(input.canvas);
  const { width, height: h } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, h);
  const outputData = output.ctx.createImageData(width, h);
  const src = inputData.data;
  const dst = outputData.data;

  const dx = Math.round(Math.cos(direction) * height);
  const dy = Math.round(Math.sin(direction) * height);
  const factor = amount / 100;

  for (let y = 0; y < h; y++) {
    for (let x = 0; x < width; x++) {
      const idx = (y * width + x) * 4;

      // Sample current and offset pixels
      const x1 = Math.max(0, Math.min(width - 1, x - dx));
      const y1 = Math.max(0, Math.min(h - 1, y - dy));
      const x2 = Math.max(0, Math.min(width - 1, x + dx));
      const y2 = Math.max(0, Math.min(h - 1, y + dy));

      const idx1 = (y1 * width + x1) * 4;
      const idx2 = (y2 * width + x2) * 4;

      for (let c = 0; c < 3; c++) {
        const diff = (src[idx1 + c] - src[idx2 + c]) * factor;
        dst[idx + c] = Math.max(0, Math.min(255, 128 + diff));
      }
      dst[idx + 3] = src[idx + 3];
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// FIND EDGES
// ============================================================================

/**
 * Find Edges effect - edge detection
 *
 * Parameters:
 * - invert: boolean
 * - blend_with_original: 0-100
 */
export function findEdgesRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const invert = params.invert ?? false;
  const blend = (params.blend_with_original ?? 0) / 100;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const outputData = output.ctx.createImageData(width, height);
  const src = inputData.data;
  const dst = outputData.data;

  // Sobel kernels
  const sobelX = [-1, 0, 1, -2, 0, 2, -1, 0, 1];
  const sobelY = [-1, -2, -1, 0, 0, 0, 1, 2, 1];

  for (let y = 1; y < height - 1; y++) {
    for (let x = 1; x < width - 1; x++) {
      let gxR = 0,
        gyR = 0;
      let gxG = 0,
        gyG = 0;
      let gxB = 0,
        gyB = 0;

      for (let ky = -1; ky <= 1; ky++) {
        for (let kx = -1; kx <= 1; kx++) {
          const idx = ((y + ky) * width + (x + kx)) * 4;
          const ki = (ky + 1) * 3 + (kx + 1);

          gxR += src[idx] * sobelX[ki];
          gyR += src[idx] * sobelY[ki];
          gxG += src[idx + 1] * sobelX[ki];
          gyG += src[idx + 1] * sobelY[ki];
          gxB += src[idx + 2] * sobelX[ki];
          gyB += src[idx + 2] * sobelY[ki];
        }
      }

      const idx = (y * width + x) * 4;
      let magR = Math.sqrt(gxR * gxR + gyR * gyR);
      let magG = Math.sqrt(gxG * gxG + gyG * gyG);
      let magB = Math.sqrt(gxB * gxB + gyB * gyB);

      if (invert) {
        magR = 255 - magR;
        magG = 255 - magG;
        magB = 255 - magB;
      }

      // Blend with original
      dst[idx] = Math.min(255, magR * (1 - blend) + src[idx] * blend);
      dst[idx + 1] = Math.min(255, magG * (1 - blend) + src[idx + 1] * blend);
      dst[idx + 2] = Math.min(255, magB * (1 - blend) + src[idx + 2] * blend);
      dst[idx + 3] = src[idx + 3];
    }
  }

  output.ctx.putImageData(outputData, 0, 0);
  return output;
}

// ============================================================================
// MOSAIC
// ============================================================================

/**
 * Mosaic effect - pixelation
 *
 * Parameters:
 * - horizontal_blocks: 2-200
 * - vertical_blocks: 2-200
 * - sharp_corners: boolean
 */
export function mosaicRenderer(
  input: EffectStackResult,
  params: EvaluatedEffectParams,
): EffectStackResult {
  const hBlocks = Math.max(2, params.horizontal_blocks ?? 10);
  const vBlocks = Math.max(2, params.vertical_blocks ?? 10);
  const sharp = params.sharp_corners ?? true;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;
  const inputData = input.ctx.getImageData(0, 0, width, height);
  const src = inputData.data;

  const blockW = width / hBlocks;
  const blockH = height / vBlocks;

  output.ctx.imageSmoothingEnabled = !sharp;

  for (let by = 0; by < vBlocks; by++) {
    for (let bx = 0; bx < hBlocks; bx++) {
      const x1 = Math.floor(bx * blockW);
      const y1 = Math.floor(by * blockH);
      const x2 = Math.floor((bx + 1) * blockW);
      const y2 = Math.floor((by + 1) * blockH);

      // Average color in block
      let totalR = 0,
        totalG = 0,
        totalB = 0,
        count = 0;
      for (let y = y1; y < y2 && y < height; y++) {
        for (let x = x1; x < x2 && x < width; x++) {
          const idx = (y * width + x) * 4;
          totalR += src[idx];
          totalG += src[idx + 1];
          totalB += src[idx + 2];
          count++;
        }
      }

      if (count > 0) {
        output.ctx.fillStyle = `rgb(${Math.round(totalR / count)}, ${Math.round(totalG / count)}, ${Math.round(totalB / count)})`;
        output.ctx.fillRect(x1, y1, x2 - x1, y2 - y1);
      }
    }
  }

  return output;
}

// ============================================================================
// REGISTRATION
// ============================================================================

/**
 * Register all stylize effect renderers
 */
export function registerStylizeEffects(): void {
  registerEffectRenderer("pixel-sort", pixelSortRenderer);
  registerEffectRenderer("glitch", glitchRenderer);
  registerEffectRenderer("vhs", vhsRenderer);
  registerEffectRenderer("rgb-split", rgbSplitRenderer);
  registerEffectRenderer("scanlines", scanlinesRenderer);
  registerEffectRenderer("halftone", halftoneRenderer);
  registerEffectRenderer("dither", ditherRenderer);
  registerEffectRenderer("ripple", rippleRenderer);
  registerEffectRenderer("emboss", embossRenderer);
  registerEffectRenderer("find-edges", findEdgesRenderer);
  registerEffectRenderer("mosaic", mosaicRenderer);
}
