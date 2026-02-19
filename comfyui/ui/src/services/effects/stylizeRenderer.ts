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
import { isFiniteNumber } from "@/utils/typeGuards";
import { SeededRandom } from "../particleSystem";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                            // pixel // sort
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: direction ∈ {"horizontal", "vertical"} ∪ {undefined}
  const directionValue = params.direction;
  const direction = typeof directionValue === "string" ? directionValue : "horizontal";
  // Validate numeric params (NaN causes visual corruption)
  // Type proof: threshold ∈ ℝ ∧ finite(threshold) → threshold ∈ [0, 1]
  const thresholdValue = params.threshold;
  const threshold = isFiniteNumber(thresholdValue)
    ? Math.max(0, Math.min(1, thresholdValue))
    : 0.25;
  // Type proof: smoothing ∈ ℝ ∧ finite(smoothing) → smoothing ∈ [0, 1]
  const smoothingValue = params.smoothing;
  const smoothing = isFiniteNumber(smoothingValue)
    ? Math.max(0, Math.min(1, smoothingValue))
    : 0.1;
  // Type proof: sort_by ∈ {"saturation", "brightness", "hue"} ∪ {undefined}
  const sortByValue = params.sort_by;
  const sortBy = typeof sortByValue === "string" ? sortByValue : "saturation";
  // Type proof: reverse ∈ {true, false}
  const reverse = typeof params.reverse === "boolean" ? params.reverse : false;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // glitch
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: glitch_amount ∈ ℝ ∧ finite(glitch_amount) → glitch_amount ∈ ℝ₊
  const glitchAmountValue = params.glitch_amount;
  const glitchAmount = isFiniteNumber(glitchAmountValue) && glitchAmountValue >= 0
    ? glitchAmountValue
    : 5;
  // Type proof: color_offset ∈ {true, false}
  const colorOffset = typeof params.color_offset === "boolean" ? params.color_offset : true;
  // Type proof: block_size ∈ ℝ ∧ finite(block_size) → block_size ∈ [1, ∞)
  const blockSizeValue = params.block_size;
  const blockSizeRaw = isFiniteNumber(blockSizeValue) && blockSizeValue >= 1
    ? blockSizeValue
    : 8;
  const blockSize = Math.max(1, blockSizeRaw);
  // Type proof: seed ∈ ℕ ∧ finite(seed) → seed ∈ ℕ
  const seedValue = params.seed;
  const seed = isFiniteNumber(seedValue) && Number.isInteger(seedValue) && seedValue >= 0
    ? seedValue
    : 12345;
  // Type proof: scanlines ∈ {true, false}
  const scanlines = typeof params.scanlines === "boolean" ? params.scanlines : true;

  if (glitchAmount === 0) return input;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;

  // Start by copying original
  output.ctx.drawImage(input.canvas, 0, 0);

  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;

  // Type proof: frame ∈ ℕ ∪ {undefined} → frame ∈ ℕ
  const frameValue = frame;
  const validFrame = isFiniteNumber(frameValue) && Number.isInteger(frameValue) && frameValue >= 0 ? frameValue : 0;
  const rng = new SeededRandom(seed + validFrame);

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                      // vhs
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: tracking ∈ ℝ ∧ finite(tracking) → tracking ∈ [0, 1]
  const trackingValue = params.tracking;
  const tracking = isFiniteNumber(trackingValue)
    ? Math.max(0, Math.min(1, trackingValue))
    : 0.5;
  // Type proof: noise ∈ ℝ ∧ finite(noise) → noise ∈ [0, 1]
  const noiseValue = params.noise;
  const noise = isFiniteNumber(noiseValue)
    ? Math.max(0, Math.min(1, noiseValue))
    : 0.3;
  // Type proof: color_bleed ∈ ℝ ∧ finite(color_bleed) → color_bleed ∈ ℝ₊
  const colorBleedValue = params.color_bleed;
  const colorBleed = isFiniteNumber(colorBleedValue) && colorBleedValue >= 0
    ? colorBleedValue
    : 3;
  // Type proof: jitter ∈ ℝ ∧ finite(jitter) → jitter ∈ [0, 1]
  const jitterValue = params.jitter;
  const jitter = isFiniteNumber(jitterValue)
    ? Math.max(0, Math.min(1, jitterValue))
    : 0.5;
  // Type proof: rolling_bands ∈ {true, false}
  const rollingBands = typeof params.rolling_bands === "boolean" ? params.rolling_bands : true;

  const output = createMatchingCanvas(input.canvas);
  const { width, height } = input.canvas;

  output.ctx.drawImage(input.canvas, 0, 0);

  const imageData = output.ctx.getImageData(0, 0, width, height);
  const data = imageData.data;

  // Type proof: frame ∈ ℕ ∪ {undefined} → frame ∈ ℕ
  const frameValue = frame;
  const validFrame = isFiniteNumber(frameValue) && Number.isInteger(frameValue) && frameValue >= 0 ? frameValue : 0;
  const rng = new SeededRandom(12345 + validFrame);

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                             // rgb // split
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: red_offset_x ∈ ℝ ∧ finite(red_offset_x) → red_offset_x ∈ ℝ
  const redOffsetXValue = params.red_offset_x;
  const redOffsetX = isFiniteNumber(redOffsetXValue) ? redOffsetXValue : 5;
  // Type proof: red_offset_y ∈ ℝ ∧ finite(red_offset_y) → red_offset_y ∈ ℝ
  const redOffsetYValue = params.red_offset_y;
  const redOffsetY = isFiniteNumber(redOffsetYValue) ? redOffsetYValue : 0;
  // Type proof: green_offset_x ∈ ℝ ∧ finite(green_offset_x) → green_offset_x ∈ ℝ
  const greenOffsetXValue = params.green_offset_x;
  const greenOffsetX = isFiniteNumber(greenOffsetXValue) ? greenOffsetXValue : 0;
  // Type proof: green_offset_y ∈ ℝ ∧ finite(green_offset_y) → green_offset_y ∈ ℝ
  const greenOffsetYValue = params.green_offset_y;
  const greenOffsetY = isFiniteNumber(greenOffsetYValue) ? greenOffsetYValue : 0;
  // Type proof: blue_offset_x ∈ ℝ ∧ finite(blue_offset_x) → blue_offset_x ∈ ℝ
  const blueOffsetXValue = params.blue_offset_x;
  const blueOffsetX = isFiniteNumber(blueOffsetXValue) ? blueOffsetXValue : -5;
  // Type proof: blue_offset_y ∈ ℝ ∧ finite(blue_offset_y) → blue_offset_y ∈ ℝ
  const blueOffsetYValue = params.blue_offset_y;
  const blueOffsetY = isFiniteNumber(blueOffsetYValue) ? blueOffsetYValue : 0;
  // Type proof: blend_mode ∈ {"screen", "add", "multiply", "overlay"} ∪ {undefined}
  const blendModeValue = params.blend_mode;
  const blendMode = typeof blendModeValue === "string" ? blendModeValue : "screen";

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                // scanlines
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: line_width ∈ ℝ ∧ finite(line_width) → line_width ∈ [1, 20]
  const lineWidthValue = params.line_width;
  const lineWidth = isFiniteNumber(lineWidthValue)
    ? Math.max(1, Math.min(20, lineWidthValue))
    : 2;
  // Type proof: line_spacing ∈ ℝ ∧ finite(line_spacing) → line_spacing ∈ [1, 20]
  const lineSpacingValue = params.line_spacing;
  const lineSpacing = isFiniteNumber(lineSpacingValue)
    ? Math.max(1, Math.min(20, lineSpacingValue))
    : 2;
  // Type proof: opacity ∈ ℝ ∧ finite(opacity) → opacity ∈ [0, 1]
  const opacityValue = params.opacity;
  const opacity = isFiniteNumber(opacityValue)
    ? Math.max(0, Math.min(1, opacityValue))
    : 0.3;
  // Type proof: direction ∈ {"horizontal", "vertical"} ∪ {undefined}
  const directionValue = params.direction;
  const direction = typeof directionValue === "string" ? directionValue : "horizontal";
  // Type proof: animate ∈ {true, false}
  const animate = typeof params.animate === "boolean" ? params.animate : false;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                 // halftone
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: dot_size ∈ ℝ ∧ finite(dot_size) → dot_size ∈ [2, ∞)
  const dotSizeValue = params.dot_size;
  const dotSizeRaw = isFiniteNumber(dotSizeValue) && dotSizeValue >= 2 ? dotSizeValue : 6;
  const dotSize = Math.max(2, dotSizeRaw);
  // Type proof: angle ∈ ℝ ∧ finite(angle) → angle ∈ ℝ
  const angleValue = params.angle;
  const angleDeg = isFiniteNumber(angleValue) ? angleValue : 45;
  const angle = (angleDeg * Math.PI) / 180;
  // Type proof: color_mode ∈ {"grayscale", "color"} ∪ {undefined}
  const colorModeValue = params.color_mode;
  const colorMode = typeof colorModeValue === "string" ? colorModeValue : "grayscale";

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // dither
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: method ∈ {"ordered", "floyd-steinberg"} ∪ {undefined}
  const methodValue = params.method;
  const method = typeof methodValue === "string" ? methodValue : "ordered";
  // Type proof: levels ∈ ℕ ∧ finite(levels) → levels ∈ [2, 256]
  const levelsValue = params.levels;
  const levelsRaw = isFiniteNumber(levelsValue) && Number.isInteger(levelsValue)
    ? levelsValue
    : 4;
  const levels = Math.max(2, Math.min(256, levelsRaw));
  // Type proof: matrix_size ∈ ℕ ∧ finite(matrix_size) → matrix_size ∈ ℕ₊
  const matrixSizeValue = params.matrix_size;
  const matrixSizeRaw = isFiniteNumber(matrixSizeValue) && Number.isInteger(matrixSizeValue) && matrixSizeValue > 0
    ? matrixSizeValue
    : 4;
  const matrixSize = matrixSizeRaw;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // ripple
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: amplitude ∈ ℝ ∧ finite(amplitude) → amplitude ∈ [0, 50]
  const amplitudeValue = params.amplitude;
  const amplitude = isFiniteNumber(amplitudeValue)
    ? Math.max(0, Math.min(50, amplitudeValue))
    : 10;
  // Type proof: wavelength ∈ ℝ ∧ finite(wavelength) → wavelength ∈ [10, 200]
  const wavelengthValue = params.wavelength;
  const wavelength = isFiniteNumber(wavelengthValue)
    ? Math.max(10, Math.min(200, wavelengthValue))
    : 50;
  // Type proof: phase ∈ ℝ ∧ finite(phase) → phase ∈ [0, 360]
  const phaseValue = params.phase;
  let phase = isFiniteNumber(phaseValue)
    ? Math.max(0, Math.min(360, phaseValue))
    : 0;
  // Type proof: center_x ∈ ℝ ∧ finite(center_x) → center_x ∈ [0, 100]
  const centerXValue = params.center_x;
  const centerXRaw = isFiniteNumber(centerXValue)
    ? Math.max(0, Math.min(100, centerXValue))
    : 50;
  const centerX = centerXRaw / 100;
  // Type proof: center_y ∈ ℝ ∧ finite(center_y) → center_y ∈ [0, 100]
  const centerYValue = params.center_y;
  const centerYRaw = isFiniteNumber(centerYValue)
    ? Math.max(0, Math.min(100, centerYValue))
    : 50;
  const centerY = centerYRaw / 100;
  // Type proof: decay ∈ ℝ ∧ finite(decay) → decay ∈ [0, 1]
  const decayValue = params.decay;
  const decay = isFiniteNumber(decayValue)
    ? Math.max(0, Math.min(1, decayValue))
    : 0.5;

  // Animate phase if frame is provided
  // Type proof: animate ∈ {true, false}
  const animateValue = params.animate;
  const animate = typeof animateValue === "boolean" ? animateValue : false;
  // Type proof: frame ∈ ℕ ∪ {undefined} → frame ∈ ℕ
  const frameValue = frame;
  const validFrame = isFiniteNumber(frameValue) && Number.isInteger(frameValue) && frameValue >= 0 ? frameValue : 0;
  if (validFrame !== undefined && animate) {
    phase = (phase + validFrame * 5) % 360;
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // emboss
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: direction ∈ ℝ ∧ finite(direction) → direction ∈ [0, 360]
  const directionValue = params.direction;
  const directionDeg = isFiniteNumber(directionValue)
    ? Math.max(0, Math.min(360, directionValue))
    : 135;
  const direction = (directionDeg * Math.PI) / 180;
  // Type proof: height ∈ ℝ ∧ finite(height) → height ∈ [1, ∞)
  const heightValue = params.height;
  const heightRaw = isFiniteNumber(heightValue) && heightValue >= 1 ? heightValue : 3;
  const height = Math.max(1, heightRaw);
  // Type proof: amount ∈ ℝ ∧ finite(amount) → amount ∈ ℝ₊
  const amountValue = params.amount;
  const amount = isFiniteNumber(amountValue) && amountValue >= 0 ? amountValue : 100;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                            // find // edges
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: invert ∈ {true, false}
  const invert = typeof params.invert === "boolean" ? params.invert : false;
  // Type proof: blend_with_original ∈ ℝ ∧ finite(blend_with_original) → blend_with_original ∈ [0, 100]
  const blendValue = params.blend_with_original;
  const blendRaw = isFiniteNumber(blendValue)
    ? Math.max(0, Math.min(100, blendValue))
    : 0;
  const blend = blendRaw / 100;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // mosaic
// ═══════════════════════════════════════════════════════════════════════════

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
  // Type proof: horizontal_blocks ∈ ℕ ∧ finite(horizontal_blocks) → horizontal_blocks ∈ [2, ∞)
  const hBlocksValue = params.horizontal_blocks;
  const hBlocksRaw = isFiniteNumber(hBlocksValue) && Number.isInteger(hBlocksValue) && hBlocksValue >= 2
    ? hBlocksValue
    : 10;
  const hBlocks = Math.max(2, hBlocksRaw);
  // Type proof: vertical_blocks ∈ ℕ ∧ finite(vertical_blocks) → vertical_blocks ∈ [2, ∞)
  const vBlocksValue = params.vertical_blocks;
  const vBlocksRaw = isFiniteNumber(vBlocksValue) && Number.isInteger(vBlocksValue) && vBlocksValue >= 2
    ? vBlocksValue
    : 10;
  const vBlocks = Math.max(2, vBlocksRaw);
  // Type proof: sharp_corners ∈ {true, false}
  const sharp = typeof params.sharp_corners === "boolean" ? params.sharp_corners : true;

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

// ═══════════════════════════════════════════════════════════════════════════
//                                                             // registration
// ═══════════════════════════════════════════════════════════════════════════

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
