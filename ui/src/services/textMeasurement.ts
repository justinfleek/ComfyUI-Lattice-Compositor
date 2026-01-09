/**
 * Text Measurement Service
 *
 * Provides accurate text measurement using Canvas API
 * for sourceRectAtTime and responsive template design.
 */

export interface TextMetrics {
  width: number;
  height: number;
  actualBoundingBoxAscent: number;
  actualBoundingBoxDescent: number;
  actualBoundingBoxLeft: number;
  actualBoundingBoxRight: number;
  fontBoundingBoxAscent: number;
  fontBoundingBoxDescent: number;
}

export interface TextRect {
  top: number;
  left: number;
  width: number;
  height: number;
}

// Cached canvas for measurements
let measureCanvas: HTMLCanvasElement | null = null;
let measureContext: CanvasRenderingContext2D | null = null;

/**
 * Get or create measurement canvas
 */
function getMeasureContext(): CanvasRenderingContext2D {
  if (!measureCanvas) {
    measureCanvas = document.createElement("canvas");
    measureCanvas.width = 1;
    measureCanvas.height = 1;
  }

  if (!measureContext) {
    measureContext = measureCanvas.getContext("2d");
    if (!measureContext) {
      throw new Error("Failed to create measurement context");
    }
  }

  return measureContext;
}

/**
 * Build CSS font string from properties
 */
export function buildFontString(
  fontFamily: string,
  fontSize: number,
  fontWeight: string | number = "normal",
  fontStyle: string = "normal",
): string {
  const weight = typeof fontWeight === "number" ? fontWeight : fontWeight;
  return `${fontStyle} ${weight} ${fontSize}px ${fontFamily}`;
}

/**
 * Measure a single line of text
 */
export function measureText(
  text: string,
  fontFamily: string,
  fontSize: number,
  fontWeight: string | number = "normal",
  fontStyle: string = "normal",
): TextMetrics {
  const ctx = getMeasureContext();
  ctx.font = buildFontString(fontFamily, fontSize, fontWeight, fontStyle);

  const metrics = ctx.measureText(text);

  return {
    width: metrics.width,
    height: fontSize, // Fallback if actual metrics not available
    actualBoundingBoxAscent: metrics.actualBoundingBoxAscent ?? fontSize * 0.8,
    actualBoundingBoxDescent:
      metrics.actualBoundingBoxDescent ?? fontSize * 0.2,
    actualBoundingBoxLeft: metrics.actualBoundingBoxLeft ?? 0,
    actualBoundingBoxRight: metrics.actualBoundingBoxRight ?? metrics.width,
    fontBoundingBoxAscent: metrics.fontBoundingBoxAscent ?? fontSize * 0.8,
    fontBoundingBoxDescent: metrics.fontBoundingBoxDescent ?? fontSize * 0.2,
  };
}

/**
 * Measure multi-line text
 */
export function measureMultilineText(
  text: string,
  fontFamily: string,
  fontSize: number,
  fontWeight: string | number = "normal",
  fontStyle: string = "normal",
  lineHeight: number = 1.2,
  letterSpacing: number = 0,
): TextRect {
  const ctx = getMeasureContext();
  ctx.font = buildFontString(fontFamily, fontSize, fontWeight, fontStyle);

  const lines = text.split("\n");
  let maxWidth = 0;
  let totalHeight = 0;
  let firstLineAscent = 0;

  lines.forEach((line, index) => {
    // Add letter spacing to width calculation
    let lineWidth = 0;
    if (letterSpacing !== 0 && line.length > 0) {
      // Measure each character with spacing
      for (let i = 0; i < line.length; i++) {
        const charMetrics = ctx.measureText(line[i]);
        lineWidth += charMetrics.width;
        if (i < line.length - 1) {
          lineWidth += letterSpacing;
        }
      }
    } else {
      lineWidth = ctx.measureText(line).width;
    }

    maxWidth = Math.max(maxWidth, lineWidth);

    // Calculate height
    if (index === 0) {
      const metrics = ctx.measureText(line || "M");
      firstLineAscent = metrics.actualBoundingBoxAscent ?? fontSize * 0.8;
    }
  });

  totalHeight = lines.length * fontSize * lineHeight;

  return {
    top: -firstLineAscent,
    left: 0,
    width: maxWidth,
    height: totalHeight,
  };
}

/**
 * Measure text with all properties (for TextLayer data)
 */
export function measureTextLayerRect(
  data: {
    text?: string;
    fontFamily?: string;
    fontSize?: number;
    fontWeight?: string | number;
    fontStyle?: string;
    lineHeight?: number;
    letterSpacing?: number;
    textAlign?: string;
  },
  includeExtents: boolean = false,
): TextRect {
  const text = data.text || "";
  const fontFamily = data.fontFamily || "Arial";
  const fontSize = data.fontSize || 72;
  const fontWeight = data.fontWeight || "normal";
  const fontStyle = data.fontStyle || "normal";
  const lineHeight = data.lineHeight || 1.2;
  const letterSpacing = data.letterSpacing || 0;
  const textAlign = data.textAlign || "left";

  const rect = measureMultilineText(
    text,
    fontFamily,
    fontSize,
    fontWeight,
    fontStyle,
    lineHeight,
    letterSpacing,
  );

  // Adjust left based on text alignment
  if (textAlign === "center") {
    rect.left = -rect.width / 2;
  } else if (textAlign === "right") {
    rect.left = -rect.width;
  }

  // Include stroke extents if requested
  if (includeExtents) {
    // Assuming a typical stroke width of 2px for now
    // In a full implementation, this would come from the layer's stroke settings
    const strokeWidth = 2;
    rect.top -= strokeWidth / 2;
    rect.left -= strokeWidth / 2;
    rect.width += strokeWidth;
    rect.height += strokeWidth;
  }

  return rect;
}

/**
 * Check if a font is available
 */
export function isFontAvailable(fontFamily: string): boolean {
  const ctx = getMeasureContext();

  // Measure with target font
  ctx.font = `72px ${fontFamily}`;
  const targetWidth = ctx.measureText("abcdefghijklmnopqrstuvwxyz").width;

  // Measure with fallback
  ctx.font = "72px monospace";
  const fallbackWidth = ctx.measureText("abcdefghijklmnopqrstuvwxyz").width;

  // If widths differ, the font is available
  return targetWidth !== fallbackWidth;
}

/**
 * Preload a font and measure when ready
 */
export async function measureTextWithFont(
  text: string,
  fontFamily: string,
  fontSize: number,
  fontWeight: string | number = "normal",
  fontStyle: string = "normal",
  timeout: number = 3000,
): Promise<TextMetrics> {
  // Try to load font if available via FontFace API
  if ("fonts" in document) {
    try {
      const fontString = buildFontString(
        fontFamily,
        fontSize,
        fontWeight,
        fontStyle,
      );

      // Wait for font to load
      await Promise.race([
        document.fonts.load(fontString, text),
        new Promise((_, reject) =>
          setTimeout(() => reject(new Error("Font load timeout")), timeout),
        ),
      ]);
    } catch (e) {
      console.warn(
        `[TextMeasurement] Font "${fontFamily}" may not be loaded:`,
        e,
      );
    }
  }

  return measureText(text, fontFamily, fontSize, fontWeight, fontStyle);
}

/**
 * Get baseline offset for vertical alignment
 */
export function getBaselineOffset(
  fontFamily: string,
  fontSize: number,
  verticalAlign: "top" | "middle" | "bottom" | "baseline" = "baseline",
): number {
  const metrics = measureText("Mg", fontFamily, fontSize);

  switch (verticalAlign) {
    case "top":
      return metrics.actualBoundingBoxAscent;
    case "middle":
      return (
        (metrics.actualBoundingBoxAscent - metrics.actualBoundingBoxDescent) / 2
      );
    case "bottom":
      return -metrics.actualBoundingBoxDescent;
    default:
      return 0;
  }
}

/**
 * Calculate character positions for text along path
 */
export function getCharacterPositions(
  text: string,
  fontFamily: string,
  fontSize: number,
  letterSpacing: number = 0,
): number[] {
  const ctx = getMeasureContext();
  ctx.font = buildFontString(fontFamily, fontSize);

  const positions: number[] = [0];
  let currentX = 0;

  for (let i = 0; i < text.length; i++) {
    const charWidth = ctx.measureText(text[i]).width;
    currentX += charWidth + letterSpacing;
    positions.push(currentX);
  }

  return positions;
}

/**
 * Cleanup cached resources
 */
export function cleanup(): void {
  measureCanvas = null;
  measureContext = null;
}

export default {
  measureText,
  measureMultilineText,
  measureTextLayerRect,
  measureTextWithFont,
  isFontAvailable,
  buildFontString,
  getBaselineOffset,
  getCharacterPositions,
  cleanup,
};
