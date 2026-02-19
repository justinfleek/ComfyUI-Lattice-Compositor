/**
 * Text Shaper Service
 *
 * Provides accurate glyph metrics for text rendering using opentype.js.
 * This service bridges the gap between font loading and text layer rendering,
 * providing accurate character widths, kerning, and layout information.
 *
 * Design:
 * - Uses opentype.js for glyph metrics and basic kerning
 * - Designed to be enhanced with harfbuzz.js for advanced OpenType features
 * - Caches shaped results for performance
 * - Thread-safe for use in Web Workers (future)
 */

import opentype from "opentype.js";
import { createLogger } from "@/utils/logger";
import { isFiniteNumber } from "@/utils/typeGuards";
import type { JSONValue } from "@/types/dataAsset";

const logger = createLogger("TextShaper");

// ============================================================================
// Types
// ============================================================================

export interface ShapedGlyph {
  /** The character this glyph represents */
  character: string;
  /** Index in the original string */
  charIndex: number;
  /** Glyph ID in the font */
  glyphId: number;
  /** Horizontal advance (distance to next glyph origin) in pixels */
  xAdvance: number;
  /** Vertical advance (usually 0 for horizontal text) in pixels */
  yAdvance: number;
  /** X offset from glyph origin in pixels */
  xOffset: number;
  /** Y offset from glyph origin in pixels */
  yOffset: number;
  /** Cumulative X position from text start in pixels */
  x: number;
  /** Cumulative Y position from text start in pixels */
  y: number;
  /** Glyph bounding box in pixels (relative to glyph origin) */
  bounds: {
    x1: number;
    y1: number;
    x2: number;
    y2: number;
  };
}

export interface ShapedText {
  /** Array of shaped glyphs */
  glyphs: ShapedGlyph[];
  /** Total text width in pixels */
  width: number;
  /** Total text height in pixels (based on font metrics) */
  height: number;
  /** Font ascender in pixels */
  ascender: number;
  /** Font descender in pixels (negative value) */
  descender: number;
  /** Line height in pixels */
  lineHeight: number;
  /** The original text */
  text: string;
  /** Font family used */
  fontFamily: string;
  /** Font size in pixels */
  fontSize: number;
  /** OpenType features that were applied */
  appliedFeatures: string[];
}

export interface TextShapingOptions {
  /** Font size in pixels */
  fontSize: number;
  /** Enable kerning (default: true) */
  kern?: boolean;
  /** Enable standard ligatures (default: true) - requires harfbuzz for full support */
  liga?: boolean;
  /** Enable contextual ligatures (default: true) - requires harfbuzz */
  clig?: boolean;
  /** Enable discretionary ligatures (default: false) - requires harfbuzz */
  dlig?: boolean;
  /** Enable small caps (default: false) - requires harfbuzz */
  smcp?: boolean;
  /** Additional letter spacing in pixels (default: 0) */
  letterSpacing?: number;
  /** Word spacing multiplier (default: 1) */
  wordSpacing?: number;
  /** Writing direction (default: 'ltr') */
  direction?: "ltr" | "rtl";
  /** Language tag for language-specific features */
  language?: string;
  /** Script tag (default: 'latn' for Latin) */
  script?: string;
}

export interface FontMetrics {
  /** Units per em in the font */
  unitsPerEm: number;
  /** Ascender in font units */
  ascender: number;
  /** Descender in font units (negative) */
  descender: number;
  /** Line gap in font units */
  lineGap: number;
  /** Cap height in font units */
  capHeight: number;
  /** x-height in font units */
  xHeight: number;
  /** Whether the font supports kerning */
  hasKerning: boolean;
  /** Whether the font has GSUB table (for ligatures) */
  hasGSUB: boolean;
  /** Whether the font has GPOS table (for advanced positioning) */
  hasGPOS: boolean;
  /** Whether the font is a variable font */
  isVariableFont: boolean;
  /** Available variable font axes */
  variableAxes: VariableFontAxis[];
}

export interface VariableFontAxis {
  /** Axis tag (e.g., 'wght', 'wdth', 'slnt') */
  tag: string;
  /** Human-readable name */
  name: string;
  /** Minimum value */
  min: number;
  /** Default value */
  default: number;
  /** Maximum value */
  max: number;
}

// ============================================================================
// Font Cache
// ============================================================================

interface CachedFont {
  font: opentype.Font;
  metrics: FontMetrics;
  loadedAt: number;
}

const fontCache = new Map<string, CachedFont>();
const shapingCache = new Map<string, ShapedText>();

const MAX_SHAPING_CACHE_SIZE = 1000;
const FONT_CACHE_TTL = 30 * 60 * 1000; // 30 minutes

// ============================================================================
// Default Options
// ============================================================================

const DEFAULT_SHAPING_OPTIONS: Required<TextShapingOptions> = {
  fontSize: 72,
  kern: true,
  liga: true,
  clig: true,
  dlig: false,
  smcp: false,
  letterSpacing: 0,
  wordSpacing: 1,
  direction: "ltr",
  language: "en",
  script: "latn",
};

// ============================================================================
// TextShaper Class
// ============================================================================

class TextShaper {
  /**
   * Load a font and cache it
   */
  async loadFont(fontFamily: string, fontUrl?: string): Promise<FontMetrics> {
    const cacheKey = fontFamily.toLowerCase();

    // Check cache
    const cached = fontCache.get(cacheKey);
    if (cached && Date.now() - cached.loadedAt < FONT_CACHE_TTL) {
      return cached.metrics;
    }

    // Determine URL
    let url = fontUrl;
    if (!url) {
      // Try common font URL patterns
      const sanitizedName = fontFamily.replace(/\s+/g, "").toLowerCase();
      url = `https://fonts.gstatic.com/s/${sanitizedName}/v1/${sanitizedName}-Regular.ttf`;
    }

    logger.info(`Loading font for shaping: ${fontFamily}`);

    try {
      const font = await opentype.load(url);
      const metrics = this.extractFontMetrics(font);

      fontCache.set(cacheKey, {
        font,
        metrics,
        loadedAt: Date.now(),
      });

      return metrics;
    } catch (error) {
      logger.error(`Failed to load font ${fontFamily}:`, error);
      throw new Error(`Failed to load font: ${fontFamily}`);
    }
  }

  /**
   * Load a font from an ArrayBuffer
   */
  loadFontFromBuffer(fontFamily: string, buffer: ArrayBuffer): FontMetrics {
    const font = opentype.parse(buffer);
    const metrics = this.extractFontMetrics(font);
    const cacheKey = fontFamily.toLowerCase();

    fontCache.set(cacheKey, {
      font,
      metrics,
      loadedAt: Date.now(),
    });

    return metrics;
  }

  /**
   * Get cached font (throws if not loaded)
   */
  private getCachedFont(fontFamily: string): CachedFont {
    const cached = fontCache.get(fontFamily.toLowerCase());
    if (!cached) {
      throw new Error(`Font not loaded: ${fontFamily}. Call loadFont() first.`);
    }
    return cached;
  }

  /**
   * Extract font metrics from opentype.Font
   */
  private extractFontMetrics(font: opentype.Font): FontMetrics {
    // Access internal OpenType tables - not fully typed in opentype.js definitions
    type FvarAxis = { tag: string; name?: { en?: string }; minValue: number; defaultValue: number; maxValue: number };
    const tables = font.tables as { gsub?: JSONValue; gpos?: JSONValue; fvar?: { axes?: FvarAxis[] } };
    const hasGSUB = !!tables.gsub;
    const hasGPOS = !!tables.gpos;
    const fvar = tables.fvar;
    const isVariableFont = !!fvar;

    const variableAxes: VariableFontAxis[] = [];
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    if (isVariableFont && typeof fvar === "object" && fvar !== null && "axes" in fvar && Array.isArray(fvar.axes)) {
      for (const axis of fvar.axes) {
        variableAxes.push({
          tag: axis.tag,
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
          name: (typeof axis.name === "object" && axis.name !== null && "en" in axis.name && typeof axis.name.en === "string")
            ? axis.name.en
            : axis.tag,
          min: axis.minValue,
          default: axis.defaultValue,
          max: axis.maxValue,
        });
      }
    }

    // Type proof: lineGap ∈ number | undefined → number
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    const fontTables = font.tables as { hhea?: { lineGap?: number } };
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    const hheaTable = (typeof fontTables === "object" && fontTables !== null && "hhea" in fontTables && typeof fontTables.hhea === "object" && fontTables.hhea !== null)
      ? fontTables.hhea
      : null;
    const lineGap = (hheaTable !== null && typeof hheaTable === "object" && "lineGap" in hheaTable && typeof hheaTable.lineGap === "number")
      ? hheaTable.lineGap
      : 0;
    const lineGapValue = isFiniteNumber(lineGap) ? lineGap : 0;

    // Type proof: capHeight ∈ number | undefined → number
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    const fontTablesOs2 = font.tables as { os2?: { sCapHeight?: number } };
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    const os2Table = (typeof fontTablesOs2 === "object" && fontTablesOs2 !== null && "os2" in fontTablesOs2 && typeof fontTablesOs2.os2 === "object" && fontTablesOs2.os2 !== null)
      ? fontTablesOs2.os2
      : null;
    const capHeightRaw = (os2Table !== null && typeof os2Table === "object" && "sCapHeight" in os2Table && typeof os2Table.sCapHeight === "number")
      ? os2Table.sCapHeight
      : 0;
    const capHeight = isFiniteNumber(capHeightRaw)
      ? capHeightRaw
      : font.ascender * 0.7;

    // Type proof: xHeight ∈ number | undefined → number
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    const fontTablesXHeight = font.tables as { os2?: { sxHeight?: number } };
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    const os2TableXHeight = (typeof fontTablesXHeight === "object" && fontTablesXHeight !== null && "os2" in fontTablesXHeight && typeof fontTablesXHeight.os2 === "object" && fontTablesXHeight.os2 !== null)
      ? fontTablesXHeight.os2
      : null;
    const xHeight = (os2TableXHeight !== null && typeof os2TableXHeight === "object" && "sxHeight" in os2TableXHeight && typeof os2TableXHeight.sxHeight === "number")
      ? os2TableXHeight.sxHeight
      : 0;
    const xHeightValue = isFiniteNumber(xHeight)
      ? xHeight
      : font.ascender * 0.5;

    return {
      unitsPerEm: font.unitsPerEm,
      ascender: font.ascender,
      descender: font.descender,
      // Access internal OpenType tables - not fully typed in opentype.js definitions
      lineGap: lineGapValue,
      capHeight,
      xHeight: xHeightValue,
      hasKerning:
        typeof font.kerningPairs === "object" && font.kerningPairs !== null &&
        Object.keys(font.kerningPairs).length > 0,
      hasGSUB,
      hasGPOS,
      isVariableFont,
      variableAxes,
    };
  }

  /**
   * Shape text with the given font and options
   * Returns accurate glyph positions and metrics
   */
  async shape(
    text: string,
    fontFamily: string,
    options?: Partial<TextShapingOptions>,
  ): Promise<ShapedText> {
    const opts = { ...DEFAULT_SHAPING_OPTIONS, ...options };
    const cacheKey = this.getShapingCacheKey(text, fontFamily, opts);

    // Check shaping cache
    const cached = shapingCache.get(cacheKey);
    if (cached) {
      return cached;
    }

    // Get font (must be pre-loaded)
    const { font, metrics } = this.getCachedFont(fontFamily);

    // Calculate scale factor
    const scale = opts.fontSize / font.unitsPerEm;

    // Shape the text
    const glyphs: ShapedGlyph[] = [];
    let x = 0;
    const y = 0;

    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      const glyph = font.charToGlyph(char);

      if (!glyph) {
        // Use notdef glyph
        const notdef = font.glyphs.get(0);
        // Type proof: advanceWidth ∈ number | undefined → number
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        const notdefAdvanceWidth = (typeof notdef === "object" && notdef !== null && "advanceWidth" in notdef && typeof notdef.advanceWidth === "number")
          ? notdef.advanceWidth
          : 0;
        const notdefAdvanceWidthValue = isFiniteNumber(notdefAdvanceWidth)
          ? notdefAdvanceWidth
          : font.unitsPerEm * 0.5;
        const advanceWidth = notdefAdvanceWidthValue * scale;
        glyphs.push({
          character: char,
          charIndex: i,
          glyphId: 0,
          xAdvance: advanceWidth,
          yAdvance: 0,
          xOffset: 0,
          yOffset: 0,
          x,
          y,
          bounds: { x1: 0, y1: 0, x2: advanceWidth, y2: opts.fontSize },
        });
        x += advanceWidth + opts.letterSpacing;
        continue;
      }

      // Get glyph metrics
      // Type proof: advanceWidth ∈ number | undefined → number
      const advanceWidthValue = isFiniteNumber(glyph.advanceWidth)
        ? glyph.advanceWidth
        : 0;
      const advanceWidth = advanceWidthValue * scale;
      const bbox = glyph.getBoundingBox();

      // Apply word spacing
      let finalAdvance = advanceWidth;
      if (char === " ") {
        finalAdvance *= opts.wordSpacing;
      }

      // Apply kerning
      let kerningAdjust = 0;
      if (opts.kern && i < text.length - 1) {
        const nextGlyph = font.charToGlyph(text[i + 1]);
        if (nextGlyph) {
          const kerning = font.getKerningValue(glyph, nextGlyph);
          kerningAdjust = kerning * scale;
        }
      }

      glyphs.push({
        character: char,
        charIndex: i,
        glyphId: glyph.index,
        xAdvance: finalAdvance + kerningAdjust,
        yAdvance: 0,
        xOffset: 0,
        yOffset: 0,
        x,
        y,
        bounds: {
          x1: bbox.x1 * scale,
          y1: bbox.y1 * scale,
          x2: bbox.x2 * scale,
          y2: bbox.y2 * scale,
        },
      });

      x += finalAdvance + kerningAdjust + opts.letterSpacing;
    }

    // Calculate text metrics
    const ascender = metrics.ascender * scale;
    const descender = metrics.descender * scale;
    const lineHeight =
      (metrics.ascender - metrics.descender + metrics.lineGap) * scale;

    const result: ShapedText = {
      glyphs,
      width: x - opts.letterSpacing, // Remove trailing letter spacing
      height: lineHeight,
      ascender,
      descender,
      lineHeight,
      text,
      fontFamily,
      fontSize: opts.fontSize,
      appliedFeatures: this.getAppliedFeatures(opts, metrics),
    };

    // Cache result
    this.addToShapingCache(cacheKey, result);

    return result;
  }

  /**
   * Shape text synchronously (font must already be loaded)
   */
  shapeSync(
    text: string,
    fontFamily: string,
    options?: Partial<TextShapingOptions>,
  ): ShapedText {
    const opts = { ...DEFAULT_SHAPING_OPTIONS, ...options };
    const { font, metrics } = this.getCachedFont(fontFamily);

    // Same logic as async shape but without await
    const scale = opts.fontSize / font.unitsPerEm;
    const glyphs: ShapedGlyph[] = [];
    let x = 0;
    const y = 0;

    for (let i = 0; i < text.length; i++) {
      const char = text[i];
      const glyph = font.charToGlyph(char);

      if (!glyph) {
        const notdef = font.glyphs.get(0);
        // Type proof: advanceWidth ∈ number | undefined → number
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        const notdefAdvanceWidth = (typeof notdef === "object" && notdef !== null && "advanceWidth" in notdef && typeof notdef.advanceWidth === "number")
          ? notdef.advanceWidth
          : 0;
        const notdefAdvanceWidthValue = isFiniteNumber(notdefAdvanceWidth)
          ? notdefAdvanceWidth
          : font.unitsPerEm * 0.5;
        const advanceWidth = notdefAdvanceWidthValue * scale;
        glyphs.push({
          character: char,
          charIndex: i,
          glyphId: 0,
          xAdvance: advanceWidth,
          yAdvance: 0,
          xOffset: 0,
          yOffset: 0,
          x,
          y,
          bounds: { x1: 0, y1: 0, x2: advanceWidth, y2: opts.fontSize },
        });
        x += advanceWidth + opts.letterSpacing;
        continue;
      }

      // Type proof: advanceWidth ∈ number | undefined → number
      const advanceWidthValue = isFiniteNumber(glyph.advanceWidth)
        ? glyph.advanceWidth
        : 0;
      const advanceWidth = advanceWidthValue * scale;
      const bbox = glyph.getBoundingBox();

      let finalAdvance = advanceWidth;
      if (char === " ") {
        finalAdvance *= opts.wordSpacing;
      }

      let kerningAdjust = 0;
      if (opts.kern && i < text.length - 1) {
        const nextGlyph = font.charToGlyph(text[i + 1]);
        if (nextGlyph) {
          const kerning = font.getKerningValue(glyph, nextGlyph);
          kerningAdjust = kerning * scale;
        }
      }

      glyphs.push({
        character: char,
        charIndex: i,
        glyphId: glyph.index,
        xAdvance: finalAdvance + kerningAdjust,
        yAdvance: 0,
        xOffset: 0,
        yOffset: 0,
        x,
        y,
        bounds: {
          x1: bbox.x1 * scale,
          y1: bbox.y1 * scale,
          x2: bbox.x2 * scale,
          y2: bbox.y2 * scale,
        },
      });

      x += finalAdvance + kerningAdjust + opts.letterSpacing;
    }

    const ascender = metrics.ascender * scale;
    const descender = metrics.descender * scale;
    const lineHeight =
      (metrics.ascender - metrics.descender + metrics.lineGap) * scale;

    return {
      glyphs,
      width: x - opts.letterSpacing,
      height: lineHeight,
      ascender,
      descender,
      lineHeight,
      text,
      fontFamily,
      fontSize: opts.fontSize,
      appliedFeatures: this.getAppliedFeatures(opts, metrics),
    };
  }

  /**
   * Get character widths array for a text string
   * This is a convenience method for TextLayer compatibility
   */
  getCharacterWidths(
    text: string,
    fontFamily: string,
    fontSize: number,
    options?: { kern?: boolean; letterSpacing?: number },
  ): number[] {
    try {
      // Type proof: kern ∈ boolean | undefined → boolean
      const kern =
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        (typeof options === "object" && options !== null && "kern" in options && typeof options.kern === "boolean")
          ? options.kern
          : true;
      // Type proof: letterSpacing ∈ number | undefined → number
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      const letterSpacing = (typeof options === "object" && options !== null && "letterSpacing" in options && typeof options.letterSpacing === "number")
        ? options.letterSpacing
        : 0;
      const letterSpacingValue = isFiniteNumber(letterSpacing) ? letterSpacing : 0;

      const shaped = this.shapeSync(text, fontFamily, {
        fontSize,
        kern,
        letterSpacing,
      });
      return shaped.glyphs.map((g) => g.xAdvance);
    } catch {
      // Fallback to heuristic if font not loaded
      return this.getHeuristicCharacterWidths(text, fontSize);
    }
  }

  /**
   * Get cumulative character positions (x coordinates)
   */
  getCharacterPositions(
    text: string,
    fontFamily: string,
    fontSize: number,
    options?: { kern?: boolean; letterSpacing?: number },
  ): number[] {
    try {
      // Type proof: kern ∈ boolean | undefined → boolean
      const kern =
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        (typeof options === "object" && options !== null && "kern" in options && typeof options.kern === "boolean")
          ? options.kern
          : true;
      // Type proof: letterSpacing ∈ number | undefined → number
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
      const letterSpacing = (typeof options === "object" && options !== null && "letterSpacing" in options && typeof options.letterSpacing === "number")
        ? options.letterSpacing
        : 0;
      const letterSpacingValue = isFiniteNumber(letterSpacing) ? letterSpacing : 0;

      const shaped = this.shapeSync(text, fontFamily, {
        fontSize,
        kern,
        letterSpacing,
      });
      return shaped.glyphs.map((g) => g.x);
    } catch {
      // Fallback to heuristic
      const widths = this.getHeuristicCharacterWidths(text, fontSize);
      const positions: number[] = [];
      let x = 0;
      for (const width of widths) {
        positions.push(x);
        x += width;
      }
      return positions;
    }
  }

  /**
   * Fallback heuristic character widths (matching original TextLayer behavior)
   */
  private getHeuristicCharacterWidths(
    text: string,
    fontSize: number,
  ): number[] {
    const avgCharWidth = fontSize * 0.6;
    const widths: number[] = [];

    for (const char of text) {
      if ("iIl1|!.,;:'\"".includes(char)) {
        widths.push(avgCharWidth * 0.4); // Narrow
      } else if ("mwMW".includes(char)) {
        widths.push(avgCharWidth * 1.3); // Wide
      } else if (char === " ") {
        widths.push(avgCharWidth * 0.5); // Space
      } else {
        widths.push(avgCharWidth); // Average
      }
    }

    return widths;
  }

  /**
   * Check if a font is loaded
   */
  isFontLoaded(fontFamily: string): boolean {
    return fontCache.has(fontFamily.toLowerCase());
  }

  /**
   * Get font metrics for a loaded font
   */
  getFontMetrics(fontFamily: string): FontMetrics | null {
    const cached = fontCache.get(fontFamily.toLowerCase());
    // Type proof: metrics ∈ FontMetrics | undefined → FontMetrics | null
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
    return (typeof cached === "object" && cached !== null && "metrics" in cached && typeof cached.metrics === "object" && cached.metrics !== null)
      ? cached.metrics
      : null;
  }

  /**
   * Clear all caches
   */
  clearCache(): void {
    fontCache.clear();
    shapingCache.clear();
    logger.debug("TextShaper caches cleared");
  }

  /**
   * Clear shaping cache only (keep fonts)
   */
  clearShapingCache(): void {
    shapingCache.clear();
  }

  /**
   * Get cache statistics
   */
  getCacheStats(): { fonts: number; shapingEntries: number } {
    return {
      fonts: fontCache.size,
      shapingEntries: shapingCache.size,
    };
  }

  // ============================================================================
  // Private Helpers
  // ============================================================================

  private getShapingCacheKey(
    text: string,
    fontFamily: string,
    opts: Required<TextShapingOptions>,
  ): string {
    return `${fontFamily.toLowerCase()}:${opts.fontSize}:${opts.kern}:${opts.letterSpacing}:${text}`;
  }

  private addToShapingCache(key: string, result: ShapedText): void {
    // Evict oldest entries if cache is full
    if (shapingCache.size >= MAX_SHAPING_CACHE_SIZE) {
      const firstKey = shapingCache.keys().next().value;
      if (firstKey) {
        shapingCache.delete(firstKey);
      }
    }
    shapingCache.set(key, result);
  }

  private getAppliedFeatures(
    opts: Required<TextShapingOptions>,
    metrics: FontMetrics,
  ): string[] {
    const features: string[] = [];

    // opentype.js only supports kerning from the kern table
    // Advanced features (liga, clig, dlig, smcp) require harfbuzz.js
    if (opts.kern && metrics.hasKerning) {
      features.push("kern");
    }

    // Note: These features are requested but not applied without harfbuzz
    // We still track them for future implementation
    if (opts.liga && metrics.hasGSUB) {
      features.push("liga (pending)");
    }
    if (opts.clig && metrics.hasGSUB) {
      features.push("clig (pending)");
    }
    if (opts.dlig && metrics.hasGSUB) {
      features.push("dlig (pending)");
    }
    if (opts.smcp && metrics.hasGSUB) {
      features.push("smcp (pending)");
    }

    return features;
  }
}

// ============================================================================
// Singleton Export
// ============================================================================

export const textShaper = new TextShaper();

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * Load a font for text shaping
 */
export async function loadFontForShaping(
  fontFamily: string,
  fontUrl?: string,
): Promise<FontMetrics> {
  return textShaper.loadFont(fontFamily, fontUrl);
}

/**
 * Shape text with accurate glyph metrics
 */
export async function shapeText(
  text: string,
  fontFamily: string,
  options?: Partial<TextShapingOptions>,
): Promise<ShapedText> {
  return textShaper.shape(text, fontFamily, options);
}

/**
 * Shape text synchronously (font must be pre-loaded)
 */
export function shapeTextSync(
  text: string,
  fontFamily: string,
  options?: Partial<TextShapingOptions>,
): ShapedText {
  return textShaper.shapeSync(text, fontFamily, options);
}

/**
 * Get accurate character widths for a text string
 */
export function getCharacterWidths(
  text: string,
  fontFamily: string,
  fontSize: number,
  options?: { kern?: boolean; letterSpacing?: number },
): number[] {
  return textShaper.getCharacterWidths(text, fontFamily, fontSize, options);
}

/**
 * Check if text shaping is available for a font
 */
export function isShapingAvailable(fontFamily: string): boolean {
  return textShaper.isFontLoaded(fontFamily);
}

export default textShaper;
