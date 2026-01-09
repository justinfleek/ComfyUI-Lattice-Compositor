/**
 * Text to Vector Service
 *
 * Converts text layers to editable spline paths using opentype.js.
 * Supports:
 * - Font loading and caching
 * - Glyph path extraction
 * - Character grouping for animation
 * - Kerning and spacing
 */

import opentype from "opentype.js";
import type {
  AnimatableProperty,
  ControlPoint,
  Layer,
  SplineData,
} from "@/types/project";
import type { BezierPath, BezierVertex, Point2D } from "@/types/shapes";
import { createLogger } from "@/utils/logger";

const logger = createLogger("TextToVector");

// ============================================================================
// Helpers
// ============================================================================

/** Create a basic AnimatableProperty with default values */
function createAnimatableProperty<T>(
  name: string,
  value: T,
  type: "number" | "position" | "color" | "enum" | "vector3",
): AnimatableProperty<T> {
  return {
    id: `prop_${name.toLowerCase().replace(/\s+/g, "_")}_${Date.now()}`,
    name,
    type,
    value,
    animated: false,
    keyframes: [],
  };
}

// ============================================================================
// Types
// ============================================================================

export interface TextToVectorResult {
  /** All paths combined */
  allPaths: BezierPath[];
  /** Per-character path groups */
  characters: CharacterVectorGroup[];
  /** Bounding box of entire text */
  bounds: BoundingBox;
  /** Original text */
  text: string;
  /** Font used */
  fontFamily: string;
  /** Font size */
  fontSize: number;
}

export interface CharacterVectorGroup {
  /** The character */
  character: string;
  /** Index in the original string */
  charIndex: number;
  /** Paths for this character (e.g., 'O' has outer and inner) */
  paths: BezierPath[];
  /** Bounding box for this character */
  bounds: BoundingBox;
  /** X advance (for positioning next character) */
  advanceWidth: number;
}

export interface BoundingBox {
  x: number;
  y: number;
  width: number;
  height: number;
}

export interface TextToVectorOptions {
  /** Font size in pixels */
  fontSize?: number;
  /** Letter spacing adjustment */
  letterSpacing?: number;
  /** Simplify paths (reduce point count) */
  simplify?: boolean;
  /** Simplification tolerance */
  simplifyTolerance?: number;
  /** Flatten curves to line segments (for LOD) */
  flattenCurves?: boolean;
  /** Curve flattening resolution */
  curveResolution?: number;
}

// ============================================================================
// Font Cache
// ============================================================================

/** Cache of loaded fonts */
const fontCache = new Map<string, opentype.Font>();

/** Font URL mapping (font family -> URL) */
const fontUrlMap = new Map<string, string>();

/**
 * Register a font URL for a font family name
 */
export function registerFontUrl(fontFamily: string, url: string): void {
  fontUrlMap.set(fontFamily.toLowerCase(), url);
}

/**
 * Load a font by family name
 * Returns cached font if already loaded
 */
export async function loadFont(fontFamily: string): Promise<opentype.Font> {
  const key = fontFamily.toLowerCase();

  // Check cache
  const cached = fontCache.get(key);
  if (cached) return cached;

  // Get URL from map or try to construct one
  let url = fontUrlMap.get(key);
  if (!url) {
    // Try Google Fonts as fallback
    url = `https://fonts.gstatic.com/s/${key.replace(/\s+/g, "")}/v1/${key.replace(/\s+/g, "")}-Regular.ttf`;
  }

  logger.info(`Loading font: ${fontFamily} from ${url}`);

  try {
    const font = await opentype.load(url);
    fontCache.set(key, font);
    return font;
  } catch (error) {
    logger.error(`Failed to load font ${fontFamily}:`, error);
    throw new Error(`Failed to load font: ${fontFamily}`);
  }
}

/**
 * Load font from ArrayBuffer
 */
export function loadFontFromBuffer(
  fontFamily: string,
  buffer: ArrayBuffer,
): opentype.Font {
  const font = opentype.parse(buffer);
  fontCache.set(fontFamily.toLowerCase(), font);
  return font;
}

/**
 * Clear font cache
 */
export function clearFontCache(): void {
  fontCache.clear();
}

// ============================================================================
// Text to Vector Conversion
// ============================================================================

const DEFAULT_OPTIONS: Required<TextToVectorOptions> = {
  fontSize: 72,
  letterSpacing: 0,
  simplify: false,
  simplifyTolerance: 0.5,
  flattenCurves: false,
  curveResolution: 16,
};

/**
 * Convert text to vector paths
 *
 * @param text The text to convert
 * @param fontFamily Font family name
 * @param options Conversion options
 */
export async function textToVector(
  text: string,
  fontFamily: string,
  options?: TextToVectorOptions,
): Promise<TextToVectorResult> {
  const opts = { ...DEFAULT_OPTIONS, ...options };

  // Load font
  const font = await loadFont(fontFamily);

  // Get the path from opentype
  const path = font.getPath(text, 0, 0, opts.fontSize);

  // Convert opentype commands to our BezierPath format
  const allPaths = commandsToBezierPaths(path.commands);

  // Get per-character paths
  const characters = getCharacterPaths(text, font, opts);

  // Calculate bounds
  const bbox = path.getBoundingBox();
  const bounds: BoundingBox = {
    x: bbox.x1,
    y: bbox.y1,
    width: bbox.x2 - bbox.x1,
    height: bbox.y2 - bbox.y1,
  };

  return {
    allPaths,
    characters,
    bounds,
    text,
    fontFamily,
    fontSize: opts.fontSize,
  };
}

/**
 * Get paths for each character individually
 */
function getCharacterPaths(
  text: string,
  font: opentype.Font,
  opts: Required<TextToVectorOptions>,
): CharacterVectorGroup[] {
  const groups: CharacterVectorGroup[] = [];
  let x = 0;

  for (let i = 0; i < text.length; i++) {
    const char = text[i];
    const glyph = font.charToGlyph(char);

    if (!glyph) {
      continue;
    }

    // Get path for this character
    const charPath = glyph.getPath(x, 0, opts.fontSize);
    const paths = commandsToBezierPaths(charPath.commands);

    // Get bounding box
    const bbox = charPath.getBoundingBox();
    const bounds: BoundingBox = {
      x: bbox.x1,
      y: bbox.y1,
      width: bbox.x2 - bbox.x1,
      height: bbox.y2 - bbox.y1,
    };

    // Calculate advance width
    const advanceWidth =
      (glyph.advanceWidth ?? 0) * (opts.fontSize / font.unitsPerEm);

    groups.push({
      character: char,
      charIndex: i,
      paths,
      bounds,
      advanceWidth,
    });

    // Advance position for next character
    x += advanceWidth + opts.letterSpacing;

    // Apply kerning if available
    if (i < text.length - 1) {
      const nextGlyph = font.charToGlyph(text[i + 1]);
      if (nextGlyph) {
        const kerning = font.getKerningValue(glyph, nextGlyph);
        x += kerning * (opts.fontSize / font.unitsPerEm);
      }
    }
  }

  return groups;
}

/**
 * Convert opentype path commands to BezierPath array
 */
function commandsToBezierPaths(commands: opentype.PathCommand[]): BezierPath[] {
  const paths: BezierPath[] = [];
  let currentPath: BezierVertex[] = [];
  let currentPoint: Point2D = { x: 0, y: 0 };
  let startPoint: Point2D = { x: 0, y: 0 };

  for (const cmd of commands) {
    switch (cmd.type) {
      case "M": // Move to
        if (currentPath.length > 0) {
          paths.push({ vertices: currentPath, closed: false });
          currentPath = [];
        }
        currentPoint = { x: cmd.x, y: cmd.y };
        startPoint = { ...currentPoint };
        break;

      case "L": // Line to
        currentPath.push({
          point: { ...currentPoint },
          inHandle: { x: 0, y: 0 },
          outHandle: { x: 0, y: 0 },
        });
        currentPoint = { x: cmd.x, y: cmd.y };
        break;

      case "C": // Cubic bezier
        currentPath.push({
          point: { ...currentPoint },
          inHandle: { x: 0, y: 0 },
          outHandle: {
            x: cmd.x1 - currentPoint.x,
            y: cmd.y1 - currentPoint.y,
          },
        });
        currentPoint = { x: cmd.x, y: cmd.y };
        break;

      case "Q": // Quadratic bezier - convert to cubic
        {
          const cp1x = currentPoint.x + (2 / 3) * (cmd.x1 - currentPoint.x);
          const cp1y = currentPoint.y + (2 / 3) * (cmd.y1 - currentPoint.y);

          currentPath.push({
            point: { ...currentPoint },
            inHandle: { x: 0, y: 0 },
            outHandle: {
              x: cp1x - currentPoint.x,
              y: cp1y - currentPoint.y,
            },
          });
          currentPoint = { x: cmd.x, y: cmd.y };
        }
        break;

      case "Z": // Close path
        currentPath.push({
          point: { ...currentPoint },
          inHandle: { x: 0, y: 0 },
          outHandle: { x: 0, y: 0 },
        });

        if (currentPath.length > 0) {
          paths.push({ vertices: currentPath, closed: true });
          currentPath = [];
        }
        currentPoint = { ...startPoint };
        break;
    }
  }

  if (currentPath.length > 0) {
    currentPath.push({
      point: { ...currentPoint },
      inHandle: { x: 0, y: 0 },
      outHandle: { x: 0, y: 0 },
    });
    paths.push({ vertices: currentPath, closed: false });
  }

  return paths;
}

// ============================================================================
// Layer Conversion
// ============================================================================

/**
 * Convert a text layer to spline layers
 */
export async function textLayerToSplines(
  textLayer: Layer,
  options?: TextToVectorOptions & {
    groupByCharacter?: boolean;
    preservePosition?: boolean;
  },
): Promise<{ layers: Partial<Layer>[]; result: TextToVectorResult }> {
  if (textLayer.type !== "text" || !textLayer.data) {
    throw new Error("Layer must be a text layer");
  }

  const textData = textLayer.data as {
    text?: string;
    font?: string;
    fontSize?: number;
  };

  const text = textData.text || "";
  const fontFamily = textData.font || "Arial";
  const fontSize = options?.fontSize ?? textData.fontSize ?? 72;

  const result = await textToVector(text, fontFamily, { ...options, fontSize });

  const layers: Partial<Layer>[] = [];
  const groupByCharacter = options?.groupByCharacter ?? true;

  const layerX = (textLayer.transform?.position?.value as any)?.x ?? 0;
  const layerY = (textLayer.transform?.position?.value as any)?.y ?? 0;

  if (groupByCharacter) {
    for (const charGroup of result.characters) {
      if (charGroup.paths.length === 0) continue;

      const controlPoints = bezierPathsToControlPoints(charGroup.paths);

      const splineData: SplineData = {
        pathData: "",
        controlPoints,
        closed: charGroup.paths[0]?.closed ?? false,
        stroke: "#ffffff",
        strokeWidth: 2,
        fill: "transparent",
      };

      layers.push({
        name: `${textLayer.name} - "${charGroup.character}"`,
        type: "spline",
        data: splineData,
        transform: {
          position: createAnimatableProperty(
            "Position",
            {
              x: layerX + charGroup.bounds.x,
              y: layerY + charGroup.bounds.y,
              z: 0,
            },
            "position",
          ),
          rotation:
            textLayer.transform?.rotation ??
            createAnimatableProperty("Rotation", 0, "number"),
          scale:
            textLayer.transform?.scale ??
            createAnimatableProperty("Scale", { x: 100, y: 100 }, "position"),
          anchorPoint: createAnimatableProperty(
            "Anchor Point",
            { x: 0, y: 0, z: 0 },
            "position",
          ),
        },
        inPoint: textLayer.inPoint,
        outPoint: textLayer.outPoint,
      } as Partial<Layer>);
    }
  } else {
    const allControlPoints = bezierPathsToControlPoints(result.allPaths);

    const splineData: SplineData = {
      pathData: "",
      controlPoints: allControlPoints,
      closed: result.allPaths[0]?.closed ?? false,
      stroke: "#ffffff",
      strokeWidth: 2,
      fill: "transparent",
    };

    layers.push({
      name: `${textLayer.name} - Vectorized`,
      type: "spline",
      data: splineData,
      transform: {
        position: createAnimatableProperty(
          "Position",
          {
            x: layerX + result.bounds.x,
            y: layerY + result.bounds.y,
            z: 0,
          },
          "position",
        ),
        rotation:
          textLayer.transform?.rotation ??
          createAnimatableProperty("Rotation", 0, "number"),
        scale:
          textLayer.transform?.scale ??
          createAnimatableProperty("Scale", { x: 100, y: 100 }, "position"),
        anchorPoint: createAnimatableProperty(
          "Anchor Point",
          { x: 0, y: 0, z: 0 },
          "position",
        ),
      },
      inPoint: textLayer.inPoint,
      outPoint: textLayer.outPoint,
    } as Partial<Layer>);
  }

  return { layers, result };
}

/**
 * Convert BezierPath array to ControlPoint array
 */
function bezierPathsToControlPoints(paths: BezierPath[]): ControlPoint[] {
  const controlPoints: ControlPoint[] = [];
  let globalIndex = 0;

  for (const path of paths) {
    for (let i = 0; i < path.vertices.length; i++) {
      const v = path.vertices[i];

      controlPoints.push({
        id: `cp_${globalIndex++}`,
        x: v.point.x,
        y: v.point.y,
        handleIn:
          v.inHandle.x !== 0 || v.inHandle.y !== 0
            ? { x: v.point.x + v.inHandle.x, y: v.point.y + v.inHandle.y }
            : null,
        handleOut:
          v.outHandle.x !== 0 || v.outHandle.y !== 0
            ? { x: v.point.x + v.outHandle.x, y: v.point.y + v.outHandle.y }
            : null,
        type: getPointType(v),
      });
    }
  }

  return controlPoints;
}

/**
 * Determine control point type based on handles
 */
function getPointType(v: BezierVertex): "corner" | "smooth" | "symmetric" {
  const hasIn = v.inHandle.x !== 0 || v.inHandle.y !== 0;
  const hasOut = v.outHandle.x !== 0 || v.outHandle.y !== 0;

  if (!hasIn && !hasOut) {
    return "corner";
  }

  if (hasIn && hasOut) {
    const inLen = Math.sqrt(v.inHandle.x ** 2 + v.inHandle.y ** 2);
    const outLen = Math.sqrt(v.outHandle.x ** 2 + v.outHandle.y ** 2);

    if (Math.abs(inLen - outLen) < 0.1) {
      const cross = v.inHandle.x * v.outHandle.y - v.inHandle.y * v.outHandle.x;
      if (Math.abs(cross) < 0.1) {
        return "symmetric";
      }
    }
    return "smooth";
  }

  return "corner";
}

// ============================================================================
// URL-Based Text to Vector (for layerActions integration)
// ============================================================================

export interface TextToVectorFromUrlOptions {
  x?: number;
  y?: number;
  kerning?: boolean;
  letterSpacing?: number;
}

/**
 * Convert text to vector paths using a font URL directly
 * Used by layerActions for text-to-spline conversion
 */
export async function textToVectorFromUrl(
  text: string,
  fontUrl: string,
  fontSize: number,
  options?: TextToVectorFromUrlOptions,
): Promise<TextToVectorResult> {
  const opts = {
    x: options?.x ?? 0,
    y: options?.y ?? 0,
    kerning: options?.kerning ?? true,
    letterSpacing: options?.letterSpacing ?? 0,
  };

  // Load font from URL
  let font: opentype.Font;
  try {
    font = await opentype.load(fontUrl);
  } catch (error) {
    logger.error(`Failed to load font from URL ${fontUrl}:`, error);
    throw new Error(`Failed to load font from URL: ${fontUrl}`);
  }

  // Get the path from opentype
  const path = font.getPath(text, opts.x, opts.y, fontSize);

  // Convert opentype commands to our BezierPath format
  const allPaths = commandsToBezierPaths(path.commands);

  // Get per-character paths
  const characters: CharacterVectorGroup[] = [];
  let x = opts.x;

  for (let i = 0; i < text.length; i++) {
    const char = text[i];
    const glyph = font.charToGlyph(char);

    if (!glyph) {
      continue;
    }

    // Get path for this character
    const charPath = glyph.getPath(x, opts.y, fontSize);
    const paths = commandsToBezierPaths(charPath.commands);

    // Get bounding box
    const bbox = charPath.getBoundingBox();
    const bounds: BoundingBox = {
      x: bbox.x1,
      y: bbox.y1,
      width: bbox.x2 - bbox.x1,
      height: bbox.y2 - bbox.y1,
    };

    // Calculate advance width
    const advanceWidth =
      (glyph.advanceWidth ?? 0) * (fontSize / font.unitsPerEm);

    characters.push({
      character: char,
      charIndex: i,
      paths,
      bounds,
      advanceWidth,
    });

    // Advance position for next character
    x += advanceWidth + opts.letterSpacing;

    // Apply kerning if available and enabled
    if (opts.kerning && i < text.length - 1) {
      const nextGlyph = font.charToGlyph(text[i + 1]);
      if (nextGlyph) {
        const kerning = font.getKerningValue(glyph, nextGlyph);
        x += kerning * (fontSize / font.unitsPerEm);
      }
    }
  }

  // Calculate overall bounds
  const pathBbox = path.getBoundingBox();
  const bounds: BoundingBox = {
    x: pathBbox.x1,
    y: pathBbox.y1,
    width: pathBbox.x2 - pathBbox.x1,
    height: pathBbox.y2 - pathBbox.y1,
  };

  return {
    allPaths,
    characters,
    bounds,
    text,
    fontFamily: font.names.fontFamily?.en || "Unknown",
    fontSize,
  };
}

export default {
  textToVector,
  textToVectorFromUrl,
  textLayerToSplines,
  loadFont,
  loadFontFromBuffer,
  registerFontUrl,
  clearFontCache,
};
