# 7. CORE SERVICES

## 7.1 Arc Length Parameterization (ui/src/services/arcLength.ts)

```typescript
/**
 * Arc Length Parameterization for Bezier Curves
 *
 * Bezier.js does NOT have a built-in arc-length to t conversion.
 * This class builds a lookup table for efficient distance -> parameter mapping.
 */
import Bezier from 'bezier-js';

interface ArcLengthEntry {
  t: number;
  length: number;
}

interface PointOnPath {
  point: { x: number; y: number };
  tangent: { x: number; y: number };
  t: number;
}

export class ArcLengthParameterizer {
  private curve: Bezier;
  private lut: ArcLengthEntry[];
  public totalLength: number;

  /**
   * @param curve - Bezier.js curve instance
   * @param resolution - Number of samples for LUT (higher = more accurate)
   */
  constructor(curve: Bezier, resolution: number = 1000) {
    this.curve = curve;
    this.lut = [];
    this.totalLength = 0;

    this.buildLUT(resolution);
  }

  /**
   * Build the arc length lookup table
   */
  private buildLUT(resolution: number): void {
    let accumulatedLength = 0;
    let prevPoint = this.curve.get(0);

    for (let i = 0; i <= resolution; i++) {
      const t = i / resolution;
      const point = this.curve.get(t);

      if (i > 0) {
        const dx = point.x - prevPoint.x;
        const dy = point.y - prevPoint.y;
        accumulatedLength += Math.sqrt(dx * dx + dy * dy);
      }

      this.lut.push({
        t: t,
        length: accumulatedLength
      });

      prevPoint = point;
    }

    this.totalLength = accumulatedLength;
  }

  /**
   * Convert arc length distance to t parameter
   *
   * @param distance - Distance along curve (0 to totalLength)
   * @returns t parameter (0 to 1)
   */
  distanceToT(distance: number): number {
    if (distance <= 0) return 0;
    if (distance >= this.totalLength) return 1;

    // Binary search in LUT
    let low = 0;
    let high = this.lut.length - 1;

    while (low < high) {
      const mid = Math.floor((low + high) / 2);

      if (this.lut[mid].length < distance) {
        low = mid + 1;
      } else {
        high = mid;
      }
    }

    // Linear interpolation between LUT entries for precision
    const entry = this.lut[low];
    const prevEntry = this.lut[Math.max(0, low - 1)];

    if (entry.length === prevEntry.length) {
      return entry.t;
    }

    const ratio = (distance - prevEntry.length) / (entry.length - prevEntry.length);
    return prevEntry.t + ratio * (entry.t - prevEntry.t);
  }

  /**
   * Get point and tangent at arc length distance
   */
  getPointAtDistance(distance: number): PointOnPath {
    const t = this.distanceToT(distance);

    return {
      point: this.curve.get(t),
      tangent: this.curve.derivative(t),
      t: t
    };
  }

  /**
   * Get evenly spaced points along the curve
   *
   * @param count - Number of points
   * @returns Array of points with position and tangent
   */
  getEvenlySpacedPoints(count: number): PointOnPath[] {
    const points: PointOnPath[] = [];
    const spacing = this.totalLength / (count - 1);

    for (let i = 0; i < count; i++) {
      const distance = i * spacing;
      points.push(this.getPointAtDistance(distance));
    }

    return points;
  }
}

/**
 * Convert Fabric.js path commands to Bezier.js curves
 */
export function fabricPathToBezier(pathCommands: any[]): Bezier | null {
  if (!pathCommands || pathCommands.length < 2) {
    return null;
  }

  let startPoint: { x: number; y: number } | null = null;

  for (const cmd of pathCommands) {
    const [command, ...coords] = cmd;

    if (command === 'M') {
      startPoint = { x: coords[0], y: coords[1] };
    } else if (command === 'C' && startPoint) {
      // Cubic bezier: startPoint, control1, control2, endPoint
      return new Bezier(
        startPoint.x, startPoint.y,
        coords[0], coords[1],  // control point 1
        coords[2], coords[3],  // control point 2
        coords[4], coords[5]   // end point
      );
    } else if (command === 'Q' && startPoint) {
      // Quadratic bezier
      return new Bezier(
        startPoint.x, startPoint.y,
        coords[0], coords[1],  // control point
        coords[2], coords[3]   // end point
      );
    }
  }

  return null;
}

export default ArcLengthParameterizer;
```

## 7.2 Font Service (ui/src/services/fontService.ts)

```typescript
/**
 * Font Loading and Enumeration Service
 *
 * Handles: Web-safe fonts, Google Fonts, and Local Font Access API (Chrome/Edge)
 */

interface FontInfo {
  family: string;
  fullName: string;
  style: string;
  source: 'system' | 'websafe' | 'google';
}

interface FontCategory {
  name: string;
  fonts: FontInfo[];
}

// Web-safe fonts that work everywhere
const WEB_SAFE_FONTS: FontInfo[] = [
  { family: 'Arial', fullName: 'Arial', style: 'normal', source: 'websafe' },
  { family: 'Arial Black', fullName: 'Arial Black', style: 'normal', source: 'websafe' },
  { family: 'Verdana', fullName: 'Verdana', style: 'normal', source: 'websafe' },
  { family: 'Tahoma', fullName: 'Tahoma', style: 'normal', source: 'websafe' },
  { family: 'Trebuchet MS', fullName: 'Trebuchet MS', style: 'normal', source: 'websafe' },
  { family: 'Times New Roman', fullName: 'Times New Roman', style: 'normal', source: 'websafe' },
  { family: 'Georgia', fullName: 'Georgia', style: 'normal', source: 'websafe' },
  { family: 'Courier New', fullName: 'Courier New', style: 'normal', source: 'websafe' },
  { family: 'Impact', fullName: 'Impact', style: 'normal', source: 'websafe' },
  { family: 'Comic Sans MS', fullName: 'Comic Sans MS', style: 'normal', source: 'websafe' },
];

// Popular Google Fonts
const GOOGLE_FONTS = [
  'Roboto', 'Open Sans', 'Lato', 'Montserrat', 'Oswald',
  'Raleway', 'Poppins', 'Nunito', 'Playfair Display', 'Merriweather',
  'Ubuntu', 'PT Sans', 'Roboto Mono', 'Bebas Neue', 'Source Sans Pro'
];

class FontService {
  private systemFonts: FontInfo[] = [];
  private loadedGoogleFonts: Set<string> = new Set();
  private initialized: boolean = false;

  /**
   * Initialize font service and attempt to load system fonts
   */
  async initialize(): Promise<void> {
    if (this.initialized) return;

    // Try to load system fonts (Chrome/Edge 103+ only)
    if ('queryLocalFonts' in window) {
      await this.loadSystemFonts();
    }

    this.initialized = true;
  }

  /**
   * Load system fonts using Local Font Access API
   * Requires user permission
   */
  private async loadSystemFonts(): Promise<void> {
    try {
      // This will prompt for permission
      const fonts = await (window as any).queryLocalFonts();

      // Group by family, keep one entry per family
      const familyMap = new Map<string, FontInfo>();

      for (const font of fonts) {
        if (!familyMap.has(font.family) || font.style === 'Regular') {
          familyMap.set(font.family, {
            family: font.family,
            fullName: font.fullName,
            style: font.style,
            source: 'system'
          });
        }
      }

      this.systemFonts = Array.from(familyMap.values())
        .sort((a, b) => a.family.localeCompare(b.family));

      console.log(`[FontService] Loaded ${this.systemFonts.length} system fonts`);
    } catch (error) {
      if ((error as Error).name === 'NotAllowedError') {
        console.log('[FontService] User denied font access permission');
      } else {
        console.error('[FontService] Error loading system fonts:', error);
      }
    }
  }

  /**
   * Get all available fonts organized by category
   */
  getFontCategories(): FontCategory[] {
    const categories: FontCategory[] = [];

    // System fonts (if available)
    if (this.systemFonts.length > 0) {
      categories.push({
        name: 'System Fonts',
        fonts: this.systemFonts
      });
    }

    // Web-safe fonts
    categories.push({
      name: 'Web Safe',
      fonts: WEB_SAFE_FONTS
    });

    // Google Fonts
    categories.push({
      name: 'Google Fonts',
      fonts: GOOGLE_FONTS.map(family => ({
        family,
        fullName: family,
        style: 'normal',
        source: 'google' as const
      }))
    });

    return categories;
  }

  /**
   * Get flat list of all font families
   */
  getAllFontFamilies(): string[] {
    const families = new Set<string>();

    WEB_SAFE_FONTS.forEach(f => families.add(f.family));
    GOOGLE_FONTS.forEach(f => families.add(f));
    this.systemFonts.forEach(f => families.add(f.family));

    return Array.from(families).sort();
  }

  /**
   * Load a Google Font dynamically
   */
  async loadGoogleFont(family: string, weights: string[] = ['400', '700']): Promise<void> {
    if (this.loadedGoogleFonts.has(family)) return;

    const weightsStr = weights.join(';');
    const url = `https://fonts.googleapis.com/css2?family=${encodeURIComponent(family)}:wght@${weightsStr}&display=swap`;

    // Create and append link element
    const link = document.createElement('link');
    link.rel = 'stylesheet';
    link.href = url;
    document.head.appendChild(link);

    // Wait for font to be ready
    try {
      await document.fonts.load(`400 16px "${family}"`);
      this.loadedGoogleFonts.add(family);
      console.log(`[FontService] Loaded Google Font: ${family}`);
    } catch (error) {
      console.error(`[FontService] Failed to load Google Font: ${family}`, error);
    }
  }

  /**
   * Ensure a font is available before using it
   */
  async ensureFont(family: string): Promise<boolean> {
    // Check if it's web-safe
    if (WEB_SAFE_FONTS.some(f => f.family === family)) {
      return true;
    }

    // Check if it's a Google Font
    if (GOOGLE_FONTS.includes(family)) {
      await this.loadGoogleFont(family);
      return true;
    }

    // Check if it's a loaded system font
    if (this.systemFonts.some(f => f.family === family)) {
      return true;
    }

    // Try to detect if font is available
    return this.isFontAvailable(family);
  }

  /**
   * Check if a font is available by measuring text
   */
  private isFontAvailable(family: string): boolean {
    const testString = 'mmmmmmmmmmlli';
    const canvas = document.createElement('canvas');
    const ctx = canvas.getContext('2d')!;

    // Measure with monospace fallback
    ctx.font = '72px monospace';
    const fallbackWidth = ctx.measureText(testString).width;

    // Measure with requested font
    ctx.font = `72px "${family}", monospace`;
    const testWidth = ctx.measureText(testString).width;

    return fallbackWidth !== testWidth;
  }
}

// Singleton instance
export const fontService = new FontService();
export default fontService;
```

## 7.3 Keyframe Interpolation (ui/src/services/interpolation.ts)

```typescript
/**
 * Keyframe Interpolation Engine
 *
 * Handles linear, bezier, and hold interpolation between keyframes.
 */
import type { Keyframe, AnimatableProperty, BezierHandle } from '@/types/project';

/**
 * Interpolate a property value at a given frame
 */
export function interpolateProperty<T>(
  property: AnimatableProperty<T>,
  frame: number
): T {
  // If not animated, return static value
  if (!property.animated || property.keyframes.length === 0) {
    return property.value;
  }

  const keyframes = property.keyframes;

  // Before first keyframe - return first keyframe value
  if (frame <= keyframes[0].frame) {
    return keyframes[0].value;
  }

  // After last keyframe - return last keyframe value
  if (frame >= keyframes[keyframes.length - 1].frame) {
    return keyframes[keyframes.length - 1].value;
  }

  // Find surrounding keyframes
  let k1: Keyframe<T> = keyframes[0];
  let k2: Keyframe<T> = keyframes[1];

  for (let i = 0; i < keyframes.length - 1; i++) {
    if (frame >= keyframes[i].frame && frame <= keyframes[i + 1].frame) {
      k1 = keyframes[i];
      k2 = keyframes[i + 1];
      break;
    }
  }

  // Calculate t (0-1) between keyframes
  const duration = k2.frame - k1.frame;
  const elapsed = frame - k1.frame;
  let t = duration > 0 ? elapsed / duration : 0;

  // Apply interpolation based on type
  switch (k1.interpolation) {
    case 'hold':
      return k1.value;

    case 'bezier':
      t = cubicBezierEasing(t, k1.outHandle, k2.inHandle);
      break;

    case 'linear':
    default:
      // t stays linear
      break;
  }

  // Interpolate the value based on type
  return interpolateValue(k1.value, k2.value, t);
}

/**
 * Cubic bezier easing function
 *
 * @param t - Linear time (0-1)
 * @param outHandle - First keyframe's out handle
 * @param inHandle - Second keyframe's in handle
 * @returns Eased time (0-1, can overshoot)
 */
function cubicBezierEasing(
  t: number,
  outHandle: BezierHandle,
  inHandle: BezierHandle
): number {
  // Control points for the easing curve
  // P0 = (0, 0), P1 = outHandle, P2 = (1-inHandle.x, 1-inHandle.y), P3 = (1, 1)
  const x1 = outHandle.x;
  const y1 = outHandle.y;
  const x2 = 1 - inHandle.x;
  const y2 = 1 - inHandle.y;

  // Find t value for given x using Newton-Raphson iteration
  let guessT = t;

  for (let i = 0; i < 8; i++) {
    const currentX = bezierPoint(guessT, 0, x1, x2, 1);
    const currentSlope = bezierDerivative(guessT, 0, x1, x2, 1);

    if (Math.abs(currentSlope) < 1e-6) break;

    const error = currentX - t;
    guessT -= error / currentSlope;

    guessT = Math.max(0, Math.min(1, guessT));
  }

  // Return y value at found t
  return bezierPoint(guessT, 0, y1, y2, 1);
}

/**
 * Cubic bezier point calculation
 */
function bezierPoint(t: number, p0: number, p1: number, p2: number, p3: number): number {
  const mt = 1 - t;
  return (
    mt * mt * mt * p0 +
    3 * mt * mt * t * p1 +
    3 * mt * t * t * p2 +
    t * t * t * p3
  );
}

/**
 * Cubic bezier derivative
 */
function bezierDerivative(t: number, p0: number, p1: number, p2: number, p3: number): number {
  const mt = 1 - t;
  return (
    3 * mt * mt * (p1 - p0) +
    6 * mt * t * (p2 - p1) +
    3 * t * t * (p3 - p2)
  );
}

/**
 * Interpolate between two values based on their type
 */
function interpolateValue<T>(v1: T, v2: T, t: number): T {
  // Number
  if (typeof v1 === 'number' && typeof v2 === 'number') {
    return (v1 + (v2 - v1) * t) as T;
  }

  // Position object
  if (
    typeof v1 === 'object' && v1 !== null &&
    'x' in v1 && 'y' in v1 &&
    typeof v2 === 'object' && v2 !== null &&
    'x' in v2 && 'y' in v2
  ) {
    return {
      x: (v1 as any).x + ((v2 as any).x - (v1 as any).x) * t,
      y: (v1 as any).y + ((v2 as any).y - (v1 as any).y) * t
    } as T;
  }

  // Color (hex string)
  if (typeof v1 === 'string' && typeof v2 === 'string' &&
      v1.startsWith('#') && v2.startsWith('#')) {
    return interpolateColor(v1, v2, t) as T;
  }

  // Default: no interpolation, return first value until t >= 0.5
  return t < 0.5 ? v1 : v2;
}

/**
 * Interpolate between two hex colors
 */
function interpolateColor(c1: string, c2: string, t: number): string {
  const r1 = parseInt(c1.slice(1, 3), 16);
  const g1 = parseInt(c1.slice(3, 5), 16);
  const b1 = parseInt(c1.slice(5, 7), 16);

  const r2 = parseInt(c2.slice(1, 3), 16);
  const g2 = parseInt(c2.slice(3, 5), 16);
  const b2 = parseInt(c2.slice(5, 7), 16);

  const r = Math.round(r1 + (r2 - r1) * t);
  const g = Math.round(g1 + (g2 - g1) * t);
  const b = Math.round(b1 + (b2 - b1) * t);

  return `#${r.toString(16).padStart(2, '0')}${g.toString(16).padStart(2, '0')}${b.toString(16).padStart(2, '0')}`;
}

/**
 * Easing presets
 */
export const EASING_PRESETS = {
  linear: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.33, y: 0.33 }
  },
  easeIn: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.33, y: 0.33 }
  },
  easeOut: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.58, y: 1 }
  },
  easeInOut: {
    outHandle: { x: 0.42, y: 0 },
    inHandle: { x: 0.58, y: 1 }
  },
  easeOutBack: {
    outHandle: { x: 0.33, y: 0.33 },
    inHandle: { x: 0.34, y: 1.56 }  // Overshoot
  }
};

/**
 * Apply an easing preset to a keyframe
 */
export function applyEasingPreset(
  keyframe: Keyframe<any>,
  presetName: keyof typeof EASING_PRESETS,
  direction: 'in' | 'out' | 'both' = 'both'
): void {
  const preset = EASING_PRESETS[presetName];

  if (direction === 'in' || direction === 'both') {
    keyframe.inHandle = { ...preset.inHandle };
  }

  if (direction === 'out' || direction === 'both') {
    keyframe.outHandle = { ...preset.outHandle };
  }

  keyframe.interpolation = presetName === 'linear' ? 'linear' : 'bezier';
}

export default { interpolateProperty, applyEasingPreset, EASING_PRESETS };
```

## 7.4 Matte Exporter (ui/src/services/matteExporter.ts)

```typescript
/**
 * Matte Export Service
 *
 * Generates frame sequences with text excluded for Wan video generation.
 */
import type { WeylProject, Layer, TextData } from '@/types/project';
import { interpolateProperty } from './interpolation';
import { ArcLengthParameterizer, fabricPathToBezier } from './arcLength';

interface ExportProgress {
  frame: number;
  total: number;
  percent: number;
}

type ProgressCallback = (progress: ExportProgress) => void;

class MatteExporter {
  private offscreenCanvas: OffscreenCanvas | null = null;
  private ctx: OffscreenCanvasRenderingContext2D | null = null;

  /**
   * Validate dimensions for Wan model requirements
   */
  validateDimensions(width: number, height: number): {
    valid: boolean;
    correctedWidth: number;
    correctedHeight: number;
    message?: string;
  } {
    // Must be divisible by 8
    const correctedWidth = Math.round(width / 8) * 8;
    const correctedHeight = Math.round(height / 8) * 8;

    // Minimum 256px
    const finalWidth = Math.max(256, correctedWidth);
    const finalHeight = Math.max(256, correctedHeight);

    const valid = width === finalWidth && height === finalHeight;

    return {
      valid,
      correctedWidth: finalWidth,
      correctedHeight: finalHeight,
      message: valid ? undefined : `Adjusted to ${finalWidth}x${finalHeight} (divisible by 8)`
    };
  }

  /**
   * Generate matte sequence for all frames
   *
   * Wan mask format:
   * - White (255) = Keep original / generate content
   * - Black (0) = Exclude from generation
   *
   * For text exclusion: Text regions are BLACK, everything else WHITE
   */
  async generateMatteSequence(
    project: WeylProject,
    onProgress?: ProgressCallback
  ): Promise<Blob[]> {
    const { width, height, frameCount } = project.composition;

    // Initialize offscreen canvas
    this.offscreenCanvas = new OffscreenCanvas(width, height);
    this.ctx = this.offscreenCanvas.getContext('2d')!;

    const frames: Blob[] = [];

    for (let frame = 0; frame < frameCount; frame++) {
      // Report progress
      if (onProgress) {
        onProgress({
          frame,
          total: frameCount,
          percent: Math.round((frame / frameCount) * 100)
        });
      }

      // Generate frame
      const frameBlob = await this.generateFrame(project, frame);
      frames.push(frameBlob);
    }

    return frames;
  }

  /**
   * Generate a single matte frame
   */
  private async generateFrame(project: WeylProject, frame: number): Promise<Blob> {
    const ctx = this.ctx!;
    const { width, height } = project.composition;

    // Clear with WHITE (include everything by default)
    ctx.fillStyle = '#FFFFFF';
    ctx.fillRect(0, 0, width, height);

    // Set BLACK for exclusion
    ctx.fillStyle = '#000000';

    // Find text layers that are visible at this frame
    const textLayers = project.layers.filter(layer =>
      layer.type === 'text' &&
      layer.visible &&
      frame >= layer.inPoint &&
      frame <= layer.outPoint
    );

    for (const layer of textLayers) {
      await this.renderTextLayerToMatte(ctx, layer, project, frame);
    }

    // Convert to PNG blob
    return await this.offscreenCanvas!.convertToBlob({ type: 'image/png' });
  }

  /**
   * Render text layer as black region on matte
   */
  private async renderTextLayerToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    project: WeylProject,
    frame: number
  ): Promise<void> {
    const textData = layer.data as TextData;
    if (!textData) return;

    // Get animated font size
    const fontSizeProp = layer.properties.find(p => p.name === 'fontSize');
    const fontSize = fontSizeProp
      ? interpolateProperty(fontSizeProp, frame)
      : textData.fontSize;

    ctx.font = `${textData.fontWeight} ${fontSize}px "${textData.fontFamily}"`;

    // Check if text is on a path
    if (textData.pathLayerId) {
      await this.renderTextOnPathToMatte(ctx, layer, textData, project, frame, fontSize);
    } else {
      this.renderTextBlockToMatte(ctx, layer, textData, frame, fontSize);
    }
  }

  /**
   * Render text that follows a spline path
   */
  private async renderTextOnPathToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    textData: TextData,
    project: WeylProject,
    frame: number,
    fontSize: number
  ): Promise<void> {
    // Find the path layer
    const pathLayer = project.layers.find(l => l.id === textData.pathLayerId);
    if (!pathLayer || pathLayer.type !== 'spline') return;

    const splineData = pathLayer.data as any;
    if (!splineData?.pathData) return;

    // Parse path to Bezier curve
    const bezierCurve = fabricPathToBezier(splineData.pathData);
    if (!bezierCurve) return;

    // Create arc length parameterizer
    const parameterizer = new ArcLengthParameterizer(bezierCurve);

    // Get animated path offset
    const offsetProp = layer.properties.find(p => p.name === 'pathOffset');
    const pathOffset = offsetProp
      ? interpolateProperty(offsetProp, frame)
      : textData.pathOffset;

    const totalLength = parameterizer.totalLength;
    let currentDistance = pathOffset * totalLength;

    // Render each character as a black rectangle
    const padding = 4; // Extra padding around characters

    for (const char of textData.text) {
      const charWidth = ctx.measureText(char).width;

      const { point, tangent } = parameterizer.getPointAtDistance(currentDistance);
      const angle = Math.atan2(tangent.y, tangent.x);

      ctx.save();
      ctx.translate(point.x, point.y);
      ctx.rotate(angle);

      // Draw black rectangle covering the character
      ctx.fillRect(
        -padding,
        -fontSize - padding,
        charWidth + padding * 2,
        fontSize + padding * 2
      );

      ctx.restore();

      currentDistance += charWidth + textData.letterSpacing;
    }
  }

  /**
   * Render regular text block (not on path)
   */
  private renderTextBlockToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    textData: TextData,
    frame: number,
    fontSize: number
  ): void {
    // Get transform
    const positionProp = layer.transform.position;
    const position = interpolateProperty(positionProp, frame);

    const rotationProp = layer.transform.rotation;
    const rotation = interpolateProperty(rotationProp, frame);

    const scaleProp = layer.transform.scale;
    const scale = interpolateProperty(scaleProp, frame);

    ctx.save();
    ctx.translate(position.x, position.y);
    ctx.rotate((rotation * Math.PI) / 180);
    ctx.scale(scale.x, scale.y);

    // Measure text
    const metrics = ctx.measureText(textData.text);
    const textWidth = metrics.width;
    const textHeight = fontSize;

    // Draw black rectangle
    const padding = 4;
    ctx.fillRect(
      -padding,
      -textHeight - padding,
      textWidth + padding * 2,
      textHeight + padding * 2
    );

    ctx.restore();
  }

  /**
   * Download frames as ZIP (requires JSZip)
   */
  async downloadAsZip(frames: Blob[], filename: string = 'matte_sequence'): Promise<void> {
    // Dynamic import JSZip
    const JSZip = (await import('jszip')).default;
    const zip = new JSZip();

    // Add frames to zip
    frames.forEach((blob, index) => {
      const frameName = `${filename}_${String(index).padStart(4, '0')}.png`;
      zip.file(frameName, blob);
    });

    // Generate and download
    const content = await zip.generateAsync({ type: 'blob' });

    const url = URL.createObjectURL(content);
    const link = document.createElement('a');
    link.href = url;
    link.download = `${filename}.zip`;
    link.click();

    URL.revokeObjectURL(url);
  }
}

export const matteExporter = new MatteExporter();
export default matteExporter;
```

## 7.5 Particle System (ui/src/services/particleSystem.ts)

```typescript
/**
 * GPU-accelerated particle system
 * Uses WebGL/WebGPU for rendering, falls back to Canvas2D
 */
import type {
  ParticleData,
  ParticleEmitter,
  ParticlePhysics,
  ParticleRendering
} from '@/types/project';
import { interpolateProperty } from './interpolation';

interface Particle {
  x: number;
  y: number;
  vx: number;
  vy: number;
  life: number;
  maxLife: number;
  size: number;
  rotation: number;
  rotationSpeed: number;
  color: string;
  opacity: number;
}

export class ParticleSystem {
  private particles: Particle[] = [];
  private emitterData: ParticleData;
  private maxParticles: number = 10000;

  // Noise for turbulence
  private noiseOffset: number = Math.random() * 1000;

  constructor(data: ParticleData) {
    this.emitterData = data;
  }

  /**
   * Update particle system for a given frame
   */
  update(frame: number, deltaTime: number = 1/16): void {
    const emitter = this.emitterData.emitter;
    const physics = this.emitterData.physics;
    const rendering = this.emitterData.rendering;

    // Get animated values at current frame
    const emitRate = interpolateProperty(emitter.rate, frame);
    const gravity = interpolateProperty(physics.gravity, frame);
    const wind = interpolateProperty(physics.wind, frame);
    const drag = interpolateProperty(physics.drag, frame);
    const turbulence = interpolateProperty(physics.turbulence, frame);

    // Emit new particles
    const emitCount = Math.floor(emitRate * deltaTime);
    for (let i = 0; i < emitCount && this.particles.length < this.maxParticles; i++) {
      this.emitParticle(frame);
    }

    // Update existing particles
    for (let i = this.particles.length - 1; i >= 0; i--) {
      const p = this.particles[i];

      // Age
      p.life -= deltaTime;
      if (p.life <= 0) {
        this.particles.splice(i, 1);
        continue;
      }

      // Physics
      p.vx += gravity.x * deltaTime;
      p.vy += gravity.y * deltaTime;
      p.vx += wind.x * deltaTime;
      p.vy += wind.y * deltaTime;

      // Turbulence (simplex noise)
      if (turbulence > 0) {
        const noiseX = this.noise2D(p.x * 0.01, p.y * 0.01 + this.noiseOffset);
        const noiseY = this.noise2D(p.x * 0.01 + 100, p.y * 0.01 + this.noiseOffset);
        p.vx += noiseX * turbulence * deltaTime;
        p.vy += noiseY * turbulence * deltaTime;
      }

      // Drag
      p.vx *= (1 - drag * deltaTime);
      p.vy *= (1 - drag * deltaTime);

      // Position
      p.x += p.vx * deltaTime * 60;  // 60 for pixels/second
      p.y += p.vy * deltaTime * 60;

      // Rotation
      p.rotation += p.rotationSpeed * deltaTime;

      // Interpolate size, color, opacity over lifetime
      const lifeRatio = 1 - (p.life / p.maxLife);
      const startSize = interpolateProperty(rendering.startSize, frame);
      const endSize = interpolateProperty(rendering.endSize, frame);
      p.size = startSize + (endSize - startSize) * lifeRatio;

      const startOpacity = interpolateProperty(rendering.startOpacity, frame);
      const endOpacity = interpolateProperty(rendering.endOpacity, frame);
      p.opacity = startOpacity + (endOpacity - startOpacity) * lifeRatio;
    }

    this.noiseOffset += deltaTime * 0.1;
  }

  /**
   * Emit a single particle
   */
  private emitParticle(frame: number): void {
    const emitter = this.emitterData.emitter;
    const rendering = this.emitterData.rendering;

    const pos = interpolateProperty(emitter.position, frame);
    const speed = interpolateProperty(emitter.speed, frame);
    const direction = interpolateProperty(emitter.direction, frame);
    const spread = interpolateProperty(emitter.spread, frame);
    const lifetime = interpolateProperty(emitter.lifetime, frame);

    // Apply variance
    const actualSpeed = speed * (1 + (Math.random() - 0.5) * 2 * emitter.speedVariance);
    const actualDir = direction + (Math.random() - 0.5) * spread;
    const actualLife = lifetime * (1 + (Math.random() - 0.5) * 2 * emitter.lifetimeVariance);

    const dirRad = actualDir * Math.PI / 180;

    const particle: Particle = {
      x: pos.x + this.getEmitterOffset(emitter, 'x'),
      y: pos.y + this.getEmitterOffset(emitter, 'y'),
      vx: Math.cos(dirRad) * actualSpeed,
      vy: Math.sin(dirRad) * actualSpeed,
      life: actualLife,
      maxLife: actualLife,
      size: interpolateProperty(rendering.startSize, frame),
      rotation: interpolateProperty(rendering.rotation, frame) * (Math.PI / 180),
      rotationSpeed: interpolateProperty(rendering.rotationSpeed, frame) * (Math.PI / 180),
      color: interpolateProperty(rendering.startColor, frame),
      opacity: interpolateProperty(rendering.startOpacity, frame)
    };

    this.particles.push(particle);
  }

  /**
   * Get random offset based on emitter shape
   */
  private getEmitterOffset(emitter: ParticleEmitter, axis: 'x' | 'y'): number {
    switch (emitter.type) {
      case 'point':
        return 0;
      case 'circle':
        const angle = Math.random() * Math.PI * 2;
        const r = Math.sqrt(Math.random()) * (emitter.radius?.value || 50);
        return axis === 'x' ? Math.cos(angle) * r : Math.sin(angle) * r;
      case 'box':
        const w = emitter.width?.value || 100;
        const h = emitter.height?.value || 100;
        return axis === 'x'
          ? (Math.random() - 0.5) * w
          : (Math.random() - 0.5) * h;
      default:
        return 0;
    }
  }

  /**
   * Render particles to canvas
   */
  render(
    ctx: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D,
    texture?: HTMLImageElement | ImageBitmap
  ): void {
    const rendering = this.emitterData.rendering;

    ctx.save();
    ctx.globalCompositeOperation = this.blendModeToComposite(rendering.blendMode);

    for (const p of this.particles) {
      ctx.save();
      ctx.translate(p.x, p.y);
      ctx.rotate(p.rotation);
      ctx.globalAlpha = p.opacity;

      if (texture) {
        // Draw texture
        const halfSize = p.size / 2;
        ctx.drawImage(texture, -halfSize, -halfSize, p.size, p.size);
      } else {
        // Draw circle fallback
        ctx.fillStyle = p.color;
        ctx.beginPath();
        ctx.arc(0, 0, p.size / 2, 0, Math.PI * 2);
        ctx.fill();
      }

      ctx.restore();
    }

    ctx.restore();
  }

  /**
   * Get particle data for WebGPU rendering
   */
  getParticleBuffer(): Float32Array {
    const data = new Float32Array(this.particles.length * 8);

    for (let i = 0; i < this.particles.length; i++) {
      const p = this.particles[i];
      const offset = i * 8;
      data[offset + 0] = p.x;
      data[offset + 1] = p.y;
      data[offset + 2] = p.size;
      data[offset + 3] = p.rotation;
      data[offset + 4] = p.opacity;
      // Pack color as RGB
      const color = this.hexToRgb(p.color);
      data[offset + 5] = color.r / 255;
      data[offset + 6] = color.g / 255;
      data[offset + 7] = color.b / 255;
    }

    return data;
  }

  get particleCount(): number {
    return this.particles.length;
  }

  private blendModeToComposite(mode: string): GlobalCompositeOperation {
    const map: Record<string, GlobalCompositeOperation> = {
      'normal': 'source-over',
      'multiply': 'multiply',
      'screen': 'screen',
      'overlay': 'overlay',
      'add': 'lighter',
      'difference': 'difference'
    };
    return map[mode] || 'source-over';
  }

  private hexToRgb(hex: string): { r: number; g: number; b: number } {
    const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return result ? {
      r: parseInt(result[1], 16),
      g: parseInt(result[2], 16),
      b: parseInt(result[3], 16)
    } : { r: 255, g: 255, b: 255 };
  }

  // Simple 2D noise (replace with proper simplex noise in production)
  private noise2D(x: number, y: number): number {
    const n = Math.sin(x * 12.9898 + y * 78.233) * 43758.5453;
    return (n - Math.floor(n)) * 2 - 1;
  }
}
```

## 7.6 Texture Extraction Service (ui/src/services/textureExtraction.ts)

```typescript
/**
 * Texture extraction from images using MatSeg-inspired approach
 * Works entirely client-side for basic extraction,
 * calls backend for SDXL generation
 */

interface ExtractedRegion {
  x: number;
  y: number;
  width: number;
  height: number;
  texture: ImageData;
  uniformityScore: number;
}

interface PBRMaps {
  albedo: ImageData;
  roughness: ImageData;
  metallic: ImageData;
  normal: ImageData;
  height: ImageData;
  ao: ImageData;
}

export class TextureExtractionService {
  private cellSize: number = 40;
  private minCells: number = 6;
  private jsDivergenceThreshold: number = 0.5;

  /**
   * Find uniform texture regions in an image
   * Based on MatSeg paper Section 3.2.1
   */
  async extractUniformRegions(imageData: ImageData): Promise<ExtractedRegion[]> {
    const { width, height, data } = imageData;
    const cellsX = Math.floor(width / this.cellSize);
    const cellsY = Math.floor(height / this.cellSize);

    // Compute color histogram for each cell
    const cellHistograms: Map<string, number[][]> = new Map();

    for (let cy = 0; cy < cellsY; cy++) {
      for (let cx = 0; cx < cellsX; cx++) {
        const histogram = this.computeCellHistogram(
          data, width,
          cx * this.cellSize, cy * this.cellSize,
          this.cellSize, this.cellSize
        );
        cellHistograms.set(`${cx},${cy}`, histogram);
      }
    }

    // Find connected regions with similar histograms
    const regions: ExtractedRegion[] = [];
    const visited = new Set<string>();

    for (let cy = 0; cy < cellsY; cy++) {
      for (let cx = 0; cx < cellsX; cx++) {
        const key = `${cx},${cy}`;
        if (visited.has(key)) continue;

        // Flood fill to find uniform region
        const regionCells = this.floodFillUniform(
          cx, cy, cellsX, cellsY,
          cellHistograms, visited
        );

        if (regionCells.length >= this.minCells * this.minCells) {
          const region = this.extractRegionTexture(
            imageData, regionCells, this.cellSize
          );
          regions.push(region);
        }
      }
    }

    return regions;
  }

  /**
   * Generate PBR material maps from RGB texture
   * Based on MatSeg paper Section 3.2.2
   */
  generatePBRMaps(texture: ImageData): PBRMaps {
    const { width, height, data } = texture;

    // Split into channels
    const r = new Uint8ClampedArray(width * height);
    const g = new Uint8ClampedArray(width * height);
    const b = new Uint8ClampedArray(width * height);
    const h = new Uint8ClampedArray(width * height);
    const s = new Uint8ClampedArray(width * height);
    const v = new Uint8ClampedArray(width * height);

    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      r[i] = data[idx];
      g[i] = data[idx + 1];
      b[i] = data[idx + 2];

      // Convert to HSV
      const hsv = this.rgbToHsv(data[idx], data[idx + 1], data[idx + 2]);
      h[i] = hsv.h;
      s[i] = hsv.s;
      v[i] = hsv.v;
    }

    // Generate maps using heuristics from the paper
    // "properties of the material (reflectivity, roughness, transparency)
    //  are correlated with simple image properties like color"

    return {
      albedo: texture,

      // Roughness: inverse of saturation (low saturation = rough surfaces)
      roughness: this.channelToImageData(
        this.invertChannel(s), width, height
      ),

      // Metallic: high saturation regions
      metallic: this.channelToImageData(
        this.thresholdChannel(s, 180), width, height
      ),

      // Height: value channel (brighter = higher)
      height: this.channelToImageData(v, width, height),

      // Normal: derived from height using Sobel
      normal: this.heightToNormal(v, width, height),

      // Ambient Occlusion: darkened value
      ao: this.channelToImageData(
        this.gaussianBlur(this.invertChannel(v), width, height, 3),
        width, height
      )
    };
  }

  /**
   * Make texture seamlessly tileable
   */
  makeSeamless(texture: ImageData, blendWidth: number = 32): ImageData {
    const { width, height } = texture;
    const result = new ImageData(width, height);
    result.data.set(texture.data);

    // Blend edges using offset blending technique
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < blendWidth; x++) {
        const t = x / blendWidth;
        const smoothT = t * t * (3 - 2 * t); // Smoothstep

        // Horizontal seam
        const srcX = width - blendWidth + x;
        this.blendPixel(result, x, y, srcX, y, smoothT);
      }
    }

    for (let x = 0; x < width; x++) {
      for (let y = 0; y < blendWidth; y++) {
        const t = y / blendWidth;
        const smoothT = t * t * (3 - 2 * t);

        // Vertical seam
        const srcY = height - blendWidth + y;
        this.blendPixel(result, x, y, x, srcY, smoothT);
      }
    }

    return result;
  }

  /**
   * Request SDXL texture generation from backend
   */
  async generateTextureSDXL(prompt: string): Promise<{
    texture: ImageData;
    pbr: PBRMaps;
  }> {
    const response = await fetch('/weyl/generate/texture', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        prompt: `${prompt}, seamless, tileable, texture, 4k`,
        negative: 'seams, borders, text, watermark, logo'
      })
    });

    const data = await response.json();

    // Decode base64 results
    const textureImage = await this.base64ToImageData(data.texture);

    return {
      texture: textureImage,
      pbr: {
        albedo: textureImage,
        roughness: await this.base64ToImageData(data.pbr.roughness),
        metallic: await this.base64ToImageData(data.pbr.metallic),
        normal: await this.base64ToImageData(data.pbr.normal),
        height: await this.base64ToImageData(data.pbr.height),
        ao: await this.base64ToImageData(data.pbr.ao)
      }
    };
  }

  // === Helper methods ===

  private computeCellHistogram(
    data: Uint8ClampedArray,
    imageWidth: number,
    x: number, y: number,
    cellWidth: number, cellHeight: number
  ): number[][] {
    // 16-bin histogram for each RGB channel
    const bins = 16;
    const histR = new Array(bins).fill(0);
    const histG = new Array(bins).fill(0);
    const histB = new Array(bins).fill(0);

    for (let cy = 0; cy < cellHeight; cy++) {
      for (let cx = 0; cx < cellWidth; cx++) {
        const px = x + cx;
        const py = y + cy;
        const idx = (py * imageWidth + px) * 4;

        histR[Math.floor(data[idx] / 16)]++;
        histG[Math.floor(data[idx + 1] / 16)]++;
        histB[Math.floor(data[idx + 2] / 16)]++;
      }
    }

    // Normalize
    const total = cellWidth * cellHeight;
    return [
      histR.map(v => v / total),
      histG.map(v => v / total),
      histB.map(v => v / total)
    ];
  }

  private jensenShannonDivergence(p: number[], q: number[]): number {
    const m = p.map((pi, i) => (pi + q[i]) / 2);
    const klPM = this.klDivergence(p, m);
    const klQM = this.klDivergence(q, m);
    return (klPM + klQM) / 2;
  }

  private klDivergence(p: number[], q: number[]): number {
    let sum = 0;
    for (let i = 0; i < p.length; i++) {
      if (p[i] > 0 && q[i] > 0) {
        sum += p[i] * Math.log(p[i] / q[i]);
      }
    }
    return sum;
  }

  private floodFillUniform(
    startX: number, startY: number,
    maxX: number, maxY: number,
    histograms: Map<string, number[][]>,
    visited: Set<string>
  ): Array<{x: number; y: number}> {
    const region: Array<{x: number; y: number}> = [];
    const queue = [{x: startX, y: startY}];
    const startHist = histograms.get(`${startX},${startY}`)!;

    while (queue.length > 0) {
      const {x, y} = queue.shift()!;
      const key = `${x},${y}`;

      if (visited.has(key)) continue;
      if (x < 0 || x >= maxX || y < 0 || y >= maxY) continue;

      const hist = histograms.get(key)!;

      // Check similarity using Jensen-Shannon divergence
      let similar = true;
      for (let c = 0; c < 3; c++) {
        if (this.jensenShannonDivergence(startHist[c], hist[c]) > this.jsDivergenceThreshold) {
          similar = false;
          break;
        }
      }

      if (!similar) continue;

      visited.add(key);
      region.push({x, y});

      // Add neighbors
      queue.push({x: x + 1, y});
      queue.push({x: x - 1, y});
      queue.push({x, y: y + 1});
      queue.push({x, y: y - 1});
    }

    return region;
  }

  private rgbToHsv(r: number, g: number, b: number): {h: number; s: number; v: number} {
    r /= 255; g /= 255; b /= 255;
    const max = Math.max(r, g, b);
    const min = Math.min(r, g, b);
    const d = max - min;

    let h = 0;
    const s = max === 0 ? 0 : d / max;
    const v = max;

    if (max !== min) {
      switch (max) {
        case r: h = (g - b) / d + (g < b ? 6 : 0); break;
        case g: h = (b - r) / d + 2; break;
        case b: h = (r - g) / d + 4; break;
      }
      h /= 6;
    }

    return {
      h: Math.round(h * 255),
      s: Math.round(s * 255),
      v: Math.round(v * 255)
    };
  }

  private invertChannel(channel: Uint8ClampedArray): Uint8ClampedArray {
    const result = new Uint8ClampedArray(channel.length);
    for (let i = 0; i < channel.length; i++) {
      result[i] = 255 - channel[i];
    }
    return result;
  }

  private thresholdChannel(channel: Uint8ClampedArray, threshold: number): Uint8ClampedArray {
    const result = new Uint8ClampedArray(channel.length);
    for (let i = 0; i < channel.length; i++) {
      result[i] = channel[i] > threshold ? 255 : 0;
    }
    return result;
  }

  private channelToImageData(channel: Uint8ClampedArray, width: number, height: number): ImageData {
    const data = new Uint8ClampedArray(width * height * 4);
    for (let i = 0; i < channel.length; i++) {
      const idx = i * 4;
      data[idx] = channel[i];
      data[idx + 1] = channel[i];
      data[idx + 2] = channel[i];
      data[idx + 3] = 255;
    }
    return new ImageData(data, width, height);
  }

  private heightToNormal(height: Uint8ClampedArray, width: number, height_: number): ImageData {
    const data = new Uint8ClampedArray(width * height_ * 4);
    const strength = 2.0;

    for (let y = 0; y < height_; y++) {
      for (let x = 0; x < width; x++) {
        const idx = y * width + x;

        // Sobel operator
        const left = x > 0 ? height[idx - 1] : height[idx];
        const right = x < width - 1 ? height[idx + 1] : height[idx];
        const up = y > 0 ? height[idx - width] : height[idx];
        const down = y < height_ - 1 ? height[idx + width] : height[idx];

        const dx = (right - left) / 255 * strength;
        const dy = (down - up) / 255 * strength;

        // Normal vector
        let nx = -dx;
        let ny = -dy;
        let nz = 1;

        // Normalize
        const len = Math.sqrt(nx*nx + ny*ny + nz*nz);
        nx /= len; ny /= len; nz /= len;

        // Convert to RGB (0-255 range, centered at 128)
        const outIdx = idx * 4;
        data[outIdx] = Math.round((nx * 0.5 + 0.5) * 255);
        data[outIdx + 1] = Math.round((ny * 0.5 + 0.5) * 255);
        data[outIdx + 2] = Math.round((nz * 0.5 + 0.5) * 255);
        data[outIdx + 3] = 255;
      }
    }

    return new ImageData(data, width, height_);
  }

  private gaussianBlur(
    channel: Uint8ClampedArray,
    width: number,
    height: number,
    radius: number
  ): Uint8ClampedArray {
    // Simple box blur approximation (3 passes ≈ Gaussian)
    let result = new Uint8ClampedArray(channel);

    for (let pass = 0; pass < 3; pass++) {
      const temp = new Uint8ClampedArray(result.length);

      for (let y = 0; y < height; y++) {
        for (let x = 0; x < width; x++) {
          let sum = 0;
          let count = 0;

          for (let dy = -radius; dy <= radius; dy++) {
            for (let dx = -radius; dx <= radius; dx++) {
              const nx = Math.max(0, Math.min(width - 1, x + dx));
              const ny = Math.max(0, Math.min(height - 1, y + dy));
              sum += result[ny * width + nx];
              count++;
            }
          }

          temp[y * width + x] = Math.round(sum / count);
        }
      }

      result = temp;
    }

    return result;
  }

  private blendPixel(
    target: ImageData,
    x1: number, y1: number,
    x2: number, y2: number,
    t: number
  ): void {
    const idx1 = (y1 * target.width + x1) * 4;
    const idx2 = (y2 * target.width + x2) * 4;

    for (let c = 0; c < 4; c++) {
      target.data[idx1 + c] = Math.round(
        target.data[idx1 + c] * (1 - t) + target.data[idx2 + c] * t
      );
    }
  }

  private extractRegionTexture(
    imageData: ImageData,
    cells: Array<{x: number; y: number}>,
    cellSize: number
  ): ExtractedRegion {
    // Find bounding box
    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;

    for (const cell of cells) {
      minX = Math.min(minX, cell.x * cellSize);
      minY = Math.min(minY, cell.y * cellSize);
      maxX = Math.max(maxX, (cell.x + 1) * cellSize);
      maxY = Math.max(maxY, (cell.y + 1) * cellSize);
    }

    const width = maxX - minX;
    const height = maxY - minY;

    // Extract texture
    const texture = new ImageData(width, height);

    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const srcIdx = ((minY + y) * imageData.width + (minX + x)) * 4;
        const dstIdx = (y * width + x) * 4;

        texture.data[dstIdx] = imageData.data[srcIdx];
        texture.data[dstIdx + 1] = imageData.data[srcIdx + 1];
        texture.data[dstIdx + 2] = imageData.data[srcIdx + 2];
        texture.data[dstIdx + 3] = imageData.data[srcIdx + 3];
      }
    }

    return {
      x: minX,
      y: minY,
      width,
      height,
      texture,
      uniformityScore: cells.length / ((width / cellSize) * (height / cellSize))
    };
  }

  private async base64ToImageData(base64: string): Promise<ImageData> {
    const img = new Image();
    img.src = `data:image/png;base64,${base64}`;
    await img.decode();

    const canvas = new OffscreenCanvas(img.width, img.height);
    const ctx = canvas.getContext('2d')!;
    ctx.drawImage(img, 0, 0);

    return ctx.getImageData(0, 0, img.width, img.height);
  }
}

export const textureExtraction = new TextureExtractionService();
```
