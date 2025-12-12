/**
 * AnimatedText - Text that can follow a path and animate
 *
 * IMPORTANT: Fabric.js 6.x uses ES6 classes, NOT createClass()
 */
import { Group, FabricText, classRegistry } from 'fabric';
import type { TextData } from '@/types/project';
import type { ArcLengthParameterizer } from '@/services/arcLength';

interface AnimatedTextOptions {
  text?: string;
  fontFamily?: string;
  fontSize?: number;
  fontWeight?: string;
  fill?: string;
  stroke?: string;
  strokeWidth?: number;
  letterSpacing?: number;
  pathLayerId?: string | null;
  pathOffset?: number;
  selectable?: boolean;
}

export class AnimatedText extends Group {
  static type = 'AnimatedText';

  static ownDefaults: Partial<AnimatedTextOptions> = {
    text: 'Text',
    fontFamily: 'Arial',
    fontSize: 48,
    fontWeight: '400',
    fill: '#ffffff',
    stroke: '',
    strokeWidth: 0,
    letterSpacing: 0,
    pathLayerId: null,
    pathOffset: 0,
    selectable: true
  };

  declare textContent: string;
  declare fontFamily: string;
  declare fontSize: number;
  declare fontWeight: string;
  declare textFill: string;
  declare textStroke: string;
  declare textStrokeWidth: number;
  declare letterSpacing: number;
  declare pathLayerId: string | null;
  declare pathOffset: number;
  declare _letterObjects: FabricText[];

  constructor(options: AnimatedTextOptions = {}) {
    super([], {
      ...AnimatedText.ownDefaults,
      ...options,
      subTargetCheck: true,
      interactive: false
    });

    this.textContent = options.text || 'Text';
    this.fontFamily = options.fontFamily || 'Arial';
    this.fontSize = options.fontSize || 48;
    this.fontWeight = options.fontWeight || '400';
    this.textFill = options.fill || '#ffffff';
    this.textStroke = options.stroke || '';
    this.textStrokeWidth = options.strokeWidth || 0;
    this.letterSpacing = options.letterSpacing || 0;
    this.pathLayerId = options.pathLayerId || null;
    this.pathOffset = options.pathOffset || 0;
    this._letterObjects = [];

    this._createLetterObjects();
  }

  /**
   * Create individual letter objects for per-character animation
   */
  private _createLetterObjects(): void {
    // Remove existing letter objects completely
    this.removeAll();
    this._letterObjects = [];

    // Create new letter objects for each character in the text
    for (const char of this.textContent) {
      const letter = new FabricText(char, {
        fontFamily: this.fontFamily,
        fontSize: this.fontSize,
        fontWeight: this.fontWeight,
        fill: this.textFill,
        stroke: this.textStroke,
        strokeWidth: this.textStrokeWidth,
        originX: 'center',
        originY: 'center',
        selectable: false,
        evented: false
      });

      // Force Fabric to calculate text dimensions
      letter.initDimensions();
      letter.setCoords();
      this._letterObjects.push(letter);
      this.add(letter);
    }

    // Layout and update group bounds
    this._layoutLettersHorizontal();
  }

  /**
   * Layout letters horizontally (default, no path)
   */
  private _layoutLettersHorizontal(): void {
    let x = 0;

    for (const letter of this._letterObjects) {
      // Use fontSize as fallback if width not calculated
      const letterWidth = letter.width || (this.fontSize * 0.6);
      letter.set({
        left: x + letterWidth / 2,
        top: this.fontSize / 2,
        angle: 0
      });
      x += letterWidth + this.letterSpacing;
    }

    // Update group dimensions to prevent clipping
    this.set({ 
      width: x || 100, 
      height: this.fontSize * 1.2 
    });
    this.setCoords();
  }

  /**
   * Position letters along a bezier path
   */
  positionOnPath(
    arcLengthParam: ArcLengthParameterizer,
    offset: number
  ): void {
    const totalLength = arcLengthParam.totalLength;
    let currentDistance = offset * totalLength;
    let maxX = 0;
    let maxY = 0;

    for (const letter of this._letterObjects) {
      const charWidth = letter.width || (this.fontSize * 0.6);

      // Clamp distance to valid range
      const clampedDistance = Math.max(0, Math.min(currentDistance, totalLength));

      // Get position at current arc length
      const { point, tangent } = arcLengthParam.getPointAtDistance(clampedDistance);

      // Calculate rotation from tangent
      const angle = Math.atan2(tangent.y, tangent.x) * (180 / Math.PI);

      letter.set({
        left: point.x,
        top: point.y,
        angle: angle
      });

      maxX = Math.max(maxX, point.x + charWidth);
      maxY = Math.max(maxY, point.y + this.fontSize);
      currentDistance += charWidth + this.letterSpacing;
    }

    this.set({ width: maxX || 100, height: maxY || this.fontSize * 1.2 });
    this.setCoords();
    this.dirty = true;
  }

  /**
   * Update text content
   */
  setText(text: string): void {
    this.textContent = text;
    this._createLetterObjects();
    this.dirty = true;

    // Force canvas to re-render
    if (this.canvas) {
      this.canvas.requestRenderAll();
    }
  }

  /**
   * Update font properties
   */
  setFont(family: string, size: number, weight?: string): void {
    this.fontFamily = family;
    this.fontSize = size;
    if (weight) this.fontWeight = weight;
    this._createLetterObjects();
  }

  /**
   * Update fill color
   */
  setFillColor(color: string): void {
    this.textFill = color;
    for (const letter of this._letterObjects) {
      letter.set('fill', color);
    }
    this.dirty = true;
  }

  /**
   * Update stroke
   */
  setStroke(color: string, width: number): void {
    this.textStroke = color;
    this.textStrokeWidth = width;
    for (const letter of this._letterObjects) {
      letter.set({
        stroke: color,
        strokeWidth: width
      });
    }
    this.dirty = true;
  }

  /**
   * Update letter spacing
   */
  setLetterSpacing(spacing: number): void {
    this.letterSpacing = spacing;
    // Re-layout based on whether we're on a path
    if (!this.pathLayerId) {
      this._layoutLettersHorizontal();
    }
  }

  /**
   * Get total text width (for horizontal layout)
   */
  getTextWidth(): number {
    let width = 0;
    for (const letter of this._letterObjects) {
      width += (letter.width || 0) + this.letterSpacing;
    }
    return Math.max(0, width - this.letterSpacing);
  }

  /**
   * Get text data for serialization
   */
  getTextData(): TextData {
    return {
      text: this.textContent,
      fontFamily: this.fontFamily,
      fontSize: this.fontSize,
      fontWeight: this.fontWeight,
      fontStyle: 'normal',
      fill: this.textFill,
      stroke: this.textStroke,
      strokeWidth: this.textStrokeWidth,
      letterSpacing: this.letterSpacing,
      lineHeight: 1.2,
      textAlign: 'left',
      pathLayerId: this.pathLayerId,
      pathOffset: this.pathOffset,
      pathAlign: 'left'
    };
  }

  /**
   * Get serializable data
   */
  getSerializableData(): Record<string, any> {
    return {
      textContent: this.textContent,
      fontFamily: this.fontFamily,
      fontSize: this.fontSize,
      fontWeight: this.fontWeight,
      textFill: this.textFill,
      textStroke: this.textStroke,
      textStrokeWidth: this.textStrokeWidth,
      letterSpacing: this.letterSpacing,
      pathLayerId: this.pathLayerId,
      pathOffset: this.pathOffset
    };
  }

  /**
   * Deserialization from JSON
   */
  static fromObject(object: Record<string, any>): Promise<AnimatedText> {
    return Promise.resolve(new AnimatedText({
      text: object.textContent,
      fontFamily: object.fontFamily,
      fontSize: object.fontSize,
      fontWeight: object.fontWeight,
      fill: object.textFill,
      stroke: object.textStroke,
      strokeWidth: object.textStrokeWidth,
      letterSpacing: object.letterSpacing,
      pathLayerId: object.pathLayerId,
      pathOffset: object.pathOffset
    }));
  }
}

// CRITICAL: Register class for serialization
classRegistry.setClass(AnimatedText);

export default AnimatedText;
