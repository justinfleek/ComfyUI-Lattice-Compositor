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
  fontStyle?: 'normal' | 'italic';
  fill?: string;
  stroke?: string;
  strokeWidth?: number;
  letterSpacing?: number;
  textAlign?: 'left' | 'center' | 'right';
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
    fontStyle: 'normal',
    fill: '#ffffff',
    stroke: '',
    strokeWidth: 0,
    letterSpacing: 0,
    textAlign: 'left',
    pathLayerId: null,
    pathOffset: 0,
    selectable: true
  };

  declare textContent: string;
  declare fontFamily: string;
  declare fontSize: number;
  declare fontWeight: string;
  declare fontStyle: 'normal' | 'italic';
  declare textFill: string;
  declare textStroke: string;
  declare textStrokeWidth: number;
  declare letterSpacing: number;
  declare textAlign: 'left' | 'center' | 'right';
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
    this.fontStyle = options.fontStyle || 'normal';
    this.textFill = options.fill || '#ffffff';
    this.textStroke = options.stroke || '';
    this.textStrokeWidth = options.strokeWidth || 0;
    this.letterSpacing = options.letterSpacing || 0;
    this.textAlign = options.textAlign || 'left';
    this.pathLayerId = options.pathLayerId || null;
    this.pathOffset = options.pathOffset || 0;
    this._letterObjects = [];

    this._createLetterObjects();
  }

  /**
   * Create individual letter objects for per-character animation
   */
  private _createLetterObjects(): void {
    this.removeAll();
    this._letterObjects = [];

    console.log('[AnimatedText] Creating letters for text:', this.textContent, 'fontSize:', this.fontSize, 'fill:', this.textFill);

    // Create a temporary canvas for measuring text dimensions
    const measureCanvas = document.createElement('canvas');
    const measureCtx = measureCanvas.getContext('2d');

    for (const char of this.textContent) {
      const letter = new FabricText(char, {
        fontFamily: this.fontFamily,
        fontSize: this.fontSize,
        fontWeight: this.fontWeight,
        fontStyle: this.fontStyle,
        fill: this.textFill,
        stroke: this.textStroke,
        strokeWidth: this.textStrokeWidth,
        originX: 'center',
        originY: 'center',
        selectable: false,
        evented: false
      });

      // Measure text width using temp canvas if letter.width is 0
      let letterWidth = letter.width;
      if ((!letterWidth || letterWidth === 0) && measureCtx) {
        measureCtx.font = `${this.fontWeight} ${this.fontSize}px ${this.fontFamily}`;
        const metrics = measureCtx.measureText(char);
        letterWidth = metrics.width;
        // Set the width on the letter object
        letter.set({ width: letterWidth });
      }

      console.log('[AnimatedText] Letter:', char, 'width:', letterWidth, 'height:', letter.height || this.fontSize);
      this._letterObjects.push(letter);
      this.add(letter);
    }

    this._layoutLettersHorizontal();
  }

  /**
   * Layout letters horizontally and update group bounds
   */
  private _layoutLettersHorizontal(): void {
    // Create a temporary canvas for measuring if needed
    const measureCanvas = document.createElement('canvas');
    const measureCtx = measureCanvas.getContext('2d');
    if (measureCtx) {
      measureCtx.font = `${this.fontWeight} ${this.fontSize}px ${this.fontFamily}`;
    }

    // First pass: calculate total width
    let totalWidth = 0;
    for (const letter of this._letterObjects) {
      let letterWidth = letter.width;
      if (!letterWidth || letterWidth === 0) {
        if (measureCtx) {
          const metrics = measureCtx.measureText(letter.text || ' ');
          letterWidth = metrics.width;
          letter.set({ width: letterWidth });
        } else {
          letterWidth = this.fontSize * 0.6;
        }
      }
      totalWidth += letterWidth + this.letterSpacing;
    }
    totalWidth -= this.letterSpacing; // Remove trailing spacing

    // Second pass: position letters centered in group
    const startX = -totalWidth / 2;
    let x = 0;

    for (const letter of this._letterObjects) {
      const letterWidth = letter.width || (this.fontSize * 0.6);
      letter.set({
        left: startX + x + letterWidth / 2,
        top: 0,
        angle: 0
      });
      x += letterWidth + this.letterSpacing;
    }

    // Update group dimensions - add padding to prevent clipping
    const groupWidth = Math.max(totalWidth, 10);
    const groupHeight = this.fontSize * 1.5; // Extra height for descenders

    this.set({
      width: groupWidth,
      height: groupHeight,
      // Disable clipping
      clipPath: undefined
    });
    this.setCoords();

    console.log('[AnimatedText] Layout complete. Group width:', groupWidth, 'height:', groupHeight, 'letterCount:', this._letterObjects.length, 'totalTextWidth:', totalWidth);
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
      const clampedDistance = Math.max(0, Math.min(currentDistance, totalLength));
      const { point, tangent } = arcLengthParam.getPointAtDistance(clampedDistance);
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

  setText(text: string): void {
    this.textContent = text;
    this._createLetterObjects();
    this.dirty = true;
    if (this.canvas) {
      this.canvas.requestRenderAll();
    }
  }

  setFont(family: string, size: number, weight?: string, style?: 'normal' | 'italic'): void {
    this.fontFamily = family;
    this.fontSize = size;
    if (weight) this.fontWeight = weight;
    if (style) this.fontStyle = style;
    this._createLetterObjects();
  }

  setFontStyle(style: 'normal' | 'italic'): void {
    this.fontStyle = style;
    for (const letter of this._letterObjects) {
      letter.set('fontStyle', style);
    }
    this.dirty = true;
  }

  setTextAlign(align: 'left' | 'center' | 'right'): void {
    this.textAlign = align;
    this._layoutLettersHorizontal();
    this.dirty = true;
  }

  setFillColor(color: string): void {
    this.textFill = color;
    for (const letter of this._letterObjects) {
      letter.set('fill', color);
    }
    this.dirty = true;
  }

  setStroke(color: string, width: number): void {
    this.textStroke = color;
    this.textStrokeWidth = width;
    for (const letter of this._letterObjects) {
      letter.set({ stroke: color, strokeWidth: width });
    }
    this.dirty = true;
  }

  setLetterSpacing(spacing: number): void {
    this.letterSpacing = spacing;
    if (!this.pathLayerId) {
      this._layoutLettersHorizontal();
    }
  }

  getTextWidth(): number {
    let width = 0;
    for (const letter of this._letterObjects) {
      width += (letter.width || 0) + this.letterSpacing;
    }
    return Math.max(0, width - this.letterSpacing);
  }

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

classRegistry.setClass(AnimatedText);
export default AnimatedText;
