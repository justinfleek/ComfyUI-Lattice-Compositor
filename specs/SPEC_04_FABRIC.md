# 6. FABRIC.JS CUSTOM CLASSES

## 6.1 SplinePath Class (ui/src/fabric/SplinePath.ts)

```typescript
/**
 * SplinePath - Custom Fabric.js class for editable bezier splines
 *
 * IMPORTANT: Fabric.js 6.x uses ES6 classes, NOT createClass()
 */
import { Path, classRegistry, TPointerEvent, Point } from 'fabric';
import type { ControlPoint, SplineData } from '@/types/project';

interface SplinePathOptions {
  controlPoints?: ControlPoint[];
  stroke?: string;
  strokeWidth?: number;
  fill?: string;
  selectable?: boolean;
}

export class SplinePath extends Path {
  // Type identifier for serialization
  static type = 'SplinePath';

  // Default values
  static ownDefaults: Partial<SplinePathOptions> = {
    stroke: '#00ff00',
    strokeWidth: 2,
    fill: '',
    selectable: true,
    controlPoints: []
  };

  // Instance properties
  declare controlPoints: ControlPoint[];
  declare _animationKeyframes: any[];

  constructor(path: string, options: SplinePathOptions = {}) {
    super(path, {
      ...SplinePath.ownDefaults,
      ...options
    });

    this.controlPoints = options.controlPoints || [];
    this._animationKeyframes = [];
  }

  /**
   * Update path data from control points
   */
  updatePathFromControlPoints(): void {
    if (this.controlPoints.length < 2) {
      this.set('path', []);
      return;
    }

    const pathCommands: any[] = [];
    const cp = this.controlPoints;

    // Move to first point
    pathCommands.push(['M', cp[0].x, cp[0].y]);

    // Create cubic bezier curves between points
    for (let i = 0; i < cp.length - 1; i++) {
      const p1 = cp[i];
      const p2 = cp[i + 1];

      // Get handle positions (or use point position if no handle)
      const h1 = p1.handleOut || { x: p1.x, y: p1.y };
      const h2 = p2.handleIn || { x: p2.x, y: p2.y };

      pathCommands.push([
        'C',
        h1.x, h1.y,
        h2.x, h2.y,
        p2.x, p2.y
      ]);
    }

    this.set('path', pathCommands);
    this.setCoords();
  }

  /**
   * Add a new control point at position
   */
  addControlPoint(x: number, y: number, depth?: number): ControlPoint {
    const point: ControlPoint = {
      id: `cp_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
      x,
      y,
      depth,
      handleIn: null,
      handleOut: null,
      type: 'corner'
    };

    this.controlPoints.push(point);
    this.updatePathFromControlPoints();

    return point;
  }

  /**
   * Move a control point
   */
  moveControlPoint(pointId: string, x: number, y: number): void {
    const point = this.controlPoints.find(p => p.id === pointId);
    if (!point) return;

    const dx = x - point.x;
    const dy = y - point.y;

    point.x = x;
    point.y = y;

    // Move handles with the point
    if (point.handleIn) {
      point.handleIn.x += dx;
      point.handleIn.y += dy;
    }
    if (point.handleOut) {
      point.handleOut.x += dx;
      point.handleOut.y += dy;
    }

    this.updatePathFromControlPoints();
  }

  /**
   * Set handle position for a control point
   */
  setHandle(
    pointId: string,
    handleType: 'in' | 'out',
    x: number,
    y: number,
    breakHandles: boolean = false
  ): void {
    const point = this.controlPoints.find(p => p.id === pointId);
    if (!point) return;

    if (handleType === 'in') {
      point.handleIn = { x, y };
    } else {
      point.handleOut = { x, y };
    }

    // Mirror handle if not breaking
    if (!breakHandles && point.type === 'smooth') {
      const handle = handleType === 'in' ? point.handleIn : point.handleOut;
      const oppositeKey = handleType === 'in' ? 'handleOut' : 'handleIn';

      if (handle) {
        const dx = handle.x - point.x;
        const dy = handle.y - point.y;

        point[oppositeKey] = {
          x: point.x - dx,
          y: point.y - dy
        };
      }
    }

    this.updatePathFromControlPoints();
  }

  /**
   * Delete a control point
   */
  deleteControlPoint(pointId: string): void {
    const index = this.controlPoints.findIndex(p => p.id === pointId);
    if (index === -1) return;

    this.controlPoints.splice(index, 1);
    this.updatePathFromControlPoints();
  }

  /**
   * Get spline data for serialization
   */
  getSplineData(): SplineData {
    return {
      pathData: this.path?.map(cmd => cmd.join(' ')).join(' ') || '',
      controlPoints: this.controlPoints,
      closed: false,
      stroke: this.stroke as string,
      strokeWidth: this.strokeWidth as number,
      fill: this.fill as string
    };
  }

  /**
   * Serialization for JSON
   */
  toObject(propertiesToInclude: string[] = []): Record<string, any> {
    return {
      ...super.toObject(propertiesToInclude),
      controlPoints: this.controlPoints,
      _animationKeyframes: this._animationKeyframes
    };
  }

  /**
   * Deserialization from JSON
   */
  static fromObject(object: Record<string, any>): Promise<SplinePath> {
    const pathString = object.path?.map((cmd: any[]) => cmd.join(' ')).join(' ') || '';

    return Promise.resolve(new SplinePath(pathString, {
      ...object,
      controlPoints: object.controlPoints || []
    }));
  }
}

// CRITICAL: Register class for serialization
classRegistry.setClass(SplinePath);

export default SplinePath;
```

## 6.2 AnimatedText Class (ui/src/fabric/AnimatedText.ts)

```typescript
/**
 * AnimatedText - Text that can follow a path and animate
 */
import { Group, FabricText, classRegistry } from 'fabric';
import type { TextData, AnimatableProperty } from '@/types/project';

interface AnimatedTextOptions {
  text?: string;
  fontFamily?: string;
  fontSize?: number;
  fill?: string;
  pathLayerId?: string | null;
}

export class AnimatedText extends Group {
  static type = 'AnimatedText';

  static ownDefaults: Partial<AnimatedTextOptions> = {
    text: 'Text',
    fontFamily: 'Arial',
    fontSize: 48,
    fill: '#ffffff',
    pathLayerId: null
  };

  declare textContent: string;
  declare fontFamily: string;
  declare fontSize: number;
  declare textFill: string;
  declare letterSpacing: number;
  declare pathLayerId: string | null;
  declare pathOffset: number;
  declare _letterObjects: FabricText[];

  constructor(options: AnimatedTextOptions = {}) {
    super([], {
      ...AnimatedText.ownDefaults,
      ...options
    });

    this.textContent = options.text || 'Text';
    this.fontFamily = options.fontFamily || 'Arial';
    this.fontSize = options.fontSize || 48;
    this.textFill = options.fill || '#ffffff';
    this.letterSpacing = 0;
    this.pathLayerId = options.pathLayerId || null;
    this.pathOffset = 0;
    this._letterObjects = [];

    this._createLetterObjects();
  }

  /**
   * Create individual letter objects for per-character animation
   */
  private _createLetterObjects(): void {
    // Remove existing letters
    this.removeAll();
    this._letterObjects = [];

    // Create new letter objects
    for (const char of this.textContent) {
      const letter = new FabricText(char, {
        fontFamily: this.fontFamily,
        fontSize: this.fontSize,
        fill: this.textFill,
        originX: 'center',
        originY: 'center'
      });

      this._letterObjects.push(letter);
      this.add(letter);
    }

    // Initial layout (horizontal)
    this._layoutLettersHorizontal();
  }

  /**
   * Layout letters horizontally (default, no path)
   */
  private _layoutLettersHorizontal(): void {
    let x = 0;

    for (const letter of this._letterObjects) {
      letter.set({
        left: x + letter.width! / 2,
        top: this.fontSize / 2,
        angle: 0
      });

      x += letter.width! + this.letterSpacing;
    }

    this.setCoords();
  }

  /**
   * Position letters along a bezier path
   *
   * @param bezierCurve - Bezier.js curve object
   * @param arcLengthParam - ArcLengthParameterizer instance
   * @param offset - 0-1 offset along path
   */
  positionOnPath(
    arcLengthParam: any, // ArcLengthParameterizer
    offset: number
  ): void {
    const totalLength = arcLengthParam.totalLength;
    let currentDistance = offset * totalLength;

    for (const letter of this._letterObjects) {
      const charWidth = letter.width || 0;

      // Get position at current arc length
      const { point, tangent } = arcLengthParam.getPointAtDistance(currentDistance);

      // Calculate rotation from tangent
      const angle = Math.atan2(tangent.y, tangent.x) * (180 / Math.PI);

      letter.set({
        left: point.x,
        top: point.y,
        angle: angle
      });

      currentDistance += charWidth + this.letterSpacing;
    }

    this.setCoords();
  }

  /**
   * Update text content
   */
  setText(text: string): void {
    this.textContent = text;
    this._createLetterObjects();
  }

  /**
   * Update font properties
   */
  setFont(family: string, size: number): void {
    this.fontFamily = family;
    this.fontSize = size;
    this._createLetterObjects();
  }

  /**
   * Get text data for serialization
   */
  getTextData(): TextData {
    return {
      text: this.textContent,
      fontFamily: this.fontFamily,
      fontSize: this.fontSize,
      fontWeight: '400',
      fontStyle: 'normal',
      fill: this.textFill,
      stroke: '',
      strokeWidth: 0,
      letterSpacing: this.letterSpacing,
      lineHeight: 1.2,
      textAlign: 'left',
      pathLayerId: this.pathLayerId,
      pathOffset: this.pathOffset,
      pathAlign: 'left'
    };
  }

  toObject(propertiesToInclude: string[] = []): Record<string, any> {
    return {
      ...super.toObject(propertiesToInclude),
      textContent: this.textContent,
      fontFamily: this.fontFamily,
      fontSize: this.fontSize,
      textFill: this.textFill,
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
      fill: object.textFill,
      pathLayerId: object.pathLayerId
    }));
  }
}

classRegistry.setClass(AnimatedText);

export default AnimatedText;
```
