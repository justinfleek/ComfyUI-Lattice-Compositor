/**
 * SplinePath - Custom Fabric.js class for editable bezier splines
 *
 * IMPORTANT: Fabric.js 6.x uses ES6 classes, NOT createClass()
 */
import { Path, classRegistry } from 'fabric';
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
      pathData: this.path?.map((cmd: any) => cmd.join(' ')).join(' ') || '',
      controlPoints: this.controlPoints,
      closed: false,
      stroke: this.stroke as string,
      strokeWidth: this.strokeWidth as number,
      fill: this.fill as string
    };
  }

  /**
   * Get serializable properties
   */
  getSerializableData(): Record<string, any> {
    return {
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
