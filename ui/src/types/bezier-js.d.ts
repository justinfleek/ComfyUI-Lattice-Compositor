// Type declarations for bezier-js
declare module 'bezier-js' {
  export interface Point {
    x: number;
    y: number;
    z?: number;
  }

  export interface BezierDerivative {
    x: number;
    y: number;
    z?: number;
  }

  export default class Bezier {
    constructor(
      p1: Point,
      p2: Point,
      p3: Point,
      p4?: Point
    );
    constructor(
      x1: number,
      y1: number,
      x2: number,
      y2: number,
      x3: number,
      y3: number,
      x4?: number,
      y4?: number
    );
    constructor(coords: number[]);
    constructor(points: Point[]);

    points: Point[];
    order: number;

    get(t: number): Point;
    compute(t: number): Point;
    derivative(t: number): BezierDerivative;
    normal(t: number): Point;
    split(t: number): { left: Bezier; right: Bezier };
    split(t1: number, t2: number): Bezier;
    length(): number;
    getLUT(steps?: number): Point[];
    project(point: Point): { x: number; y: number; t: number; d: number };
    offset(d: number): Bezier[];
    simple(): boolean;
    reduce(): Bezier[];
    scale(d: number): Bezier;
    outline(d: number): { curves: Bezier[] };
    outline(d1: number, d2: number): { curves: Bezier[] };
    intersects(curve: Bezier, threshold?: number): string[] | number[];
    lineIntersects(line: { p1: Point; p2: Point }): number[];
    bbox(): {
      x: { min: number; max: number };
      y: { min: number; max: number };
    };
    hull(t: number): Point[];
    roots(line?: { p1: Point; p2: Point }): number[];
    extrema(): { x: number[]; y: number[]; values: number[] };
    curvature(t: number): { k: number; r: number };
    raise(): Bezier;
    toString(): string;
  }
}
