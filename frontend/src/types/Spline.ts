export interface SplinePoint {
  x: number;
  y: number;
  z: number;
}

export interface Spline {
  id: string;
  points: SplinePoint[];
  closed: boolean;
}
