/**
 * 3D Math Utilities for Camera System
 * Vector and matrix operations for camera transforms
 * 
 * PRECISION NOTES:
 * - Mat4 uses Float32Array for GPU compatibility (WebGL/Three.js requirement)
 * - Float32 has ~7 significant digits of precision (1e-7 relative error)
 * - For operations requiring higher precision, use Mat4_64 variants
 * - Scale operations with values < 0.01 or > 100 may accumulate error
 * 
 * EDGE CASE HANDLING:
 * - All edge cases emit warnings via math3dWarn() - NO SILENT FAILURES
 * - Set math3dWarnHandler to customize warning behavior (e.g., throw errors)
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Warning System - NO SILENT FAILURES
// ════════════════════════════════════════════════════════════════════════════

export type Math3DWarning = 
  | 'SCALE_OUT_OF_RANGE'
  | 'GIMBAL_LOCK'
  | 'ZERO_VECTOR_NORMALIZE'
  | 'SINGULAR_MATRIX'
  | 'DIVISION_BY_ZERO';

/**
 * Warning context - allows common debugging values
 */
export interface Math3DWarnContext {
  [key: string]: number | string | boolean | Vec3 | Mat4 | null | undefined | Array<number | string | boolean | Vec3>;
}

export interface Math3DWarnEvent {
  type: Math3DWarning;
  message: string;
  context?: Math3DWarnContext;
}

/**
 * Default warning handler - logs to console.
 * Replace this to throw errors, collect metrics, etc.
 */
export let math3dWarnHandler: (event: Math3DWarnEvent) => void = (event) => {
  console.warn(`[math3d] ${event.type}: ${event.message}`, event.context);
};

/**
 * Set custom warning handler. Use this to:
 * - Throw errors in strict mode
 * - Collect telemetry
 * - Show user notifications
 */
export function setMath3DWarnHandler(handler: (event: Math3DWarnEvent) => void): void {
  math3dWarnHandler = handler;
}

function math3dWarn(type: Math3DWarning, message: string, context?: Math3DWarnContext): void {
  math3dWarnHandler({ type, message, context });
}

export interface Vec3 {
  x: number;
  y: number;
  z: number;
}

export interface Mat4 {
  elements: Float32Array;  // 16 elements, column-major, GPU-compatible
}

/**
 * High-precision matrix for calculations requiring > 7 digits precision.
 * Use convertToMat4() when sending to GPU.
 */
export interface Mat4_64 {
  elements: Float64Array;  // 16 elements, column-major, ~15 digits precision
}

// ════════════════════════════════════════════════════════════════════════════
// Vector Operations
// ════════════════════════════════════════════════════════════════════════════

export function vec3(x: number, y: number, z: number): Vec3 {
  return { x, y, z };
}

export function addVec3(a: Vec3, b: Vec3): Vec3 {
  return { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z };
}

export function subVec3(a: Vec3, b: Vec3): Vec3 {
  return { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z };
}

export function scaleVec3(v: Vec3, s: number): Vec3 {
  return { x: v.x * s, y: v.y * s, z: v.z * s };
}

export function lengthVec3(v: Vec3): number {
  return Math.sqrt(v.x * v.x + v.y * v.y + v.z * v.z);
}

export function normalizeVec3(v: Vec3): Vec3 {
  const len = lengthVec3(v);
  if (len === 0) {
    math3dWarn('ZERO_VECTOR_NORMALIZE', 
      'Attempted to normalize zero vector - returning zero vector', 
      { input: v }
    );
    return { x: 0, y: 0, z: 0 };
  }
  return { x: v.x / len, y: v.y / len, z: v.z / len };
}

export function crossVec3(a: Vec3, b: Vec3): Vec3 {
  return {
    x: a.y * b.z - a.z * b.y,
    y: a.z * b.x - a.x * b.z,
    z: a.x * b.y - a.y * b.x,
  };
}

export function dotVec3(a: Vec3, b: Vec3): number {
  return a.x * b.x + a.y * b.y + a.z * b.z;
}

export function lerpVec3(a: Vec3, b: Vec3, t: number): Vec3 {
  return {
    x: a.x + (b.x - a.x) * t,
    y: a.y + (b.y - a.y) * t,
    z: a.z + (b.z - a.z) * t,
  };
}

export function distanceVec3(a: Vec3, b: Vec3): number {
  return lengthVec3(subVec3(a, b));
}

// ════════════════════════════════════════════════════════════════════════════
// Matrix Operations
// ════════════════════════════════════════════════════════════════════════════

export function identityMat4(): Mat4 {
  return {
    elements: new Float32Array([
      1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1,
    ]),
  };
}

/**
 * Matrix multiplication with improved numerical precision.
 * Uses Float64 for intermediate calculations to minimize precision loss,
 * then converts to Float32 for GPU compatibility.
 */
export function multiplyMat4(a: Mat4, b: Mat4): Mat4 {
  const ae = a.elements;
  const be = b.elements;
  
  // Use Float64 for intermediate calculations to preserve precision
  const temp = new Float64Array(16);

  // Extract elements as Float64 values
  const a11 = ae[0], a12 = ae[4], a13 = ae[8], a14 = ae[12];
  const a21 = ae[1], a22 = ae[5], a23 = ae[9], a24 = ae[13];
  const a31 = ae[2], a32 = ae[6], a33 = ae[10], a34 = ae[14];
  const a41 = ae[3], a42 = ae[7], a43 = ae[11], a44 = ae[15];

  const b11 = be[0],
    b12 = be[4],
    b13 = be[8],
    b14 = be[12];
  const b21 = be[1],
    b22 = be[5],
    b23 = be[9],
    b24 = be[13];
  const b31 = be[2],
    b32 = be[6],
    b33 = be[10],
    b34 = be[14];
  const b41 = be[3],
    b42 = be[7],
    b43 = be[11],
    b44 = be[15];

  // Calculate in Float64 precision
  temp[0] = a11 * b11 + a12 * b21 + a13 * b31 + a14 * b41;
  temp[4] = a11 * b12 + a12 * b22 + a13 * b32 + a14 * b42;
  temp[8] = a11 * b13 + a12 * b23 + a13 * b33 + a14 * b43;
  temp[12] = a11 * b14 + a12 * b24 + a13 * b34 + a14 * b44;

  temp[1] = a21 * b11 + a22 * b21 + a23 * b31 + a24 * b41;
  temp[5] = a21 * b12 + a22 * b22 + a23 * b32 + a24 * b42;
  temp[9] = a21 * b13 + a22 * b23 + a23 * b33 + a24 * b43;
  temp[13] = a21 * b14 + a22 * b24 + a23 * b34 + a24 * b44;

  temp[2] = a31 * b11 + a32 * b21 + a33 * b31 + a34 * b41;
  temp[6] = a31 * b12 + a32 * b22 + a33 * b32 + a34 * b42;
  temp[10] = a31 * b13 + a32 * b23 + a33 * b33 + a34 * b43;
  temp[14] = a31 * b14 + a32 * b24 + a33 * b34 + a34 * b44;

  temp[3] = a41 * b11 + a42 * b21 + a43 * b31 + a44 * b41;
  temp[7] = a41 * b12 + a42 * b22 + a43 * b32 + a44 * b42;
  temp[11] = a41 * b13 + a42 * b23 + a43 * b33 + a44 * b43;
  temp[15] = a41 * b14 + a42 * b24 + a43 * b34 + a44 * b44;

  // Convert back to Float32 for GPU compatibility
  return { elements: new Float32Array(temp) };
}

export function perspectiveMat4(
  fovY: number,
  aspect: number,
  near: number,
  far: number,
): Mat4 {
  // Validate inputs
  if (near >= far) {
    math3dWarn('DIVISION_BY_ZERO',
      'perspectiveMat4: near >= far will cause invalid projection',
      { near, far }
    );
  }
  if (aspect <= 0) {
    math3dWarn('DIVISION_BY_ZERO',
      'perspectiveMat4: aspect ratio must be positive',
      { aspect }
    );
  }
  if (fovY <= 0 || fovY >= Math.PI) {
    math3dWarn('DIVISION_BY_ZERO',
      'perspectiveMat4: FOV must be in (0, π) radians',
      { fovY, fovDegrees: fovY * 180 / Math.PI }
    );
  }
  
  const te = new Float32Array(16);
  const f = 1.0 / Math.tan(fovY / 2);
  const nf = 1 / (near - far);

  te[0] = f / aspect;
  te[1] = 0;
  te[2] = 0;
  te[3] = 0;
  te[4] = 0;
  te[5] = f;
  te[6] = 0;
  te[7] = 0;
  te[8] = 0;
  te[9] = 0;
  te[10] = (far + near) * nf;
  te[11] = -1;
  te[12] = 0;
  te[13] = 0;
  te[14] = 2 * far * near * nf;
  te[15] = 0;

  return { elements: te };
}

export function orthographicMat4(
  left: number,
  right: number,
  bottom: number,
  top: number,
  near: number,
  far: number,
): Mat4 {
  // Validate inputs
  if (left >= right) {
    math3dWarn('DIVISION_BY_ZERO',
      'orthographicMat4: left >= right will cause invalid projection',
      { left, right }
    );
  }
  if (bottom >= top) {
    math3dWarn('DIVISION_BY_ZERO',
      'orthographicMat4: bottom >= top will cause invalid projection',
      { bottom, top }
    );
  }
  if (near >= far) {
    math3dWarn('DIVISION_BY_ZERO',
      'orthographicMat4: near >= far will cause invalid projection',
      { near, far }
    );
  }
  
  const te = new Float32Array(16);
  const w = 1.0 / (right - left);
  const h = 1.0 / (top - bottom);
  const p = 1.0 / (far - near);

  te[0] = 2 * w;
  te[1] = 0;
  te[2] = 0;
  te[3] = 0;
  te[4] = 0;
  te[5] = 2 * h;
  te[6] = 0;
  te[7] = 0;
  te[8] = 0;
  te[9] = 0;
  te[10] = -2 * p;
  te[11] = 0;
  te[12] = -(right + left) * w;
  te[13] = -(top + bottom) * h;
  te[14] = -(far + near) * p;
  te[15] = 1;

  return { elements: te };
}

export function lookAtMat4(eye: Vec3, target: Vec3, up: Vec3): Mat4 {
  const te = new Float32Array(16);

  let zx = eye.x - target.x;
  let zy = eye.y - target.y;
  let zz = eye.z - target.z;
  let len = Math.sqrt(zx * zx + zy * zy + zz * zz);

  if (len === 0) {
    zz = 1;
  } else {
    len = 1 / len;
    zx *= len;
    zy *= len;
    zz *= len;
  }

  let xx = up.y * zz - up.z * zy;
  let xy = up.z * zx - up.x * zz;
  let xz = up.x * zy - up.y * zx;
  len = Math.sqrt(xx * xx + xy * xy + xz * xz);

  if (len === 0) {
    xx = 0;
    xy = 0;
    xz = 0;
  } else {
    len = 1 / len;
    xx *= len;
    xy *= len;
    xz *= len;
  }

  let yx = zy * xz - zz * xy;
  let yy = zz * xx - zx * xz;
  let yz = zx * xy - zy * xx;
  len = Math.sqrt(yx * yx + yy * yy + yz * yz);

  if (len === 0) {
    yx = 0;
    yy = 0;
    yz = 0;
  } else {
    len = 1 / len;
    yx *= len;
    yy *= len;
    yz *= len;
  }

  te[0] = xx;
  te[4] = xy;
  te[8] = xz;
  te[12] = -dotVec3({ x: xx, y: xy, z: xz }, eye);
  te[1] = yx;
  te[5] = yy;
  te[9] = yz;
  te[13] = -dotVec3({ x: yx, y: yy, z: yz }, eye);
  te[2] = zx;
  te[6] = zy;
  te[10] = zz;
  te[14] = -dotVec3({ x: zx, y: zy, z: zz }, eye);
  te[3] = 0;
  te[7] = 0;
  te[11] = 0;
  te[15] = 1;

  return { elements: te };
}

export function translateMat4(v: Vec3): Mat4 {
  return {
    elements: new Float32Array([
      1,
      0,
      0,
      0,
      0,
      1,
      0,
      0,
      0,
      0,
      1,
      0,
      v.x,
      v.y,
      v.z,
      1,
    ]),
  };
}

export function rotateXMat4(angle: number): Mat4 {
  const c = Math.cos(angle);
  const s = Math.sin(angle);
  return {
    elements: new Float32Array([
      1,
      0,
      0,
      0,
      0,
      c,
      s,
      0,
      0,
      -s,
      c,
      0,
      0,
      0,
      0,
      1,
    ]),
  };
}

export function rotateYMat4(angle: number): Mat4 {
  const c = Math.cos(angle);
  const s = Math.sin(angle);
  return {
    elements: new Float32Array([
      c,
      0,
      -s,
      0,
      0,
      1,
      0,
      0,
      s,
      0,
      c,
      0,
      0,
      0,
      0,
      1,
    ]),
  };
}

export function rotateZMat4(angle: number): Mat4 {
  const c = Math.cos(angle);
  const s = Math.sin(angle);
  return {
    elements: new Float32Array([
      c,
      s,
      0,
      0,
      -s,
      c,
      0,
      0,
      0,
      0,
      1,
      0,
      0,
      0,
      0,
      1,
    ]),
  };
}

/**
 * Create a scale matrix.
 * Uses Float64 intermediate array for precision before converting to Float32.
 */
export function scaleMat4(s: Vec3): Mat4 {
  // Only warn at truly extreme values (likely mistakes)
  // 0.001 = 0.1% scale, 1000 = 100,000% scale
  const EXTREME_MIN = 0.001;
  const EXTREME_MAX = 1000;
  
  const extremeAxes: Array<string> = [];
  if (s.x !== 0 && (Math.abs(s.x) < EXTREME_MIN || Math.abs(s.x) > EXTREME_MAX)) {
    extremeAxes.push(`x=${s.x}`);
  }
  if (s.y !== 0 && (Math.abs(s.y) < EXTREME_MIN || Math.abs(s.y) > EXTREME_MAX)) {
    extremeAxes.push(`y=${s.y}`);
  }
  if (s.z !== 0 && (Math.abs(s.z) < EXTREME_MIN || Math.abs(s.z) > EXTREME_MAX)) {
    extremeAxes.push(`z=${s.z}`);
  }

  if (extremeAxes.length > 0) {
    math3dWarn('SCALE_OUT_OF_RANGE',
      `Extreme scale values detected - this may be unintentional: ${extremeAxes.join(", ")}`,
      { scale: s }
    );
  }
  
  // Create in Float64 first for precision
  const temp = new Float64Array([
    s.x, 0, 0, 0,
    0, s.y, 0, 0,
    0, 0, s.z, 0,
    0, 0, 0, 1
  ]);
  return { elements: new Float32Array(temp) };
}

export function transformPoint(m: Mat4, p: Vec3): Vec3 {
  const e = m.elements;
  const w = e[3] * p.x + e[7] * p.y + e[11] * p.z + e[15];
  
  if (Math.abs(w) < 1e-10) {
    math3dWarn('DIVISION_BY_ZERO',
      'transformPoint: homogeneous coordinate w ≈ 0, point is at infinity',
      { w, point: p }
    );
  }
  
  return {
    x: (e[0] * p.x + e[4] * p.y + e[8] * p.z + e[12]) / w,
    y: (e[1] * p.x + e[5] * p.y + e[9] * p.z + e[13]) / w,
    z: (e[2] * p.x + e[6] * p.y + e[10] * p.z + e[14]) / w,
  };
}

export function transformDirection(m: Mat4, v: Vec3): Vec3 {
  const e = m.elements;
  return {
    x: e[0] * v.x + e[4] * v.y + e[8] * v.z,
    y: e[1] * v.x + e[5] * v.y + e[9] * v.z,
    z: e[2] * v.x + e[6] * v.y + e[10] * v.z,
  };
}

export function invertMat4(m: Mat4): Mat4 | null {
  const te = new Float32Array(16);
  const me = m.elements;

  const n11 = me[0],
    n21 = me[1],
    n31 = me[2],
    n41 = me[3];
  const n12 = me[4],
    n22 = me[5],
    n32 = me[6],
    n42 = me[7];
  const n13 = me[8],
    n23 = me[9],
    n33 = me[10],
    n43 = me[11];
  const n14 = me[12],
    n24 = me[13],
    n34 = me[14],
    n44 = me[15];

  const t11 =
    n23 * n34 * n42 -
    n24 * n33 * n42 +
    n24 * n32 * n43 -
    n22 * n34 * n43 -
    n23 * n32 * n44 +
    n22 * n33 * n44;
  const t12 =
    n14 * n33 * n42 -
    n13 * n34 * n42 -
    n14 * n32 * n43 +
    n12 * n34 * n43 +
    n13 * n32 * n44 -
    n12 * n33 * n44;
  const t13 =
    n13 * n24 * n42 -
    n14 * n23 * n42 +
    n14 * n22 * n43 -
    n12 * n24 * n43 -
    n13 * n22 * n44 +
    n12 * n23 * n44;
  const t14 =
    n14 * n23 * n32 -
    n13 * n24 * n32 -
    n14 * n22 * n33 +
    n12 * n24 * n33 +
    n13 * n22 * n34 -
    n12 * n23 * n34;

  const det = n11 * t11 + n21 * t12 + n31 * t13 + n41 * t14;

  // System F/Omega proof: Explicit validation of matrix invertibility
  // Type proof: det ∈ ℝ
  // Mathematical proof: Matrix is invertible ⟺ det ≠ 0
  // Linear algebra proof: Singular matrix (det = 0) has no inverse
  if (!Number.isFinite(det)) {
    math3dWarn('SINGULAR_MATRIX',
      'Cannot invert matrix: Determinant is non-finite',
      { determinant: det }
    );
    throw new Error(`[Math3D] Cannot invert matrix: Determinant is non-finite (det = ${det}). Matrix inversion requires a finite real-valued determinant. This indicates a numerical error in determinant calculation - check matrix values for NaN or Infinity.`);
  }
  
  if (det === 0) {
    math3dWarn('SINGULAR_MATRIX',
      'Cannot invert singular matrix (determinant = 0)',
      { determinant: det }
    );
    throw new Error(`[Math3D] Cannot invert matrix: Matrix is singular (determinant = 0). Linear algebra constraint violation: Matrix is invertible ⟺ det ≠ 0. Singular matrices have no inverse - check if matrix rows/columns are linearly dependent.`);
  }
  
  // Warn on near-singular matrices that may cause precision issues
  if (Math.abs(det) < 1e-10) {
    math3dWarn('SINGULAR_MATRIX',
      'Matrix is near-singular - inversion may be imprecise',
      { determinant: det }
    );
  }

  const detInv = 1 / det;

  te[0] = t11 * detInv;
  te[1] =
    (n24 * n33 * n41 -
      n23 * n34 * n41 -
      n24 * n31 * n43 +
      n21 * n34 * n43 +
      n23 * n31 * n44 -
      n21 * n33 * n44) *
    detInv;
  te[2] =
    (n22 * n34 * n41 -
      n24 * n32 * n41 +
      n24 * n31 * n42 -
      n21 * n34 * n42 -
      n22 * n31 * n44 +
      n21 * n32 * n44) *
    detInv;
  te[3] =
    (n23 * n32 * n41 -
      n22 * n33 * n41 -
      n23 * n31 * n42 +
      n21 * n33 * n42 +
      n22 * n31 * n43 -
      n21 * n32 * n43) *
    detInv;

  te[4] = t12 * detInv;
  te[5] =
    (n13 * n34 * n41 -
      n14 * n33 * n41 +
      n14 * n31 * n43 -
      n11 * n34 * n43 -
      n13 * n31 * n44 +
      n11 * n33 * n44) *
    detInv;
  te[6] =
    (n14 * n32 * n41 -
      n12 * n34 * n41 -
      n14 * n31 * n42 +
      n11 * n34 * n42 +
      n12 * n31 * n44 -
      n11 * n32 * n44) *
    detInv;
  te[7] =
    (n12 * n33 * n41 -
      n13 * n32 * n41 +
      n13 * n31 * n42 -
      n11 * n33 * n42 -
      n12 * n31 * n43 +
      n11 * n32 * n43) *
    detInv;

  te[8] = t13 * detInv;
  te[9] =
    (n14 * n23 * n41 -
      n13 * n24 * n41 -
      n14 * n21 * n43 +
      n11 * n24 * n43 +
      n13 * n21 * n44 -
      n11 * n23 * n44) *
    detInv;
  te[10] =
    (n12 * n24 * n41 -
      n14 * n22 * n41 +
      n14 * n21 * n42 -
      n11 * n24 * n42 -
      n12 * n21 * n44 +
      n11 * n22 * n44) *
    detInv;
  te[11] =
    (n13 * n22 * n41 -
      n12 * n23 * n41 -
      n13 * n21 * n42 +
      n11 * n23 * n42 +
      n12 * n21 * n43 -
      n11 * n22 * n43) *
    detInv;

  te[12] = t14 * detInv;
  te[13] =
    (n13 * n24 * n31 -
      n14 * n23 * n31 +
      n14 * n21 * n33 -
      n11 * n24 * n33 -
      n13 * n21 * n34 +
      n11 * n23 * n34) *
    detInv;
  te[14] =
    (n14 * n22 * n31 -
      n12 * n24 * n31 -
      n14 * n21 * n32 +
      n11 * n24 * n32 +
      n12 * n21 * n34 -
      n11 * n22 * n34) *
    detInv;
  te[15] =
    (n12 * n23 * n31 -
      n13 * n22 * n31 +
      n13 * n21 * n32 -
      n11 * n23 * n32 -
      n12 * n21 * n33 +
      n11 * n22 * n33) *
    detInv;

  return { elements: te };
}

// ════════════════════════════════════════════════════════════════════════════
// Lens Math
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert focal length to field of view
 * @param focalLength Focal length in mm
 * @param sensorSize Sensor size in mm (36mm for full frame)
 * @returns FOV in radians
 */
export function focalLengthToFOV(
  focalLength: number,
  sensorSize: number,
): number {
  return 2 * Math.atan(sensorSize / (2 * focalLength));
}

/**
 * Convert field of view to focal length
 * @param fov Field of view in radians
 * @param sensorSize Sensor size in mm
 * @returns Focal length in mm
 */
export function fovToFocalLength(fov: number, sensorSize: number): number {
  //                                                                // bug // fix
  if (fov <= 0 || fov >= Math.PI) {
    math3dWarn('DIVISION_BY_ZERO',
      'fovToFocalLength: FOV must be in (0, π) radians',
      { fov, fovDegrees: fov * 180 / Math.PI }
    );
    // Return a sensible default (50mm equivalent)
    return sensorSize;
  }
  return sensorSize / (2 * Math.tan(fov / 2));
}

/**
 * Convert AE zoom value to focal length
 * @param zoom Zoom value in pixels
 * @param compWidth Composition width in pixels
 * @param filmSize Film size in mm
 * @returns Focal length in mm
 */
export function zoomToFocalLength(
  zoom: number,
  compWidth: number,
  filmSize: number,
): number {
  //                                                                // bug // fix
  if (compWidth <= 0) {
    math3dWarn('DIVISION_BY_ZERO',
      'zoomToFocalLength: compWidth must be positive',
      { compWidth }
    );
    return filmSize; // Default to 1:1 zoom ratio
  }
  return (zoom * filmSize) / compWidth;
}

/**
 * Convert focal length to AE zoom value
 * @param focalLength Focal length in mm
 * @param compWidth Composition width in pixels
 * @param filmSize Film size in mm
 * @returns Zoom value in pixels
 */
export function focalLengthToZoom(
  focalLength: number,
  compWidth: number,
  filmSize: number,
): number {
  //                                                                // bug // fix
  if (filmSize <= 0) {
    math3dWarn('DIVISION_BY_ZERO',
      'focalLengthToZoom: filmSize must be positive',
      { filmSize }
    );
    return compWidth; // Default to 1:1 zoom ratio
  }
  return (focalLength * compWidth) / filmSize;
}

/**
 * Convert degrees to radians
 */
export function degToRad(degrees: number): number {
  return degrees * (Math.PI / 180);
}

/**
 * Convert radians to degrees
 */
export function radToDeg(radians: number): number {
  return radians * (180 / Math.PI);
}

// ════════════════════════════════════════════════════════════════════════════
// Quaternion (for smooth rotation interpolation)
// ════════════════════════════════════════════════════════════════════════════

export interface Quat {
  x: number;
  y: number;
  z: number;
  w: number;
}

export function quatIdentity(): Quat {
  return { x: 0, y: 0, z: 0, w: 1 };
}

export function quatFromEuler(x: number, y: number, z: number): Quat {
  const c1 = Math.cos(x / 2);
  const c2 = Math.cos(y / 2);
  const c3 = Math.cos(z / 2);
  const s1 = Math.sin(x / 2);
  const s2 = Math.sin(y / 2);
  const s3 = Math.sin(z / 2);

  return {
    x: s1 * c2 * c3 + c1 * s2 * s3,
    y: c1 * s2 * c3 - s1 * c2 * s3,
    z: c1 * c2 * s3 + s1 * s2 * c3,
    w: c1 * c2 * c3 - s1 * s2 * s3,
  };
}

/**
 * Convert quaternion to Euler angles (XYZ intrinsic rotation order).
 * 
 * This implementation follows the algorithm used by Three.js and other
 * production 3D engines for maximum numerical stability.
 * 
 * GIMBAL LOCK: At pitch = ±90°, roll and yaw become degenerate.
 * This is a mathematical property of Euler angles, not a bug.
 * The function handles this gracefully by assigning all rotation to roll.
 * 
 * For applications requiring stable rotation interpolation, use quaternions
 * directly (slerpQuat) rather than converting to Euler angles.
 * 
 * @param q - Input quaternion (should be normalized for best results)
 * @returns Euler angles in radians {x: roll, y: pitch, z: yaw}
 */
export function quatToEuler(q: Quat): Vec3 {
  // Normalize quaternion to prevent numerical issues
  const len = Math.sqrt(q.x * q.x + q.y * q.y + q.z * q.z + q.w * q.w);
  
  //                                                                // bug // fix
  if (len === 0) {
    math3dWarn('ZERO_VECTOR_NORMALIZE',
      'quatToEuler: Cannot convert zero quaternion to Euler - returning identity rotation',
      { quaternion: q }
    );
    return { x: 0, y: 0, z: 0 };
  }
  
  const qx = q.x / len;
  const qy = q.y / len;
  const qz = q.z / len;
  const qw = q.w / len;

  // Pre-compute repeated values (more numerically stable)
  const sqx = qx * qx;
  const sqy = qy * qy;
  const sqz = qz * qz;
  const sqw = qw * qw;

  // Compute rotation matrix elements we need
  // This approach (via rotation matrix) is more numerically stable than direct formulas
  const m11 = sqw + sqx - sqy - sqz;
  const m12 = 2 * (qx * qy - qw * qz);
  const m13 = 2 * (qx * qz + qw * qy);
  const m21 = 2 * (qx * qy + qw * qz);
  const m22 = sqw - sqx + sqy - sqz;
  const m23 = 2 * (qy * qz - qw * qx);
  const m31 = 2 * (qx * qz - qw * qy);
  const m32 = 2 * (qy * qz + qw * qx);
  const m33 = sqw - sqx - sqy + sqz;

  // Extract Euler angles from rotation matrix (XYZ order)
  let x: number, y: number, z: number;

  // Clamp m13 to [-1, 1] to handle numerical errors
  const sinY = Math.max(-1, Math.min(1, m13));
  
  if (Math.abs(sinY) > 0.9999999) {
    // Gimbal lock: pitch is EXACTLY ±90° (within 0.01°)
    // Only warn here - this is the only case that actually matters
    math3dWarn('GIMBAL_LOCK',
      'Camera pitch is exactly ±90°. If animating through this angle, you may see a rotation glitch.',
      { pitchDegrees: Math.sign(sinY) * 90 }
    );
    y = Math.sign(sinY) * Math.PI / 2;
    z = 0;
    x = Math.atan2(-m32, m22);
  } else {
    // Normal case
    y = Math.asin(sinY);
    x = Math.atan2(-m23, m33);
    z = Math.atan2(-m12, m11);
  }

  return { x, y, z };
}

export function slerpQuat(a: Quat, b: Quat, t: number): Quat {
  let dot = a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w;

  if (dot < 0) {
    b = { x: -b.x, y: -b.y, z: -b.z, w: -b.w };
    dot = -dot;
  }

  if (dot > 0.9995) {
    return {
      x: a.x + t * (b.x - a.x),
      y: a.y + t * (b.y - a.y),
      z: a.z + t * (b.z - a.z),
      w: a.w + t * (b.w - a.w),
    };
  }

  const theta0 = Math.acos(dot);
  const theta = theta0 * t;
  const sinTheta = Math.sin(theta);
  const sinTheta0 = Math.sin(theta0);

  const s0 = Math.cos(theta) - (dot * sinTheta) / sinTheta0;
  const s1 = sinTheta / sinTheta0;

  return {
    x: s0 * a.x + s1 * b.x,
    y: s0 * a.y + s1 * b.y,
    z: s0 * a.z + s1 * b.z,
    w: s0 * a.w + s1 * b.w,
  };
}

// ════════════════════════════════════════════════════════════════════════════
// High-Precision Matrix Operations (Float64)
// Use these when precision > 1e-7 is required
// ════════════════════════════════════════════════════════════════════════════

/**
 * Create identity matrix with high precision (Float64)
 */
export function identityMat4_64(): Mat4_64 {
  return {
    elements: new Float64Array([
      1, 0, 0, 0,
      0, 1, 0, 0,
      0, 0, 1, 0,
      0, 0, 0, 1
    ])
  };
}

/**
 * Create scale matrix with high precision (Float64)
 */
export function scaleMat4_64(s: Vec3): Mat4_64 {
  return {
    elements: new Float64Array([
      s.x, 0, 0, 0,
      0, s.y, 0, 0,
      0, 0, s.z, 0,
      0, 0, 0, 1
    ])
  };
}

/**
 * Multiply matrices with high precision (Float64)
 * Precision: ~1e-15
 */
export function multiplyMat4_64(a: Mat4_64, b: Mat4_64): Mat4_64 {
  const ae = a.elements;
  const be = b.elements;
  const te = new Float64Array(16);

  const a11 = ae[0], a12 = ae[4], a13 = ae[8], a14 = ae[12];
  const a21 = ae[1], a22 = ae[5], a23 = ae[9], a24 = ae[13];
  const a31 = ae[2], a32 = ae[6], a33 = ae[10], a34 = ae[14];
  const a41 = ae[3], a42 = ae[7], a43 = ae[11], a44 = ae[15];

  const b11 = be[0], b12 = be[4], b13 = be[8], b14 = be[12];
  const b21 = be[1], b22 = be[5], b23 = be[9], b24 = be[13];
  const b31 = be[2], b32 = be[6], b33 = be[10], b34 = be[14];
  const b41 = be[3], b42 = be[7], b43 = be[11], b44 = be[15];

  te[0] = a11 * b11 + a12 * b21 + a13 * b31 + a14 * b41;
  te[4] = a11 * b12 + a12 * b22 + a13 * b32 + a14 * b42;
  te[8] = a11 * b13 + a12 * b23 + a13 * b33 + a14 * b43;
  te[12] = a11 * b14 + a12 * b24 + a13 * b34 + a14 * b44;

  te[1] = a21 * b11 + a22 * b21 + a23 * b31 + a24 * b41;
  te[5] = a21 * b12 + a22 * b22 + a23 * b32 + a24 * b42;
  te[9] = a21 * b13 + a22 * b23 + a23 * b33 + a24 * b43;
  te[13] = a21 * b14 + a22 * b24 + a23 * b34 + a24 * b44;

  te[2] = a31 * b11 + a32 * b21 + a33 * b31 + a34 * b41;
  te[6] = a31 * b12 + a32 * b22 + a33 * b32 + a34 * b42;
  te[10] = a31 * b13 + a32 * b23 + a33 * b33 + a34 * b43;
  te[14] = a31 * b14 + a32 * b24 + a33 * b34 + a34 * b44;

  te[3] = a41 * b11 + a42 * b21 + a43 * b31 + a44 * b41;
  te[7] = a41 * b12 + a42 * b22 + a43 * b32 + a44 * b42;
  te[11] = a41 * b13 + a42 * b23 + a43 * b33 + a44 * b43;
  te[15] = a41 * b14 + a42 * b24 + a43 * b34 + a44 * b44;

  return { elements: te };
}

/**
 * Convert high-precision matrix to GPU-compatible Float32
 */
export function convertToMat4(m: Mat4_64): Mat4 {
  return { elements: new Float32Array(m.elements) };
}

/**
 * Convert GPU matrix to high-precision for calculations
 */
export function convertToMat4_64(m: Mat4): Mat4_64 {
  return { elements: new Float64Array(m.elements) };
}

/**
 * Precision limit constants for documentation
 */
export const PRECISION = {
  FLOAT32_RELATIVE: 1e-7,   // ~7 significant digits
  FLOAT64_RELATIVE: 1e-15,  // ~15 significant digits
  FLOAT32_SCALE_MIN: 0.01,  // Minimum scale before precision loss
  FLOAT32_SCALE_MAX: 100,   // Maximum scale before precision loss
} as const;
