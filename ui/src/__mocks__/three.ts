/**
 * Three.js mock for testing
 * Provides minimal stubs for Three.js classes used in the codebase
 */

// Vector classes
export class Vector2 {
  x: number;
  y: number;
  constructor(x = 0, y = 0) {
    this.x = x;
    this.y = y;
  }
  set(x: number, y: number) {
    this.x = x;
    this.y = y;
    return this;
  }
  copy(v: Vector2) {
    this.x = v.x;
    this.y = v.y;
    return this;
  }
  clone() {
    return new Vector2(this.x, this.y);
  }
  add(v: Vector2) {
    this.x += v.x;
    this.y += v.y;
    return this;
  }
  sub(v: Vector2) {
    this.x -= v.x;
    this.y -= v.y;
    return this;
  }
  multiplyScalar(s: number) {
    this.x *= s;
    this.y *= s;
    return this;
  }
  length() {
    return Math.sqrt(this.x * this.x + this.y * this.y);
  }
  normalize() {
    const l = this.length();
    if (l > 0) {
      this.x /= l;
      this.y /= l;
    }
    return this;
  }
}

export class Vector3 {
  x: number;
  y: number;
  z: number;
  constructor(x = 0, y = 0, z = 0) {
    this.x = x;
    this.y = y;
    this.z = z;
  }
  set(x: number, y: number, z: number) {
    this.x = x;
    this.y = y;
    this.z = z;
    return this;
  }
  copy(v: Vector3) {
    this.x = v.x;
    this.y = v.y;
    this.z = v.z;
    return this;
  }
  clone() {
    return new Vector3(this.x, this.y, this.z);
  }
  add(v: Vector3) {
    this.x += v.x;
    this.y += v.y;
    this.z += v.z;
    return this;
  }
  sub(v: Vector3) {
    this.x -= v.x;
    this.y -= v.y;
    this.z -= v.z;
    return this;
  }
  multiplyScalar(s: number) {
    this.x *= s;
    this.y *= s;
    this.z *= s;
    return this;
  }
  length() {
    return Math.sqrt(this.x * this.x + this.y * this.y + this.z * this.z);
  }
  normalize() {
    const l = this.length();
    if (l > 0) {
      this.x /= l;
      this.y /= l;
      this.z /= l;
    }
    return this;
  }
  applyMatrix4(_m: Matrix4) {
    return this;
  }
  applyQuaternion(_q: Quaternion) {
    return this;
  }
}

export class Vector4 {
  x: number;
  y: number;
  z: number;
  w: number;
  constructor(x = 0, y = 0, z = 0, w = 1) {
    this.x = x;
    this.y = y;
    this.z = z;
    this.w = w;
  }
}

// Quaternion
export class Quaternion {
  x = 0;
  y = 0;
  z = 0;
  w = 1;
  setFromEuler(_e: Euler) {
    return this;
  }
  setFromAxisAngle(_axis: Vector3, _angle: number) {
    return this;
  }
  multiply(_q: Quaternion) {
    return this;
  }
  clone() {
    return new Quaternion();
  }
}

// Euler
export class Euler {
  x = 0;
  y = 0;
  z = 0;
  order = "XYZ";
  constructor(x = 0, y = 0, z = 0, order = "XYZ") {
    this.x = x;
    this.y = y;
    this.z = z;
    this.order = order;
  }
  set(x: number, y: number, z: number, order?: string) {
    this.x = x;
    this.y = y;
    this.z = z;
    if (order) this.order = order;
    return this;
  }
}

// Matrix
export class Matrix4 {
  elements = new Float32Array(16);
  constructor() {
    this.identity();
  }
  identity() {
    this.elements.set([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]);
    return this;
  }
  multiply(_m: Matrix4) {
    return this;
  }
  multiplyMatrices(_a: Matrix4, _b: Matrix4) {
    return this;
  }
  makeRotationFromEuler(_e: Euler) {
    return this;
  }
  makeScale(_x: number, _y: number, _z: number) {
    return this;
  }
  makeTranslation(_x: number, _y: number, _z: number) {
    return this;
  }
  compose(_p: Vector3, _q: Quaternion, _s: Vector3) {
    return this;
  }
  decompose(_p: Vector3, _q: Quaternion, _s: Vector3) {
    return this;
  }
  getInverse(_m: Matrix4) {
    return this;
  }
  invert() {
    return this;
  }
}

// Color
export class Color {
  r = 1;
  g = 1;
  b = 1;
  constructor(color?: string | number) {
    if (color !== undefined) this.set(color);
  }
  set(_color: string | number) {
    return this;
  }
  setHex(_hex: number) {
    return this;
  }
  getHex() {
    return 0xffffff;
  }
  clone() {
    return new Color();
  }
}

// Object3D
export class Object3D {
  id = Math.random();
  uuid = Math.random().toString();
  name = "";
  type = "Object3D";
  parent: Object3D | null = null;
  children: Object3D[] = [];
  position = new Vector3();
  rotation = new Euler();
  quaternion = new Quaternion();
  scale = new Vector3(1, 1, 1);
  matrix = new Matrix4();
  matrixWorld = new Matrix4();
  visible = true;
  renderOrder = 0;
  userData: Record<string, any> = {};

  add(object: Object3D) {
    object.parent = this;
    this.children.push(object);
    return this;
  }
  remove(object: Object3D) {
    const idx = this.children.indexOf(object);
    if (idx >= 0) {
      this.children.splice(idx, 1);
      object.parent = null;
    }
    return this;
  }
  traverse(callback: (obj: Object3D) => void) {
    callback(this);
    for (const child of this.children) {
      child.traverse(callback);
    }
  }
  updateMatrix() {}
  updateMatrixWorld(_force?: boolean) {}
  lookAt(_v: Vector3 | number, _y?: number, _z?: number) {}
  clear() {
    this.children = [];
    return this;
  }
}

export class Group extends Object3D {
  type = "Group";
}

export class Scene extends Object3D {
  type = "Scene";
  background: Color | null = null;
}

// Geometry
export class BufferGeometry {
  uuid = Math.random().toString();
  attributes: Record<string, any> = {};
  index: any = null;
  dispose() {}
  setAttribute(_name: string, _attr: any) {
    return this;
  }
  setFromPoints(_points: Vector3[]) {
    return this;
  }
  computeBoundingBox() {}
  computeBoundingSphere() {}
}

export class PlaneGeometry extends BufferGeometry {}
export class BoxGeometry extends BufferGeometry {}
export class SphereGeometry extends BufferGeometry {}
export class ConeGeometry extends BufferGeometry {}
export class CircleGeometry extends BufferGeometry {}

// Materials
export class Material {
  uuid = Math.random().toString();
  transparent = false;
  opacity = 1;
  visible = true;
  side = 0;
  depthTest = true;
  depthWrite = true;
  blending = 1;
  needsUpdate = false;
  dispose() {}
  clone() {
    return new Material();
  }
}

export class MeshBasicMaterial extends Material {
  color = new Color();
  map: any = null;
  wireframe = false;
}

export class MeshStandardMaterial extends Material {
  color = new Color();
  map: any = null;
  metalness = 0;
  roughness = 1;
}

export class LineBasicMaterial extends Material {
  color = new Color();
}

export class ShaderMaterial extends Material {
  uniforms: Record<string, any> = {};
  vertexShader = "";
  fragmentShader = "";
}

export class SpriteMaterial extends Material {
  color = new Color();
  map: any = null;
}

export class PointsMaterial extends Material {
  color = new Color();
  size = 1;
  sizeAttenuation = true;
}

// Mesh and primitives
export class Mesh extends Object3D {
  type = "Mesh";
  geometry: BufferGeometry;
  material: Material;
  constructor(geometry?: BufferGeometry, material?: Material) {
    super();
    this.geometry = geometry || new BufferGeometry();
    this.material = material || new MeshBasicMaterial();
  }
}

export class Line extends Object3D {
  type = "Line";
  geometry: BufferGeometry;
  material: Material;
  constructor(geometry?: BufferGeometry, material?: Material) {
    super();
    this.geometry = geometry || new BufferGeometry();
    this.material = material || new LineBasicMaterial();
  }
}

export class Sprite extends Object3D {
  type = "Sprite";
  material: SpriteMaterial;
  constructor(material?: SpriteMaterial) {
    super();
    this.material = material || new SpriteMaterial();
  }
}

export class Points extends Object3D {
  type = "Points";
  geometry: BufferGeometry;
  material: Material;
  constructor(geometry?: BufferGeometry, material?: Material) {
    super();
    this.geometry = geometry || new BufferGeometry();
    this.material = material || new PointsMaterial();
  }
}

// Camera
export class Camera extends Object3D {
  type = "Camera";
  matrixWorldInverse = new Matrix4();
  projectionMatrix = new Matrix4();
  projectionMatrixInverse = new Matrix4();
}

export class PerspectiveCamera extends Camera {
  type = "PerspectiveCamera";
  fov = 50;
  aspect = 1;
  near = 0.1;
  far = 2000;
  zoom = 1;
  constructor(fov?: number, aspect?: number, near?: number, far?: number) {
    super();
    if (fov !== undefined) this.fov = fov;
    if (aspect !== undefined) this.aspect = aspect;
    if (near !== undefined) this.near = near;
    if (far !== undefined) this.far = far;
  }
  updateProjectionMatrix() {}
}

export class OrthographicCamera extends Camera {
  type = "OrthographicCamera";
  left = -1;
  right = 1;
  top = 1;
  bottom = -1;
  near = 0.1;
  far = 2000;
  zoom = 1;
  updateProjectionMatrix() {}
}

// Lights
export class Light extends Object3D {
  type = "Light";
  color = new Color();
  intensity = 1;
}

export class AmbientLight extends Light {
  type = "AmbientLight";
}

export class PointLight extends Light {
  type = "PointLight";
  distance = 0;
  decay = 2;
}

export class DirectionalLight extends Light {
  type = "DirectionalLight";
  target = new Object3D();
}

export class SpotLight extends Light {
  type = "SpotLight";
  distance = 0;
  angle = Math.PI / 3;
  penumbra = 0;
  decay = 2;
  target = new Object3D();
}

// Texture
export class Texture {
  uuid = Math.random().toString();
  image: any = null;
  needsUpdate = false;
  wrapS = 1000;
  wrapT = 1000;
  magFilter = 1006;
  minFilter = 1008;
  dispose() {}
}

export class CanvasTexture extends Texture {
  constructor(_canvas?: HTMLCanvasElement) {
    super();
  }
}

// Renderer
export class WebGLRenderer {
  domElement = document.createElement("canvas");
  shadowMap = { enabled: false, type: 0 };
  info = {
    memory: { geometries: 0, textures: 0 },
    render: { calls: 0, triangles: 0, frame: 0 },
  };
  setSize(_w: number, _h: number) {}
  setPixelRatio(_r: number) {}
  setClearColor(_c: Color | number, _a?: number) {}
  render(_scene: Scene, _camera: Camera) {}
  dispose() {}
  getRenderTarget() {
    return null;
  }
  setRenderTarget(_target: any) {}
  readRenderTargetPixels(
    _target: any,
    _x: number,
    _y: number,
    _w: number,
    _h: number,
    _buffer: any,
  ) {}
  getContext() {
    return {};
  }
}

export class WebGLRenderTarget {
  width: number;
  height: number;
  texture = new Texture();

  constructor(width: number, height: number, _options?: any) {
    this.width = width;
    this.height = height;
  }
  setSize(width: number, height: number) {
    this.width = width;
    this.height = height;
  }
  dispose() {}
}

// Buffer attributes
export class BufferAttribute {
  array: Float32Array;
  itemSize: number;
  count: number;
  needsUpdate = false;

  constructor(array: Float32Array, itemSize: number) {
    this.array = array;
    this.itemSize = itemSize;
    this.count = array.length / itemSize;
  }

  // Setter methods used by GPUParticleSystem.updateInstanceBuffers()
  setXY(index: number, x: number, y: number) {
    const offset = index * this.itemSize;
    this.array[offset] = x;
    this.array[offset + 1] = y;
    return this;
  }

  setXYZ(index: number, x: number, y: number, z: number) {
    const offset = index * this.itemSize;
    this.array[offset] = x;
    this.array[offset + 1] = y;
    this.array[offset + 2] = z;
    return this;
  }

  setXYZW(index: number, x: number, y: number, z: number, w: number) {
    const offset = index * this.itemSize;
    this.array[offset] = x;
    this.array[offset + 1] = y;
    this.array[offset + 2] = z;
    this.array[offset + 3] = w;
    return this;
  }

  // Getter methods
  getX(index: number) {
    return this.array[index * this.itemSize];
  }

  getY(index: number) {
    return this.array[index * this.itemSize + 1];
  }

  getZ(index: number) {
    return this.array[index * this.itemSize + 2];
  }

  getW(index: number) {
    return this.array[index * this.itemSize + 3];
  }
}

export class Float32BufferAttribute extends BufferAttribute {
  constructor(array: number[] | Float32Array, itemSize: number) {
    super(
      array instanceof Float32Array ? array : new Float32Array(array),
      itemSize,
    );
  }
}

// Instanced buffer attribute for particle systems
export class InstancedBufferAttribute extends BufferAttribute {
  meshPerAttribute: number;

  constructor(array: Float32Array, itemSize: number, normalized = false, meshPerAttribute = 1) {
    super(array, itemSize);
    // normalized is accepted but not used in mock
    void normalized;
    this.meshPerAttribute = meshPerAttribute;
  }
}

// Instanced buffer geometry for particle systems
export class InstancedBufferGeometry extends BufferGeometry {
  type = "InstancedBufferGeometry";
  instanceCount = Infinity;

  copy(_source: InstancedBufferGeometry) {
    return this;
  }
}

// Raycaster
export class Raycaster {
  ray = { origin: new Vector3(), direction: new Vector3() };
  near = 0;
  far = Infinity;
  setFromCamera(_coords: Vector2, _camera: Camera) {}
  intersectObjects(_objects: Object3D[], _recursive?: boolean): any[] {
    return [];
  }
}

// Loaders
export class TextureLoader {
  load(_url: string, onLoad?: (tex: Texture) => void): Texture {
    const tex = new Texture();
    if (onLoad) setTimeout(() => onLoad(tex), 0);
    return tex;
  }
}

// Constants
export const DoubleSide = 2;
export const FrontSide = 0;
export const BackSide = 1;
export const AdditiveBlending = 2;
export const NormalBlending = 1;
export const MultiplyBlending = 4;
export const SubtractiveBlending = 3;
export const ClampToEdgeWrapping = 1001;
export const RepeatWrapping = 1000;
export const MirroredRepeatWrapping = 1002;
export const NearestFilter = 1003;
export const LinearFilter = 1006;
export const LinearMipMapLinearFilter = 1008;
export const GLSL3 = "glsl3";

// Math utilities
export const MathUtils = {
  clamp: (value: number, min: number, max: number) =>
    Math.max(min, Math.min(max, value)),
  lerp: (a: number, b: number, t: number) => a + (b - a) * t,
  degToRad: (degrees: number) => degrees * (Math.PI / 180),
  radToDeg: (radians: number) => radians * (180 / Math.PI),
  generateUUID: () => Math.random().toString(36).slice(2, 11),
};
