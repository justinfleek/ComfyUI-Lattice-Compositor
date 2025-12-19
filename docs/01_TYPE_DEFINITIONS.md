# WEYL COMPOSITOR — TYPE DEFINITIONS

**Document ID**: 01_TYPE_DEFINITIONS  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [00_MASTER_GROUND_TRUTH.md](./00_MASTER_GROUND_TRUTH.md)

> This document defines all core TypeScript types used throughout Weyl Compositor.
> All types are designed to be **immutable** and **serializable**.

---

## 1. DESIGN PRINCIPLES

| Principle | Implementation |
|-----------|----------------|
| **Immutability** | All properties use `readonly` |
| **Serialization** | All types are JSON-serializable |
| **Determinism** | No functions, closures, or non-deterministic values |
| **Separation** | Source types (data) vs Evaluated types (output) |

---

## 2. MATH PRIMITIVES

### 2.1 Vec2

```typescript
interface Vec2 {
  readonly x: number
  readonly y: number
}
```

### 2.2 Vec3

```typescript
interface Vec3 {
  readonly x: number
  readonly y: number
  readonly z: number
}
```

### 2.3 Vec4

```typescript
interface Vec4 {
  readonly x: number
  readonly y: number
  readonly z: number
  readonly w: number
}
```

### 2.4 Color

RGBA color in **linear color space**, values in **0-1 range**.

```typescript
type Color = Vec4
```

**Important**: Colors must be linear, not sRGB. Conversion happens only at final export.

### 2.5 Mat4

4x4 transformation matrix in **column-major order** (OpenGL/WebGL convention).

```typescript
interface Mat4 {
  readonly elements: readonly [
    number, number, number, number,
    number, number, number, number,
    number, number, number, number,
    number, number, number, number
  ]
}
```

### 2.6 Rect

Axis-aligned bounding rectangle.

```typescript
interface Rect {
  readonly x: number
  readonly y: number
  readonly width: number
  readonly height: number
}
```

---

## 3. ANIMATION TYPES

### 3.1 InterpolationType

```typescript
type InterpolationType = 'linear' | 'bezier' | 'hold'
```

| Type | Behavior |
|------|----------|
| `linear` | Straight-line interpolation |
| `bezier` | Cubic bezier curve with tangent handles |
| `hold` | No interpolation; holds previous value until next keyframe |

### 3.2 EasingConfig

```typescript
interface EasingConfig {
  readonly inHandle: Vec2   // x: time influence, y: value influence
  readonly outHandle: Vec2
}
```

### 3.3 Keyframe

```typescript
interface Keyframe<T> {
  readonly frame: number
  readonly value: T
  readonly interpolation: InterpolationType
  readonly easing?: EasingConfig
}
```

### 3.4 AnimatableProperty

```typescript
interface AnimatableProperty<T> {
  readonly keyframes: readonly Keyframe<T>[]
  readonly defaultValue: T
  readonly driver?: PropertyDriver
}
```

### 3.5 TransformProperties

```typescript
interface TransformProperties {
  readonly position: AnimatableProperty<Vec3>
  readonly rotation: AnimatableProperty<Vec3>   // Euler angles in degrees
  readonly scale: AnimatableProperty<Vec3>      // 1.0 = 100%
  readonly anchor: AnimatableProperty<Vec3>
  readonly opacity: AnimatableProperty<number>  // 0-1
}
```

---

## 4. LAYER TYPES

### 4.1 LayerType

```typescript
type LayerType =
  | 'solid'
  | 'image'
  | 'video'
  | 'text'
  | 'shape'
  | 'particle'
  | 'null'
  | 'camera'
  | 'light'
  | 'adjustment'
  | 'precomp'
```

### 4.2 BlendMode

```typescript
type BlendMode =
  | 'normal'
  | 'add'
  | 'multiply'
  | 'screen'
  | 'overlay'
  | 'darken'
  | 'lighten'
```

### 4.3 Base Layer

```typescript
interface Layer {
  readonly id: string
  readonly name: string
  readonly type: LayerType
  readonly startFrame: number
  readonly endFrame: number
  readonly transform: TransformProperties
  readonly visible: AnimatableProperty<boolean>
  readonly blendMode: BlendMode
  readonly opacity: AnimatableProperty<number>
  readonly parentId?: string
  readonly maskIds?: readonly string[]
}
```

### 4.4 Specific Layer Types

```typescript
interface SolidLayer extends Layer {
  readonly type: 'solid'
  readonly color: AnimatableProperty<Color>
  readonly width: number
  readonly height: number
}

interface ImageLayer extends Layer {
  readonly type: 'image'
  readonly assetId: string
}

interface VideoLayer extends Layer {
  readonly type: 'video'
  readonly assetId: string
  readonly timeRemap?: AnimatableProperty<number>
  readonly loop: boolean
}

interface TextLayer extends Layer {
  readonly type: 'text'
  readonly content: AnimatableProperty<string>
  readonly fontId: string
  readonly fontSize: AnimatableProperty<number>
  readonly fill: AnimatableProperty<Color>
  readonly stroke?: AnimatableProperty<StrokeStyle>
}

interface ShapeLayer extends Layer {
  readonly type: 'shape'
  readonly paths: AnimatableProperty<readonly BezierPath[]>
  readonly fill?: AnimatableProperty<FillStyle>
  readonly stroke?: AnimatableProperty<StrokeStyle>
}

interface ParticleLayer extends Layer {
  readonly type: 'particle'
  readonly config: ParticleSystemConfig
}

interface NullLayer extends Layer {
  readonly type: 'null'
}

interface CameraLayer extends Layer {
  readonly type: 'camera'
  readonly cameraType: 'perspective' | 'orthographic'
  readonly position: AnimatableProperty<Vec3>
  readonly target: AnimatableProperty<Vec3>
  readonly roll: AnimatableProperty<number>
  readonly fov: AnimatableProperty<number>
  readonly near: number
  readonly far: number
  readonly pathBinding?: CameraPathBinding
}

interface PrecompLayer extends Layer {
  readonly type: 'precomp'
  readonly compositionId: string
  readonly timeMapping: PrecompTimeMapping
  readonly inheritCamera: boolean
}
```

---

## 5. PROJECT TYPES

### 5.1 Composition

```typescript
interface Composition {
  readonly id: string
  readonly name: string
  readonly width: number
  readonly height: number
  readonly frameRate: number
  readonly frameCount: number
  readonly startFrame: number
  readonly backgroundColor: Color
  readonly layers: readonly Layer[]
  readonly activeCameraId?: string
}
```

### 5.2 Asset

```typescript
interface Asset {
  readonly id: string
  readonly name: string
  readonly type: AssetType
  readonly sourcePath: string
  readonly hash: string  // SHA-256
  readonly importedAt: string
}

type AssetType = 'image' | 'video' | 'audio' | 'font' | 'svg' | 'lottie'
```

### 5.3 WeylProject

```typescript
interface WeylProject {
  readonly id: string
  readonly name: string
  readonly version: string
  readonly mainCompositionId: string
  readonly compositions: readonly Composition[]
  readonly assets: readonly Asset[]
  readonly audioAssetId?: string
  readonly audioAnalysis?: AudioAnalysis
}
```

---

## 6. EVALUATED TYPES (OUTPUT)

### 6.1 EvaluatedTransform

```typescript
interface EvaluatedTransform {
  readonly position: Vec3
  readonly rotation: Vec3
  readonly scale: Vec3
  readonly anchor: Vec3
  readonly opacity: number
  readonly matrix: Mat4
}
```

### 6.2 EvaluatedLayer

```typescript
interface EvaluatedLayer {
  readonly id: string
  readonly type: LayerType
  readonly frame: number
  readonly visible: boolean
  readonly transform: EvaluatedTransform
  readonly blendMode: BlendMode
  readonly opacity: number
  readonly content: LayerContent
}
```

### 6.3 EvaluatedCamera

```typescript
interface EvaluatedCamera {
  readonly id: string
  readonly frame: number
  readonly position: Vec3
  readonly target: Vec3
  readonly forward: Vec3
  readonly up: Vec3
  readonly right: Vec3
  readonly fov: number
  readonly near: number
  readonly far: number
  readonly viewMatrix: Mat4
  readonly projectionMatrix: Mat4
}
```

### 6.4 FrameState

```typescript
interface FrameState {
  readonly frame: number
  readonly timestamp: number
  readonly layers: readonly EvaluatedLayer[]
  readonly camera: EvaluatedCamera
  readonly particles: ParticleSnapshot
  readonly audio: EvaluatedAudio
}
```

---

## 7. SUPPORTING TYPES

### 7.1 BezierPath

```typescript
interface BezierPath {
  readonly closed: boolean
  readonly segments: readonly BezierSegment[]
}

interface BezierSegment {
  readonly p0: Vec2
  readonly c1: Vec2
  readonly c2: Vec2
  readonly p1: Vec2
}
```

### 7.2 Spline3D

```typescript
interface Spline3D {
  readonly id: string
  readonly name: string
  readonly points: readonly SplinePoint[]
  readonly closed: boolean
}

interface SplinePoint {
  readonly position: Vec3
  readonly inTangent?: Vec3
  readonly outTangent?: Vec3
}
```

### 7.3 PropertyDriver

```typescript
interface PropertyDriver {
  readonly source: PropertyPath | AudioSourcePath
  readonly transform?: MappingFunction
}

interface PropertyPath {
  readonly layerId: string
  readonly property: string
}

interface AudioSourcePath {
  readonly type: 'audio'
  readonly feature: 'amplitude' | 'rms' | 'spectrum' | 'beat' | 'onset'
  readonly band?: number
}

type MappingFunction = (value: number, frame: number) => number
```

---

## 8. AUDIT CHECKLIST

Claude Code must verify:

- [ ] All types exist in source code
- [ ] All properties use `readonly`
- [ ] All arrays use `readonly` arrays
- [ ] No mutable state in data structures
- [ ] All types are JSON-serializable
- [ ] Vec2, Vec3, Vec4, Mat4 used consistently
- [ ] Color uses Vec4, not {r,g,b,a}
- [ ] AnimatableProperty<T> wraps all animatable values
- [ ] FrameState structure matches specification
- [ ] Evaluated types are distinct from source types

**Any deviation from these types must be flagged.**

---

**Previous**: [00_MASTER_GROUND_TRUTH.md](./00_MASTER_GROUND_TRUTH.md)  
**Next**: [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)
