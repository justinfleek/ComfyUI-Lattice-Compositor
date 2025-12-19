# WEYL COMPOSITOR — CAMERA & SPLINE SYSTEM

**Document ID**: 06_CAMERA_SPLINE  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> Cameras are **evaluated data**, not interactive runtime objects.
> If camera motion depends on playback history, the system is broken.

---

## 1. DESIGN INTENT

The Weyl camera system mirrors professional DCC tools:

- **Adobe After Effects** — 3D camera with keyframes
- **Cinema 4D** — Spline-driven camera paths
- **Houdini** — Object-level camera evaluation
- **Nuke** — 3D camera workflows

It explicitly **rejects**:

- ❌ Game-engine camera patterns (delta-time updates)
- ❌ Mouse-driven viewports as render cameras
- ❌ Stateful camera simulation
- ❌ Frame-rate dependent motion

---

## 2. TWO CAMERA CONCEPTS

### 2.1 Scene Camera (Authoritative)

The camera used for **rendering and export**.

| Property | Value |
|----------|-------|
| Evaluated by | MotionEngine |
| Produces | View/projection matrices |
| Exports | Trajectory for diffusion models |
| Stored in | Project data |
| Keyframable | ✅ Yes |

### 2.2 Editor Camera (UI Only)

The camera used for **scene navigation** in the editor.

| Property | Value |
|----------|-------|
| Purpose | "Fly out of camera" inspection |
| Controls | Orbit, pan, zoom |
| Affects rendering | ❌ Never |
| Exported | ❌ Never |
| Stored in project | ❌ No |

**CRITICAL RULE**: Editor Camera state must **NEVER** leak into Scene Camera evaluation.

```typescript
// ❌ FORBIDDEN: Editor camera affecting scene
sceneCamera.position = editorCamera.position
renderWithCamera(isPlaying ? sceneCamera : editorCamera)

// ✅ REQUIRED: Complete separation
const sceneCamera = motionEngine.evaluate(frame, project).camera
const editorCamera = editorViewState.camera  // Completely separate
```

---

## 3. WORLD COORDINATE SYSTEM

Weyl uses a **right-handed** coordinate system:

```
       +Y (Up)
        |
        |
        |_______ +X (Right)
       /
      /
     +Z (Forward, into scene)
```

All cameras, layers, splines, and particles operate in this consistent world space.

**Audit Instruction**: Claude Code must verify all coordinate calculations use this convention. Mixed conventions are violations.

---

## 4. CAMERA DATA MODEL

### 4.1 Camera Layer (Source Data)

```typescript
interface CameraLayer extends Layer {
  readonly type: 'camera'
  readonly cameraType: 'perspective' | 'orthographic'
  
  // Transform properties
  readonly position: AnimatableProperty<Vec3>
  readonly target: AnimatableProperty<Vec3>
  readonly roll: AnimatableProperty<number>      // Degrees
  
  // Lens properties
  readonly fov: AnimatableProperty<number>       // Degrees, perspective only
  readonly zoom: AnimatableProperty<number>      // Orthographic only
  readonly near: number                          // Near clip plane
  readonly far: number                           // Far clip plane
  
  // Optional spline binding
  readonly pathBinding?: CameraPathBinding
}
```

### 4.2 Camera Path Binding

```typescript
interface CameraPathBinding {
  readonly positionSplineId?: string     // Spline for camera position
  readonly targetSplineId?: string       // Spline for look-at target
  readonly t: AnimatableProperty<number> // 0-1 position along spline
  readonly lookMode: 'alongPath' | 'atTarget' | 'custom'
}
```

### 4.3 Evaluated Camera (Output)

```typescript
interface EvaluatedCamera {
  readonly id: string
  readonly frame: number
  
  // Position and orientation
  readonly position: Vec3
  readonly target: Vec3
  readonly forward: Vec3       // Normalized direction vector
  readonly up: Vec3            // Normalized up vector (roll applied)
  readonly right: Vec3         // Normalized right vector
  
  // Lens
  readonly fov: number
  readonly near: number
  readonly far: number
  
  // Matrices
  readonly viewMatrix: Mat4
  readonly projectionMatrix: Mat4
}
```

---

## 5. SPLINE SYSTEM

### 5.1 Spline Data Model

```typescript
interface Spline3D {
  readonly id: string
  readonly name: string
  readonly points: readonly SplinePoint[]
  readonly closed: boolean
}

interface SplinePoint {
  readonly position: Vec3
  readonly inTangent?: Vec3   // Bezier handle for incoming curve
  readonly outTangent?: Vec3  // Bezier handle for outgoing curve
}

interface SplineEvaluation {
  readonly position: Vec3
  readonly tangent: Vec3      // Direction of travel
  readonly normal: Vec3       // Perpendicular to tangent
  readonly t: number          // Normalized position [0-1]
}
```

### 5.2 Spline Evaluation (Pure Function)

```typescript
function evaluateSpline(spline: Spline3D, t: number): SplineEvaluation {
  // Clamp or wrap t based on closed status
  const clampedT = spline.closed 
    ? t - Math.floor(t)  // Wrap for closed splines
    : Math.max(0, Math.min(1, t))  // Clamp for open splines
  
  // Handle edge cases
  const segmentCount = spline.closed 
    ? spline.points.length 
    : spline.points.length - 1
  
  if (segmentCount === 0) {
    return {
      position: spline.points[0]?.position ?? { x: 0, y: 0, z: 0 },
      tangent: { x: 0, y: 0, z: 1 },
      normal: { x: 1, y: 0, z: 0 },
      t: clampedT
    }
  }

  // Find segment
  const segmentT = clampedT * segmentCount
  const segmentIndex = Math.min(Math.floor(segmentT), segmentCount - 1)
  const localT = segmentT - segmentIndex

  // Get control points
  const p0 = spline.points[segmentIndex]
  const p1 = spline.points[(segmentIndex + 1) % spline.points.length]

  // Cubic Bezier control points
  const c0 = p0.position
  const c1 = p0.outTangent ?? p0.position
  const c2 = p1.inTangent ?? p1.position
  const c3 = p1.position

  // Evaluate position
  const position = cubicBezier(c0, c1, c2, c3, localT)

  // Evaluate tangent (derivative)
  const tangent = normalizeVec3(cubicBezierDerivative(c0, c1, c2, c3, localT))

  // Compute normal (perpendicular to tangent)
  const worldUp = { x: 0, y: 1, z: 0 }
  const right = normalizeVec3(crossVec3(tangent, worldUp))
  const normal = crossVec3(right, tangent)

  return Object.freeze({ position, tangent, normal, t: clampedT })
}
```

### 5.3 Cubic Bezier Helpers

```typescript
function cubicBezier(p0: Vec3, p1: Vec3, p2: Vec3, p3: Vec3, t: number): Vec3 {
  const mt = 1 - t
  const mt2 = mt * mt
  const mt3 = mt2 * mt
  const t2 = t * t
  const t3 = t2 * t

  return {
    x: mt3 * p0.x + 3 * mt2 * t * p1.x + 3 * mt * t2 * p2.x + t3 * p3.x,
    y: mt3 * p0.y + 3 * mt2 * t * p1.y + 3 * mt * t2 * p2.y + t3 * p3.y,
    z: mt3 * p0.z + 3 * mt2 * t * p1.z + 3 * mt * t2 * p2.z + t3 * p3.z
  }
}

function cubicBezierDerivative(p0: Vec3, p1: Vec3, p2: Vec3, p3: Vec3, t: number): Vec3 {
  const mt = 1 - t
  const mt2 = mt * mt
  const t2 = t * t

  return {
    x: 3 * mt2 * (p1.x - p0.x) + 6 * mt * t * (p2.x - p1.x) + 3 * t2 * (p3.x - p2.x),
    y: 3 * mt2 * (p1.y - p0.y) + 6 * mt * t * (p2.y - p1.y) + 3 * t2 * (p3.y - p2.y),
    z: 3 * mt2 * (p1.z - p0.z) + 6 * mt * t * (p2.z - p1.z) + 3 * t2 * (p3.z - p2.z)
  }
}
```

---

## 6. CAMERA EVALUATION

### 6.1 Evaluation Function (Pure)

```typescript
function evaluateCamera(
  composition: Composition,
  frame: number,
  activeCameraId: string | undefined,
  propertyValues: Map<string, any>
): EvaluatedCamera {
  // Find active camera layer
  const cameraLayer = composition.layers.find(
    l => l.type === 'camera' && l.id === activeCameraId
  ) as CameraLayer | undefined
  
  // Use default if no camera
  if (!cameraLayer) {
    return createDefaultCamera(composition, frame)
  }
  
  // Evaluate position (from keyframes or spline)
  let position: Vec3
  let target: Vec3
  
  if (cameraLayer.pathBinding?.positionSplineId) {
    // Camera bound to spline
    const spline = findSpline(composition, cameraLayer.pathBinding.positionSplineId)
    const t = getPropertyValue(cameraLayer.pathBinding.t, propertyValues)
    const evaluation = evaluateSpline(spline, t)
    position = evaluation.position
    
    // Determine target based on look mode
    switch (cameraLayer.pathBinding.lookMode) {
      case 'alongPath':
        target = addVec3(position, evaluation.tangent)
        break
      case 'atTarget':
        if (cameraLayer.pathBinding.targetSplineId) {
          const targetSpline = findSpline(composition, cameraLayer.pathBinding.targetSplineId)
          target = evaluateSpline(targetSpline, t).position
        } else {
          target = getPropertyValue(cameraLayer.target, propertyValues)
        }
        break
      case 'custom':
        target = getPropertyValue(cameraLayer.target, propertyValues)
        break
    }
  } else {
    // Camera uses direct keyframes
    position = getPropertyValue(cameraLayer.position, propertyValues)
    target = getPropertyValue(cameraLayer.target, propertyValues)
  }
  
  const roll = getPropertyValue(cameraLayer.roll, propertyValues)
  const fov = getPropertyValue(cameraLayer.fov, propertyValues)
  
  // Compute derived vectors
  const forward = normalizeVec3(subtractVec3(target, position))
  const right = normalizeVec3(crossVec3(forward, { x: 0, y: 1, z: 0 }))
  const up = crossVec3(right, forward)
  
  // Apply roll
  const rollRad = roll * Math.PI / 180
  const rolledUp = rotateAroundAxis(up, forward, rollRad)
  const rolledRight = rotateAroundAxis(right, forward, rollRad)
  
  // Compute matrices
  const viewMatrix = createViewMatrix(position, target, rolledUp)
  const projectionMatrix = createPerspectiveMatrix(
    fov,
    composition.width / composition.height,
    cameraLayer.near,
    cameraLayer.far
  )
  
  return Object.freeze({
    id: cameraLayer.id,
    frame,
    position,
    target,
    forward,
    up: rolledUp,
    right: rolledRight,
    fov,
    near: cameraLayer.near,
    far: cameraLayer.far,
    viewMatrix,
    projectionMatrix
  })
}
```

### 6.2 Default Camera

```typescript
function createDefaultCamera(composition: Composition, frame: number): EvaluatedCamera {
  // After Effects-style default: camera positioned to see full comp
  const aspectRatio = composition.width / composition.height
  const fov = 39.6  // AE default
  const distance = (composition.height / 2) / Math.tan((fov / 2) * Math.PI / 180)
  
  const position = { x: composition.width / 2, y: composition.height / 2, z: -distance }
  const target = { x: composition.width / 2, y: composition.height / 2, z: 0 }
  
  return Object.freeze({
    id: '__default__',
    frame,
    position,
    target,
    forward: { x: 0, y: 0, z: 1 },
    up: { x: 0, y: 1, z: 0 },
    right: { x: 1, y: 0, z: 0 },
    fov,
    near: 1,
    far: 10000,
    viewMatrix: createViewMatrix(position, target, { x: 0, y: 1, z: 0 }),
    projectionMatrix: createPerspectiveMatrix(fov, aspectRatio, 1, 10000)
  })
}
```

---

## 7. CAMERA TRAJECTORY EXPORT

### 7.1 Trajectory Frame Format

```typescript
interface CameraTrajectoryFrame {
  readonly frame: number
  readonly position: Vec3
  readonly forward: Vec3
  readonly up: Vec3
  readonly fov: number
}
```

### 7.2 Export Function

```typescript
function exportCameraTrajectory(
  project: WeylProject,
  frameRange: [number, number],
  audioAnalysis?: AudioAnalysis
): CameraTrajectoryFrame[] {
  const trajectory: CameraTrajectoryFrame[] = []

  for (let frame = frameRange[0]; frame <= frameRange[1]; frame++) {
    const frameState = motionEngine.evaluate(frame, project, audioAnalysis)
    
    trajectory.push(Object.freeze({
      frame,
      position: frameState.camera.position,
      forward: frameState.camera.forward,
      up: frameState.camera.up,
      fov: frameState.camera.fov
    }))
  }

  return Object.freeze(trajectory)
}
```

### 7.3 Output Formats

Camera trajectories can be exported as:

| Format | Shape/Structure | Use Case |
|--------|-----------------|----------|
| **JSON** | Array of `CameraTrajectoryFrame` | General interchange |
| **Tensor** | `[FRAMES, 10]` (pos xyz, fwd xyz, up xyz, fov) | Diffusion model conditioning |
| **NPY** | NumPy array | Python/ComfyUI workflows |
| **Alembic** | Standard DCC format | Future: Blender/Maya interchange |

### 7.4 Export File Naming

```
exports/
├── camera/
│   ├── trajectory.json           # Full trajectory
│   ├── trajectory.npy            # NumPy tensor
│   └── metadata.json             # Export settings
```

---

## 8. SUPPORTED CAMERA RIGS

These common camera motions must be expressible through keyframes and/or splines:

| Rig | Implementation |
|-----|----------------|
| **Dolly** | Z position keyframes |
| **Truck** | X/Y position keyframes |
| **Orbit** | Target-relative position on circular path or spline |
| **Crane** | Y position keyframes with fixed target |
| **Rail** | Position bound to spline with `t` animated |
| **Handheld** | Noise-based position/rotation offsets (deterministic via seed) |
| **Zoom** | FOV keyframes (perspective) or zoom keyframes (ortho) |
| **Push** | Combined dolly + zoom for Vertigo effect |

**All rigs reduce to keyframes and/or splines. No rig introduces simulation or hidden state.**

---

## 9. SPLINE USES BEYOND CAMERA

Splines are a general-purpose primitive used for:

| Use Case | Description |
|----------|-------------|
| **Camera Path** | Position/target binding |
| **Text on Path** | Text layout along spline |
| **Particle Emitter** | Emit particles along spline |
| **Motion Path** | Layer position follows spline |
| **Mask Path** | Animated vector masks |

All uses share the same `Spline3D` data model and `evaluateSpline` function.

---

## 10. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Delta-time camera movement
camera.position.x += velocity.x * deltaTime
camera.position.y += velocity.y * deltaTime

// ❌ FORBIDDEN: Accumulated roll
this.accumulatedRoll += rollSpeed * dt

// ❌ FORBIDDEN: Real-time in camera
const elapsed = performance.now() - this.startTime
camera.position.x = Math.sin(elapsed * 0.001)

// ❌ FORBIDDEN: Interactive lookAt in render loop
camera.lookAt(mouseWorldPosition)

// ❌ FORBIDDEN: Editor camera affecting render
if (isEditing) renderWith(editorCamera)
else renderWith(sceneCamera)

// ✅ REQUIRED: Pure evaluation
const position = interpolateProperty(cameraLayer.position, frame)
const target = interpolateProperty(cameraLayer.target, frame)
const viewMatrix = createViewMatrix(position, target, up)

// ✅ REQUIRED: Spline evaluation is pure
const t = interpolateProperty(pathBinding.t, frame)
const { position, tangent } = evaluateSpline(spline, t)
```

---

## 11. TESTING REQUIREMENTS

```typescript
describe('Camera Evaluation', () => {
  it('produces identical output for same frame', () => {
    const a = evaluateCamera(comp, 100, cameraId, props)
    const b = evaluateCamera(comp, 100, cameraId, props)
    expect(a).toEqual(b)
    expect(a.viewMatrix).toEqual(b.viewMatrix)
  })

  it('is scrub-order independent', () => {
    const a = evaluateCamera(comp, 50, cameraId, props)
    evaluateCamera(comp, 200, cameraId, props)
    evaluateCamera(comp, 10, cameraId, props)
    const b = evaluateCamera(comp, 50, cameraId, props)
    expect(a).toEqual(b)
  })

  it('returns frozen output', () => {
    const result = evaluateCamera(comp, 100, cameraId, props)
    expect(Object.isFrozen(result)).toBe(true)
  })

  it('spline evaluation is deterministic', () => {
    const a = evaluateSpline(spline, 0.5)
    const b = evaluateSpline(spline, 0.5)
    expect(a).toEqual(b)
  })

  it('editor camera does not affect scene camera', () => {
    editorCamera.position = { x: 999, y: 999, z: 999 }
    const sceneResult = evaluateCamera(comp, 100, cameraId, props)
    expect(sceneResult.position).not.toEqual(editorCamera.position)
  })
})
```

---

## 12. AUDIT CHECKLIST

Claude Code must verify:

- [ ] Scene Camera and Editor Camera are completely separate systems
- [ ] Camera evaluation is a pure function in MotionEngine
- [ ] No delta-time or accumulated state in camera code
- [ ] Spline evaluation uses cubic Bezier correctly
- [ ] View and projection matrices computed from evaluated values
- [ ] Camera trajectory export produces identical results across runs
- [ ] Roll is applied correctly around forward axis
- [ ] Default camera matches After Effects conventions
- [ ] All outputs are frozen/immutable
- [ ] Coordinate system is consistently right-handed (+X right, +Y up, +Z forward)

**Any camera code that maintains state between frames is a violation.**

---

**Previous**: [05_PARTICLE_SYSTEM.md](./05_PARTICLE_SYSTEM.md)  
**Next**: [07_TEXT_SHAPE.md](./07_TEXT_SHAPE.md)
