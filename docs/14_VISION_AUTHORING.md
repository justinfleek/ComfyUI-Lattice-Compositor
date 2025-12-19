# WEYL COMPOSITOR — VISION-GUIDED AUTHORING

**Document ID**: 14_VISION_AUTHORING  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> **Prompts generate editable authoring data, not motion.**
> AI involvement ends once a prompt is resolved.
> Motion is evaluated exclusively by MotionEngine.

---

## 1. CORE PRINCIPLE

Vision-Guided Authoring uses AI to **assist setup**, not to **control evaluation**.

```
User Prompt
       ↓
AI Analysis (VLM)
       ↓
Structured Intent
       ↓
Deterministic Translation
       ↓
Keyframes / Configuration
       ↓
User Accepts
       ↓
MotionEngine Evaluates (AI no longer involved)
```

**The AI's job ends at keyframe generation. MotionEngine is the sole evaluator.**

---

## 2. WHAT VISION-GUIDED AUTHORING IS

| Allowed | Description |
|---------|-------------|
| ✅ Scene understanding | AI analyzes image/video content |
| ✅ Motion suggestions | AI proposes camera movements, effects |
| ✅ Setup assistance | AI helps configure layers, particles |
| ✅ Intent translation | Natural language → structured data → keyframes |
| ✅ Depth estimation | AI generates depth maps (one-time) |
| ✅ Segmentation | AI creates masks (one-time) |

---

## 3. WHAT VISION-GUIDED AUTHORING IS NOT

| Forbidden | Description |
|-----------|-------------|
| ❌ Runtime evaluation | AI does not evaluate frames |
| ❌ Frame stepping | AI does not advance simulations |
| ❌ Interpolation | AI does not compute in-between values |
| ❌ Live inference | AI does not run during playback/scrub |
| ❌ Non-deterministic output | AI results must be reproducible |

---

## 4. MOTION INTENT RESOLVER

### 4.1 Interface

```typescript
interface MotionIntentResolver {
  resolve(
    prompt: string,
    context: SceneContext,
    model: VisionModelId
  ): Promise<MotionIntentResult>
}

interface SceneContext {
  readonly composition: Composition
  readonly selectedLayers: readonly string[]
  readonly currentFrame: number
  readonly frameImage?: ImageData  // Current frame for VLM analysis
  readonly audioAnalysis?: AudioAnalysis
}

interface MotionIntentResult {
  readonly description: string  // Human-readable summary
  readonly confidence: number   // 0-1
  readonly cameraIntents?: readonly CameraMotionIntent[]
  readonly layerIntents?: readonly LayerMotionIntent[]
  readonly particleIntents?: readonly ParticleMotionIntent[]
  readonly splineIntents?: readonly SplineMotionIntent[]
}
```

### 4.2 Supported Vision Models

The system must be **model-agnostic**:

| Model | Type | Use Case |
|-------|------|----------|
| Qwen-VL / Qwen2-VL | Open source | Local inference |
| GPT-4V / GPT-4o | API | Cloud inference |
| Claude Vision | API | Cloud inference |
| LLaVA | Open source | Local inference |
| Rule-based | Fallback | When AI unavailable |

**Why model-agnostic matters**: AI outputs are normalized to structured intents immediately, so the downstream pipeline is model-independent.

---

## 5. INTENT TYPES

### 5.1 Camera Motion Intent

```typescript
interface CameraMotionIntent {
  readonly type: CameraMotionType
  readonly intensity: MotionIntensity
  readonly axis?: 'x' | 'y' | 'z' | 'all'
  readonly durationFrames?: number
  readonly suggestedEasing?: EasingType
  readonly noiseAmount?: number  // For handheld
  readonly orbitCenter?: Vec3    // For orbit
}

type CameraMotionType = 
  | 'dolly'      // Forward/backward
  | 'truck'      // Left/right
  | 'pedestal'   // Up/down
  | 'pan'        // Rotate horizontally
  | 'tilt'       // Rotate vertically
  | 'roll'       // Rotate around view axis
  | 'orbit'      // Around a point
  | 'drift'      // Slow random movement
  | 'handheld'   // Organic shake
  | 'crane'      // Vertical arc
  | 'zoom'       // FOV change

type MotionIntensity = 'very_subtle' | 'subtle' | 'medium' | 'strong' | 'dramatic'

type EasingType = 'linear' | 'easeIn' | 'easeOut' | 'easeInOut' | 'bounce' | 'elastic'
```

### 5.2 Layer Motion Intent

```typescript
interface LayerMotionIntent {
  readonly targetLayerId?: string  // Specific layer or all selected
  readonly motionType: LayerMotionType
  readonly amplitude: number       // Scale of motion
  readonly frequency?: number      // For oscillating motions
  readonly phase?: number          // Offset in cycle
  readonly axis?: 'x' | 'y' | 'z' | 'scale' | 'rotation'
}

type LayerMotionType = 
  | 'parallax'   // Depth-based offset
  | 'float'      // Gentle up/down
  | 'sway'       // Side-to-side
  | 'breathe'    // Scale oscillation
  | 'drift'      // Slow random
  | 'noise'      // Turbulent movement
  | 'pulse'      // Opacity oscillation
  | 'rotate'     // Continuous rotation
```

### 5.3 Particle Motion Intent

```typescript
interface ParticleMotionIntent {
  readonly behavior: ParticleBehavior
  readonly direction?: Vec3
  readonly intensity: number
  readonly spread?: number
  readonly lifetime?: number
  readonly colorScheme?: 'warm' | 'cool' | 'neutral' | 'custom'
}

type ParticleBehavior = 
  | 'flow'       // Directional stream
  | 'drift'      // Floating particles
  | 'spray'      // Fan-out emission
  | 'turbulence' // Chaotic movement
  | 'explosion'  // Burst from point
  | 'vortex'     // Spiral motion
  | 'rain'       // Downward fall
  | 'snow'       // Slow fall with drift
  | 'fireflies'  // Random glowing
  | 'dust'       // Ambient particles
```

### 5.4 Spline Motion Intent

```typescript
interface SplineMotionIntent {
  readonly usage: SplineUsage
  readonly smoothness: number      // 0-1, curve smoothness
  readonly complexity: number      // Number of control points
  readonly worldSpace: boolean     // World or local coords
  readonly suggestedPoints?: readonly Vec3[]  // AI-suggested path
}

type SplineUsage = 
  | 'camera_path'   // Camera follows spline
  | 'emitter_path'  // Particles emit along spline
  | 'text_path'     // Text follows spline
  | 'layer_path'    // Layer follows spline
```

---

## 6. INTENT TRANSLATOR

### 6.1 Interface

```typescript
interface MotionIntentTranslator {
  translateCameraIntent(
    intent: CameraMotionIntent,
    camera: CameraLayer,
    composition: Composition
  ): KeyframeBatch[]
  
  translateLayerIntent(
    intent: LayerMotionIntent,
    layer: Layer,
    composition: Composition
  ): KeyframeBatch[]
  
  translateParticleIntent(
    intent: ParticleMotionIntent,
    composition: Composition
  ): ParticleSystemConfig
  
  translateSplineIntent(
    intent: SplineMotionIntent,
    composition: Composition
  ): Spline3D
}

interface KeyframeBatch {
  readonly propertyPath: PropertyPath
  readonly keyframes: readonly Keyframe<unknown>[]
}
```

### 6.2 Camera Intent Translation

```typescript
function translateCameraIntent(
  intent: CameraMotionIntent,
  camera: CameraLayer,
  composition: Composition
): KeyframeBatch[] {
  const fps = composition.frameRate
  const duration = intent.durationFrames ?? fps * 5  // Default 5 seconds
  const distance = intensityToDistance(intent.intensity)
  
  switch (intent.type) {
    case 'dolly':
      return translateDolly(camera, distance, duration, intent)
    case 'drift':
      return translateDrift(camera, distance, duration, intent)
    case 'handheld':
      return translateHandheld(camera, distance, duration, intent)
    case 'orbit':
      return translateOrbit(camera, distance, duration, intent)
    // ... other types
  }
}

function translateDolly(
  camera: CameraLayer,
  distance: number,
  duration: number,
  intent: CameraMotionIntent
): KeyframeBatch[] {
  const currentPos = camera.position.defaultValue
  const direction = intent.axis === 'z' ? { x: 0, y: 0, z: 1 } : { x: 0, y: 0, z: 1 }
  
  const targetPos = {
    x: currentPos.x + direction.x * distance,
    y: currentPos.y + direction.y * distance,
    z: currentPos.z + direction.z * distance
  }
  
  return [{
    propertyPath: { layerId: camera.id, property: 'position' },
    keyframes: [
      {
        frame: 0,
        value: currentPos,
        interpolation: 'bezier',
        easing: getEasingConfig(intent.suggestedEasing ?? 'easeInOut')
      },
      {
        frame: duration,
        value: targetPos,
        interpolation: 'bezier'
      }
    ]
  }]
}

function intensityToDistance(intensity: MotionIntensity): number {
  switch (intensity) {
    case 'very_subtle': return 0.5
    case 'subtle': return 1.5
    case 'medium': return 4
    case 'strong': return 10
    case 'dramatic': return 25
    default: return 2
  }
}
```

---

## 7. DEPTH AND SEGMENTATION

### 7.1 One-Time AI Operations

These AI operations run **once** at setup time, not during evaluation:

| Operation | Output | When |
|-----------|--------|------|
| Depth estimation | Depth map asset | On image import or user request |
| Segmentation | Mask layers | On image import or user request |
| Subject detection | Layer bounds | On import |
| Scene analysis | Intent suggestions | On user prompt |

### 7.2 Depth Estimation

```typescript
interface DepthEstimationResult {
  readonly depthMap: Float32Array  // Normalized depth [0,1]
  readonly width: number
  readonly height: number
  readonly model: string  // Which model was used
  readonly confidence: number
}

async function estimateDepth(
  image: ImageData,
  model: DepthModelId = 'depth-anything-v2'
): Promise<DepthEstimationResult> {
  // Run AI model once
  const result = await depthModel.predict(image)
  
  // Store as asset, not computed per-frame
  return {
    depthMap: result.depth,
    width: image.width,
    height: image.height,
    model,
    confidence: result.confidence
  }
}
```

---

## 8. FULL WORKFLOW EXAMPLE

```
1. User imports image
   ↓
2. AI runs depth estimation (one-time)
   → Depth map stored as asset
   ↓
3. AI runs segmentation (one-time)
   → Mask layers created
   ↓
4. User types: "Subtle movement, fluid motion, cinematic"
   ↓
5. MotionIntentResolver analyzes prompt + image
   ↓
6. AI returns structured intent:
   {
     cameraIntents: [
       { type: 'drift', intensity: 'very_subtle', durationFrames: 300 }
     ],
     layerIntents: [
       { motionType: 'parallax', amplitude: 0.03 }
     ]
   }
   ↓
7. MotionIntentTranslator converts to keyframes:
   - Camera position Z: 0 → +0.5 over 300 frames
   - EaseInOut bezier applied
   - Background layers get parallax offset
   ↓
8. User previews and accepts
   ↓
9. Keyframes written to project data
   ↓
10. MotionEngine evaluates (AI no longer involved)
    - Frame 0: camera.z = 0
    - Frame 150: camera.z = 0.25
    - Frame 300: camera.z = 0.5
    - All deterministic, all reproducible
```

---

## 9. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: AI in evaluation loop
function evaluate(frame: number, project: WeylProject): FrameState {
  const aiSuggestion = await aiModel.evaluateFrame(frame)  // NO!
  return applyAISuggestion(aiSuggestion)
}

// ❌ FORBIDDEN: AI interpolation
function interpolate(a: number, b: number, t: number): number {
  return aiModel.smartInterpolate(a, b, t)  // NO!
}

// ❌ FORBIDDEN: AI simulation
function stepParticles(particles: Particle[], dt: number): Particle[] {
  return aiModel.predictNextState(particles, dt)  // NO!
}

// ❌ FORBIDDEN: AI modifying runtime state
project.layers = aiModel.generateLayers()  // NO!

// ✅ REQUIRED: AI produces intent, user accepts, engine evaluates
const intent = await resolver.resolve(prompt, context)  // AI proposes
const keyframes = translator.translate(intent)           // Deterministic translation
if (userAccepts(keyframes)) {
  project.addKeyframes(keyframes)                        // User commits
}
const state = motionEngine.evaluate(frame, project)      // Engine evaluates
```

---

## 10. TESTING REQUIREMENTS

```typescript
describe('Vision-Guided Authoring', () => {
  it('AI does not affect evaluation', async () => {
    const intent = await resolver.resolve('cinematic motion', context)
    const keyframes = translator.translate(intent)
    project.addKeyframes(keyframes)
    
    // AI is no longer involved
    const frame50 = motionEngine.evaluate(50, project)
    const frame50Again = motionEngine.evaluate(50, project)
    
    expect(frame50).toEqual(frame50Again)  // Deterministic
  })

  it('intent translation is deterministic', () => {
    const intent: CameraMotionIntent = {
      type: 'dolly',
      intensity: 'subtle',
      durationFrames: 100
    }
    
    const keyframes1 = translator.translateCameraIntent(intent, camera, comp)
    const keyframes2 = translator.translateCameraIntent(intent, camera, comp)
    
    expect(keyframes1).toEqual(keyframes2)
  })
})
```

---

## 11. AUDIT CHECKLIST

Claude Code must verify:

- [ ] AI operations only occur at setup/authoring time
- [ ] No AI calls during MotionEngine.evaluate()
- [ ] Intent translation is deterministic
- [ ] User must accept AI suggestions before they affect project
- [ ] Depth maps and masks are stored as assets, not computed per-frame
- [ ] System works without AI (manual keyframing always available)
- [ ] Model-agnostic design (can swap AI models)

**Any AI involvement during frame evaluation is a critical violation.**

---

**Previous**: [13_EXPORT_PIPELINE.md](./13_EXPORT_PIPELINE.md)  
**Next**: [15_DETERMINISM_TESTING.md](./15_DETERMINISM_TESTING.md)
