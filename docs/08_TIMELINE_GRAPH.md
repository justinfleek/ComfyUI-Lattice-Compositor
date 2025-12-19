# WEYL COMPOSITOR — TIMELINE & GRAPH EDITOR

**Document ID**: 08_TIMELINE_GRAPH  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> The Timeline and Graph Editor are **editors of data**, not **evaluators of motion**.
> They select frames and edit keyframes. They never interpolate or evaluate.

---

## 1. CORE PHILOSOPHY

The Timeline and Graph Editor are conceptually equivalent to:

- **After Effects** Timeline / Graph Editor
- **Nuke** Dope Sheet / Curve Editor
- **TouchDesigner** parameter editors

They are **NOT**:

- ❌ Simulation drivers
- ❌ Animation engines
- ❌ Time authorities
- ❌ Interpolation systems

---

## 2. SINGLE SOURCE OF TRUTH

> **The Timeline does not know what anything "looks like."**

Only **MotionEngine** answers:
> "What is the evaluated state of the project at frame N?"

The Timeline merely **selects which frame** to ask about.

```typescript
// The relationship between Timeline and MotionEngine
interface TimelineContract {
  // Timeline controls THIS (UI state only):
  currentFrame: number
  isPlaying: boolean
  workAreaStart: number
  workAreaEnd: number
  
  // Timeline NEVER touches evaluation
  // MotionEngine is the ONLY evaluator
}

interface MotionEngineContract {
  // MotionEngine controls THIS:
  evaluate(frame: number, project: WeylProject): FrameState
  
  // MotionEngine NEVER touches:
  // - UI state
  // - currentFrame
  // - playback controls
}
```

---

## 3. TIMELINE RESPONSIBILITIES

### 3.1 Timeline MAY (Data Operations Only)

| Action | Type | Description |
|--------|------|-------------|
| Set `currentFrame` | UI state | Which frame is displayed |
| Start/stop playback | UI state | Playback toggle |
| Create keyframes | Data edit | Add keyframe to property |
| Move keyframes | Data edit | Change keyframe time/value |
| Delete keyframes | Data edit | Remove keyframe |
| Reorder layers | Data edit | Change layer stacking |
| Toggle visibility | UI state | Eye icon in UI |
| Define work area | UI state | Render range selection |
| Display waveforms | UI state | Pre-computed audio visualization |

### 3.2 Timeline MUST NOT (Evaluation Violations)

| Forbidden Action | Why It's Wrong |
|------------------|----------------|
| Interpolate values | MotionEngine's job |
| Advance simulations | Creates playback dependency |
| Call `step()`, `tick()`, `update()` | Implies incremental state |
| Cache evaluated values | MotionEngine may return different results |
| Mutate engine state | Engine state is derived, not stored |
| Compute property values | Only MotionEngine interpolates |

**Audit Instruction**: Claude Code must search for any Timeline code that evaluates property values directly. Such code must be deleted.

---

## 4. PLAYBACK MODEL

### 4.1 Playback Is UI, Not Simulation

Playback is a **UI convenience**, not a simulation loop.

| Aspect | Description |
|--------|-------------|
| What it does | Advances `currentFrame` over time |
| What it triggers | Re-evaluation via MotionEngine |
| What it NEVER does | Accumulate time, advance state, depend on prior frames |

### 4.2 Correct Playback Flow

```
requestAnimationFrame
       ↓
UI updates currentFrame (based on elapsed wall-time)
       ↓
MotionEngine.evaluate(currentFrame, project)
       ↓
RenderEngine.applyFrameState(frameState)
       ↓
Display updated
```

**Playback speed affects how fast frames are requested, not how frames are evaluated.**

### 4.3 Playback Implementation

```typescript
class PlaybackController {
  private animationFrameId: number | null = null
  private lastTimestamp: number = 0
  private currentFrame: number = 0
  
  // Configuration
  readonly frameRate: number = 30
  readonly startFrame: number = 0
  readonly endFrame: number = 300
  readonly loop: boolean = true
  
  play(): void {
    this.lastTimestamp = performance.now()
    this.tick()
  }
  
  pause(): void {
    if (this.animationFrameId !== null) {
      cancelAnimationFrame(this.animationFrameId)
      this.animationFrameId = null
    }
  }
  
  private tick = (): void => {
    const now = performance.now()
    const elapsedMs = now - this.lastTimestamp
    const framesElapsed = (elapsedMs / 1000) * this.frameRate
    
    if (framesElapsed >= 1) {
      // Advance UI frame counter (NOT engine state)
      this.currentFrame = Math.floor(this.currentFrame + framesElapsed)
      
      // Handle loop/stop
      if (this.currentFrame > this.endFrame) {
        this.currentFrame = this.loop 
          ? this.startFrame 
          : this.endFrame
        if (!this.loop) {
          this.pause()
          return
        }
      }
      
      this.lastTimestamp = now
      
      // Request new evaluation (does NOT "advance" anything)
      this.onFrameChange(this.currentFrame)
    }
    
    this.animationFrameId = requestAnimationFrame(this.tick)
  }
  
  private onFrameChange(frame: number): void {
    // MotionEngine evaluates the frame FROM SCRATCH
    // No dependency on prior evaluation
    const frameState = motionEngine.evaluate(frame, this.project)
    renderEngine.applyFrameState(frameState)
  }
  
  // Scrubbing uses the exact same path
  scrubTo(frame: number): void {
    this.currentFrame = frame
    this.onFrameChange(frame)
  }
}
```

---

## 5. SCRUBBING RULE (CRITICAL)

> Scrubbing to the same frame must **always** produce identical output.

### 5.1 Required Behavior

| Requirement | Description |
|-------------|-------------|
| Order independence | Scrub order does not affect result |
| No prior dependency | No system may rely on prior frame evaluation |
| Complete replacement | Entire evaluated state is replaced on each scrub |

### 5.2 Scrubbing Test

```typescript
// This test MUST pass
describe('Scrubbing Determinism', () => {
  it('produces identical output regardless of scrub path', () => {
    const project = loadTestProject()
    
    // Path A: Direct
    const resultA = motionEngine.evaluate(300, project)
    
    // Path B: Through other frames
    motionEngine.evaluate(0, project)
    motionEngine.evaluate(500, project)
    motionEngine.evaluate(10, project)
    const resultB = motionEngine.evaluate(300, project)
    
    // Results MUST be identical
    expect(resultA).toEqual(resultB)
    expect(hashFrameState(resultA)).toBe(hashFrameState(resultB))
  })
})
```

### 5.3 Failure Indicators

If any of these occur, the system is broken:

| Symptom | Cause |
|---------|-------|
| ❌ Scrubbing causes particles to drift | Particles depend on prior evaluation |
| ❌ Forward vs backward scrub differs | Incremental state accumulation |
| ❌ Audio-reactive values change after scrubs | Audio not pre-computed |
| ❌ Multiple scrubs to same frame differ | Hidden state mutation |

---

## 6. GRAPH EDITOR RESPONSIBILITIES

### 6.1 Graph Editor MAY (Data Operations Only)

| Action | Type | Description |
|--------|------|-------------|
| Display curves | UI | Visualize keyframe data |
| Edit keyframe values | Data edit | Change Y value |
| Edit keyframe time | Data edit | Change X position |
| Edit interpolation type | Data edit | Linear, bezier, hold |
| Edit easing parameters | Data edit | Bezier handles |
| Copy/paste keyframes | Data edit | Duplicate data |

### 6.2 Graph Editor MUST NOT

| Forbidden Action | Why It's Wrong |
|------------------|----------------|
| Sample audio | Audio analysis is pre-computed |
| Interpolate values | MotionEngine's job |
| Apply easing at runtime | Easing is evaluation, not editing |
| Depend on playback order | Must be order-independent |
| Store evaluated values | Only MotionEngine evaluates |

---

## 7. INTERPOLATION FLOW (MANDATORY PATH)

```
┌────────────────────────────────────────────────────────────────┐
│                     Graph Editor                               │
│  - Displays keyframes                                          │
│  - User edits keyframe data                                    │
└────────────────────────────────────────────────────────────────┘
                              │
                              │ (Data change only)
                              ▼
┌────────────────────────────────────────────────────────────────┐
│                   AnimatableProperty                           │
│  - Updated keyframe data                                       │
│  - No interpolation yet                                        │
└────────────────────────────────────────────────────────────────┘
                              │
                              │ (When frame is requested)
                              ▼
┌────────────────────────────────────────────────────────────────┐
│              MotionEngine.evaluate(frame)                      │
│  - Calls interpolateProperty(property, frame)                  │
│  - Applies easing functions                                    │
│  - Returns evaluated value                                     │
└────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌────────────────────────────────────────────────────────────────┐
│                    Evaluated Value                             │
│  - Used by RenderEngine                                        │
│  - Exported to conditioning buffers                            │
└────────────────────────────────────────────────────────────────┘
```

**No shortcuts. No alternate paths. All interpolation goes through MotionEngine.**

---

## 8. DATA MODELS

### 8.1 Timeline State (UI Only)

```typescript
interface TimelineState {
  // Current playhead position
  readonly currentFrame: number
  
  // Playback state
  readonly isPlaying: boolean
  readonly playbackSpeed: number  // 1.0 = normal, 0.5 = half, 2.0 = double
  
  // Work area (render range)
  readonly workAreaStart: number
  readonly workAreaEnd: number
  
  // Viewport state
  readonly visibleFrameRange: [number, number]
  readonly zoom: number
  readonly scrollPosition: number
  
  // Selection state
  readonly selectedLayerIds: readonly string[]
  readonly selectedKeyframes: readonly KeyframeSelection[]
}

interface KeyframeSelection {
  readonly layerId: string
  readonly propertyPath: string
  readonly frame: number
}
```

### 8.2 Keyframe Data (Project Data)

```typescript
interface Keyframe<T> {
  readonly frame: number
  readonly value: T
  readonly interpolation: InterpolationType
  readonly easing?: EasingConfig
}

type InterpolationType = 'linear' | 'bezier' | 'hold'

interface EasingConfig {
  // Bezier handles for curve control
  readonly inHandle: Vec2   // x: time influence, y: value influence
  readonly outHandle: Vec2
}
```

### 8.3 Graph Editor State (UI Only)

```typescript
interface GraphEditorState {
  // Which properties are visible
  readonly visibleProperties: readonly PropertyPath[]
  
  // Viewport
  readonly valueRange: [number, number]  // Y axis
  readonly frameRange: [number, number]  // X axis
  readonly zoom: Vec2
  
  // Selection
  readonly selectedKeyframes: readonly KeyframeSelection[]
  readonly selectedHandles: readonly HandleSelection[]
}

interface HandleSelection {
  readonly keyframe: KeyframeSelection
  readonly handle: 'in' | 'out'
}
```

---

## 9. UI ACTIONS AND DATA FLOW

### 9.1 Scrub Action

```typescript
// User drags playhead to frame 150
function handleScrub(frame: number): void {
  // 1. Update UI state (Timeline only)
  timelineStore.setCurrentFrame(frame)
  
  // 2. Request evaluation (MotionEngine)
  const frameState = motionEngine.evaluate(frame, project)
  
  // 3. Apply to render (RenderEngine)
  renderEngine.applyFrameState(frameState)
}
```

### 9.2 Keyframe Edit Action

```typescript
// User drags keyframe to new position
function handleKeyframeMove(
  layerId: string,
  propertyPath: string,
  oldFrame: number,
  newFrame: number,
  newValue: number
): void {
  // 1. Update project data (immutable update)
  const updatedProject = updateKeyframe(project, {
    layerId,
    propertyPath,
    oldFrame,
    newFrame,
    value: newValue
  })
  
  // 2. Save to project store
  projectStore.setProject(updatedProject)
  
  // 3. Re-evaluate current frame (if needed)
  const frameState = motionEngine.evaluate(
    timelineStore.currentFrame, 
    updatedProject
  )
  renderEngine.applyFrameState(frameState)
}
```

### 9.3 Play Action

```typescript
function handlePlay(): void {
  // 1. Update UI state
  timelineStore.setIsPlaying(true)
  
  // 2. Start playback loop (UI-driven)
  playbackController.play()
  
  // Playback loop internally:
  // - Advances currentFrame over time
  // - Calls motionEngine.evaluate() for each frame
  // - Never accumulates state
}
```

---

## 10. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Timeline evaluating values
timeline.setFrame(n)
const value = interpolate(property, n)  // Timeline doing interpolation!

// ❌ FORBIDDEN: Graph Editor sampling audio
graphEditor.displayAudioCurve()
const amplitude = audioContext.getByteFrequencyData()  // Runtime audio!

// ❌ FORBIDDEN: Playback advancing simulation
playback.tick()
simulation.step(dt)  // Incremental advancement!
particle.update()    // State mutation!

// ❌ FORBIDDEN: UI storing evaluated values
uiStore.evaluatedPosition = interpolate(position, frame)  // Cached evaluation!

// ❌ FORBIDDEN: Incremental time
this.currentTime += deltaTime  // Accumulated time!
engine.update(dt)              // Delta-based update!

// ✅ REQUIRED: Clean separation
timeline.setCurrentFrame(n)                              // UI state only
const frameState = motionEngine.evaluate(n, project)     // Engine evaluates
renderEngine.applyFrameState(frameState)                 // Render applies
```

---

## 11. WAVEFORM DISPLAY

### 11.1 Waveform Is Pre-Computed

Audio waveforms displayed in the Timeline are **pre-computed** during audio import, not sampled at runtime.

```typescript
interface AudioAsset extends Asset {
  readonly type: 'audio'
  readonly duration: number
  readonly sampleRate: number
  
  // Pre-computed visualization data
  readonly waveform: Float32Array  // Normalized amplitude per display unit
  readonly peaks: Float32Array     // Peak values for zoomed-out view
}
```

### 11.2 Waveform Never Affects Evaluation

The waveform is purely visual. Audio-reactive properties use `AudioAnalysis` (see [10_AUDIO_REACTIVITY.md](./10_AUDIO_REACTIVITY.md)), which is also pre-computed.

---

## 12. TESTING REQUIREMENTS

```typescript
describe('Timeline', () => {
  it('does not interpolate values', () => {
    const spy = vi.spyOn(motionEngine, 'evaluate')
    
    // Timeline action
    timeline.setCurrentFrame(100)
    
    // Timeline should NOT call evaluate directly
    // The view layer calls evaluate after observing the state change
    expect(spy).not.toHaveBeenCalled()
  })
  
  it('scrubbing is order-independent', () => {
    // See Section 5.2
  })
})

describe('Graph Editor', () => {
  it('only edits keyframe data', () => {
    const before = project.layers[0].transform.position.keyframes
    
    graphEditor.moveKeyframe({
      layerId: 'layer-0',
      propertyPath: 'transform.position',
      oldFrame: 0,
      newFrame: 10,
      value: { x: 100, y: 200, z: 0 }
    })
    
    const after = project.layers[0].transform.position.keyframes
    
    // Data changed
    expect(after).not.toEqual(before)
    
    // No evaluation occurred
    expect(motionEngine.evaluate).not.toHaveBeenCalled()
  })
})

describe('Playback', () => {
  it('does not accumulate state', () => {
    playbackController.play()
    
    // Simulate several frames
    for (let i = 0; i < 100; i++) {
      vi.advanceTimersByTime(33)  // ~30fps
    }
    
    playbackController.pause()
    
    // Verify each evaluate call was independent
    const evaluateCalls = motionEngine.evaluate.mock.calls
    for (const [frame, proj] of evaluateCalls) {
      // Each call should produce same result if called again
      const result1 = motionEngine.evaluate(frame, proj)
      const result2 = motionEngine.evaluate(frame, proj)
      expect(result1).toEqual(result2)
    }
  })
})
```

---

## 13. AUDIT CHECKLIST

Claude Code must verify:

- [ ] Timeline only modifies UI state (`currentFrame`, `isPlaying`)
- [ ] Timeline never calls interpolation functions
- [ ] Graph Editor only edits keyframe data
- [ ] Graph Editor never evaluates property values
- [ ] Playback uses `requestAnimationFrame`, not `setInterval` with accumulated time
- [ ] Playback calls `motionEngine.evaluate()` for each frame independently
- [ ] No `step()`, `tick()`, or `update()` methods on engine systems
- [ ] No evaluated values stored in UI state
- [ ] Audio waveforms are pre-computed, not runtime-sampled
- [ ] Scrubbing to same frame always produces identical results

**Any Timeline or Graph Editor code that evaluates properties is a critical violation.**

---

**Previous**: [07_TEXT_SHAPE.md](./07_TEXT_SHAPE.md)  
**Next**: [09_PICKWHIP_DEPENDENCIES.md](./09_PICKWHIP_DEPENDENCIES.md)
