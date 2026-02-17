# Service API Reference

> Last Updated: December 2025

Reference documentation for Lattice Compositor's 181 service files.

---

## Service Categories

| Category | Files | Purpose |
|----------|-------|---------|
| Animation | 15 | Keyframes, easing, expressions |
| Audio | 12 | Analysis, reactivity, stems |
| Camera | 8 | 3D camera, trajectories |
| Effects | 20 | Effect renderers |
| Export | 10 | Video, matte, trajectory export |
| Layers | 26 | Layer type implementations |
| Particles | 8 | Particle simulation |
| Security | 6 | Validation, sanitization |
| AI | 8 | Agent tools, prompts |
| Utility | 68 | Helpers, converters |

---

## Animation Services

### interpolation.ts
Keyframe interpolation engine.

```typescript
function interpolate(
  keyframes: Keyframe[],
  frame: number,
  property: string
): number | number[]
```

### easing.ts
35 easing functions for animation curves.

```typescript
type EasingFunction = (t: number) => number;

const easings: Record<string, EasingFunction> = {
  linear: (t) => t,
  easeInQuad: (t) => t * t,
  easeOutQuad: (t) => t * (2 - t),
  easeInOutQuad: (t) => t < 0.5 ? 2 * t * t : -1 + (4 - 2 * t) * t,
  // ... 31 more
};
```

### expressions.ts
Expression language parser and evaluator.

```typescript
function evaluateExpression(
  expression: string,
  context: ExpressionContext
): number | number[]

// Context provides:
// - time: current time in seconds
// - frame: current frame number
// - value: current property value
// - wiggle(freq, amp): procedural noise
// - repeatAfter(duration): loop expression
```

### propertyDriver.ts
PropertyLink system for connecting properties.

```typescript
function createPropertyLink(
  sourceLayer: string,
  sourceProperty: string,
  targetLayer: string,
  targetProperty: string,
  options?: { offset?: number; multiplier?: number }
): PropertyLink
```

---

## Audio Services

### fftAnalyzer.ts
Real-time FFT analysis of audio.

```typescript
function analyzeAudio(
  audioBuffer: AudioBuffer,
  frame: number,
  fps: number
): FrequencyData

interface FrequencyData {
  bass: number;      // 20-250 Hz
  mid: number;       // 250-4000 Hz
  high: number;      // 4000-20000 Hz
  overall: number;   // Average amplitude
}
```

### beatDetection.ts
Automatic beat detection.

```typescript
function detectBeats(
  audioBuffer: AudioBuffer
): Beat[]

interface Beat {
  time: number;
  strength: number;
  type: 'kick' | 'snare' | 'hihat';
}
```

### stemSeparation.ts
Audio stem separation via Demucs.

```typescript
async function separateStems(
  audioFile: File
): Promise<StemResult>

interface StemResult {
  vocals: AudioBuffer;
  drums: AudioBuffer;
  bass: AudioBuffer;
  other: AudioBuffer;
}
```

---

## Camera Services

### cameraPresets.ts
22 camera animation presets.

```typescript
type CameraPreset =
  | 'orbit'
  | 'dolly'
  | 'crane'
  | 'reveal'
  | 'spiral'
  | 'push'
  | 'pull'
  | 'pan'
  | 'tilt'
  | 'roll'
  // ... 12 more

function applyCameraPreset(
  camera: Camera,
  preset: CameraPreset,
  duration: number
): Keyframe[]
```

### trajectoryExport.ts
Export camera paths for AI video models.

```typescript
function exportMotionCtrl(
  camera: Camera,
  frameCount: number
): MotionCtrlData

function exportCameraCtrl(
  camera: Camera,
  frameCount: number
): CameraCtrlJSON

function exportWanTrajectory(
  points: Point[],
  frameCount: number
): WanTrajectoryData
```

---

## Effect Services

### blurRenderer.ts
Blur effect implementations.

```typescript
function renderGaussianBlur(
  canvas: HTMLCanvasElement,
  radius: number,
  quality: number
): void

function renderDirectionalBlur(
  canvas: HTMLCanvasElement,
  angle: number,
  distance: number
): void
```

### colorRenderer.ts
Color correction effects.

```typescript
function renderLevels(
  canvas: HTMLCanvasElement,
  inputBlack: number,
  inputWhite: number,
  gamma: number,
  outputBlack: number,
  outputWhite: number
): void

function renderHueSaturation(
  canvas: HTMLCanvasElement,
  hue: number,
  saturation: number,
  lightness: number
): void
```

---

## Export Services

### videoExport.ts
Video encoding and export.

```typescript
async function exportVideo(
  project: LatticeProject,
  options: ExportOptions
): Promise<Blob>

interface ExportOptions {
  format: 'webm' | 'mp4';
  quality: number;
  width: number;
  height: number;
  frameRate: number;
}
```

### matteExport.ts
Matte sequence export for AI models.

```typescript
async function exportMatteSequence(
  project: LatticeProject,
  layers: string[],
  outputDir: string
): Promise<void>
```

---

## Security Services

### sesEvaluator.ts
Secure expression evaluation using SES.

```typescript
function createSandbox(): Compartment

function evaluateInSandbox(
  code: string,
  context: Record<string, unknown>
): unknown
```

### urlValidator.ts
URL validation and sanitization.

```typescript
function validateUrl(url: string): ValidationResult
function sanitizeUrl(url: string): string
function isAllowedProtocol(url: string): boolean
```

### jsonSanitizer.ts
JSON validation and sanitization.

```typescript
function sanitizeJSON(data: unknown): unknown
function validateProjectStructure(
  project: unknown,
  context: string
): void  // throws ValidationError
```

---

## AI Services

### agentTools.ts
30+ tool definitions for AI agent.

```typescript
const tools: AgentTool[] = [
  { name: 'createLayer', handler: createLayerTool },
  { name: 'addKeyframe', handler: addKeyframeTool },
  { name: 'applyEffect', handler: applyEffectTool },
  { name: 'setProperty', handler: setPropertyTool },
  // ... 26 more
];
```

### stateSerializer.ts
Serialize project state for AI context.

```typescript
function serializeForAgent(
  project: LatticeProject
): AgentContext

interface AgentContext {
  compositions: CompositionSummary[];
  selectedLayers: LayerSummary[];
  currentFrame: number;
  availableTools: string[];
}
```

---

## Particle Services

### cpuSimulation.ts
Deterministic particle simulation.

```typescript
function simulateParticles(
  emitter: ParticleEmitter,
  frame: number,
  checkpoint?: ParticleCheckpoint
): ParticleState

function createCheckpoint(
  state: ParticleState,
  frame: number
): ParticleCheckpoint
```

### particlePresets.ts
24 built-in particle presets.

```typescript
type ParticlePreset =
  | 'fire'
  | 'smoke'
  | 'snow'
  | 'rain'
  | 'confetti'
  | 'magic'
  | 'sparks'
  | 'bubbles'
  // ... 16 more

function applyPreset(
  emitter: ParticleEmitter,
  preset: ParticlePreset
): void
```

---

## Usage Examples

### Adding a keyframe
```typescript
import { addKeyframe } from '@/services/animation/keyframes';

addKeyframe(layer, 'position.x', 0, 100);   // Frame 0: x = 100
addKeyframe(layer, 'position.x', 30, 500);  // Frame 30: x = 500
```

### Applying an effect
```typescript
import { applyEffect } from '@/services/effects';

applyEffect(layer, {
  type: 'gaussianBlur',
  params: { radius: 10, quality: 3 }
});
```

### Exporting for AI
```typescript
import { exportWanTrajectory } from '@/services/export/trajectoryExport';

const trajectory = exportWanTrajectory(points, 81);
downloadJSON(trajectory, 'trajectory.json');
```
