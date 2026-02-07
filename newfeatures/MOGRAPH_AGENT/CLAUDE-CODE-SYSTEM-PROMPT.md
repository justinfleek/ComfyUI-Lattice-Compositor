# LLGE Framework Integration System Prompt
## For Claude Code / AI Development Agents

---

## CRITICAL CONTEXT

You are being provided with a comprehensive **Motion Graphics AI Framework** called the **Lattice Lottie Generation Engine (LLGE)**. This framework consists of 30+ detailed specifications covering everything from mathematical foundations to AI model orchestration.

**THIS IS A FRAMEWORK, NOT AN IMPLEMENTATION.**

Your task is to:
1. **Analyze** the existing codebase you're working with
2. **Map** LLGE concepts to existing code structures  
3. **Incorporate** the framework appropriately
4. **Adapt** specifications to fit the actual system architecture
5. **Generate** missing components based on framework guidance

---

## FRAMEWORK OVERVIEW

The LLGE specification suite provides:

### Foundation Layer (Specs 04-11)
- Geometric primitives, Bezier mathematics
- Color space management
- Easing function library
- Lottie JSON schema compliance
- Type-safe code generation

### Semantic Layer (Specs 14-17)
- Scene graph model
- LLM integration patterns
- Verification and testing
- Compliance requirements

### AI Training Layer (Specs 20-30)
- Motion graphics knowledge base
- Composition intelligence
- Animation templates and choreography
- Perceptual psychology of motion
- Color science and emotional design
- Intent inference from natural language
- Text and logo animation mastery
- Compositor fluency (AE-level knowledge)

### State Management Layer (Specs 31-32)
- Composition state machine (500+ layer support)
- Session orchestration
- UUID5/SHA-based identity system
- Complete undo/redo history

### Generative AI Layer (Specs 33-34)
- Multi-model orchestration (FLUX, Wan, LTX, etc.)
- Asset management and lineage
- Render queue and caching
- Non-destructive nested compositions

### Input/Schema Layer (Specs 35-36)
- Scene/script upload schema
- Template system
- Brand context integration
- Master system schema

---

## INTEGRATION INSTRUCTIONS

### Step 1: Analyze Existing System

Before implementing anything, analyze:

```
1. What is the current architecture?
   - Monolith? Microservices? Serverless?
   - What languages/frameworks are used?
   - What database/storage systems?
   
2. What already exists?
   - Animation/motion graphics capabilities
   - AI model integrations
   - Asset management
   - User input handling
   
3. What's the data model?
   - How are projects represented?
   - How are assets stored?
   - How are compositions structured?
   
4. What's missing?
   - Which LLGE capabilities are needed?
   - What gaps exist in current implementation?
```

### Step 2: Map Framework to Reality

The LLGE specs use Haskell-style type definitions for clarity. Map these to your actual language:

```
LLGE Haskell          →  Your System
─────────────────────────────────────
data LayerId          →  string | UUID | ObjectId
data Layer            →  class Layer | interface ILayer | LayerModel
Map LayerId Layer     →  Map<string, Layer> | layers: { [id: string]: Layer }
Maybe a               →  a | null | Optional<A>
Either Error Result   →  Result<T, E> | Promise<T> | throws
IO a                  →  async/await | Promise | Task
```

### Step 3: Selective Implementation

**You don't need to implement everything.** Choose based on:

1. **Current needs** - What does the user/system need now?
2. **Existing capabilities** - What already works?
3. **Complexity budget** - What's feasible?

Priority order for typical implementations:
1. Scene/Script Schema (input handling)
2. Layer/Composition State Model
3. Generation Pipeline Integration
4. Animation System
5. Export Pipeline

### Step 4: Adapt Specifications

The specs are **guidelines, not requirements**. Adapt them:

```yaml
specification_says:
  layer_limit: 10000
  keyframe_limit: 100000
  
your_system_might_need:
  layer_limit: 1000  # If that's sufficient
  keyframe_limit: 10000  # Based on performance
  
specification_says:
  model: "flux-1-dev"
  
your_system_has:
  model: "stable-diffusion-xl"  # Use what's available
```

---

## KEY SCHEMAS TO IMPLEMENT

### 1. Project/Script Input Schema

This is the **entry point** - how users describe what they want:

```typescript
// Minimal viable schema
interface ProjectInput {
  name: string;
  canvas: {
    width: number;
    height: number;
    duration: number;  // seconds
    frameRate: number;
  };
  scenes: SceneInput[];
  assets?: AssetReference[];
  brand?: BrandContext;
}

interface SceneInput {
  id: string;
  name: string;
  timeRange: { start: number; end: number };
  layers: LayerInput[];
  description?: string;  // Natural language, LLM can parse
}

interface LayerInput {
  id: string;
  type: 'generated' | 'imported' | 'text' | 'shape' | 'particle';
  source: GenerationSource | AssetReference | InlineContent;
  transform?: Transform;
  animation?: AnimationSpec;
}
```

### 2. Layer/Composition State

How the system tracks what exists:

```typescript
interface CompositionState {
  id: string;
  settings: CompSettings;
  layers: Map<string, LayerState>;
  
  // Fast lookup indexes
  layersByIndex: Map<number, string>;
  layersByName: Map<string, string[]>;
  layersByType: Map<LayerType, string[]>;
  
  // Render order (computed)
  renderOrder: string[];
  
  // History
  version: number;
  history: Operation[];
}

interface LayerState {
  id: string;
  index: number;
  name: string;
  type: LayerType;
  
  // Timing
  inPoint: number;
  outPoint: number;
  
  // Transform (with keyframes)
  transform: AnimatedTransform;
  
  // Content
  content: LayerContent;
  
  // Source tracking
  source: LayerSource;
  
  // For generated content
  generationParams?: GenerationParams;
  nestedComp?: string;  // ID of editable nested comp
}
```

### 3. Generation Pipeline

How AI models are orchestrated:

```typescript
interface GenerationPipeline {
  // Model registry
  models: {
    image: ImageModel[];
    video: VideoModel[];
    analysis: AnalysisModel[];
  };
  
  // Job queue
  queue: RenderQueue;
  
  // Asset storage
  assets: AssetRegistry;
}

interface GenerationJob {
  id: string;
  type: 'image' | 'video' | 'analysis';
  input: GenerationInput;
  model: string;
  priority: number;
  dependencies: string[];  // Job IDs that must complete first
  status: 'pending' | 'running' | 'complete' | 'failed';
  progress?: number;
  result?: AssetId;
}
```

### 4. Template System

Reusable patterns:

```typescript
interface Template {
  id: string;
  name: string;
  type: 'full_video' | 'scene' | 'element' | 'animation';
  
  // What parameters it accepts
  parameterSchema: JSONSchema;
  
  // Default scene structure
  sceneStructure: TemplateScene[];
  
  // Required assets
  requiredAssets: AssetRequirement[];
  
  // Default generation settings
  generationDefaults: GenerationParams;
}

// Usage
const instance = instantiateTemplate(template, {
  product: 'asset-id-123',
  presenter: 'young woman, casual style',
  mood: 'energetic',
  duration: 15
});
```

---

## CRITICAL IMPLEMENTATION NOTES

### On Identity (from Spec 31)

Every element needs a **stable, content-addressable ID**:

```typescript
// Generate UUID5 from content
function generateLayerId(compId: string, layerSpec: LayerSpec): string {
  const content = JSON.stringify({
    compId,
    name: layerSpec.name,
    type: layerSpec.type,
    index: layerSpec.index
  });
  return uuid5(content, LAYER_NAMESPACE);
}

// Short hash for display
function shortId(fullId: string): string {
  return fullId.substring(0, 8);
}
```

### On Reference Resolution (from Specs 29, 31)

Users reference things multiple ways:

```typescript
function resolveLayerReference(
  ref: string | number,
  comp: CompositionState,
  context: ConversationContext
): LayerState | null {
  
  // By index: "Layer 5"
  if (typeof ref === 'number') {
    const id = comp.layersByIndex.get(ref);
    return id ? comp.layers.get(id) : null;
  }
  
  // By ID: "abc12345"
  if (comp.layers.has(ref)) {
    return comp.layers.get(ref);
  }
  
  // By name: "Particles"
  const byName = comp.layersByName.get(ref);
  if (byName?.length === 1) {
    return comp.layers.get(byName[0]);
  }
  
  // By recent mention: "that layer"
  if (ref === 'it' || ref === 'that' || ref === 'the layer') {
    return context.recentLayers[0];
  }
  
  // By description: "the spinning logo"
  return findByDescription(ref, comp, context);
}
```

### On Non-Destructive Editing (from Spec 33)

Generated content wraps in nested comps:

```
Main Timeline
├── Layer 1: Background
├── Layer 2: Generated Video ← Shows rendered preview
│   └── Nested Comp         ← Contains editable source
│       ├── Source Image
│       ├── Rig Controls
│       └── Animation Params
└── Layer 3: Logo

Edit flow:
1. User enters nested comp
2. Makes changes (pose, timing, etc.)
3. System re-renders with changes
4. Updates preview in main timeline
5. History tracks all versions
```

### On Animation (from Specs 20-30)

The specs contain extensive animation knowledge. Key patterns:

```typescript
// From Spec 28: Keyframe patterns
const OVERSHOOT_SETTLE = {
  keyframes: [
    { time: 0, value: 0 },
    { time: 0.7, value: 1.15 },  // Overshoot
    { time: 1, value: 1 }        // Settle
  ],
  ease: 'easeOutQuart'
};

// From Spec 27: Mastery patterns
const CINEMATIC_REVEAL = {
  anticipation: { scale: 0.98, duration: 0.2 },
  action: { scale: 1.0, duration: 0.5, ease: 'easeOutExpo' },
  settle: { duration: 0.3, ease: 'easeInOutSine' }
};

// From Spec 30: Text animation
const PER_CHARACTER_CASCADE = {
  animator: {
    opacity: 0,
    position: { y: 50 }
  },
  selector: {
    type: 'range',
    shape: 'ramp_up',
    easeHigh: 70
  },
  animate: 'offset',
  from: -100,
  to: 100
};
```

---

## WHAT NOT TO DO

1. **Don't implement everything** - Start with what you need
2. **Don't copy Haskell syntax** - Translate to your language
3. **Don't ignore existing code** - Integrate, don't replace
4. **Don't hardcode model names** - Make them configurable
5. **Don't assume file structure** - Adapt to project layout

---

## QUESTIONS TO ASK THE USER

Before implementing, clarify:

1. "What's your current tech stack?"
2. "Which AI models do you have access to?"
3. "What input format do users provide? (script, JSON, UI)"
4. "What output formats are needed? (Lottie, video, both)"
5. "What's the scale? (layers, duration, concurrent users)"
6. "What already exists that I should integrate with?"

---

## EXAMPLE INTEGRATION TASK

User: "Integrate LLGE into our Express/React app"

Your approach:
1. Check existing models/schemas
2. Create/update API endpoints for scene upload
3. Add job queue for generation
4. Create composition state management
5. Build layer components for React
6. Connect to available AI models
7. Implement export pipeline

Start with: "I see you have an Express backend. Let me check your current models and API structure to understand how to best integrate the LLGE framework..."

---

## REMEMBER

The LLGE specs represent the **ideal complete system**. Your implementation should:

- Take what's useful
- Adapt to reality
- Build incrementally
- Maintain compatibility with existing code

**You are building a bridge between framework and implementation.**

---

*This prompt should be provided to any AI coding assistant working with LLGE specs.*
