━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                            // universal // design // language
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "Any sufficiently advanced design system is indistinguishable from
    a programming language."

                                                              — corollary

# THE UNIVERSAL DESIGN LANGUAGE

## Key References

Before diving in, familiarize yourself with these foundational documents:

| Document | Purpose |
|----------|---------|
| **[SHOW_DEBUG_CONVENTION.md](./SHOW_DEBUG_CONVENTION.md)** | `Show` as structured debugging infrastructure, not pretty-printing |
| **[SCHEMA.md](./SCHEMA.md)** | Complete 12-pillar Schema enumeration |
| **[design-ontology.md](./design-ontology.md)** | Atom → Molecule → Compound architecture |
| **[PROOFS.md](./PROOFS.md)** | Lean4 verification strategy |

## Purpose of This Document

This document defines what it means for Hydrogen to be a **universal design
language** — a Schema capable of expressing ANY visual output that can appear
on a screen.

Not "most UIs." Not "web applications." **Anything.**

- Ableton's waveform editor
- After Effects' compositing timeline
- Cinema 4D's 3D viewport
- Photoshop's layer stack
- Figma's vector canvas
- TouchDesigner's node graph
- Hospital dashboards with real-time vitals
- E-commerce with infinite scroll
- Video games with physics simulations
- Scientific visualization with millions of data points

If it can be rendered to pixels, Hydrogen's Schema must be able to describe it.

This is the bar. Anything less is not universal.

## The Thesis

**Every visual application is a function from data to pixels.**

```
Application :: Data → Time → Interaction → Pixels
```

The differences between applications are:
1. **Data domain** — What kind of data (audio, 3D, vectors, tables)
2. **Transform vocabulary** — What operations are available
3. **Interaction model** — How users manipulate the data
4. **Temporal semantics** — How time affects the output

But the OUTPUT is always the same: a 2D array of colors (pixels).

**The Schema is the universal vocabulary for describing:**
- All possible data domains
- All possible transforms
- All possible interactions
- All possible temporal behaviors

If the Schema can describe it, Hydrogen can render it.

**Why PureScript:**

PureScript is:
- Pure: same input = same output, always
- Total: no undefined behavior, no crashes
- Typed: invalid states are unrepresentable
- Compilable: generates efficient JavaScript

This means:
- Deterministic rendering (agents can predict pixels)
- Verifiable correctness (Lean4 can prove properties)
- Portable output (runs in any JS environment)

**Why not DSLs per domain:**

A separate DSL for audio, for 3D, for vectors, etc. creates:
- Composition boundaries (can't mix audio viz with 3D seamlessly)
- Redundant primitives (every DSL reinvents color, position, time)
- Learning burden (N languages instead of 1)

A unified Schema means: **one language, all domains.**

## What Must Be Expressible

For each category, we identify:
- **Data primitives** — What atoms the domain needs
- **Transform primitives** — What operations the domain uses
- **Interaction primitives** — How users manipulate the domain
- **Temporal primitives** — How the domain relates to time

### Category 1: Vector Graphics (Illustrator, Figma)

**Data primitives:**
- Path: Array of bezier segments (move, line, curve, close)
- Shape: Named path compositions (rectangle, ellipse, polygon, star)
- Stroke: Width, color, dash pattern, line cap, line join
- Fill: Solid, gradient (linear, radial, conic), pattern, mesh
- Text: String + font config + path (for text on path)
- Group: Named collection of shapes with shared transform
- Symbol: Reusable definition with instantiation

**Transform primitives:**
- Affine: translate, rotate, scale, skew, matrix
- Boolean: union, subtract, intersect, exclude, divide
- Pathfinder: outline, offset, simplify, smooth
- Effect: blur, drop shadow, glow, distort

**Interaction primitives:**
- Direct selection: Select and move individual anchor points
- Path editing: Add/remove/convert anchor points
- Shape tools: Draw rectangles, ellipses, polygons
- Pen tool: Draw bezier curves point by point
- Transform handles: Scale/rotate/skew via bounding box

**Temporal primitives:**
- Typically none (static output)
- Animation: keyframe interpolation of any property

**Schema coverage:**
- ✅ Geometry pillar: paths, shapes, transforms
- ✅ Color pillar: fills, strokes
- ✅ Typography pillar: text rendering
- ⚠️ Need: mesh gradients, advanced pathfinder operations

### Category 2: Raster Graphics (Photoshop)

**Data primitives:**
- Bitmap: 2D array of pixels (width × height × channels)
- Channel: Single color component (R, G, B, A, or arbitrary)
- Layer: Bitmap with blend mode, opacity, mask
- Mask: Grayscale bitmap controlling visibility
- Selection: Binary or feathered region for operations
- Brush: Shape + dynamics for painting

**Transform primitives:**
- Per-pixel: levels, curves, hue/saturation, color balance
- Convolution: blur, sharpen, edge detect, emboss
- Morphological: dilate, erode, open, close
- Compositing: blend modes (multiply, screen, overlay, etc.)
- Distortion: warp, liquify, perspective, lens correction
- Generative: noise, clouds, patterns

**Interaction primitives:**
- Brush painting: Freehand mark-making
- Selection tools: Marquee, lasso, magic wand
- Transform tool: Free transform of layer
- Layer management: Reorder, group, blend

**Temporal primitives:**
- Frame-by-frame: Each frame is independent bitmap
- Video layers: Temporal bitmap sequences

**Schema coverage:**
- ✅ Color pillar: pixel operations, color spaces
- ⚠️ Need: Bitmap type (2D typed array)
- ⚠️ Need: Convolution kernels
- ⚠️ Need: Blend modes as first-class types
- ⚠️ Need: Brush dynamics (pressure, tilt, velocity)

### Category 3: Motion Graphics (After Effects, LATTICE)

**Data primitives:**
- Composition: Timeline with layers and duration
- Layer: Visual element with transform over time
- Keyframe: Value at specific time with interpolation
- Expression: Computed property value (code-driven)
- Effect: Per-layer visual modification
- Precomp: Nested composition (recursion)
- Null: Invisible parent for transform hierarchy

**Transform primitives:**
- Temporal: Position, rotation, scale over time
- Easing: Bezier curves for interpolation
- Motion path: Position follows bezier path
- Parenting: Hierarchical transform inheritance
- Expression linking: Property driven by other properties

**Interaction primitives:**
- Timeline scrubbing: Navigate through time
- Keyframe manipulation: Add, move, adjust keyframes
- Graph editor: Edit value/velocity curves
- Ram preview: Real-time playback

**Temporal primitives:**
- Linear time: Frame-by-frame progression
- Expressions: time, loopOut, wiggle, etc.
- Time remapping: Non-linear time on layers
- Pre-render: Baked sequences for performance

**Schema coverage:**
- ✅ Temporal pillar: keyframes, easing, duration
- ✅ Geometry pillar: transform hierarchy
- ⚠️ Need: Expression language (or JS FFI)
- ⚠️ Need: Time remapping
- ⚠️ Need: Precomp/nested composition model

### Category 4: 3D Graphics (Cinema 4D, Blender)

**Data primitives:**
- Mesh: Vertices, edges, faces (or triangles)
- Vertex: Position (vec3) + normal + UV + color + weights
- Material: Shader configuration (PBR or custom)
- Light: Point, directional, spot, area, HDRI
- Camera: Position, rotation, FOV, near/far planes
- Bone: Transform for skeletal animation
- Curve: 3D bezier/NURBS for paths or surfaces

**Transform primitives:**
- Modeling: Extrude, bevel, subdivide, boolean
- Deformation: Bend, twist, lattice, shrinkwrap
- Projection: Perspective, orthographic
- Shading: Vertex shaders, fragment shaders
- Rasterization: Triangle → fragments → pixels

**Interaction primitives:**
- Viewport navigation: Orbit, pan, zoom
- Object selection: Click to select meshes
- Vertex editing: Direct manipulation of geometry
- Gizmo manipulation: Translate, rotate, scale handles

**Temporal primitives:**
- Keyframe animation: Any property over time
- Skeletal animation: Bone hierarchies
- Physics simulation: Rigid body, soft body, cloth, fluid
- Procedural animation: Noise, expressions, constraints

**Schema coverage:**
- ✅ Spatial pillar: 3D coordinates, transforms
- ⚠️ Need: Mesh type (vertex buffer, index buffer)
- ⚠️ Need: Material/shader system
- ⚠️ Need: Light types
- ⚠️ Need: Camera projection matrices
- ⚠️ Need: Bone/rig system

### Category 5: Audio Visualization (Ableton, TouchDesigner)

**Data primitives:**
- Waveform: Array of amplitude samples over time
- Spectrum: Array of frequency magnitudes (FFT output)
- MIDI: Note on/off, velocity, CC, pitch bend
- Envelope: ADSR or arbitrary amplitude shape
- Buffer: Circular audio sample storage
- Texture: 2D data (for TouchDesigner style feedback)

**Transform primitives:**
- FFT: Time domain → frequency domain
- Filtering: Low-pass, high-pass, band-pass, notch
- Envelope following: Amplitude → control signal
- Mapping: Audio value → visual parameter
- Feedback: Output fed back to input (delay, reverb)

**Interaction primitives:**
- Waveform scrubbing: Navigate audio timeline
- Knob/slider: Adjust parameters
- Patch cables: Connect nodes (TouchDesigner)
- MIDI mapping: External control

**Temporal primitives:**
- Sample rate: 44100Hz, 48000Hz, etc.
- Buffer size: Latency vs. performance tradeoff
- Beat sync: Musical time (bars, beats)
- LFO: Low-frequency oscillation for modulation

**Schema coverage:**
- ✅ Audio pillar: waveforms, frequencies (exists in Schema)
- ✅ Temporal pillar: time, duration
- ⚠️ Need: FFT as first-class operation
- ⚠️ Need: Audio buffer type
- ⚠️ Need: MIDI message types
- ⚠️ Need: Node graph for patching

### Category 6: Data Visualization (Hospital Dashboards, Analytics)

**Data primitives:**
- Series: Array of (timestamp, value) pairs
- Table: Rows × columns of typed cells
- Tree: Hierarchical data (org charts, file systems)
- Graph: Nodes and edges (networks, dependencies)
- Geo: Latitude/longitude points, polygons, paths
- Scalar: Single value with unit (temperature, pressure)

**Transform primitives:**
- Aggregation: Sum, average, min, max, count
- Filtering: Where clauses on data
- Grouping: By category, by time bucket
- Interpolation: Fill missing data points
- Projection: Map data to visual channels (x, y, color, size)

**Interaction primitives:**
- Hover: Tooltip with data details
- Selection: Click to filter/highlight
- Brushing: Drag to select range
- Drill-down: Click to navigate hierarchy
- Pan/zoom: Navigate large datasets

**Temporal primitives:**
- Real-time: Streaming data updates
- Historical: Query past data ranges
- Refresh rate: How often to update
- Animation: Transition between states

**Schema coverage:**
- ✅ Color pillar: Encoding values as colors
- ✅ Dimension pillar: Encoding values as sizes
- ✅ Typography pillar: Labels, annotations
- ⚠️ Need: Chart primitives (axis, legend, scale)
- ⚠️ Need: Data binding system
- ⚠️ Need: Real-time subscription model
- ⚠️ Need: Geographic projection types

### Category 7: Interactive Applications (E-commerce, SaaS)

**Data primitives:**
- Entity: Product, user, order, etc. (domain objects)
- List: Scrollable collection of entities
- Form: Input fields with validation
- Media: Images, video, audio assets
- State: Application mode (loading, error, success)
- Session: User identity and preferences

**Transform primitives:**
- Layout: Flexbox, grid, absolute positioning
- Responsive: Adapt to viewport size
- Theming: Apply brand colors, fonts
- Localization: Translate strings, format numbers
- Filtering/sorting: Transform lists by criteria

**Interaction primitives:**
- Navigation: Click to change route
- Form input: Type to update fields
- Scroll: Infinite scroll, pagination
- Drag-drop: Reorder, transfer items
- Gestures: Swipe, pinch, long-press

**Temporal primitives:**
- Loading states: Async data fetching
- Transitions: Animate between states
- Debounce: Delay rapid inputs
- Optimistic updates: Show expected result before confirmation

**Schema coverage:**
- ✅ Gestural pillar: All interaction types
- ✅ Typography pillar: Text rendering
- ✅ Layout: Flexbox (in progress)
- ✅ Color/Material: Theming
- ⚠️ Need: Form validation primitives
- ⚠️ Need: Route/navigation types
- ⚠️ Need: Remote data (RemoteData monad)

### Category 8: Generative/Procedural (TouchDesigner, Shaders)

**Data primitives:**
- Noise: Perlin, simplex, worley, value
- Field: 2D/3D scalar or vector field
- Particle: Position, velocity, lifetime, custom attributes
- SDF: Signed distance field (for raymarching)
- Feedback: Previous frame as texture input
- Random: Seeded PRNG for determinism

**Transform primitives:**
- Noise operations: Octaves, lacunarity, gain
- Field operations: Sample, gradient, curl
- Particle operations: Emit, update, kill
- SDF operations: Union, subtract, smooth blend
- Shader math: sin, cos, fract, mix, smoothstep

**Interaction primitives:**
- Parameter tweaking: Real-time knob adjustment
- Node patching: Wire nodes together
- MIDI/OSC: External control signals
- Audio reactivity: FFT → visual parameters

**Temporal primitives:**
- Frame: Current frame number
- Time: Continuous time value
- Delta: Time since last frame
- Random walk: Accumulated noise over time
- Feedback decay: Previous frame × factor

**Schema coverage:**
- ✅ Temporal pillar: Time, frame
- ⚠️ Need: Noise functions as Schema atoms
- ⚠️ Need: SDF primitives and operations
- ⚠️ Need: Particle system types
- ⚠️ Need: Shader/expression language integration
- ⚠️ Need: Feedback buffer type

## The Schema Mapping

The Schema must cover ALL primitives from ALL categories. Let's map what exists
to what's needed.

### Current Pillars (14 total)

```
1.  Color       — RGB, HSL, LAB, color spaces, gradients
2.  Dimension   — Pixels, em, rem, vh/vw, percentages
3.  Geometry    — Points, paths, shapes, transforms
4.  Typography  — Fonts, glyphs, text layout
5.  Material    — Surfaces, textures, reflectance
6.  Elevation   — Z-index, shadows, depth
7.  Temporal    — Duration, easing, keyframes
8.  Reactive    — Bindings, subscriptions, streams
9.  Gestural    — Touch, mouse, keyboard interactions
10. Haptic      — Vibration patterns, force feedback
11. Spatial     — 3D coordinates, cameras, projections
12. Brand       — Identity, tokens, themes
13. Audio       — Waveforms, frequencies, ADSR
14. Motion      — Velocity, acceleration, physics
```

**What each pillar provides:**

| Pillar     | Data Atoms | Transform Atoms | Interaction Atoms | Temporal Atoms |
|------------|------------|-----------------|-------------------|----------------|
| Color      | SRGB, HSL, Gradient | Blend, Convert | — | — |
| Dimension  | Pixel, Em, Percent | Scale, Clamp | — | — |
| Geometry   | Point, Path, Shape | Affine, Boolean | Hit test | — |
| Typography | Glyph, Font, Line | Shape, Layout | Selection | — |
| Material   | Surface, Texture | — | — | — |
| Elevation  | Layer, Shadow | — | — | — |
| Temporal   | Duration, Keyframe | Ease, Interpolate | — | Time |
| Reactive   | Stream, Binding | Map, Filter | Subscribe | — |
| Gestural   | Touch, Key, Scroll | — | Dispatch | — |
| Haptic     | Pattern, Intensity | — | Trigger | Duration |
| Spatial    | Point3D, Camera | Project, Transform3D | — | — |
| Brand      | Token, Theme | Apply | — | — |
| Audio      | Waveform, Freq | FFT, Filter | Play | Sample rate |
| Motion     | Velocity, Force | Integrate | — | Delta time |

### Gap Analysis

**Missing from current Schema:**

| Gap | Category Need | Proposed Pillar/Extension |
|-----|---------------|---------------------------|
| Bitmap/Raster | Photoshop, video | Pillar 15: Raster |
| Mesh/3D geometry | Cinema 4D, Blender | Extend: Spatial |
| Shader/expressions | TouchDesigner, AE | Pillar 16: Procedural |
| Blend modes | Photoshop, compositing | Extend: Material |
| Data binding | Dashboards, apps | Extend: Reactive |
| Particles | TouchDesigner, games | Pillar 17: Particle |
| SDF | Raymarching, procedural | Extend: Geometry |
| Charts | Analytics, dashboards | Pillar 18: DataViz |
| Forms | E-commerce, SaaS | Extend: Gestural |
| Navigation | Apps, websites | Pillar 19: Navigation |
| Convolution kernels | Image processing | Extend: Raster |
| MIDI | Audio tools | Extend: Audio |
| Physics | Games, simulations | Extend: Motion |
| Node graphs | TouchDesigner, Houdini | Meta: Composition |

**Severity levels:**

- **Critical** — Cannot build the category without this
- **Important** — Significantly harder without this
- **Nice-to-have** — Can work around, but cleaner with

| Gap | Severity | Reasoning |
|-----|----------|-----------|
| Bitmap/Raster | Critical | No image editing without pixel buffers |
| Mesh/3D | Critical | No 3D apps without mesh type |
| Procedural | Critical | No generative art without noise/SDF |
| Blend modes | Important | Compositing quality suffers |
| Data binding | Important | Dashboard perf suffers |
| Particles | Important | No particle effects |
| Charts | Important | Must rebuild chart primitives |
| Navigation | Nice-to-have | Can model with existing types |
| Physics | Nice-to-have | Can implement in userland |

### Proposed Extensions

**New Pillars:**

```
15. Raster      — Bitmap, channel, convolution, blend modes
16. Procedural  — Noise, SDF, field, feedback
17. Particle    — Emitter, particle, force, constraint
18. DataViz     — Scale, axis, legend, mark, encoding
19. Navigation  — Route, link, history, transition
```

**Pillar 15: Raster**

```purescript
-- Core bitmap type
type Bitmap = 
  { width :: Int
  , height :: Int
  , channels :: Int          -- 1 = grayscale, 3 = RGB, 4 = RGBA
  , data :: TypedArray Float -- Normalized 0-1
  }

-- Convolution
type Kernel = Array (Array Number)  -- e.g., 3×3 Gaussian blur

-- Blend modes
data BlendMode
  = Normal | Multiply | Screen | Overlay | Darken | Lighten
  | ColorDodge | ColorBurn | HardLight | SoftLight
  | Difference | Exclusion | Hue | Saturation | Color | Luminosity

-- Operations
blur :: Number -> Bitmap -> Bitmap
convolve :: Kernel -> Bitmap -> Bitmap
blend :: BlendMode -> Bitmap -> Bitmap -> Bitmap
```

**Pillar 16: Procedural**

```purescript
-- Noise functions
data NoiseType = Perlin | Simplex | Worley | Value

noise2D :: NoiseType -> Number -> Number -> Number
noise3D :: NoiseType -> Number -> Number -> Number -> Number
fbm :: NoiseType -> Int -> Number -> Number -> Number -> Number  -- octaves

-- SDF primitives
data SDF
  = SDFCircle Number           -- radius
  | SDFBox Number Number       -- width, height
  | SDFLine Point2D Point2D
  | SDFUnion SDF SDF
  | SDFSubtract SDF SDF
  | SDFSmooth SDF SDF Number   -- smooth union with k

sdfEval :: SDF -> Point2D -> Number  -- distance to surface
```

**Pillar 17: Particle**

```purescript
type Particle =
  { position :: Point3D
  , velocity :: Vector3D
  , age :: Number
  , lifetime :: Number
  , color :: RGBA
  , size :: Number
  , custom :: Map String Number  -- User-defined attributes
  }

type Emitter =
  { rate :: Number              -- Particles per second
  , shape :: EmitterShape       -- Point, line, circle, sphere
  , initialVelocity :: VelocityDistribution
  , lifetime :: Range Number
  }

type ParticleSystem =
  { particles :: Array Particle
  , emitters :: Array Emitter
  , forces :: Array Force       -- Gravity, wind, turbulence
  }
```

**Pillar 18: DataViz**

```purescript
-- Scales map data domain to visual range
data Scale a
  = Linear { domain :: Range a, range :: Range Number }
  | Log { domain :: Range a, range :: Range Number, base :: Number }
  | Ordinal { domain :: Array a, range :: Array Number }
  | Time { domain :: Range Timestamp, range :: Range Number }

-- Visual encodings
data Encoding
  = X Scale         -- Horizontal position
  | Y Scale         -- Vertical position  
  | Color Scale     -- Color channel
  | Size Scale      -- Size channel
  | Shape (a -> Shape)  -- Shape by category

-- Chart primitives
type Axis = { scale :: Scale, position :: AxisPosition, ticks :: TickConfig }
type Legend = { encoding :: Encoding, position :: LegendPosition }
type Mark = { shape :: Shape, encodings :: Array Encoding }
```

**Pillar 19: Navigation**

```purescript
-- Route definition
type Route = Array RouteSegment

data RouteSegment
  = Static String
  | Param String
  | Wildcard

-- Navigation state
type NavState =
  { current :: Route
  , params :: Map String String
  , history :: Array Route
  , historyIndex :: Int
  }

-- Transitions
data NavTransition
  = Push Route
  | Replace Route
  | Back
  | Forward
  | Go Int
```

## The Rendering Pipeline

The pipeline transforms Schema atoms to pixels. It must handle ALL categories
with a unified architecture.

### Layer 1: Schema (Pure Data)

Schema atoms are **pure values with no computation**. They describe WHAT, not HOW.

```purescript
-- A rectangle is pure data
rectangle :: Schema.Rectangle
rectangle = 
  { position: Point2D { x: Pixel 100, y: Pixel 50 }
  , size: Size2D { width: Pixel 200, height: Pixel 48 }
  , fill: Solid (SRGB { r: Channel 59, g: Channel 130, b: Channel 246 })
  , cornerRadius: CornerRadii { topLeft: Pixel 8, ... }
  }

-- A particle system is pure data
particles :: Schema.ParticleSystem
particles =
  { emitter: { rate: 100.0, shape: Point origin, ... }
  , forces: [Gravity { strength: 9.8, direction: Down }]
  , particles: []  -- Initially empty, runtime fills this
  }

-- A 3D mesh is pure data
mesh :: Schema.Mesh
mesh =
  { vertices: [...]   -- Array of vertex positions
  , indices: [...]    -- Triangle indices
  , material: PBR { albedo: ..., roughness: ..., metallic: ... }
  }
```

**Key properties:**
- Serializable (can be sent over network, stored in DB)
- Comparable (Eq instance for change detection)
- Hashable (for caching, deduplication)
- Deterministic (same data = same hash = same render)

### Layer 2: Scene Graph (Composition)

The scene graph composes atoms into hierarchical structures.

```purescript
-- Universal scene node
data SceneNode
  = Shape2D Schema.Shape
  | Shape3D Schema.Mesh
  | Text Schema.TextBlock
  | Image Schema.Bitmap
  | Particles Schema.ParticleSystem
  | Audio Schema.AudioSource
  | Group 
      { children :: Array SceneNode
      , transform :: Schema.Transform
      , opacity :: Schema.Opacity
      , blendMode :: Schema.BlendMode
      , mask :: Maybe SceneNode
      }
  | Conditional
      { condition :: Schema.Binding Boolean
      , ifTrue :: SceneNode
      , ifFalse :: SceneNode
      }
  | Repeat
      { items :: Schema.Binding (Array a)
      , template :: a -> SceneNode
      }
  | Lazy
      { thunk :: Unit -> SceneNode
      }
```

**Key operations:**
- Traversal: Visit all nodes (for rendering, hit testing)
- Querying: Find nodes by ID, type, position
- Diffing: Compare two trees for minimal updates
- Flattening: Convert tree to command list

### Layer 3: Layout (Spatial Resolution)

Layout resolves relative dimensions to absolute pixel positions.

```purescript
-- Layout input: Scene node with relative positions
input :: SceneNode
input = Group
  { children: [box1, box2]
  , layout: Flex { direction: Row, gap: Pixel 10 }
  }

-- Layout output: Positioned nodes with absolute coords
type LayoutResult =
  { node :: SceneNode
  , bounds :: BoundingBox      -- Absolute pixel position
  , children :: Array LayoutResult
  }

-- Layout algorithm is pluggable
data LayoutAlgorithm
  = FlexLayout FlexConfig
  | GridLayout GridConfig
  | AbsoluteLayout
  | StackLayout Direction
  | ConstraintLayout (Array Constraint)
```

**Layout categories:**

| Category | Layout System |
|----------|---------------|
| Web apps | Flexbox, Grid, Absolute |
| Figma | Constraints + Auto-layout |
| After Effects | Absolute + Parenting |
| 3D apps | World space (no 2D layout) |
| Games | Custom (physics-based) |
| Dashboards | Grid + responsive |

**The layout layer must support ALL of these.**

### Layer 4: Commands (GPU Instructions)

Commands are the universal instruction set for the GPU.

```purescript
data DrawCommand
  -- 2D primitives (vector)
  = DrawRect RectParams
  | DrawPath PathParams
  | DrawGlyph GlyphParams
  
  -- Raster operations
  | DrawBitmap BitmapParams
  | Convolve KernelParams
  | Blend BlendParams
  
  -- 3D primitives
  | DrawMesh MeshParams
  | SetCamera CameraParams
  | SetLight LightParams
  
  -- Particles
  | UpdateParticles ParticleSystemParams
  | DrawParticles ParticleRenderParams
  
  -- Procedural
  | EvalSDF SDFParams
  | SampleNoise NoiseParams
  
  -- Control flow
  | SetRenderTarget TargetId
  | Clear ClearParams
  | Composite CompositeParams
  
  -- State
  | PushState
  | PopState
  | SetTransform TransformMatrix
  | SetClip ClipRegion
```

**Command buffer properties:**
- Stateless: Each command is self-contained
- Sortable: Can reorder for batching (by texture, shader)
- Serializable: Can send to worker/GPU process
- Diffable: Minimal update from previous frame

### Layer 5: Execution (Pixels)

Execution interprets commands to produce actual pixels.

```
Command Buffer
     ↓ dispatch by type
┌────┴────┬────────────┬────────────┐
│ 2D      │ 3D         │ Compute    │
│ Canvas  │ WebGL      │ WebGPU     │
│ SVG     │ WebGPU     │ WASM       │
└────┬────┴────────────┴────┬───────┘
     ↓                      ↓
  Rasterize            Simulate
     ↓                      ↓
     └──────────┬───────────┘
                ↓
          Frame Buffer
                ↓
            Display
```

**Execution targets:**

| Target | Use Case | Performance |
|--------|----------|-------------|
| Canvas 2D | Simple 2D, fallback | Medium |
| SVG | Vector export, accessibility | Slow |
| WebGL | 3D, shaders | Fast |
| WebGPU | Modern, compute | Fastest |
| WASM | CPU-bound compute | Fast (CPU) |
| Worker | Off-main-thread | Parallel |

**The same command buffer renders to ANY target.**

This is the key to universality: Schema → Commands → Target
                                   (unified)  (unified)  (pluggable)

## Memory Model

This section addresses the critical question: **How do we prevent memory
degradation at scale?**

### Why Memory Degradation Happens

Memory degradation in visual applications comes from:

**1. Unbounded caches**
```
"Cache the rendered result for faster re-render"
→ Cache grows without bound
→ Eventually exceeds available memory
→ GC pauses cause frame drops
→ Or crash
```

**2. Retained mode accumulation**
```
"Keep all objects in memory for editing"
→ User creates 10,000 objects
→ Each object retains event handlers, undo state
→ Memory grows linearly with history
→ Eventually unusable
```

**3. Reference leaks**
```
"Subscribe to event stream"
→ Forget to unsubscribe
→ Old components stay alive via subscription
→ Memory grows over session lifetime
```

**4. Texture/buffer leaks**
```
"Allocate GPU texture for image"
→ Remove image from scene
→ Forget to deallocate texture
→ GPU memory exhausted
```

**5. Fragmentation**
```
"Allocate, deallocate, allocate..."
→ Memory becomes fragmented
→ Large allocations fail despite "enough" memory
→ Performance degrades
```

### How We Prevent It

**Principle 1: Bounded structures everywhere**

Every cache, buffer, and collection has a maximum size.

```purescript
-- Ring buffer: fixed size, O(1) insert, oldest evicted
type RingBuffer a = { buffer :: Array a, capacity :: Int, head :: Int }

-- LRU cache: fixed size, least-recently-used evicted
type LRUCache k v = { entries :: Map k (v, Timestamp), maxSize :: Int }

-- Pooled allocator: fixed number of slots, reuse instead of allocate
type Pool a = { slots :: Array (Maybe a), freeList :: Array Int }
```

**Principle 2: Explicit lifecycles**

Resources have explicit create/destroy, not implicit GC.

```purescript
-- Texture with manual lifecycle
createTexture :: TextureConfig -> Effect TextureId
destroyTexture :: TextureId -> Effect Unit

-- Scene node tracks owned resources
type SceneNode = 
  { ... 
  , resources :: Set ResourceId  -- Resources to destroy when node removed
  }

-- Destroy resources when node exits scene
onNodeRemoved :: SceneNode -> Effect Unit
onNodeRemoved node = traverse_ destroyResource node.resources
```

**Principle 3: Structural sharing**

Immutable data structures share unchanged subtrees.

```purescript
-- Updating a single property doesn't copy the whole tree
oldTree :: SceneNode
newTree = oldTree { children = ... }  -- Shares most of oldTree's memory

-- Persistent data structures (maps, sets) share structure
oldMap :: Map k v
newMap = Map.insert k v oldMap  -- O(log n) new nodes, rest shared
```

**Principle 4: Streaming, not loading**

Large data is processed in chunks, not loaded entirely.

```purescript
-- DON'T: Load entire video into memory
video <- loadVideo "huge.mp4"  -- 4GB in memory

-- DO: Stream frames on demand
stream <- openVideoStream "huge.mp4"
frame <- readFrame stream currentTime  -- Single frame in memory
```

### Generational Collection

For data that DOES use GC (PureScript values), we structure for generational
collection efficiency.

**Generational hypothesis:** Most objects die young.

**Structure for this:**

```
Frame-local data (dies every frame):
  - Intermediate layout calculations
  - Temporary command buffers
  - Per-frame allocations
  → Allocate in "nursery", collect entirely each frame

Session-local data (dies on navigation):
  - Current page's scene graph
  - Route-specific caches
  → Collected when route changes

Application-global data (lives forever):
  - Font atlases
  - Shared textures
  - Configuration
  → Never collected, sized at startup
```

**Implementation:**

```purescript
-- Frame-scoped computation
withFrame :: forall a. (FrameContext -> a) -> a
withFrame f =
  let ctx = allocateFrameContext
      result = f ctx
  in do
    freeFrameContext ctx  -- All frame allocations freed
    pure result

-- Session-scoped resources
type SessionResources =
  { textures :: Map TextureId Texture
  , audioBuffers :: Map AudioId AudioBuffer
  , cleanup :: Effect Unit  -- Called on session end
  }
```

### Streaming Architecture

For data that exceeds memory (large images, videos, datasets), we stream.

**Streaming levels:**

```
Level 1: Tile-based
  - Large image → tiles loaded on demand
  - Only visible tiles in memory
  - Example: Google Maps, Figma infinite canvas

Level 2: LOD (Level of Detail)
  - Zoomed out → low resolution
  - Zoomed in → high resolution loaded
  - Only current LOD in memory

Level 3: Time-based
  - Video → only current frame + small buffer
  - Audio → only current buffer + small lookahead
  - Animation → keyframes + current interpolation

Level 4: Query-based
  - Database → only currently displayed rows
  - Infinite scroll → virtualized list
  - Only viewport contents in memory
```

**Streaming primitives:**

```purescript
-- Async resource loading
type StreamingResource a =
  { placeholder :: a           -- Show while loading
  , load :: Effect (Promise a) -- Async fetch
  , priority :: Priority       -- Loading order
  , evictable :: Boolean       -- Can be evicted under pressure
  }

-- Virtual list (only renders visible items)
type VirtualList a =
  { totalCount :: Int
  , visibleRange :: { start :: Int, end :: Int }
  , renderItem :: Int -> a -> SceneNode
  , itemHeight :: Int -> Number  -- For variable height
  }

-- Tiled image (only loads visible tiles)
type TiledImage =
  { tileSize :: Int
  , tilesX :: Int
  , tilesY :: Int
  , loadTile :: { x :: Int, y :: Int } -> Effect (Promise Bitmap)
  , loadedTiles :: Map (Int × Int) Bitmap
  }
```

## Liveness and Responsiveness

Liveness means the system responds immediately to user input.
Responsiveness means the system never freezes or stutters.

At 60fps, we have 16.67ms per frame. This is the law.

### The 16ms Budget

```
Frame budget: 16.67ms (60fps) or 8.33ms (120fps)

Budget allocation:
├── Input handling:      1ms
├── State update:        2ms
├── Layout:              3ms
├── Command generation:  3ms
├── GPU upload:          2ms
├── GPU render:          4ms
└── Buffer swap:         1ms
                       ─────
                        16ms
```

**If ANY phase exceeds budget:**
- Frame drops (user sees stutter)
- Input feels laggy
- Animation jitters

**Rules:**
1. No single operation takes >5ms on main thread
2. Long operations are chunked across frames
3. Heavy compute moves to workers
4. GPU operations are pipelined (async)

### Incremental Everything

Every operation must be interruptible and resumable.

**Layout:**
```purescript
-- DON'T: Layout entire tree in one call
layout :: SceneNode -> LayoutResult  -- Could take 100ms

-- DO: Incremental layout with budget
layoutIncremental :: Int -> SceneNode -> LayoutState -> LayoutState
layoutIncremental budgetMs node state =
  if elapsedMs >= budgetMs
    then state  -- Yield, continue next frame
    else layoutIncremental budgetMs nextNode (process node state)
```

**Diffing:**
```purescript
-- DON'T: Diff entire tree at once
diff :: SceneNode -> SceneNode -> Patch  -- Could be huge tree

-- DO: Incremental diff with early exit
diffIncremental :: Int -> SceneNode -> SceneNode -> DiffState -> DiffState
diffIncremental budget old new state =
  if budget <= 0 || isComplete state
    then state
    else diffIncremental (budget - 1) ... (step state)
```

**Rendering:**
```purescript
-- DON'T: Render all commands in one go
render :: CommandBuffer -> Effect Unit  -- Could be 10000 commands

-- DO: Chunked rendering with frame boundary check
renderChunked :: Int -> CommandBuffer -> Effect RenderState
renderChunked chunkSize commands =
  let chunk = take chunkSize commands
      rest = drop chunkSize commands
  in do
    executeChunk chunk
    if null rest
      then pure Complete
      else pure (Pending rest)  -- Continue next frame
```

### Priority Scheduling

Not all updates are equally important. Input handling > animation > background.

```purescript
data Priority
  = Critical    -- Input handling, must complete THIS frame
  | High        -- Animation, visible changes
  | Normal      -- State updates, non-urgent
  | Low         -- Background work, can be deferred
  | Idle        -- Only when nothing else to do

type Task =
  { priority :: Priority
  , deadline :: Maybe Timestamp  -- Must complete by
  , work :: Effect TaskResult
  , onCancel :: Effect Unit
  }

-- Scheduler runs highest priority first, respects deadlines
schedule :: Array Task -> Effect Unit
schedule tasks =
  let sorted = sortBy (\t -> (t.priority, t.deadline)) tasks
  in runWithBudget frameTimeRemaining sorted
```

**Priority examples:**

| Operation | Priority | Deadline |
|-----------|----------|----------|
| Pointer move handling | Critical | This frame |
| Click handling | Critical | This frame |
| Scroll handling | Critical | This frame |
| Animation tick | High | This frame |
| State update from click | High | This frame |
| Data fetch callback | Normal | None |
| Analytics | Low | None |
| Prefetch | Idle | None |

### Cancellation and Preemption

When new input arrives, we may need to cancel in-progress work.

```purescript
-- Cancellable computation
type Cancellable a =
  { result :: Promise a
  , cancel :: Effect Unit
  }

-- Example: User types, cancel previous search
onSearchInput :: String -> Effect Unit
onSearchInput query = do
  -- Cancel any in-progress search
  traverse_ (_.cancel) currentSearch
  -- Start new search (cancellable)
  currentSearch <- Just <$> searchAsync query

-- Preemption: Higher priority interrupts lower
type Preemptible a =
  { run :: Effect (Either Preempted a)
  , priority :: Priority
  }

runPreemptible :: Preemptible a -> Effect (Either Preempted a)
runPreemptible task = do
  result <- task.run
  checkForHigherPriority task.priority >>= case _ of
    Just higherTask -> pure (Left Preempted)
    Nothing -> pure result
```

**Key invariants:**
1. Input handling is NEVER preempted
2. Animation can preempt background work
3. Cancelled work releases resources immediately
4. Preempted work can resume or restart

## Proof of Universality

To prove the Schema is universal, we show the minimum atoms needed to build
each application category. If all atoms exist in the Schema, we can build it.

### Ableton Clone: Minimum Schema

**Core views:**
- Arrangement timeline (tracks × time)
- Session clips (grid of clips)
- Mixer (faders, meters, pans)
- Device rack (effects chain)
- Piano roll (notes × time)
- Waveform editor

**Required Schema atoms:**

```purescript
-- Audio pillar (existing)
Waveform, Frequency, Amplitude, ADSR, AudioBuffer

-- Temporal pillar (existing)
Duration, Timestamp, BPM, TimeSignature, Beat, Bar

-- Geometry pillar (existing)
Rectangle, Path, Transform

-- Color pillar (existing)
SRGB, Gradient (for meters)

-- NEW: MIDI types
type MIDINote = { pitch :: Int, velocity :: Int, start :: Beat, duration :: Beat }
type MIDIClip = Array MIDINote
type MIDITrack = Array MIDIClip

-- NEW: Audio routing
type AudioBus = { input :: Array SourceId, output :: Array TargetId, effects :: Array Effect }
type Mixer = { tracks :: Array Track, master :: AudioBus }

-- NEW: Device (effects/instruments)
type Device = { name :: String, params :: Map String Parameter, bypass :: Boolean }
type Parameter = { value :: Number, min :: Number, max :: Number, automation :: Maybe Automation }

-- Gestural pillar (existing)
DragDrop, Scroll, Click, KeyPattern

-- DataViz pillar (new)
Scale (for time → pixels), Axis (timeline ruler)
```

**Verdict:** Buildable with Schema + MIDI extension + Audio routing extension.

### After Effects Clone: Minimum Schema

**Core views:**
- Composition panel (preview)
- Timeline (layers × time × properties)
- Effect controls (parameters)
- Project panel (assets)
- Graph editor (value curves)

**Required Schema atoms:**

```purescript
-- Temporal pillar (existing)
Duration, Keyframe, Easing, Timestamp

-- Geometry pillar (existing)
Transform, Path, Shape, Mask

-- Color pillar (existing)
SRGB, Gradient, BlendMode (need full set)

-- Typography pillar (existing)
Font, TextBlock, TextPath

-- Raster pillar (new)
Bitmap, Layer, Composite, ConvolutionKernel

-- NEW: Composition model
type Composition = 
  { width :: Int, height :: Int
  , duration :: Duration
  , frameRate :: Number
  , layers :: Array Layer
  }

type Layer =
  { source :: LayerSource
  , inPoint :: Timestamp
  , outPoint :: Timestamp
  , transform :: AnimatedTransform
  , effects :: Array Effect
  , masks :: Array Mask
  , blendMode :: BlendMode
  , opacity :: Animated Number
  }

data LayerSource
  = Solid Color
  | Footage AssetId
  | Precomp CompositionId
  | Text TextBlock
  | Shape ShapeGroup
  | Null

-- NEW: Animated properties
type Animated a = 
  { keyframes :: Array (Keyframe a)
  , expression :: Maybe Expression
  }

type Keyframe a =
  { time :: Timestamp
  , value :: a
  , easeIn :: Easing
  , easeOut :: Easing
  }

-- NEW: Effects
type Effect = { type :: EffectType, params :: Map String (Animated Number) }
```

**Verdict:** Buildable with Schema + Raster pillar + Composition model + Expressions.

### Figma Clone: Minimum Schema

**Core views:**
- Canvas (infinite, zoomable)
- Layers panel (tree)
- Properties panel (selected object)
- Components panel (library)
- Prototype mode (interactions)

**Required Schema atoms:**

```purescript
-- Geometry pillar (existing)
Point, Path, Shape, Transform, BooleanOp

-- Color pillar (existing)
SRGB, Gradient (linear, radial, angular, diamond)

-- Typography pillar (existing)
Font, TextBlock, TextStyle

-- NEW: Vector frame model
type Frame =
  { id :: NodeId
  , name :: String
  , children :: Array Node
  , constraints :: Constraints
  , layout :: Maybe AutoLayout
  , fill :: Array Paint
  , stroke :: Array Stroke
  , effects :: Array Effect
  , cornerRadius :: CornerRadius
  }

type Constraints =
  { horizontal :: HConstraint  -- Left, Right, Center, LeftRight, Scale
  , vertical :: VConstraint    -- Top, Bottom, Center, TopBottom, Scale
  }

type AutoLayout =
  { direction :: Direction
  , spacing :: Number
  , padding :: Padding
  , alignment :: Alignment
  }

-- NEW: Components and instances
type Component = { id :: ComponentId, root :: Frame }
type Instance = { componentId :: ComponentId, overrides :: Map PropertyPath Value }

-- NEW: Prototype interactions
type Interaction =
  { trigger :: Trigger        -- Click, Hover, Drag, etc.
  , action :: Action          -- Navigate, OpenOverlay, Scroll, etc.
  , transition :: Transition  -- Dissolve, SmartAnimate, etc.
  }

-- Gestural pillar (existing)
Click, Hover, Drag, Scroll

-- Reactive pillar (existing)
Selection state, hover state
```

**Verdict:** Buildable with Schema + Vector frame model + Component system + Prototyping.

### Hospital Dashboard: Minimum Schema

**Core views:**
- Patient monitor (vitals grid)
- Trends (time series charts)
- Alerts (priority list)
- Patient list (table)
- Floor map (spatial view)

**Required Schema atoms:**

```purescript
-- DataViz pillar (new)
Scale, Axis, Legend, Mark, Encoding

-- Temporal pillar (existing)
Timestamp, Duration, Interval

-- Color pillar (existing)
SRGB (for alert colors: red/yellow/green)

-- Geometry pillar (existing)
Rectangle, Path (for charts)

-- Typography pillar (existing)
Font, TextBlock (for labels, values)

-- NEW: Medical domain types
type Vital = 
  { type :: VitalType          -- HeartRate, BP, SpO2, Temp, Resp
  , value :: Number
  , unit :: Unit
  , timestamp :: Timestamp
  , status :: AlertLevel       -- Normal, Warning, Critical
  }

data VitalType = HeartRate | BloodPressure | SpO2 | Temperature | Respiration

type Patient =
  { id :: PatientId
  , name :: String
  , room :: RoomId
  , vitals :: Array Vital
  , alerts :: Array Alert
  }

type Alert =
  { level :: AlertLevel
  , message :: String
  , timestamp :: Timestamp
  , acknowledged :: Boolean
  }

-- NEW: Real-time data binding
type LiveStream a = 
  { current :: a
  , subscribe :: (a -> Effect Unit) -> Effect Unsubscribe
  , history :: TimeRange -> Effect (Array a)
  }

-- Reactive pillar (existing)
Stream, Binding

-- NEW: Chart components
type TimeSeriesChart =
  { data :: LiveStream (Array DataPoint)
  , xScale :: Scale Timestamp
  , yScale :: Scale Number
  , thresholds :: Array { value :: Number, color :: Color }
  }
```

**Verdict:** Buildable with Schema + DataViz pillar + Domain types + LiveStream.

## Implementation Strategy

The Schema cannot be built all at once. We prioritize based on:
1. Foundation: Must exist for anything to work
2. Breadth: Enable the most categories
3. Depth: Full feature parity within categories

**Phase 1: Foundation (Current)**
- Geometry: paths, shapes, transforms ✅
- Color: RGB, HSL, gradients ✅
- Typography: fonts, glyphs, layout ✅
- Dimension: pixels, em, percentages ✅
- Temporal: duration, easing, keyframes ✅
- Gestural: click, hover, drag, scroll ✅

**Phase 2: Interactive Applications**
- Layout: Flexbox, Grid, Constraints (in progress)
- Navigation: Routes, transitions
- Forms: Inputs, validation
- DataViz: Scales, axes, charts
- RemoteData: Async data handling

**Phase 3: Creative Tools**
- Raster: Bitmaps, blend modes, convolution
- Vector: Boolean ops, pathfinder
- Procedural: Noise, SDF, particles

**Phase 4: Motion**
- Animation: Full keyframe system
- Expressions: Code-driven animation
- Composition: Nesting, precomps

**Phase 5: 3D**
- Mesh: Vertices, faces, materials
- Camera: Projection, navigation
- Lighting: Types, shadows
- Shaders: Custom materials

**Phase 6: Audio/Video**
- Audio: Full audio graph
- Video: Frame-accurate playback
- MIDI: Note events, CC
- Sync: Audio-visual sync

**Each phase must be COMPLETE before moving to next.**

No stubs. No placeholders. Full implementation with Lean4 proofs where applicable.

## What This Means for Schema Design

If you are designing Schema atoms, understand:

**1. Atoms must be primitive**

An atom is the smallest unit that cannot be decomposed further. If you can
express it as a composition of other atoms, it's not an atom — it's a molecule.

```purescript
-- This is an atom (cannot decompose further)
type Pixel = Int  -- Bounded 0 to MAX_INT

-- This is a molecule (composed of atoms)
type Point2D = { x :: Pixel, y :: Pixel }

-- This is a compound (composed of molecules)
type Rectangle = { position :: Point2D, size :: Size2D }
```

**2. Atoms must be bounded**

Every atom must have defined minimum, maximum, and behavior at boundaries.

```purescript
-- Bounded with wraparound
type Hue = BoundedInt 0 359  -- 360 wraps to 0

-- Bounded with clamping
type Opacity = BoundedNumber 0.0 1.0  -- 1.1 clamps to 1.0

-- Bounded with explicit error
type Index = BoundedInt 0 (length - 1)  -- Out of bounds is type error
```

**3. Atoms must be universal**

An atom should apply to ALL categories, not just one. If it only applies to
audio, it goes in the Audio pillar. If it applies to audio AND video AND
animation, it goes in Temporal.

**4. Atoms must be deterministic**

Same input = same output. Always. No randomness without explicit seed.

```purescript
-- Deterministic
noise :: Seed -> Number -> Number -> Number  -- Same seed+coords = same value

-- NOT deterministic (forbidden)
random :: Unit -> Number  -- Different every call
```

**5. Atoms must be serializable**

Every atom can be converted to bytes and back without loss.

```purescript
class Serializable a where
  serialize :: a -> ByteString
  deserialize :: ByteString -> Either Error a
  
  -- Roundtrip law
  -- deserialize (serialize a) == Right a
```

**The test for universality:**

When you add an atom, ask:
- Can Ableton use this? 
- Can After Effects use this?
- Can a hospital dashboard use this?
- Can a game use this?

If the answer is "no" for any major category, the atom is too specific.
Move it to a domain module, not the universal Schema.

────────────────────────────────────────────────────────────────────────────────

**The Universal Design Language is not an aspiration. It is an engineering
requirement.**

When agents operate at billion-scale, they cannot learn N different languages
for N different application types. They need ONE language that expresses
EVERYTHING.

Hydrogen's Schema is that language.

Build it correctly. Build it completely. Build it universally.

────────────────────────────────────────────────────────────────────────────────

                                                       — Opus 4.5 // 2026-02-25

