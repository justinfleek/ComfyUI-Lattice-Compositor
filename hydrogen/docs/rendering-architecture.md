# Hydrogen Rendering Architecture

**Pure Data at Every Layer**

This document defines the complete rendering stack for Hydrogen — from total
display pixels down to individual atoms. Every layer is pure data. No CSS. No
JavaScript. No browser required.

---

## The Stack (Bottom to Top)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              WORLD MODEL                                     │
│         Interactive game spaces, 3D environments, simulations               │
│                    (can live inside any Viewport)                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                               ELEMENTS                                       │
│     Compounds composed from Molecules composed from Atoms                    │
│  ColorPicker, Calendar, DataGrid, Button, Text, Icon, Animation...         │
├─────────────────────────────────────────────────────────────────────────────┤
│                              VIEWPORTS                                       │
│            Containers that house Elements / World Models                     │
│      Shape, position, elevation, noise, triggers, interactions              │
├─────────────────────────────────────────────────────────────────────────────┤
│                               CANVAS                                         │
│                  Total display pixels of target device                       │
│                    The absolute rendering surface                            │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Layer 1: Canvas

**The absolute rendering surface.**

The Canvas represents the total pixel grid of the target display. It is the
foundation — the coordinate system against which everything else is positioned.

```purescript
-- | Canvas — the total display surface
-- |
-- | At billion-agent scale, a Canvas might be:
-- | - A phone screen (390 × 844 pixels)
-- | - A 4K monitor (3840 × 2160 pixels)  
-- | - A distributed display wall (15360 × 4320 pixels)
-- | - A headset viewport (per-eye: 2160 × 2160 pixels)
-- |
-- | The Canvas is pure data describing the target.
type Canvas =
  { size :: Size2D Pixel          -- Width × Height in device pixels
  , density :: DPR                -- Device pixel ratio (1.0, 2.0, 3.0...)
  , colorSpace :: ColorSpace      -- sRGB, DisplayP3, Rec2020, etc.
  , refreshRate :: Hertz          -- 60Hz, 120Hz, 144Hz, etc.
  , hdr :: Maybe HDRCapability    -- HDR metadata if supported
  }
```

**Key properties:**
- The Canvas does NOT know about DOM, browsers, or operating systems
- It is a pure description of the rendering target
- Multiple Canvases can exist (multi-monitor, VR, distributed)
- Canvas → GPU is the only place where "pixels hit reality"

---

## Layer 2: Viewports

**Containers that live ABOVE the Canvas.**

Viewports are the bento boxes — the modules, widgets, panels that organize
the display. Each Viewport:

- Has a **shape** (any geometry, not just rectangles)
- Has a **position** relative to Canvas or parent Viewport
- Has an **elevation** (z-depth above the Canvas plane)
- Contains **Elements** or **World Models**
- Has **interaction parameters** (hover behavior, elevation changes)
- Has **noise settings** for diffusion-model backgrounds
- Can be **animated** (Lottie, Rive, spring physics, path animations)

```purescript
-- | Viewport — a container above the Canvas
-- |
-- | Viewports are NOT HTML divs. They are pure data describing
-- | a region of the display with specific properties.
type Viewport msg =
  { id :: ViewportId                -- UUID5 deterministic identifier
  , shape :: Shape                  -- Rectangle, RoundedRect, Circle, Path...
  , bounds :: Bounds2D Pixel        -- Position and size relative to parent
  , elevation :: Elevation          -- Z-depth above canvas plane
  , cornerRadius :: Maybe CornerRadii
  , stroke :: Maybe Stroke          -- Border around the viewport
  , fill :: ViewportFill            -- Solid, gradient, noise, diffusion...
  , clip :: ClipBehavior            -- How children are clipped
  , children :: ViewportContent msg -- Elements, sub-viewports, or world model
  , interactions :: Array (Interaction msg)
  , animations :: Array Animation
  , triggers :: Array (Trigger msg) -- Events that affect other viewports
  }

-- | What a Viewport contains
data ViewportContent msg
  = Elements (Array (Element msg))       -- UI compounds
  | SubViewports (Array (Viewport msg))  -- Nested viewports
  | WorldModel WorldModelRef             -- Reference to a 3D/interactive space
  | Diffusion DiffusionSurface           -- Real-time generated content
  | Mixed                                -- Combination (layered)
      { elements :: Array (Element msg)
      , subViewports :: Array (Viewport msg)
      , worldModel :: Maybe WorldModelRef
      }
```

### Viewport Elevation

Elevation is literal — viewports exist at different heights above the Canvas.
When you hover over a viewport, it can rise. When you click, it can press down.

```purescript
-- | Elevation — distance above the canvas plane
-- |
-- | Not "z-index" (an arbitrary integer). Actual depth in pixels or millimeters.
-- | Affects shadows, parallax, and interaction priority.
type Elevation =
  { rest :: Distance              -- Resting elevation
  , hover :: Distance             -- Elevation on hover
  , pressed :: Distance           -- Elevation when pressed
  , transition :: SpringConfig    -- How elevation animates
  }

-- | Distance above canvas (bounded, positive)
newtype Distance = Distance (BoundedNumber 0.0 1000.0)
```

### Viewport Interactions

Viewports respond to pointer events, gestures, and triggers from other viewports.

```purescript
-- | Interaction — how a viewport responds to input
data Interaction msg
  = OnHover
      { elevationDelta :: Distance    -- Raise by this amount
      , scale :: Factor               -- Scale factor (1.0 = no change)
      , filter :: Maybe FilterEffect  -- Blur, brightness, etc.
      , msg :: Maybe msg              -- Optional message to emit
      }
  | OnPress
      { elevationDelta :: Distance    -- Usually negative (press down)
      , scale :: Factor
      , haptic :: Maybe HapticPattern
      , msg :: msg                    -- Message on press
      }
  | OnDrag DragConfig msg
  | OnGesture GestureType msg
  | OnTrigger TriggerId msg           -- Respond to external trigger
```

### Viewport Fill and Diffusion

A viewport's background can be anything — solid color, gradient, procedural
noise, or real-time diffusion model output.

```purescript
-- | ViewportFill — what fills the viewport background
data ViewportFill
  = Solid Color
  | Gradient GradientDef
  | Noise NoiseConfig                 -- Procedural noise texture
  | Diffusion DiffusionConfig         -- Real-time AI-generated content
  | Image ImageRef
  | Video VideoRef
  | Transparent

-- | DiffusionConfig — settings for real-time diffusion model rendering
-- |
-- | This allows a viewport background to be literally ANYTHING.
-- | "Turn a button background into anything in real time."
type DiffusionConfig =
  { model :: DiffusionModelRef        -- Which model to use
  , prompt :: PromptData              -- What to generate
  , seed :: NoiseSeed                 -- Deterministic seed
  , strength :: Ratio                 -- How much to diffuse (0 = keep, 1 = full)
  , steps :: Int                      -- Inference steps per frame
  , mask :: Maybe MaskData            -- Where to apply diffusion
  , controlNet :: Maybe ControlNetRef -- Pose, depth, edge guidance
  }
```

---

## Layer 3: Elements

**The composable UI atoms, molecules, and compounds.**

Elements live INSIDE Viewports. They are the actual UI components — buttons,
text, icons, sliders, color pickers, calendars, data grids.

Elements follow the atomic design pattern:
- **Atoms**: Primitive bounded values (Hue, Pixel, Opacity, FontWeight)
- **Molecules**: Combinations of atoms (HSL, Point2D, FontStyle)
- **Compounds**: Complex components (ColorPicker, DatePicker, DataGrid)

```purescript
-- | Element — pure data describing a UI component
-- |
-- | Elements are NOT DOM nodes. They are not virtual DOM.
-- | They are pure data that describes what should be rendered.
data Element msg
  = Text String
  | Element
      { tag :: ElementType            -- Button, Input, Container, etc.
      , attributes :: ElementAttributes msg
      , children :: Array (Element msg)
      }
  | Keyed
      { tag :: ElementType
      , attributes :: ElementAttributes msg
      , children :: Array (Tuple Key (Element msg))
      }
  | Lazy
      { thunk :: Unit -> Element msg
      , key :: String
      }
  | Animation AnimationElement msg    -- Lottie, Rive, path animation
  | Empty
```

### Element Ordering and Z-Stacking

Elements within a Viewport have their own ordering — draw order matters.

```purescript
-- | ElementAttributes — properties of an element
type ElementAttributes msg =
  { position :: Position              -- Absolute, relative, flex, grid
  , size :: Maybe Size2D
  , zOrder :: ZOrder                  -- Draw order within viewport
  , opacity :: Opacity
  , transform :: Maybe Transform2D
  , fill :: Maybe Fill
  , stroke :: Maybe Stroke
  , cornerRadius :: Maybe CornerRadii
  , shadow :: Maybe Shadow
  , blur :: Maybe Blur
  , interactions :: Array (ElementInteraction msg)
  , animations :: Array Animation
  , accessibility :: AccessibilityAttributes
  }

-- | ZOrder — draw order within a viewport (not CSS z-index)
-- |
-- | Bounded integer. Higher = drawn later = appears on top.
newtype ZOrder = ZOrder (BoundedInt 0 999)
```

### Lottie and Path Animations

Elements can be animated — Lottie JSON, Rive state machines, or raw path
animations with keyframes.

```purescript
-- | AnimationElement — an element that animates
data AnimationElement msg
  = Lottie LottieConfig msg           -- Lottie JSON animation
  | Rive RiveConfig msg               -- Rive state machine
  | PathAnimation PathAnimConfig msg  -- SVG path morphing
  | SpriteAnimation SpriteConfig msg  -- Sprite sheet
  | Keyframes KeyframeConfig msg      -- CSS-style keyframes (but pure data)

-- | LottieConfig — configuration for Lottie animation
type LottieConfig =
  { data :: LottieData                -- The animation data (pure JSON)
  , autoplay :: Boolean
  , loop :: LoopBehavior
  , speed :: PlaybackSpeed
  , direction :: PlayDirection
  , segment :: Maybe (Tuple Frame Frame)  -- Play specific segment
  , triggers :: Array LottieTrigger   -- Pause at frame, play on hover, etc.
  }
```

---

## Layer 4: World Models

**Interactive 3D spaces that can live inside any Viewport.**

A Viewport can contain a World Model — a complete 3D environment rendered
via WebGPU. This could be:

- A product configurator (rotate, zoom, customize)
- A game space (characters, physics, AI)
- A data visualization (3D scatter plots, network graphs)
- A simulation (molecular dynamics, fluid flow)
- An architectural walkthrough

```purescript
-- | WorldModel — a 3D interactive space
-- |
-- | World Models are NOT Unity or Unreal. They are pure data
-- | describing a scene graph, physics, and interactions.
type WorldModel =
  { id :: WorldModelId
  , scene :: SceneGraph               -- Nodes, transforms, geometries
  , camera :: Camera                  -- Perspective, orthographic, etc.
  , lights :: Array Light
  , materials :: MaterialLibrary
  , physics :: Maybe PhysicsWorld     -- Optional physics simulation
  , audio :: Maybe AudioGraph         -- Spatial audio
  , ai :: Maybe AIController          -- NPC behavior, pathfinding
  , interactions :: WorldInteractions -- How user interacts with world
  }

-- | SceneGraph — the 3D scene as pure data
type SceneGraph =
  { root :: SceneNode
  , renderSettings :: RenderSettings
  , environment :: Environment        -- Skybox, ambient, fog
  }

-- | SceneNode — a node in the scene graph
data SceneNode
  = Group
      { id :: NodeId
      , transform :: Transform3D
      , children :: Array SceneNode
      }
  | Mesh
      { id :: NodeId
      , transform :: Transform3D
      , geometry :: GeometryRef
      , material :: MaterialRef
      , animations :: Array Animation3D
      }
  | Instance
      { id :: NodeId
      , transform :: Transform3D
      , prototype :: SceneNodeRef
      }
```

---

## Data Flow

**Pure data flows down. Messages flow up.**

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            HASKELL BACKEND                                   │
│                         (business logic, state)                              │
│                                                                              │
│    State × Msg → State × [Cmd]                                              │
│    view :: State → Canvas                                                   │
└────────────────────────────────────┬────────────────────────────────────────┘
                                     │ Canvas data (pure)
                                     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                          PURESCRIPT LAYER                                    │
│                    (type-safe translation layer)                             │
│                                                                              │
│    Canvas → Array Viewport → Array Element → GPU Commands                   │
│                                                                              │
│    - Validates all bounds                                                    │
│    - Computes layouts (ILP constraints)                                      │
│    - Resolves animations (spring physics, keyframes)                        │
│    - Diffs against previous frame                                           │
│    - Emits GPU draw commands                                                │
└────────────────────────────────────┬────────────────────────────────────────┘
                                     │ GPU commands (pure data)
                                     ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            GPU RUNTIME                                       │
│                    (minimal interpreter, executes commands)                  │
│                                                                              │
│    - Reads GPU commands as pure data                                        │
│    - Creates/updates vertex buffers                                          │
│    - Runs shaders                                                            │
│    - Outputs pixels                                                          │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Message Flow (Up)

When a user interacts with an Element or Viewport, messages flow back up:

```
User taps button in Element
         │
         ▼
Element emits Msg
         │
         ▼
Viewport forwards Msg (possibly transforms it)
         │
         ▼
Canvas collects Msg
         │
         ▼
PureScript serializes Msg
         │
         ▼
Haskell update function receives Msg
         │
         ▼
New State produced → New Canvas data → cycle repeats
```

---

## Triggers Between Viewports

Viewports can trigger events in other viewports. This enables complex
interactions without coupling the viewports together.

```purescript
-- | Trigger — an event that affects another viewport
data Trigger msg
  = Trigger
      { id :: TriggerId
      , source :: ViewportId          -- Where the trigger originates
      , target :: ViewportId          -- Which viewport receives it
      , condition :: TriggerCondition -- When to fire
      , effect :: TriggerEffect       -- What happens
      , msg :: Maybe msg              -- Optional message to emit
      }

-- | TriggerCondition — when a trigger fires
data TriggerCondition
  = OnSourceHover
  | OnSourcePress
  | OnSourceDrag DragPhase
  | OnSourceAnimationComplete AnimationId
  | OnSourceValueChange PropertyPath
  | OnTime Timestamp
  | OnIntersection IntersectionConfig -- When viewports overlap

-- | TriggerEffect — what happens when trigger fires
data TriggerEffect
  = SetElevation Distance
  | SetOpacity Opacity
  | SetTransform Transform2D
  | PlayAnimation AnimationId
  | PauseAnimation AnimationId
  | SetFill ViewportFill
  | ApplyFilter FilterEffect
  | SendMessage                       -- Use the Msg parameter
```

---

## Noise and Diffusion Integration

Every Viewport can have procedural noise or real-time diffusion model output
as its background. This is configured as pure data.

```purescript
-- | NoiseConfig — procedural noise texture
type NoiseConfig =
  { noiseType :: NoiseType            -- Perlin, Simplex, Worley, FBM
  , frequency :: NoiseFrequency
  , amplitude :: NoiseAmplitude
  , octaves :: NoiseOctaves
  , seed :: NoiseSeed
  , colorMapping :: ColorMapping      -- How noise values map to colors
  , animated :: Maybe NoiseAnimation  -- Evolving noise over time
  }

-- | DiffusionSurface — real-time AI-generated content
-- |
-- | The viewport becomes a window into whatever the model generates.
-- | A button background could be "flowing lava" or "calm water"
-- | or "abstract art in the style of Kandinsky" — all in real time.
type DiffusionSurface =
  { model :: DiffusionModelRef
  , prompt :: PromptData
  , negativePrompt :: Maybe PromptData
  , seed :: NoiseSeed                 -- Deterministic
  , scheduler :: SchedulerType        -- DDPM, DDIM, Euler, etc.
  , steps :: InferenceSteps
  , guidance :: GuidanceScale
  , controlNets :: Array ControlNetConfig
  , inpainting :: Maybe InpaintConfig -- Mask regions for regeneration
  , latentBlending :: Maybe BlendConfig -- Blend multiple prompts
  , frameCoherence :: CoherenceConfig -- Temporal consistency for animation
  }
```

---

## Why This Architecture?

### 1. Pure Data at Every Layer

Every layer — Canvas, Viewport, Element, WorldModel — is pure data.
No effects. No state. No side effects. This means:

- **Deterministic**: Same input → same output, always
- **Serializable**: Send over network, save to disk, diff, cache
- **Testable**: Property tests at every layer
- **Diffable**: Structural diff for efficient updates

### 2. No Browser Required

The browser is ONE possible runtime. The same pure data can be interpreted by:

- WebGPU runtime in browser
- Native GPU runtime on desktop/mobile
- Distributed renderer across a cluster
- Headless renderer for SSR/SSG
- Another AI agent composing UI

### 3. Billion-Agent Scale

When billions of agents are creating and composing UI:

- **No string parsing**: HSL is three atoms, not "hsl(210, 50%, 50%)"
- **No cascade chaos**: No CSS specificity wars
- **No ambiguity**: Every value is bounded with explicit behavior
- **Deterministic identity**: UUID5 from content = same UI = same hash

### 4. Everything Composes

A ColorPicker is a compound of:
- Hue slider (molecule: Slider + Hue atom)
- Saturation/Lightness plane (molecule: 2D picker + SL atoms)
- Preview swatch (molecule: Rectangle + HSL molecule)
- Input fields (molecules: Input + Channel atoms)

Each piece is independently:
- Usable
- Styleable
- Animatable
- Testable
- Serializable

---

## Implementation Status

| Layer | Status | Location |
|-------|--------|----------|
| Canvas | Defined | `Hydrogen.Schema.Dimension` |
| Viewport | Needs creation | `Hydrogen.Viewport` |
| Element | Complete | `Hydrogen.Render.Element` |
| WorldModel | Partial | `Hydrogen.GPU.Scene3D` |
| Triggers | Needs creation | `Hydrogen.Viewport.Trigger` |
| Noise | Complete | `Hydrogen.Schema.Material.Noise` |
| Diffusion | Partial | `Hydrogen.GPU.Diffusion` |

### Next Steps

1. **Create `Hydrogen.Viewport`** — the Viewport layer with pure data types
2. **Create `Hydrogen.Viewport.Trigger`** — inter-viewport communication
3. **Integrate Viewport → GPU pipeline** — viewport data to draw commands
4. **Add Lottie/Rive types** — animation as pure data
5. **Add DiffusionSurface types** — real-time generation config

---

```
                                                         — Opus 4.5 // 2026-02-27
```
