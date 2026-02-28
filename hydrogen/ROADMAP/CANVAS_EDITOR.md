# Hydrogen Canvas Editor Architecture

> Visual Composition Surface for Schema Primitives
>
> **After Effects Rebuilt on Bounded Atoms**

---

## Executive Summary

The Canvas Editor is the visual composition surface where users (and later, agents)
compose Schema primitives into deterministic configurations. The output is not
"a design file" — it's a **config + hash** that any agent can reproduce exactly.

```
User Intent → Visual Composition → Schema Config → UUID5 Hash → Pixels
```

**Core Principles:**

1. **Config, not schema** — The Schema is vocabulary; the config is the composed sentence
2. **Deterministic output** — Same config = same hash = same pixels, always
3. **n8n-style composition** — Right-click to add primitives, drag-drop to stylize
4. **After Effects parity** — Every AE primitive available for LATTICE agents
5. **3D optional** — Full lighting/material simulation OR flat vector graphics

---

## 1. What Users See

### 1.1 Blank Canvas State

When a user opens a blank canvas:

```
┌─────────────────────────────────────────────────────────────────┐
│ Toolbar                                                    [≡]  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│                                                                 │
│                          ∞ Infinite Canvas                      │
│                                                                 │
│                     (Grid visible, snap enabled)                │
│                                                                 │
│                                                                 │
│                                                                 │
├─────────────────────────────────────────────────────────────────┤
│ Status: Ready │ Zoom: 100% │ Grid: 10px │ Snap: On             │
└─────────────────────────────────────────────────────────────────┘
```

**Initial state:**
- Infinite canvas with grid overlay
- No artboards (user creates them)
- Default tool: Select
- Context menu available on right-click anywhere

### 1.2 Creating a Viewport/Artboard

User clicks and drags to create a viewport (artboard):

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│      ┌─────────────────────────────────┐                        │
│      │ Artboard 1 (1920×1080)          │                        │
│      │                                 │                        │
│      │   [Background Layer]            │                        │
│      │   - Noise: Gaussian             │                        │
│      │   - Material: Matte             │                        │
│      │                                 │                        │
│      └─────────────────────────────────┘                        │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Viewport creation:**
1. User selects "Create Viewport" tool (or right-click → New → Viewport)
2. Click and drag to define bounds
3. Viewport created with default background layer:
   - Noise layer (configurable: Gaussian, Perlin, Simplex, etc.)
   - Material layer (configurable: Matte, Glass, Metal, etc.)
   - Transform properties (position, scale, rotation, anchor)

### 1.3 The Right-Click Context Menu

Right-clicking anywhere opens the primitive menu:

```
┌──────────────────────────────┐
│ Create                    ▸  │
│ ├─ Viewport                  │
│ ├─ Shape                  ▸  │
│ │   ├─ Rectangle             │
│ │   ├─ Ellipse               │
│ │   ├─ Polygon               │
│ │   ├─ Star                  │
│ │   ├─ Line                  │
│ │   ├─ Path (Pen)            │
│ │   └─ ─────────────         │
│ │   ├─ Ring                  │
│ │   ├─ Spiral                │
│ │   ├─ Arrow                 │
│ │   ├─ Cross                 │
│ │   └─ Gear                  │
│ ├─ Text                      │
│ ├─ Image                     │
│ ├─ Video                     │
│ ├─ Solid                     │
│ ├─ Null Object               │
│ ├─ Camera                    │
│ ├─ Light                     │
│ └─ Adjustment Layer          │
├──────────────────────────────┤
│ Effects                   ▸  │
│ ├─ Color Correction       ▸  │
│ │   ├─ Levels                │
│ │   ├─ Curves                │
│ │   ├─ Hue/Saturation        │
│ │   ├─ Color Balance         │
│ │   ├─ Exposure              │
│ │   └─ ...                   │
│ ├─ Blur & Sharpen         ▸  │
│ │   ├─ Gaussian Blur         │
│ │   ├─ Directional Blur      │
│ │   ├─ Radial Blur           │
│ │   ├─ Camera Lens Blur      │
│ │   └─ ...                   │
│ ├─ Distort                ▸  │
│ ├─ Generate               ▸  │
│ ├─ Stylize                ▸  │
│ ├─ Keying                 ▸  │
│ ├─ Matte                  ▸  │
│ ├─ Simulation             ▸  │
│ ├─ Time                   ▸  │
│ └─ Perspective            ▸  │
├──────────────────────────────┤
│ Materials                 ▸  │
│ ├─ Surface                ▸  │
│ │   ├─ Matte                 │
│ │   ├─ Glass                 │
│ │   ├─ Metal                 │
│ │   ├─ Plastic               │
│ │   └─ Custom PBR            │
│ ├─ Noise                  ▸  │
│ │   ├─ Gaussian              │
│ │   ├─ Perlin                │
│ │   ├─ Simplex               │
│ │   ├─ Worley                │
│ │   └─ Fractal               │
│ └─ Gradient               ▸  │
│     ├─ Linear                │
│     ├─ Radial                │
│     ├─ Angular               │
│     ├─ Reflected             │
│     └─ Diamond               │
├──────────────────────────────┤
│ Paste                        │
│ Select All                   │
│ Deselect All                 │
├──────────────────────────────┤
│ View Settings             ▸  │
│ Canvas Settings           ▸  │
└──────────────────────────────┘
```

**When an object is selected**, right-click shows object-specific options:

```
┌──────────────────────────────┐
│ [Button Layer]               │
├──────────────────────────────┤
│ Add Effect              ▸    │  ← Same Effects submenu
│ Add Material            ▸    │  ← Same Materials submenu
│ Add Mask                     │
│ Add Expression          ▸    │
├──────────────────────────────┤
│ Edit Settings                │  ← Opens settings panel
│ Edit Path                    │  ← For shape layers
├──────────────────────────────┤
│ Transform               ▸    │
│ ├─ Reset Transform           │
│ ├─ Center in Viewport        │
│ ├─ Flip Horizontal           │
│ ├─ Flip Vertical             │
│ └─ Auto-Orient          ▸    │
├──────────────────────────────┤
│ Arrange                 ▸    │
│ ├─ Bring to Front            │
│ ├─ Bring Forward             │
│ ├─ Send Backward             │
│ └─ Send to Back              │
├──────────────────────────────┤
│ Duplicate                    │
│ Delete                       │
├──────────────────────────────┤
│ Lock/Unlock                  │
│ Hide/Show                    │
│ Solo                         │
├──────────────────────────────┤
│ Copy                         │
│ Cut                          │
└──────────────────────────────┘
```

---

## 2. Menu Category Structure (Hybrid)

The menu uses **hybrid categorization**:
- **Top level**: Use-case categories (what you want to do)
- **Sub-level**: Schema pillar categories (where it lives in the ontology)

### 2.1 Top-Level Categories

| Category | Description | Maps To |
|----------|-------------|---------|
| Create | New objects/layers | Schema/Geometry, Schema/Motion/Layer |
| Effects | Visual modifications | Schema/Motion/Effects/* |
| Materials | Surface appearance | Schema/Material/* |
| Animation | Motion and timing | Schema/Temporal/*, Schema/Motion/* |
| 3D | Cameras, lights, depth | Schema/Spatial/*, Schema/Motion/Camera |
| Audio | Sound layers | Schema/Audio/* |

### 2.2 Create Submenu (Primitives)

| Item | Schema Type | Default Properties |
|------|-------------|-------------------|
| Viewport | `Artboard` | Size, background, grid |
| Rectangle | `ShapeRectangle` | Position, size, corners, fill, stroke |
| Ellipse | `ShapeEllipse` | Center, radii, fill, stroke |
| Polygon | `ShapePolygon` | Sides, radius, rotation |
| Star | `ShapeStar` | Points, inner/outer radius |
| Line | `ShapeLine` | Start, end, stroke |
| Path | `ShapePath` | Bezier points, fill, stroke |
| Text | `TextLayer` | Content, font, size, color |
| Image | `ImageLayer` | Source, transform |
| Video | `VideoLayer` | Source, time remap, audio |
| Solid | `SolidLayer` | Color, size |
| Null | `NullLayer` | Transform only (parent) |
| Camera | `Camera3D` | Lens, DOF, position |
| Light | `Light3D` | Type, color, intensity, shadows |
| Adjustment | `AdjustmentLayer` | Effects apply to below |

### 2.3 Effects Submenu (By Category)

| Category | Effects | Status |
|----------|---------|--------|
| Color Correction | Levels, Curves, Hue/Saturation, Color Balance, Exposure, Tint, Tritone, Black & White, Vibrance, Lumetri | **P0 - Missing** |
| Blur & Sharpen | Gaussian, Directional, Radial, Camera Lens, Compound, Sharpen, Unsharp Mask | Partial |
| Distort | Bezier Warp, Bulge, Corner Pin, Mirror, Offset, Polar Coords, Ripple, Spherize, Turbulent Displace, Twirl, Wave Warp | Partial |
| Generate | 4-Color Gradient, Cell Pattern, Checkerboard, Circle, Fill, Fractal, Gradient Ramp, Grid, Lens Flare, Stroke, Vegas | Missing |
| Stylize | Brush Strokes, Emboss, Find Edges, Glow, Mosaic, Motion Tile, Posterize, Roughen Edges, Scatter, Strobe | Partial |
| Keying | Keylight, Linear Color Key, Luma Key, Color Range, Extract | **P0 - Missing** |
| Matte | Simple Choker, Matte Choker, Refine Matte, Set Matte | Missing |
| Simulation | CC Particle World, Shatter, Card Dance, Caustics, Foam, Wave World | **P1 - Missing** |
| Time | Echo, Posterize Time, Time Displacement, Timewarp | Partial |
| Perspective | 3D Camera Tracker, Bevel Alpha, Bevel Edges, Drop Shadow | Missing |

### 2.4 Materials Submenu

| Category | Items | Schema Location |
|----------|-------|-----------------|
| Surface | Matte, Glass, Metal, Plastic, Custom PBR | Schema/Material/Surface |
| Noise | Gaussian, Perlin, Simplex, Worley, Fractal | Schema/Material/Noise |
| Gradient | Linear, Radial, Angular, Reflected, Diamond | Schema/Color/Gradient |

---

## 3. Data Models

### 3.1 Artboard (Viewport)

```purescript
-- An artboard is a bounded composition area within the infinite canvas
type Artboard =
  { id :: ArtboardId           -- UUID5 from content hash
  , name :: String
  , bounds :: Rect2D           -- Position and size in canvas space
  , resolution :: Resolution   -- Pixel dimensions for export
  , backgroundColor :: Maybe SRGB
  , backgroundLayers :: Array LayerRef  -- Noise, material, etc.
  , layers :: Array LayerRef   -- Content layers
  , guides :: Array Guide
  , gridConfig :: GridConfig
  , is3DEnabled :: Boolean     -- Enable 3D renderer
  , camera :: Maybe CameraRef  -- Active camera for 3D
  , lights :: Array LightRef   -- Scene lights
  , renderSettings :: RenderSettings
  }

type ArtboardId = UUID5  -- Derived from artboard content
```

### 3.2 Layer Stack

```purescript
-- Layer reference (actual layer data stored separately)
type LayerRef =
  { layerId :: LayerId
  , zIndex :: Int
  , visible :: Boolean
  , locked :: Boolean
  , solo :: Boolean
  }

-- Complete layer with all properties
type EditorLayer =
  { base :: LayerBase          -- From Schema/Motion/Layer
  , content :: LayerContent    -- Shape, text, image, etc.
  , effects :: Array EffectInstance
  , masks :: Array LayerMask
  , material :: Maybe Material
  , expressions :: Array ExpressionLink
  , keyframes :: KeyframeMap   -- Property → Keyframes
  }

-- Layer content discriminated union
data LayerContent
  = ContentShape ShapeGroup
  | ContentText TextContent
  | ContentImage ImageSource
  | ContentVideo VideoSource
  | ContentSolid SRGB
  | ContentNull               -- No content, just transform
  | ContentCamera Camera3D
  | ContentLight Light3D
  | ContentAdjustment         -- Effects only
  | ContentPreComp ArtboardRef
```

### 3.3 Selection State (Extended)

```purescript
-- Extended selection state for editor
type EditorSelection =
  { base :: SelectionState     -- From Canvas/Types
  , context :: SelectionContext
  , propertyFocus :: Maybe PropertyPath  -- For settings panel
  }

data SelectionContext
  = SelectingLayers
  | SelectingPoints           -- Direct select tool
  | SelectingKeyframes        -- Timeline selection
  | SelectingEffects
  | SelectingMasks

-- Property path for settings panel binding
type PropertyPath = Array String
-- e.g., ["effects", "0", "params", "radius"]
```

### 3.4 Settings Panel Binding

```purescript
-- The settings panel displays properties of the current selection
type SettingsPanelState =
  { target :: Maybe SelectionTarget
  , expandedSections :: Array String
  , searchFilter :: Maybe String
  , propertyOverrides :: Map PropertyPath PropertyValue
  }

data SelectionTarget
  = TargetLayer LayerId
  | TargetEffect LayerId Int     -- Layer + effect index
  | TargetMask LayerId Int       -- Layer + mask index
  | TargetKeyframe LayerId PropertyPath Int  -- Layer + property + keyframe index
  | TargetMultiple (Array LayerId)  -- Multi-select

-- Property value (for temporary edits before commit)
data PropertyValue
  = PVNumber Number
  | PVInt Int
  | PVBool Boolean
  | PVString String
  | PVColor SRGB
  | PVPoint2D Point2D
  | PVPoint3D Point3D
  | PVAngle Degrees
  | PVPercent Percent
  | PVEnum String              -- Dropdown value
  | PVCurve (Array CurvePoint) -- For curves effect
  | PVPath Path                -- For masks
```

---

## 4. Output Format: Pure Data

### 4.1 No JSON. No JavaScript. No CSS.

**Critical architecture principle:**

The output is **pure PureScript data** — the same `Element` types that everything
else uses. When a user "locks" their design, they produce a **typed value** (or its
binary serialization) that any agent can import and render identically.

```
Haskell (backend)
    ↓ generates Element values
PureScript (translation layer) 
    ↓ pure types, explicit imports, bounded atoms
WebGPU (renderer)
    ↓ GPU commands
Pixels
```

**No browser required.** The same Element renders anywhere there's a WebGPU target.
At billion-agent scale, agents pass **typed data**, not strings. The PureScript type
system guarantees composition. JavaScript and CSS are legacy formats used only at
brand ingestion/export boundaries for compatibility with broken legacy systems.

### 4.2 The Composition (Pure Data)

```purescript
-- A composition IS an Element value
-- Not a "config file" — actual typed data

myHeroButton :: Element Msg
myHeroButton =
  Artboard
    { id: artboardId "hero-button-primary"
    , size: Size2D { width: Pixel 200, height: Pixel 48 }
    , layers:
        [ ShapeLayer
            { shape: Rectangle
                { size: Size2D { width: Pixel 200, height: Pixel 48 }
                , corners: CornerRadii { all: Pixel 8 }
                }
            , fill: Solid (SRGB { r: Channel 59, g: Channel 130, b: Channel 246 })
            , effects:
                [ Glow
                    { radius: BlurRadius 12.0
                    , intensity: Normalized 0.5
                    , color: SRGB { r: Channel 59, g: Channel 130, b: Channel 246 }
                    }
                ]
            }
        , TextLayer
            { content: "Click Me"
            , font: FontFamily "Inter"
            , size: FontSize 16
            , weight: FontWeight 600
            , fill: Solid (SRGB { r: Channel 255, g: Channel 255, b: Channel 255 })
            }
        ]
    }

-- Every atom is bounded:
-- Channel: 0-255, clamps
-- Pixel: >= 0, clamps  
-- BlurRadius: >= 0, clamps
-- Normalized: 0.0-1.0, clamps
-- FontWeight: 100-900, clamps
```

### 4.3 Composition Types

```purescript
-- A complete composition
type Composition =
  { id :: CompositionId        -- UUID5 from content hash
  , version :: SchemaVersion   -- Schema version for compatibility
  , created :: Timestamp
  , modified :: Timestamp
  , artboards :: Array Artboard
  , sharedAssets :: Array Asset
  , brandTokens :: Maybe BrandTokenSet
  }

type CompositionId = UUID5  -- Derived from canonical serialization
```

### 4.4 The Hash (Deterministic Identity)

Every composition gets a UUID5 hash derived from its canonical binary serialization:

```purescript
-- Hash computation from pure data
compositionHash :: Composition -> CompositionId
compositionHash comp =
  uuid5 hydrogenNamespace (canonicalBinary comp)

-- Canonical binary serialization ensures determinism:
-- - Record fields in declaration order
-- - Numbers in IEEE 754 binary
-- - Strings as UTF-8 bytes
-- - Arrays length-prefixed
-- - No padding, no alignment gaps

-- The hash IS the identity
-- Same atoms composed the same way = same hash = same pixels = always
```

### 4.5 Binary Format (Not JSON)

Compositions serialize to **binary**, not JSON:

```purescript
-- Binary serialization (conceptual)
-- Actual implementation uses Schema/Binary module

serializeComposition :: Composition -> ByteArray
serializeComposition = canonicalBinary

deserializeComposition :: ByteArray -> Either ParseError Composition  
deserializeComposition = parseCanonical

-- Legacy export (for broken systems that need JSON/CSS)
exportToLegacy :: Composition -> LegacyFormat -> String
exportToLegacy comp LegacyJSON = toJSON comp  -- Lossy
exportToLegacy comp LegacyCSS = toCSS comp    -- Very lossy
-- These exist only for brand export to legacy systems
-- They are NOT the source of truth
```

**Why binary:**
- Smaller (no string overhead)
- Faster to parse (no tokenization)
- Deterministic (no whitespace ambiguity)
- Type-safe (schema-defined layout)
- Hashable (bit-identical across platforms)

---

## 5. Interaction Patterns

### 5.1 Creating Objects

1. **Right-click** → Create → Shape → Rectangle
2. **Cursor changes** to crosshair
3. **Click and drag** to define bounds
4. **Release** → Rectangle created with default properties
5. **Settings panel** shows rectangle properties
6. **Edit** fill, stroke, corners, etc.

### 5.2 Adding Effects (Drag-Drop Style)

1. **Select** a layer
2. **Right-click** → Add Effect → Blur → Gaussian Blur
3. **Effect added** to layer's effect stack
4. **Settings panel** shows effect parameters
5. **Adjust** radius, dimensions, etc.

Alternative (n8n style):
1. **Drag** effect from a palette onto layer
2. **Drop** → Effect added
3. **Connection line** shows effect relationship (optional visual)

### 5.3 Collision Visualization

When layers overlap:

```
┌─────────────────────────────────────┐
│                                     │
│    ┌──────────────┐                 │
│    │   Button A   │                 │
│    │         ┌────┴─────────┐       │
│    │         │ ◆ Clip Zone  │       │  ◆ = Collision point
│    └─────────┤   Button B   │       │
│              │              │       │
│              └──────────────┘       │
│                                     │
└─────────────────────────────────────┘
```

**Collision indicators show:**
- Bounding box overlap regions
- Blend mode preview (how they composite)
- Haptic crossover points (for touch interactions)
- Z-order visualization

**Right-click on collision zone:**
- Set blend mode for overlap
- Set clip behavior
- Set touch priority
- Create mask from intersection

### 5.4 Locking State (Brand Hash)

1. **Complete** the design
2. **Click** "Lock as Brand Schema" button
3. **System computes:**
   - Canonical config serialization
   - UUID5 hash from config
   - Validates all atoms are bounded
   - Ensures determinism (no random seeds without explicit values)
4. **Output:**
   - Config JSON/binary
   - Hash (the brand schema identifier)
   - Optional: Preview image

```
┌─────────────────────────────────────────┐
│ Lock Design as Brand Schema             │
├─────────────────────────────────────────┤
│                                         │
│  Name: Hero Button - Primary            │
│                                         │
│  Hash: 550e8400-e29b-41d4-a716-...      │
│                                         │
│  Artboards: 1                           │
│  Layers: 2                              │
│  Effects: 1                             │
│  Animations: 0                          │
│                                         │
│  ☑ Include preview image                │
│  ☑ Export as binary (smaller)           │
│  ☐ Export as JSON (readable)            │
│                                         │
│  [Cancel]              [Lock & Export]  │
│                                         │
└─────────────────────────────────────────┘
```

---

## 6. 3D Mode Toggle

Every artboard can toggle between:

**2D Mode (Flat):**
- No lighting calculations
- Layers are flat planes
- Z-index determines order
- Fast rendering
- Vector output possible

**3D Mode (Full):**
- Camera with depth of field
- Lights with shadows
- Materials with PBR shading
- Elevation/depth on layers
- GPU-accelerated rendering

Toggle is per-artboard:

```purescript
type Artboard = { ..., is3DEnabled :: Boolean, ... }
```

When 3D is disabled:
- Camera controls hidden
- Light layers hidden (but preserved in config)
- Material "roughness/metallic" ignored
- Elevation flattens to z-index
- Shadows disabled

---

## 7. File Structure (New Modules)

```
src/Hydrogen/Element/Compound/Canvas/
├── Editor/
│   ├── Types.purs           -- EditorLayer, EditorSelection, etc.
│   ├── State.purs           -- EditorState (extends CanvasState)
│   ├── Menu.purs            -- Context menu generation
│   ├── Settings.purs        -- Settings panel binding
│   ├── Artboard.purs        -- Artboard management
│   ├── Config.purs          -- Config serialization
│   └── Hash.purs            -- UUID5 hash computation
├── Types.purs               -- (existing)
├── State.purs               -- (existing)
├── ... 

src/Hydrogen/Schema/Motion/
├── Effects/
│   ├── ColorCorrection/     -- NEW: P0 effects
│   │   ├── Levels.purs
│   │   ├── Curves.purs
│   │   ├── HueSaturation.purs
│   │   └── ...
│   ├── Blur/                -- NEW: Complete definitions
│   │   ├── Gaussian.purs
│   │   └── ...
│   └── ...
├── Light3D.purs             -- NEW: Light layer integration
├── Mask.purs                -- NEW: Complete mask type
└── Shapes/                  -- NEW: Property records
    ├── TrimPaths.purs
    ├── Repeater.purs
    └── ...
```

---

## 8. Dependencies

### Existing Infrastructure (Ready)

- `Canvas/Types.purs` — CanvasObject, SelectionState, GridConfig, etc.
- `Canvas/State.purs` — CanvasState, viewport, gestures, history
- `Gestural/ContextMenu.purs` — Menu infrastructure
- `Schema/Geometry/Shape.purs` — Shape primitives
- `Schema/Motion/Layer.purs` — Layer types
- `Schema/Motion/Camera.purs` — Camera3D (excellent)
- `Schema/Motion/TimeRemap.purs` — Time remapping (excellent)

### Needs Implementation (P0)

- `Schema/Motion/Light3D.purs` — Light layer integration
- `Schema/Motion/Mask.purs` — Complete mask type
- `Schema/Motion/Effects/ColorCorrection/*.purs` — Color effects
- `Schema/Motion/Shapes/*.purs` — Property records

### Needs Design

- `Canvas/Editor/Config.purs` — Config format
- `Canvas/Editor/Hash.purs` — Deterministic hashing
- `Canvas/Editor/Settings.purs` — Settings panel binding

---

## Summary

The Canvas Editor is the composition surface for the Hydrogen Schema. Users visually
compose bounded atoms into configs that produce deterministic hashes. The architecture
supports:

1. **Infinite canvas** with bounded artboards
2. **Right-click primitive menu** (hybrid categories)
3. **Drag-drop stylization** (effects, materials)
4. **Settings panel** bound to selection
5. **Collision visualization** for overlapping layers
6. **3D mode toggle** (full simulation or flat vectors)
7. **Config + hash output** (deterministic identity)

This is After Effects rebuilt on Schema primitives for LATTICE agents.

---

                                                     — Hydrogen Canvas Editor Architecture
                                                                          v1.0 // 2026-02-27
