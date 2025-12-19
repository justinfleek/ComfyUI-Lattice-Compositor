# Node-Based Timeline Specification

## Overview

The Weyl timeline uses a **node graph paradigm** where layers, effects, and modifiers are represented as nodes that connect to timeline clips. This combines the familiar timeline metaphor with the flexibility of node-based compositing.

## Core Concepts

### 1. Timeline Clips (Base Nodes)
Timeline clips represent media or generated content with duration.

```
┌────────────────────────────────────────┐
│  📺 Video Clip                         │
│  ├─ In: 0:00  Out: 5:00               │
│  └─ Source: scene_01.mp4              │
│                                        │
│  [○ Input]                [Output ○]   │
└────────────────────────────────────────┘
```

**Clip Types:**
- Video Clip
- Audio Clip
- Image Clip
- Solid Color
- Text (generated)
- Shape (generated)
- Particle System (generated)
- Nested Composition

### 2. Parameter Nodes
Parameter nodes modify properties of connected clips.

```
┌─────────────────────────┐
│  ⚙️ Transform           │
│  ├─ Position: 960, 540 │
│  ├─ Scale: 100%        │
│  ├─ Rotation: 0°       │
│  └─ Anchor: center     │
│                        │
│  [○ In]    [Out ○]     │
└─────────────────────────┘
```

**Parameter Node Types:**
- Transform (position, scale, rotation)
- Opacity / Blend Mode
- Color Correction
- Time Remap
- Audio Levels

### 3. Effect Nodes
Effect nodes process the visual output of connected clips.

```
┌─────────────────────────┐
│  ✨ Gaussian Blur       │
│  ├─ Radius: 10px       │
│  └─ Quality: High      │
│                        │
│  [○ In]    [Out ○]     │
└─────────────────────────┘
```

**Effect Categories:**
- Blur (Gaussian, Motion, Radial, Zoom)
- Color (Curves, HSL, Tint, Grade)
- Stylize (Glow, Shadow, Stroke)
- Distort (Bulge, Twirl, Wave)
- Generate (Gradient, Noise, Checkerboard)

### 4. Modifier Nodes
Modifier nodes control how parameters animate over time.

```
┌─────────────────────────┐
│  🔄 Jitter              │
│  ├─ Frequency: 2       │
│  ├─ Amplitude: 10      │
│  └─ Octaves: 3         │
│                        │
│  [○ Target]  [Value ○] │
└─────────────────────────┘
```

**Modifier Types:**
- Jitter (wiggle)
- Loop (repeat after/before)
- Spring (elastic)
- Audio Reactive
- Expression

---

## Connection Types

### Visual Flow (Thick Lines)
Visual data flows through thick gradient lines.

```
[Video] ═══════════════► [Blur] ═══════════════► [Output]
```

### Parameter Links (Thin Lines)
Parameter modifications use thin colored lines.

```
                    ┌──────────────┐
                    │ Transform    │
                    └──────┬───────┘
                           │ (thin line)
                           ▼
[Video] ═══════════════════════════════════► [Output]
```

### Modifier Connections (Dashed Lines)
Modifiers connect with dashed lines to parameters.

```
┌─────────┐
│ Jitter  │╌╌╌╌╌╌╌╌╌╌╌╌┐
└─────────┘            │
                       ▼
          ┌──────────────┐
          │ Position: X  │
          └──────────────┘
```

---

## Timeline View

### Collapsed View (Standard Timeline)
In collapsed view, connections are shown as subtle curves between tracks.

```
│ 0s   │ 1s   │ 2s   │ 3s   │ 4s   │ 5s   │
├──────┴──────┴──────┴──────┴──────┴──────┤
│  ╭──────────────────────────────╮        │  Video
│  │ 📺 Scene 01                  │        │
│  ╰──────────────────────────────╯        │
│           ╲                              │
│            ╲ (bezier connection)         │
│             ╲                            │
│  ╭───────────╲──────────────────╮        │  Effect
│  │ ✨ Blur    ▼                 │        │
│  ╰──────────────────────────────╯        │
│                    ╲                     │
│  ╭──────────────────╲───────────╮        │  Text
│  │ T "Welcome"       ▼          │        │
│  ╰──────────────────────────────╯        │
```

### Expanded View (Node Graph)
Expanding a track reveals its full node graph.

```
┌─ Video Track ─────────────────────────────────────────────┐
│                                                           │
│   ┌──────────┐      ┌───────────┐      ┌──────────┐     │
│   │ 📺 Video │═════►│ Transform │═════►│ ✨ Blur  │═══► │
│   └──────────┘      └─────┬─────┘      └──────────┘     │
│                           │                              │
│                     ┌─────┴─────┐                        │
│                     │ 🔄 Jitter │                        │
│                     │ (position)│                        │
│                     └───────────┘                        │
│                                                           │
└───────────────────────────────────────────────────────────┘
```

---

## Stacking Behavior

### Effect Stacking
Multiple effects chain in order (top to bottom = left to right in graph).

```
Timeline View:          Node Graph:
┌─────────────┐
│ 📺 Video    │         [Video]═►[Blur]═►[Glow]═►[Output]
├─────────────┤
│ ✨ Blur     │───┐
├─────────────┤   │
│ ✨ Glow     │───┘
└─────────────┘
```

### Parameter Stacking
Multiple parameter nodes combine additively.

```
┌──────────────┐     ┌──────────────┐
│ Transform A  │     │ Transform B  │
│ Scale: 150%  │     │ Rotation: 45°│
└──────┬───────┘     └──────┬───────┘
       │                    │
       └────────┬───────────┘
                │
                ▼
         [Combined: Scale 150%, Rotation 45°]
```

### Layer Linking
Layers can be parented/linked for hierarchical transforms.

```
┌─────────────┐
│ Control     │ (parent)
│ Layer       │
└──────┬──────┘
       │ (parent link)
       ├──────────────┐
       │              │
       ▼              ▼
┌──────────┐   ┌──────────┐
│ Text A   │   │ Text B   │
└──────────┘   └──────────┘
```

---

## UI Interactions

### Creating Connections
1. **Drag from output port** to input port
2. **Right-click clip** → "Connect to..." → Select target
3. **Keyboard shortcut** (P) to link selected items

### Connection Visualization
- **Hover over clip**: Highlight all connected nodes
- **Click connection**: Show connection properties
- **Double-click connection**: Insert node in chain

### Quick Actions
| Action | Shortcut | Description |
|--------|----------|-------------|
| Add Effect | E | Add effect to selected clip |
| Add Transform | T | Add transform node |
| Add Modifier | M | Add modifier to selected property |
| Expand/Collapse | Tab | Toggle node graph view |
| Break Connection | X | Remove selected connection |

---

## Data Model

### Timeline Clip
```typescript
interface TimelineClip {
  id: string;
  type: 'video' | 'audio' | 'image' | 'solid' | 'text' | 'shape' | 'particle' | 'nested';
  inPoint: number;
  outPoint: number;
  source?: string;

  // Node connections
  inputs: ConnectionPort[];
  outputs: ConnectionPort[];

  // Inline parameters (not from nodes)
  transform: Transform;
  opacity: number;
}
```

### Node
```typescript
interface Node {
  id: string;
  type: 'effect' | 'parameter' | 'modifier';
  category: string;
  name: string;

  // Parameters with keyframe support
  parameters: Record<string, AnimatableProperty>;

  // Connection ports
  inputs: ConnectionPort[];
  outputs: ConnectionPort[];

  // Position in expanded node view
  position: { x: number; y: number };
}
```

### Connection
```typescript
interface Connection {
  id: string;
  sourceNode: string;
  sourcePort: string;
  targetNode: string;
  targetPort: string;

  // Visual properties
  type: 'visual' | 'parameter' | 'modifier';
  color?: string;
}
```

---

## Implementation Phases

### Phase 1: Connection Visualization
- Add bezier curves between related timeline items
- Color-code by relationship type
- Hover highlighting

### Phase 2: Effect Node System
- Create effect node data model
- Effect chain ordering
- Node insertion/removal

### Phase 3: Parameter Nodes
- Separate transform into linkable node
- Parameter node stacking
- Node-based keyframes

### Phase 4: Modifier Nodes
- Jitter/wiggle as nodes
- Loop modifiers
- Audio reactive nodes

### Phase 5: Expanded Node View
- Full node graph view per track
- Drag-and-drop node creation
- Connection editing

---

## Benefits

1. **Visual Clarity**: See relationships between layers at a glance
2. **Reusability**: Share effects/parameters between clips
3. **Flexibility**: Reorder effect chains without layer management
4. **Non-Destructive**: All modifications are node-based, easily removable
5. **ComfyUI Alignment**: Mental model matches ComfyUI's node workflow
