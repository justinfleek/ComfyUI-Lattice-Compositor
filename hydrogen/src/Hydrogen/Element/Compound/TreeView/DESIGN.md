# TreeView Ultimate Design

## Vision

The TreeView must be capable of rendering **ANY hierarchical data visualization** 
that could ever appear on a display. From file explorers to org charts to neural 
network visualizations to phylogenetic trees to circuit diagrams.

## Dimensions of Variation

### 1. LAYOUT GEOMETRY

How nodes are spatially arranged:

| Layout | Description | Use Cases |
|--------|-------------|-----------|
| IndentedList | Traditional vertical list with indentation | File explorers, menus |
| Radial | Nodes arranged in concentric circles from center | Data exploration, relationships |
| Sunburst | Radial with arcs representing hierarchy | Disk usage, composition |
| Treemap | Nested rectangles, area = value | Storage visualization |
| Icicle | Horizontal/vertical partitions | Call stacks, hierarchy |
| Dendrogram | Biological tree with branch lengths | Phylogenetics, clustering |
| OrgChart | Top-down organizational hierarchy | Company structure |
| MindMap | Central node radiating outward | Brainstorming, concepts |
| CirclePack | Nested circles, area = value | Bubble charts |
| Force | Physics-based node positioning | Network graphs |
| Tidy | Aesthetic tree layout algorithm | Generic trees |
| Reingold-Tilford | Classic tree drawing algorithm | Balanced trees |

### 2. CONNECTION LINES

How parent-child relationships are visually connected:

| Style | Description |
|-------|-------------|
| None | No visible connections |
| Straight | Direct lines between nodes |
| Orthogonal | Right-angle connectors (elbow) |
| Curved | Bezier curves |
| Diagonal | Angled straight lines |
| Step | Staircase pattern |
| Bundle | Bundled edge visualization |

Line properties:
- Stroke width (Device.Pixel)
- Stroke color (Color.RGB)
- Stroke pattern (Solid, Dashed, Dotted, custom)
- Arrow heads (None, Start, End, Both)
- Curvature amount (0.0 = straight, 1.0 = max curve)

### 3. NODE CONTENT

What can appear inside a node:

| Content Type | Description |
|--------------|-------------|
| Text | Simple label |
| RichText | Formatted text with styles |
| Icon+Text | Icon followed by label |
| Card | Multi-line card with title, subtitle, metadata |
| Avatar | Profile image (for org charts) |
| Badge | Status indicators, counts |
| Progress | Progress bar within node |
| Sparkline | Mini chart in node |
| Custom | Arbitrary Element content |

Node slots:
- Leading (before main content - expand icon, checkbox)
- Content (main node content)
- Trailing (after main content - actions, badges)
- Below (content below main row - details, children preview)

### 4. NODE SHAPE

The visual container for node content:

| Shape | Description |
|-------|-------------|
| Rectangle | Standard rectangular node |
| RoundedRect | Rounded corners |
| Pill | Fully rounded ends |
| Circle | Circular nodes (for radial) |
| Diamond | Rotated square |
| Hexagon | Six-sided |
| Custom | SVG path |

Shape properties:
- Fill (Color, Gradient, Pattern)
- Stroke (Color, Width, Pattern)
- Shadow (Elevation)
- Size (Fixed, FitContent, Proportional)

### 5. NODE STATES

Visual states a node can be in:

| State | Description |
|-------|-------------|
| Default | Normal appearance |
| Hovered | Mouse over |
| Pressed | Mouse down |
| Selected | In selection |
| Focused | Keyboard focus |
| Disabled | Not interactive |
| Loading | Fetching children |
| Error | Failed to load |
| Dragging | Being dragged |
| DropTarget | Valid drop zone |
| Matched | Matches search/filter |
| Dimmed | Doesn't match filter (but visible) |
| Highlighted | Programmatic highlight |
| Edited | Inline editing active |

### 6. TRANSITIONS/ANIMATION

Motion atoms for tree changes:

| Animation | Description |
|-----------|-------------|
| Expand/Collapse | Children appear/disappear |
| Enter/Exit | Node added/removed |
| Move | Node position changes |
| Reorder | Sibling order changes |
| Layout | Overall layout changes |
| Drag | Drag preview movement |
| Selection | Selection highlight |
| Focus | Focus ring |
| StateChange | Any state transition |

Animation properties:
- Duration (Temporal.Milliseconds)
- Easing (Schema.Motion.Easing)
- Delay (Temporal.Milliseconds)
- Stagger (for groups)

### 7. INTERACTION MODES

How users interact with the tree:

| Mode | Description |
|------|-------------|
| ReadOnly | View only |
| Selectable | Can select nodes |
| Checkable | Has checkboxes |
| Editable | Can edit labels inline |
| Reorderable | Can drag to reorder |
| Nestable | Can drag to change parent |
| Expandable | Can expand/collapse |
| Filterable | Can filter/search |
| Zoomable | Can zoom in/out |
| Pannable | Can pan viewport |

### 8. VIRTUALIZATION

For large trees (100k+ nodes):

| Strategy | Description |
|----------|-------------|
| None | Render all nodes |
| Windowed | Only render visible viewport |
| Paginated | Load pages of children |
| Infinite | Infinite scroll |
| LOD | Level-of-detail (collapse far nodes) |

### 9. ACCESSIBILITY

A11y atoms:

| Feature | Description |
|---------|-------------|
| ARIA | Full ARIA tree semantics |
| Keyboard | Complete keyboard navigation |
| Focus | Focus management and indicators |
| Announcements | Live region updates |
| ReducedMotion | Respect prefers-reduced-motion |
| HighContrast | High contrast mode support |
| RTL | Right-to-left layout |
| Zoom | Browser zoom support |

### 10. DATA BINDING

How data flows:

| Pattern | Description |
|---------|-------------|
| Controlled | External state management |
| Uncontrolled | Internal state with callbacks |
| Lazy | Children loaded on demand |
| Streaming | Real-time data updates |
| Optimistic | Optimistic UI updates |

## Schema Atoms Needed

### New Schema Modules

```
Hydrogen.Schema.Graph.Layout
  - TreeLayout (all layout algorithms)
  - LayoutDirection (TB, BT, LR, RL)
  - LayoutSpacing (sibling, parent-child, level)
  - NodeSizing (fixed, fit, proportional)

Hydrogen.Schema.Graph.Connection
  - ConnectionStyle (straight, curved, orthogonal, etc.)
  - ConnectionTerminal (arrow heads)
  - ConnectionRouting (direct, bundled, etc.)
  - BranchingPattern (for dendrograms)

Hydrogen.Schema.Graph.NodeShape
  - NodeShape (rectangle, circle, diamond, etc.)
  - ShapeFill (solid, gradient, pattern)
  - ShapeStroke (width, dash, color)

Hydrogen.Schema.Graph.Viewport
  - ViewportBounds (visible area)
  - ZoomLevel (current zoom)
  - PanOffset (current pan)
  - FitMode (contain, cover, actual)
```

### Molecule Compositions

```
TreeNode = NodeId × NodeContent × NodeShape × NodeState × Children
TreeEdge = SourceId × TargetId × ConnectionStyle × EdgeData
TreeLayout = LayoutAlgorithm × LayoutParams × LayoutConstraints
TreeViewport = Bounds × Zoom × Pan × FitMode
TreeInteraction = Modes × Handlers × Gestures
TreeA11y = ARIA × Keyboard × Announcements × Preferences
```

### Compound Assembly

```
TreeView = Tree × Layout × Connections × Viewport × Interaction × A11y × Animation
```

## Implementation Plan

1. Create Schema atoms in Hydrogen.Schema.Graph.*
2. Update TreeView/Types.purs with new atom types
3. Create TreeView/Layout.purs with layout algorithms
4. Create TreeView/Connection.purs with line rendering
5. Create TreeView/Content.purs with node content slots
6. Create TreeView/Viewport.purs with zoom/pan/virtualization
7. Create TreeView/Animation.purs with transitions
8. Update TreeView/Render.purs to compose everything
9. Update TreeView.purs leader with full API
