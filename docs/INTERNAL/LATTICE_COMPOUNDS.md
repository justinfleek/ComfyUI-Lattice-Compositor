# Hydrogen Motion Graphics Compounds for LATTICE

**Status**: Phase 1 complete (Halogen), Element port pending  
**Last Updated**: 2026-02-24  
**Owner**: Hydrogen Framework Team

> **Note:** 19 Motion compounds exist in `src/Hydrogen/Compound/Motion/` (Halogen).
> They have NOT yet been ported to `src/Hydrogen/Element/Compound/Motion/` (Schema-native).
> See SESSION_NOTES.md for current porting status.

---

## Executive Summary

LATTICE is the motion graphics and video rendering engine for the Continuity Project.
It requires specialized UI compounds that Hydrogen's general-purpose library does not
currently provide. This document tracks the ~85 compounds needed across 12 categories.

Hydrogen has **150+ general-purpose compounds** but is missing **motion graphics-specific
components**. This document defines the architecture, implementation order, and design
patterns for these new compounds.

---

## Architecture Principles

### 1. Schema Integration

All motion compounds integrate with `Hydrogen.Schema.Dimension.Temporal`:
- `Frames`, `FrameRate`, `Seconds` for time representation
- `fps24`, `fps30`, `fps60` etc. for standard frame rates
- Type-safe conversions via `TemporalUnit` class

### 2. Atoms-Molecules-Compounds Pattern

Following the Schema ontology:
- **Atoms**: Primitive values (`Frame`, `Timecode`, `ZoomLevel`)
- **Molecules**: Composed primitives (`TimeRange`, `KeyframeData`)
- **Compounds**: Full components (`AnimationTimeline`, `CurveEditor`)

### 3. Slot Architecture

Complex compounds use Halogen's slot system for composition:

```purescript
-- AnimationTimeline contains child compounds
type Slots =
  ( timeRuler :: H.Slot TimeRuler.Query TimeRuler.Output Unit
  , playhead :: H.Slot Playhead.Query Playhead.Output Unit
  , layerTrack :: H.Slot LayerTrack.Query LayerTrack.Output LayerId
  )
```

### 4. Bidirectional Query Pattern

Parent-child communication follows Halogen conventions:
- **Queries**: Parent asks child for state or commands actions
- **Output**: Child notifies parent of events

---

## Directory Structure

```
src/Hydrogen/
  Compound/
    Motion/                           # NEW: Motion graphics components
      Timeline/
        AnimationTimeline.purs        # Main container
        TimeRuler.purs                # Frame/timecode ruler
        Playhead.purs                 # Draggable playhead
        LayerTrack.purs               # Layer with in/out points
        PropertyTrack.purs            # Property animation track
        KeyframeMarker.purs           # Keyframe indicator
        AudioTrack.purs               # Audio waveform track
        WorkArea.purs                 # Work area brackets
        CompositionTabs.purs          # Multi-comp tab bar
      Timeline.purs                   # Re-exports

      Curve/
        CurveEditor.purs              # Main curve editor
        BezierCurve.purs              # Editable bezier
        CurveHandle.purs              # Tangent handles
        CurveKeyframe.purs            # Keyframe on curve
        EasingPreview.purs            # Inline easing preview
        EasingPicker.purs             # Easing preset selector
      Curve.purs                      # Re-exports

      Canvas/
        TransformGizmo.purs           # Bounding box handles
        MotionPath.purs               # Bezier motion path
        SelectionMarquee.purs         # Selection tool
        AnchorPoint.purs              # Anchor indicator
        GuideLines.purs               # Draggable guides
        SafeZones.purs                # Safe zone overlays
        GridOverlay.purs              # Configurable grid
      Canvas.purs                     # Re-exports

      Input/
        ScrubableNumber.purs          # Drag-to-scrub input
        AngleDial.purs                # Circular angle input
        PositionXY.purs               # Linked X/Y pair
        PositionXYZ.purs              # 3D position triplet
        DimensionInput.purs           # W/H with aspect lock
        TimecodeInput.purs            # Timecode entry
      Input.purs                      # Re-exports

      Property/
        PropertyRow.purs              # Label + value + keyframe
        PropertyGroup.purs            # Collapsible group
        KeyframeToggle.purs           # Stopwatch toggle
        ExpressionEditor.purs         # Expression input
        PropertyLink.purs             # Pickwhip control
      Property.purs                   # Re-exports

      Layer/
        LayerRow.purs                 # Layer item
        LayerIcon.purs                # Type icons
        LayerVisibility.purs          # Eye toggle
        LayerLock.purs                # Lock toggle
        LayerParenting.purs           # Parent pickwhip
        LayerModes.purs               # Blend mode dropdown
      Layer.purs                      # Re-exports

      Scope/
        Histogram.purs                # RGB/Luma histogram
        Waveform.purs                 # Video waveform
        Vectorscope.purs              # Color vectorscope
        RGBParade.purs                # RGB parade
      Scope.purs                      # Re-exports

      Render/
        RenderQueue.purs              # Render queue list
        RenderProgress.purs           # Progress bar
        OutputModule.purs             # Format config
        FormatSelector.purs           # Output format
      Render.purs                     # Re-exports

      Shape/
        PathEditor.purs               # Bezier path editing
        PathPoint.purs                # Path vertex
        StrokeEditor.purs             # Stroke controls
        FillEditor.purs               # Fill type selector
        ShapeModifierStack.purs       # Modifier stack
        TrimPathControls.purs         # Trim controls
      Shape.purs                      # Re-exports

  Schema/
    Motion/                           # NEW: Motion graphics atoms
      Timecode.purs                   # SMPTE timecode type
      TimeRange.purs                  # In/out point pair
      KeyframeData.purs               # Keyframe value + tangents
      Easing.purs                     # Easing curve types
      ZoomLevel.purs                  # Timeline zoom state
    Motion.purs                       # Re-exports
```

---

## Phase 1: Core Timeline (6 compounds)

The foundation everything else builds on.

### 1.1 AnimationTimeline

**Purpose**: Main timeline container with ruler, playback, scrubbing

**Dependencies**: TimeRuler, Playhead, LayerTrack, PropertyTrack, KeyframeMarker

**State**:
```purescript
type State =
  { frameRate :: FrameRate
  , duration :: Frames
  , currentFrame :: Frames
  , zoomLevel :: ZoomLevel
  , scrollOffset :: Number
  , isPlaying :: Boolean
  , workAreaStart :: Maybe Frames
  , workAreaEnd :: Maybe Frames
  , layers :: Array LayerState
  , selectedLayers :: Array LayerId
  , selectedKeyframes :: Array KeyframeId
  }
```

**Queries**:
```purescript
data Query a
  = SetCurrentFrame Frames a
  | Play a
  | Pause a
  | Stop a
  | SetZoomLevel ZoomLevel a
  | GetCurrentFrame (Frames -> a)
  | GetPlaybackState (Boolean -> a)
```

**Output**:
```purescript
data Output
  = FrameChanged Frames
  | PlaybackStateChanged Boolean
  | SelectionChanged (Array LayerId) (Array KeyframeId)
  | ZoomChanged ZoomLevel
  | WorkAreaChanged (Maybe Frames) (Maybe Frames)
```

---

### 1.2 TimeRuler

**Purpose**: Frame/timecode ruler with zoom levels

**Features**:
- Display modes: frames, timecode (SMPTE), seconds
- Tick marks at major/minor intervals
- Frame numbers at major ticks
- Click to seek
- Drag to scrub

**Props**:
```purescript
type TimeRulerProps =
  { frameRate :: FrameRate
  , duration :: Frames
  , currentFrame :: Frames
  , zoomLevel :: ZoomLevel
  , displayMode :: TimeDisplayMode  -- Frames | Timecode | Seconds
  , scrollOffset :: Number
  }
```

---

### 1.3 Playhead

**Purpose**: Draggable playhead with frame/timecode display

**Features**:
- Vertical line spanning timeline height
- Draggable head at top
- Frame/timecode display tooltip
- Snapping to frame boundaries
- Keyboard nudge (left/right arrows)

**Props**:
```purescript
type PlayheadProps =
  { currentFrame :: Frames
  , frameRate :: FrameRate
  , displayMode :: TimeDisplayMode
  , height :: Number
  }
```

---

### 1.4 LayerTrack

**Purpose**: Horizontal track for a layer with in/out points

**Features**:
- Layer bar showing duration
- Draggable in/out handles
- Drag to move layer in time
- Trim handles on edges
- Selection highlight
- Collapse/expand for property tracks

**State**:
```purescript
type LayerTrackState =
  { layerId :: LayerId
  , name :: String
  , inPoint :: Frames
  , outPoint :: Frames
  , isExpanded :: Boolean
  , isSelected :: Boolean
  , isLocked :: Boolean
  , isVisible :: Boolean
  , color :: Color
  }
```

---

### 1.5 PropertyTrack

**Purpose**: Collapsible property animation track (child of LayerTrack)

**Features**:
- Property name label
- Keyframe markers along track
- Value graph preview (optional)
- Expression indicator
- Expand to show value at current time

**Props**:
```purescript
type PropertyTrackProps =
  { propertyId :: PropertyId
  , propertyName :: String
  , keyframes :: Array KeyframeData
  , hasExpression :: Boolean
  , valueType :: PropertyValueType
  }
```

---

### 1.6 KeyframeMarker

**Purpose**: Diamond/circle keyframe indicator, draggable

**Features**:
- Diamond shape (default) or circle (hold keyframe)
- Draggable in time
- Multi-select support (Shift+click)
- Context menu (delete, copy, ease)
- Color based on interpolation type

**Props**:
```purescript
type KeyframeMarkerProps =
  { keyframeId :: KeyframeId
  , frame :: Frames
  , interpolationType :: InterpolationType
  , isSelected :: Boolean
  , isBezier :: Boolean
  }

data InterpolationType
  = Linear
  | Bezier
  | Hold
  | Auto
```

---

## Phase 2: Property System (6 compounds)

Motion graphics-specific input controls.

### 2.1 ScrubableNumber

**Purpose**: Drag-to-scrub numeric input (After Effects style)

**Features**:
- Click to edit as text
- Drag left/right to change value
- Shift+drag for fine control
- Ctrl+drag for coarse control
- Optional unit suffix display
- Min/max bounds

### 2.2 PropertyRow

**Purpose**: Property label + value + keyframe toggle

**Features**:
- Property name (clickable to select)
- Current value display/edit
- Keyframe stopwatch toggle
- Expression indicator icon
- Reset to default button

### 2.3 KeyframeToggle

**Purpose**: Stopwatch icon, toggles animation on property

**Features**:
- Active state (has keyframes)
- Click to add keyframe at current time
- Alt+click to remove all keyframes
- Visual feedback for keyframe at current time

### 2.4 PropertyGroup

**Purpose**: Collapsible property group (Transform, Effects, etc.)

**Features**:
- Expand/collapse arrow
- Group name
- Contains PropertyRow children
- Nested groups support (Effects > Blur > Amount)

### 2.5 AngleDial

**Purpose**: Circular angle input with visual dial

**Features**:
- 0-360 degree display
- Drag to rotate
- Click center for text input
- Visual arc indicator
- Revolution counter for >360

### 2.6 PositionXY

**Purpose**: Linked X/Y position input pair

**Features**:
- Two ScrubableNumber inputs
- Link/unlink button
- Proportional scaling when linked
- Coordinate system indicator

---

## Phase 3: Curve Editor (6 compounds)

Bezier easing and value curves.

### 3.1 CurveEditor

**Purpose**: Main curve editor canvas with grid

**Features**:
- Grid with value/time axes
- Multiple curves (one per property)
- Pan and zoom
- Fit to selection
- Value/speed graph toggle

### 3.2 BezierCurve

**Purpose**: Editable bezier curve with handles

**Features**:
- Smooth curve rendering
- SVG path for crisp display
- Color per curve (property color)
- Hover highlight

### 3.3 CurveHandle

**Purpose**: Draggable bezier handle (in/out tangents)

**Features**:
- In and out tangent handles
- Lock/unlock handles
- Unified/split tangents
- Visual connection line to keyframe

### 3.4 CurveKeyframe

**Purpose**: Keyframe point on curve, selectable

**Features**:
- Diamond marker on curve
- Draggable in 2D (time + value)
- Multi-select
- Double-click for value entry

### 3.5 EasingPicker

**Purpose**: Easing preset selector dropdown

**Features**:
- Common presets (ease-in, ease-out, ease-in-out)
- Visual preview of each curve
- Custom option (opens curve editor)
- Recently used section

### 3.6 EasingPreview

**Purpose**: Small inline easing curve preview

**Features**:
- Mini curve display
- Hover to show larger preview
- Click to edit
- Display current easing name

---

## Phase 4: Canvas Overlays (5 compounds)

2D compositing canvas controls.

### 4.1 TransformGizmo

**Purpose**: Bounding box with rotation/scale handles

**Features**:
- 8 scale handles (corners + edges)
- Rotation handle (offset from top)
- Center pivot indicator
- Shift for proportional scale
- Alt for scale from center

### 4.2 MotionPath

**Purpose**: Bezier motion path visualization

**Features**:
- Path line showing trajectory
- Dots at keyframe positions
- Tangent handles visible
- Temporal spacing indicators

### 4.3 MotionPathHandle

**Purpose**: Draggable path vertex/tangent handle

**Features**:
- Vertex point (keyframe position)
- In/out tangent handles
- Convert smooth/corner

### 4.4 AnchorPoint

**Purpose**: Anchor point indicator/dragger

**Features**:
- Crosshair display
- Draggable to reposition
- Snap to layer center
- Offset from layer origin display

### 4.5 SelectionMarquee

**Purpose**: Rectangular selection tool

**Features**:
- Drag to draw rectangle
- Selection preview
- Shift to add to selection
- Alt to subtract from selection

---

## Phase 5: Layer System (4 compounds)

Layer panel compounds.

### 5.1 LayerRow

**Purpose**: Layer item with icon, name, toggles

**Features**:
- Layer type icon
- Editable name
- Visibility toggle (eye)
- Lock toggle
- Solo toggle
- Color label
- Drag to reorder

### 5.2 LayerIcon

**Purpose**: Layer type icon (camera, solid, text, etc.)

**Types**:
- Composition, Solid, Shape, Text, Camera, Light, Null, Adjustment, Audio

### 5.3 LayerVisibility

**Purpose**: Eye icon toggle

**States**: Visible, Hidden, Solo

### 5.4 LayerLock

**Purpose**: Lock icon toggle

**States**: Unlocked, Locked, Partially Locked

---

## Component Summary by Priority

| Priority | Count | Components |
|----------|-------|------------|
| Critical | 18 | AnimationTimeline, Playhead, LayerTrack, PropertyTrack, KeyframeMarker, TimeRuler, CurveEditor, BezierCurve, CurveHandle, CurveKeyframe, TransformGizmo, MotionPath, MotionPathHandle, ScrubableNumber, AngleDial, PropertyRow, KeyframeToggle, ExpressionEditor |
| High | 38 | AudioTrack, AudioWaveform, CompositionTabs, EasingPreview, EasingPicker, SelectionMarquee, AnchorPoint, GuideLines, PositionXY, PositionXYZ, DimensionInput, PropertyGroup, PropertyLink, LayerRow, LayerIcon, LayerVisibility, LayerLock, Histogram, Waveform, Vectorscope, EmitterVisualizer, ForceFieldEditor, CameraGizmo, DOFControls, FocalLengthSlider, RenderQueue, RenderProgress, OutputModule, PathEditor, PathPoint, StrokeEditor, FillEditor, CompositionSettings, KeyframeInterpolation |
| Medium | 29 | TimelineZoom, WorkArea, TimecodeInput, ValueGraph, SpeedGraph, SafeZones, GridOverlay, RulerOverlay, MaskPath, PercentageSlider, PropertyMeter, ColorProperty, GradientProperty, LayerSolo, LayerParenting, LayerModes, RGBParade, ParticlePreview, VelocityCone, TurbulencePreview, CollisionPlaneEditor, CameraPathPreview, ViewportCube, ExportPreview, FormatSelector, ShapeModifierStack, TrimPathControls, RepeaterControls, RoundCornersControl |

---

## Build Order

### Phase 1: Core Timeline (Start Here)
1. AnimationTimeline
2. TimeRuler
3. Playhead
4. LayerTrack
5. KeyframeMarker
6. PropertyTrack

### Phase 2: Property System
7. ScrubableNumber
8. PropertyRow
9. KeyframeToggle
10. PropertyGroup
11. AngleDial
12. PositionXY

### Phase 3: Curve Editor
13. CurveEditor
14. BezierCurve
15. CurveHandle
16. CurveKeyframe
17. EasingPicker
18. EasingPreview

### Phase 4: Canvas Overlays
19. TransformGizmo
20. MotionPath
21. MotionPathHandle
22. AnchorPoint
23. SelectionMarquee

### Phase 5: Layer System
24. LayerRow
25. LayerIcon
26. LayerVisibility
27. LayerLock

### Phase 6: Everything Else
Scopes, Particle UI, Camera, Export, Shapes, Dialogs

---

## Schema Types Required

New types needed in `Hydrogen.Schema.Motion`:

```purescript
-- Timecode.purs
newtype Timecode = Timecode
  { hours :: Int
  , minutes :: Int
  , seconds :: Int
  , frames :: Int
  , dropFrame :: Boolean
  }

-- TimeRange.purs
newtype TimeRange = TimeRange
  { inPoint :: Frames
  , outPoint :: Frames
  }

-- KeyframeData.purs
type KeyframeData =
  { id :: KeyframeId
  , frame :: Frames
  , value :: KeyframeValue
  , inTangent :: Tangent
  , outTangent :: Tangent
  , interpolation :: InterpolationType
  }

-- Easing.purs
data EasingPreset
  = Linear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseInBack
  | EaseOutBack
  | EaseInOutBack
  | EaseInElastic
  | EaseOutElastic
  | EaseInBounce
  | EaseOutBounce
  | Custom CubicBezier

newtype CubicBezier = CubicBezier
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  }

-- ZoomLevel.purs
newtype ZoomLevel = ZoomLevel Number  -- 1.0 = 100%, 0.5 = 50%, 2.0 = 200%
```

---

## Session Log

### 2026-02-24

- Updated status: 19 Halogen components exist, Element port pending
- Cross-referenced with SESSION_NOTES.md

### 2026-02-22

- Initial documentation created
- Phase 1 implementation started (Halogen)
- Created Motion/ directory structure with 19 components:
  - Curve/: BezierCurve, CurveEditor, CurveHandle, CurveKeyframe, EasingPicker, EasingPreview
  - Property/: AngleDial, KeyframeToggle, PositionXY, PositionXYZ, PropertyGroup, PropertyRow, ScrubableNumber
  - Timeline/: AnimationTimeline, KeyframeMarker, LayerTrack, Playhead, PropertyTrack, TimeRuler
