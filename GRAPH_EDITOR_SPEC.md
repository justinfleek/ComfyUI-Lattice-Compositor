# Weyl Compositor - Graph Editor Specification

## Overview

This specification defines the complete feature set for the Weyl Compositor Graph Editor, modeled after Adobe After Effects with implementation guidance from the Friction graphics editor.

## Reference Sources

- [Adobe Keyframe Interpolation](https://helpx.adobe.com/after-effects/using/keyframe-interpolation.html)
- [Adobe Speed Control](https://helpx.adobe.com/after-effects/using/speed.html)
- [Adobe Keyboard Shortcuts](https://helpx.adobe.com/after-effects/using/keyboard-shortcuts-reference.html)
- [Friction Source Code](https://github.com/friction/friction) - graphboxeslist.cpp, keysview.cpp, graphkey.h

---

## A) GRAPH TYPES

### A1. Value Graph (Primary)
**What it does in AE:**
- Shows property values on Y-axis, time on X-axis
- Vertical position represents actual property value (position in px, opacity in %, rotation in degrees)
- Slope of curve represents speed (steeper = faster change)
- Bezier handles control the curve shape directly

**How Friction implements:**
- `graph_drawKeysPath()` renders QPainterPath using `cubicTo()` for bezier segments
- Transform matrix maps frame/value to screen: `transform.scale(mPixelsPerFrame, -mPixelsPerValUnit)`
- Value precision adapts based on zoom level (`mValuePrec`)

**Our implementation approach:**
- Canvas-based rendering with `ctx.bezierCurveTo()`
- Use `frameDuration` and `valueDelta` for normalization
- Support negative Y values (value can decrease)
- Show value units on Y-axis (px, %, deg based on property type)

### A2. Speed Graph (Secondary)
**What it does in AE:**
- Shows velocity (rate of change) on Y-axis, time on X-axis
- Flat line = constant speed, curve = acceleration/deceleration
- Peak height = maximum speed during that segment
- Cannot show value changes for curved motion paths (only scalar properties)

**Mathematical relationship:**
- Speed graph is the **derivative** of the value graph
- `speed = d(value)/d(time)`

**How Friction implements:**
- Not directly implemented - Friction uses value graph only
- Speed can be inferred from curve steepness

**Our implementation approach:**
- Phase 2 feature - compute derivative of value curve
- Display as separate toggle mode
- Limited to scalar properties (opacity, rotation, single-dimension position)
- Show "px/sec", "%/sec", "deg/sec" units

### A3. Toggle Between Graphs
**AE behavior:**
- Button in Graph Editor toolbar
- Defaults to "Edit Speed Graph" for most properties
- Position with curved path shows Speed Graph by default (Value Graph is misleading)

**Our implementation:**
- Toggle button: "Value" | "Speed"
- Default to Value Graph (more intuitive for beginners)
- Store preference per property type

---

## B) KEYFRAME TYPES

### B1. Linear (Diamond icon: ◇)
**What it does in AE:**
- Uniform rate of change between keyframes
- Creates mechanical, robotic motion
- Straight line segments in value graph
- Sharp corners at keyframes

**Visual indicator:** Diamond shape, fully outlined

**Our implementation:**
```typescript
interpolation: 'linear'
inHandle: { frame: 0, value: 0, enabled: false }
outHandle: { frame: 0, value: 0, enabled: false }
```

### B2. Auto Bezier (Circle icon: ○)
**What it does in AE:**
- Automatically smooths transitions
- Handles adjust automatically when keyframe values change
- Creates symmetrical curves through keyframes
- Direction handles are linked and auto-computed

**Visual indicator:** Circle/dot shape

**When to use:** Middle keyframes in a smooth path where you want automatic smoothing

**Our implementation:**
```typescript
interpolation: 'bezier'
controlMode: 'symmetric'  // Handles auto-adjust
// System computes handle positions based on neighboring keyframes
```

**Handle computation (from Friction):**
```cpp
// GraphKey::makeC0C1Smooth()
// Calculates smooth tangent through keyframe based on neighbors
```

### B3. Continuous Bezier (Filled diamond with handles)
**What it does in AE:**
- Smooth curve but handles can be manually adjusted
- Moving one handle affects the other to maintain smoothness
- Handles stay collinear (180° apart) but can have different lengths

**Visual indicator:** Diamond with visible bezier handles

**Our implementation:**
```typescript
interpolation: 'bezier'
controlMode: 'smooth'  // Handles stay collinear
inHandle: { frame: -5, value: 10, enabled: true }
outHandle: { frame: 5, value: -10, enabled: true }
// Note: handles point in opposite directions
```

### B4. Bezier (Fully manual handles)
**What it does in AE:**
- Complete control over both handles independently
- Handles can be any angle and length
- Creates sharp corners in motion while maintaining bezier curves

**Visual indicator:** Diamond with independent handles (can form angles)

**Our implementation:**
```typescript
interpolation: 'bezier'
controlMode: 'corner'  // Handles fully independent
inHandle: { frame: -5, value: 20, enabled: true }
outHandle: { frame: 3, value: 5, enabled: true }
// Handles can point in any direction
```

### B5. Hold (Square icon: □)
**What it does in AE:**
- Value stays constant until next keyframe
- Instant jump at next keyframe
- Creates strobe/step effects
- Temporal only (no spatial component)

**Visual indicator:** Square shape

**Our implementation:**
```typescript
interpolation: 'hold'
// Handles ignored - value is k1.value until frame reaches k2.frame
```

### B6. Roving Keyframes (Small circle icon)
**What it does in AE:**
- Only for spatial properties (Position, Anchor Point)
- Keyframe timing adjusts automatically to smooth speed
- Frame position "roves" based on path geometry
- Cannot be first or last keyframe

**Visual indicator:** Smaller circle, slightly transparent

**When to use:** Motion path where you want consistent speed regardless of path curvature

**Our implementation (Phase 2):**
```typescript
interpolation: 'bezier'
roving: true  // New flag
// System recomputes frame position based on arc length
```

**Computation approach:**
- Calculate arc length of bezier path
- Distribute roving keyframes by equal arc-length intervals
- Preserve first/last keyframe timing

---

## C) EASY EASE SYSTEM

### C1. Easy Ease (F9)
**What it does in AE:**
- Applies smooth deceleration and acceleration
- Sets both in and out handles to 0 velocity with 33.33% influence
- Creates natural "cushioned" motion

**Default values:**
- Speed: 0 (at keyframe)
- Influence: 33.33% (both directions)

**Our implementation:**
```typescript
// On F9 press for selected keyframes:
function applyEasyEase(keyframe: Keyframe) {
  keyframe.interpolation = 'bezier';
  keyframe.controlMode = 'smooth';
  // 33.33% of segment duration as handle length
  // Value delta scaled to create 0-velocity at keyframe
}
```

### C2. Easy Ease In (Shift+F9)
**What it does in AE:**
- Applies ease only to incoming motion (deceleration)
- Object slows down as it approaches keyframe
- Outgoing handles unchanged

**Our implementation:**
```typescript
function applyEasyEaseIn(keyframe: Keyframe) {
  keyframe.inHandle = computeEaseHandle(keyframe, 'in', 0.3333);
  // outHandle unchanged
}
```

### C3. Easy Ease Out (Ctrl+Shift+F9)
**What it does in AE:**
- Applies ease only to outgoing motion (acceleration)
- Object accelerates away from keyframe
- Incoming handles unchanged

### C4. Influence Values
**AE specifics:**
- Default Easy Ease: 33.33% influence
- Professional recommendation: 75% for "silky smooth" animation
- Can be set via Animation > Keyframe Velocity dialog

**Influence formula:**
```
handle_length = segment_duration * (influence / 100)
```

**Keyframe Velocity Dialog fields:**
- Incoming Velocity (pixels/sec, %/sec, or deg/sec)
- Incoming Influence (0-100%)
- Outgoing Velocity
- Outgoing Influence
- Continuous checkbox (locks in/out to same values)

**Our implementation:**
- Right-click keyframe > "Keyframe Velocity..."
- Dialog with numeric inputs for velocity and influence
- Apply button computes handle positions

---

## D) DIMENSION SEPARATION

### D1. Separate Dimensions
**What it does in AE:**
- Splits Position property into X Position, Y Position, (Z Position for 3D)
- Each dimension gets independent keyframes and curves
- Enables different easing per axis (e.g., ease X, linear Y)

**How to access in AE:**
1. Right-click Position property > "Separate Dimensions"
2. Graph Editor button: "Separate Dimensions" (when Position selected)

**Visual change:**
- Position row replaced with X Position, Y Position rows
- Each gets its own keyframe track

### D2. Limitations
- Only works for Position property (and 3D Position)
- Cannot separate Scale, Rotation, or custom multi-dimensional properties
- Workaround: Use expression with sliders

### D3. Recombine
**AE behavior:**
- Right-click > uncheck "Separate Dimensions"
- Keyframes merged back to Position property
- May lose some precision in conversion

**Our implementation:**
```typescript
// Layer property structure
transform: {
  position: AnimatableProperty<{x, y}>  // Combined (default)
  // OR
  positionX: AnimatableProperty<number>  // Separated
  positionY: AnimatableProperty<number>
  positionSeparated: boolean  // Flag
}
```

**UI:**
- Right-click menu on Position property
- "Separate Dimensions" toggle
- Graph editor shows separated curves in different colors

---

## E) SELECTION & TRANSFORM

### E1. Marquee/Box Select
**AE behavior:**
- Click and drag to draw selection rectangle
- All keyframes within rectangle become selected
- Shift+drag to add to selection
- Click empty area to deselect

**Friction implementation:**
```cpp
// keysview.cpp
if(mSelecting) {
    p->drawRect(mSelectionRect);
}
// Selection rectangle drawn with dotted blue line
```

**Our implementation:**
- Track mousedown position
- Draw dashed rectangle during drag
- On mouseup, find keyframes within bounds
- Support shift-modifier for additive selection

### E2. Transform Box
**AE behavior:**
- Enable via "Show Transform Box" button
- Appears when multiple keyframes selected
- Has 8 handles (corners + midpoints) and anchor point
- Drag handles to scale, drag center to move

**Operations:**
| Action | Result |
|--------|--------|
| Drag handle | Scale time/value |
| Shift+drag corner | Proportional scale |
| Drag center | Move all keyframes |
| Drag anchor point | Relocate transform center |
| Ctrl+Alt+drag corner | Taper values |
| Negative scale | Reverse keyframes in time |

### E3. Scale Keyframes
**AE behavior:**
- Horizontal scaling: Change timing (closer = faster, farther = slower)
- Vertical scaling: Change value range (amplitude)
- Negative horizontal = reverse animation order
- Preserves relative positions

**Our implementation:**
```typescript
function scaleKeyframes(keyframes: Keyframe[],
                       anchorFrame: number,
                       anchorValue: number,
                       scaleX: number,
                       scaleY: number) {
  for (const kf of keyframes) {
    kf.frame = anchorFrame + (kf.frame - anchorFrame) * scaleX;
    kf.value = anchorValue + (kf.value - anchorValue) * scaleY;
    // Also scale handle offsets
    kf.inHandle.frame *= scaleX;
    kf.inHandle.value *= scaleY;
    kf.outHandle.frame *= scaleX;
    kf.outHandle.value *= scaleY;
  }
}
```

### E4. Move Multiple Keyframes
**AE behavior:**
- Select keyframes, drag to move
- Horizontal: shift in time
- Vertical: shift in value
- Snap to frames when Snap enabled

### E5. Align Keyframes
**AE behavior (via Animation menu):**
- Align to current time
- Distribute evenly in time

**Our implementation:**
- Right-click menu > "Align to Playhead"
- Right-click menu > "Distribute Evenly"

---

## F) GRAPH EDITOR TOOLBAR

### F1. Fit Selection to View
**What it does:**
- Zooms and pans to show all selected keyframes
- Adjusts both time (horizontal) and value (vertical) scale
- Leaves padding around selection

**Keyboard shortcut:** None standard (double-click background in some versions)

### F2. Fit All Graphs to View
**What it does:**
- Shows all keyframes for all visible properties
- Useful reset when zoomed in too far

**Our implementation:**
```typescript
function fitAllToView() {
  const allKeyframes = getAllVisibleKeyframes();
  const minFrame = Math.min(...allKeyframes.map(k => k.frame));
  const maxFrame = Math.max(...allKeyframes.map(k => k.frame));
  const minValue = Math.min(...allKeyframes.map(k => getValue(k)));
  const maxValue = Math.max(...allKeyframes.map(k => getValue(k)));

  setViewRange(minFrame - padding, maxFrame + padding,
               minValue - padding, maxValue + padding);
}
```

### F3. Snap Toggle
**What it does:**
- When enabled, keyframes snap to: frames, other keyframes, playhead, in/out points, markers
- Orange line appears when snapping

**Our implementation:**
- Snap targets: frame boundaries, existing keyframes, playhead position
- Visual feedback: orange vertical line at snap point
- Hold Ctrl/Cmd to temporarily toggle snap behavior

### F4. Reference Graph (Ghost Overlay)
**What it does:**
- Shows a dimmed copy of another property's graph for comparison
- Useful for matching timing between properties

**Our implementation (Phase 2):**
- Dropdown to select reference property
- Render as semi-transparent overlay
- Different color from active graph

### F5. Show Audio Waveforms
**What it does:**
- Displays audio waveform behind graph
- Helps sync animation to music/sound

**Our implementation (Phase 3):**
- Requires audio layer support
- Render waveform as background graphic

### F6. Show Layer In/Out Points
**What it does:**
- Vertical lines at layer start/end frames
- Helps align keyframes to layer bounds

**Our implementation:**
- Draw vertical dashed lines at layer.inPoint and layer.outPoint
- Use layer color for line

### F7. Transform Box Toggle
**What it does:**
- Shows/hides the transform bounding box
- When hidden, individual keyframe dragging only

---

## G) TIMELINE FEATURES (Related to Graph Editor)

### G1. Work Area Bar
**What it does:**
- Defines preview/render region
- Gray bar with blue handles at top of timeline
- B key = set start to current time
- N key = set end to current time

**Our implementation:**
```typescript
interface WorkArea {
  startFrame: number;
  endFrame: number;
}

// Render only work area when exporting
// Preview plays only work area by default
```

### G2. Layer Bar Trimming
**What it does:**
- Drag layer bar ends to trim in/out points
- Does not delete keyframes outside trim (non-destructive)

### G3. Time-Reverse Keyframes
**What it does:**
- Animation > Keyframe Assistant > Time-Reverse Keyframes
- Flips selected keyframes in time order
- First becomes last, last becomes first

**Shortcut:** Ctrl+Alt+R (Windows) / Cmd+Opt+R (Mac)

**Our implementation:**
```typescript
function timeReverseKeyframes(keyframes: Keyframe[]) {
  const minFrame = Math.min(...keyframes.map(k => k.frame));
  const maxFrame = Math.max(...keyframes.map(k => k.frame));

  for (const kf of keyframes) {
    kf.frame = maxFrame - (kf.frame - minFrame);
    // Swap in/out handles
    [kf.inHandle, kf.outHandle] = [kf.outHandle, kf.inHandle];
  }

  // Re-sort by frame
  keyframes.sort((a, b) => a.frame - b.frame);
}
```

### G4. J/K Navigation
**What it does:**
- J = Go to previous keyframe
- K = Go to next keyframe
- Works across all visible properties

**Our implementation:**
```typescript
function goToNextKeyframe() {
  const currentFrame = store.currentFrame;
  const allKeyframes = getAllKeyframesForSelectedLayers();
  const nextKf = allKeyframes.find(kf => kf.frame > currentFrame);
  if (nextKf) store.setCurrentFrame(nextKf.frame);
}
```

### G5. U Key - Reveal Animated Properties
**What it does:**
- U = Show only properties with keyframes on selected layer(s)
- UU = Show all modified properties (including expressions)

**Our implementation:**
- Filter property display in timeline
- Collapse non-animated properties
- Expand animated properties automatically

### G6. Solo Properties in Graph
**What it does:**
- Isolate single property in graph editor
- Click property icon to solo
- Shift+click to add to solo group

---

## H) VISUAL FEEDBACK

### H1. Influence Display When Dragging
**What it does:**
- Shows percentage as tooltip when dragging handles
- Updates in real-time during drag

**Our implementation:**
```typescript
// During handle drag
const influence = Math.abs(handle.frame / segmentDuration * 100);
showTooltip(`${influence.toFixed(1)}%`);
```

### H2. Motion Path in Composition View
**What it does:**
- Dotted line showing position animation path
- Dots represent frames (spacing shows speed)
- Bezier handles visible at keyframes

**Our implementation (Phase 2):**
- Render in canvas viewport (separate from graph editor)
- Draw dots at frame intervals
- Show handles for selected keyframes

### H3. Current Value Readout
**What it does:**
- Shows interpolated value at current frame
- Updates as playhead moves
- Displayed in property row

**Our implementation:**
- Already have `getInterpolatedValue()` function
- Display next to property name
- Highlight when differs from keyframe value

### H4. Handle Length Indicators
**What it does:**
- Lines from keyframe point to handle
- Color-coded (different for in/out)

**Friction implementation:**
```cpp
// Different colors for in/out handles
// C0 (in) typically one color, C1 (out) another
```

**Our implementation:**
- inHandle line: blue/cyan
- outHandle line: red/orange
- Keyframe point: yellow/gold
- Handle end points: white circles

---

## I) KEYBOARD SHORTCUTS

### Navigation
| Shortcut | Action |
|----------|--------|
| J | Previous keyframe |
| K | Next keyframe |
| Home | Go to frame 0 |
| End | Go to last frame |
| Page Up | Back 10 frames |
| Page Down | Forward 10 frames |

### Keyframe Operations
| Shortcut | Action |
|----------|--------|
| F9 | Easy Ease (both) |
| Shift+F9 | Easy Ease In |
| Ctrl+Shift+F9 | Easy Ease Out |
| Ctrl+Shift+K | Keyframe Velocity dialog |
| Alt+Click keyframe | Delete keyframe |
| Ctrl+Click keyframe | Add/remove from selection |

### Graph Editor
| Shortcut | Action |
|----------|--------|
| Shift+F3 | Toggle Graph Editor |
| = / - | Zoom in/out horizontally |
| Alt + scroll | Zoom vertically |
| Space + drag | Pan view |
| F | Fit selection to view |
| Shift+F | Fit all to view |

### Property Reveal
| Shortcut | Action |
|----------|--------|
| U | Show animated properties |
| UU | Show all modified properties |
| P | Show Position |
| S | Show Scale |
| R | Show Rotation |
| T | Show Opacity (T for Transparency) |

### Selection
| Shortcut | Action |
|----------|--------|
| Ctrl+A | Select all keyframes |
| Ctrl+Shift+A | Deselect all |
| Ctrl+Alt+A | Select all keyframes in view |

### Transform
| Shortcut | Action |
|----------|--------|
| Ctrl+C | Copy keyframes |
| Ctrl+V | Paste keyframes |
| Ctrl+Shift+V | Paste reversed |
| Delete | Delete selected keyframes |
| Ctrl+Alt+R | Time-reverse keyframes |

---

## Implementation Priority

### Phase 1: Core Graph Editor (MVP)
1. Value graph rendering with bezier curves
2. Keyframe point display and selection
3. Handle display and dragging
4. Linear, Bezier, Hold interpolation
5. Basic zoom/pan
6. F9 Easy Ease
7. J/K navigation

### Phase 2: Advanced Editing
1. Transform box for multi-keyframe operations
2. Marquee selection
3. Dimension separation for Position
4. Keyframe Velocity dialog
5. Snap functionality
6. Auto Bezier mode
7. Speed Graph view

### Phase 3: Professional Features
1. Roving keyframes
2. Reference graph overlay
3. Audio waveform display
4. Motion path in viewport
5. Expression-based easing presets

---

## Data Structure Reference

### Current (after refactor)
```typescript
interface BezierHandle {
  frame: number;   // Offset from keyframe frame
  value: number;   // Offset from keyframe value
  enabled: boolean;
}

type ControlMode = 'symmetric' | 'smooth' | 'corner';

interface Keyframe<T> {
  id: string;
  frame: number;
  value: T;
  interpolation: InterpolationType;
  inHandle: BezierHandle;
  outHandle: BezierHandle;
  controlMode: ControlMode;
}
```

### Friction Reference (from graphkey.h)
```cpp
enum class CtrlsMode : short {
    symmetric,  // same length, opposite direction
    smooth,     // different length, opposite direction (collinear)
    corner      // fully independent
};

class GraphKey {
    ClampedPoint mC0;  // inHandle (control point 0)
    ClampedPoint mC1;  // outHandle (control point 1)
    CtrlsMode mCtrlsMode;

    // Methods
    void makeC0C1Smooth();  // Compute smooth tangent
    void setC0EnabledAction(bool enabled);
    void setC1EnabledAction(bool enabled);
};
```

---

## Testing Checklist

### Interpolation
- [ ] Linear interpolation produces straight lines
- [ ] Bezier handles affect curve shape correctly
- [ ] Hold interpolation maintains value until next keyframe
- [ ] Easy Ease creates smooth 33.33% influence curves
- [ ] Symmetric mode links handle lengths
- [ ] Smooth mode maintains collinearity
- [ ] Corner mode allows independent handles

### Visual
- [ ] Keyframe diamonds render at correct positions
- [ ] Handle lines connect keyframe to control points
- [ ] Curve renders smoothly through control points
- [ ] Selected keyframes have distinct styling
- [ ] Playhead indicator is visible and accurate

### Interaction
- [ ] Click keyframe to select
- [ ] Shift+click to add to selection
- [ ] Drag keyframe to move in time/value
- [ ] Drag handle to adjust curve
- [ ] Double-click to add keyframe
- [ ] Right-click for context menu
- [ ] Mouse wheel zooms
- [ ] Middle-mouse pan

### Keyboard
- [ ] F9 applies easy ease
- [ ] J/K navigate keyframes
- [ ] Delete removes selected keyframes
- [ ] Space+drag pans view
