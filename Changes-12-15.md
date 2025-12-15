# Weyl Compositor - Ground Truth Analysis & Overhaul Spec
## December 15, 2024

---

## PART 1: After Effects Ground Truth Analysis

### 1.1 Overall Layout (from reference images)

**Main Workspace Structure:**
- **Top**: Menu bar + Toolbar (Selection, Hand, Zoom, Rotation, Camera tools, Pen, Text, Shape tools)
- **Left Panel**: Project panel (assets, compositions, folders)
- **Center**: Composition viewer with playback controls below
- **Right Panel**: Properties panel (context-sensitive based on selection)
- **Bottom**: Timeline panel (layer tracks, keyframes, graph editor)

**Color Scheme:**
- Background: Dark gray (#1e1e1e to #2a2a2a)
- Panel borders: Near-black (#000 to #111)
- Text: Light gray (#aaa to #ccc)
- Accent/Selection: Blue (#4a90d9)
- Values: Cyan/Blue (#3498db) for numeric values
- Keyframes: Yellow/Gold (#f1c40f)
- Playhead: Red (#e74c3c)

---

### 1.2 Timeline Panel Analysis

**From `timeline-with-text-options-1.png` through `timeline-with-text-options-34png.png`:**

**Header Row (left to right):**
1. Timecode display: `0;00;00;00` format (hours;minutes;seconds;frames)
2. Search field (magnifying glass icon)
3. Layer control icons row

**Layer Row Columns (from `timeline-with-text-options-3.png`):**
| Column | Width | Content |
|--------|-------|---------|
| Shy | 16px | Eye icon for shy layers |
| Collapse | 16px | Star icon |
| Layer # | 24px | Number (1, 2, 3...) |
| Layer Name | flex | Type icon + Name (editable) |
| Mode | 70px | Blend mode dropdown (Normal, Add, Multiply, Screen, etc.) |
| Track Matte | 50px | TrkMat dropdown |
| Parent & Link | 70px | Parent layer dropdown |

**Property Hierarchy (expanded text layer):**
```
▼ Text
    ○ Source Text
  ▼ Path Options
      Path: [None dropdown]
  ▼ More Options
      Anchor Point Grouping: [Character dropdown]
    ○ Grouping Alignment: 0.0, 0.0 %
      Fill & Stroke: [Per Character Palette dropdown]
      Inter-Character Blending: [Normal dropdown]
  ▼ Transform
      Reset (link)
    ○ Anchor Point: 0.0, 0.0
    ○ Position: 360.0, 640.0
    ○ Scale: (link icon) 100.0, 100.0 %
    ○ Rotation: 0 x +0.0°
    ○ Opacity: 100 %
```

**Key Observations:**
- Stopwatch icon (○) before animatable properties
- Values in CYAN color
- Linked values show chain icon
- Rotation shows "0 x +0.0°" format (revolutions + degrees)
- "Reset" link for Transform section
- Dropdowns for mode selections

---

### 1.3 Properties Panel Analysis (Right Side)

**From `text-layer-side-panel-full.png`:**

**Header:** "Properties: TEXT"

**Section 1: Layer Transform**
```
Layer Transform          Reset
○ Anchor Point    0       0
○ Position        360     640
○ Scale        (link) 100%    100%
○ Rotation        0x+0°
○ Opacity         100%
```

**Section 2: Text**
```
Text                               ≡
[Font Family Dropdown: Impact]     ▼
[Font Weight: Regular]             ▼

TT  52 px  ▼    △  51 px  ▼
VA  Metrics ▼   VA  28    ▼
☑ Fill  [color swatch]   ✎
☐ Stroke [color swatch]  ✎
↑T 100%  ▼    T↓ 100%    ▼
A≡ 0 px  ▼    ⚡ 0%      ▼

TT  Tτ      T¹  T₁

☐ Ligatures    ☐ Hindi Digits
... Less
```

**Section 3: Paragraph**
```
Paragraph                          ≡
[Alignment buttons: Left, Center, Right, Justify variations]
⊢⊣ 0 px    ⊣⊢ 0 px
⊢≡ 0 px    ≡⊣ 0 px
⊢_ 0 px
⊣⊢ ⊣|     [box icons]
... Less
```

**Section 4: Text Animation**
```
Text Animation
+ Add Animator
```

**Additional Sections (collapsed):**
- Align
- Audio
- Effects & Presets

---

### 1.4 Solid Layer Dialog

**From `new-solid-popup.png`:**

```
┌─────────────────────────────────────┐
│ Solid Settings                    X │
├─────────────────────────────────────┤
│ Name: [Dark Gray Solid 1          ] │
├─────────────────────────────────────┤
│ Size                                │
│   Width:  720 px                    │
│   Height: 1280 px                   │
│            ☐ Lock Aspect Ratio      │
│                 to 9:16 (0.56)      │
│   Units: [pixels ▼]                 │
│   Pixel Aspect Ratio: [Square ▼]   │
│   Width: 100.0 % of comp            │
│   Height: 100.0 % of comp           │
│   Frame Aspect Ratio: 9:16 (0.56)   │
│         [Make Comp Size]            │
├─────────────────────────────────────┤
│ Color                               │
│   [color swatch] ✎                  │
│                                     │
│ ☐ Preview                           │
│            [OK]  [Cancel]           │
└─────────────────────────────────────┘
```

---

### 1.5 Light Layer Settings

**From `new-light-options-1.png` through `light-properties-panel-closeup.png`:**

**Light Settings Dialog:**
```
┌─────────────────────────────────────┐
│ Light Settings                    X │
├─────────────────────────────────────┤
│ Name: [Spot Light 1               ] │
├─────────────────────────────────────┤
│ Settings                            │
│   Light Type: [Spot ▼]              │
│     Options: Parallel, Spot,        │
│              Point, Ambient         │
│   Color: [white swatch] ✎           │
│   Intensity: 100 %                  │
│   Cone Angle: 90 °                  │
│   Cone Feather: 50 %                │
│   Falloff: [None ▼]                 │
│     Options: None, Smooth,          │
│              Inverse Square Clamped │
│   Radius: 500                       │
│   Falloff Distance: 500             │
│            ☐ Casts Shadows          │
│   Shadow Darkness: 100 %            │
│   Shadow Diffusion: 0 px            │
│                                     │
│ Note: Shadows are only cast from    │
│ layers with 'Cast Shadows' enabled  │
│ to layers with 'Accepts Shadows'    │
│ enabled.                            │
│                                     │
│ ☐ Preview                           │
│            [OK]  [Cancel]           │
└─────────────────────────────────────┘
```

**Light Properties Panel (right side):**
```
Properties: Spot Light 1

Layer Transform          Reset
○ Point of Interest  360    640    0
○ Position           390    610   -250
○ Orientation        0°     0°     0°
○ X Rotation         0x+0°
○ Y Rotation         0x+0°
○ Z Rotation         0x+0°

Light Options
  Light Type    [Spot ▼]
○ Intensity     100%
○ Color         [swatch] ✎
○ Cone Angle    90°
○ Cone Feather  50%
  Falloff       [None ▼]
  Casts Shadows ☑
○ Shadow Darkn... 100%
○ Shadow Diffusi... 0 px
```

---

### 1.6 Blend Modes (Complete List)

**From `blend-modes.png`:**

```
Normal
Dissolve
Dancing Dissolve
─────────────
Darken
Multiply
Color Burn
Classic Color Burn
Linear Burn
Darker Color
─────────────
Add
Lighten
Screen
Color Dodge
Classic Color Dodge
Linear Dodge
Lighter Color
─────────────
Overlay
Soft Light
Hard Light
Linear Light
Vivid Light
Pin Light
Hard Mix
─────────────
Difference
Classic Difference
Exclusion
Subtract
Divide
─────────────
Hue
Saturation
Color
Luminosity
─────────────
Stencil Alpha
Stencil Luma
Silhouette Alpha
Silhouette Luma
─────────────
Alpha Add
Luminescent Premul
```

---

### 1.7 Shape Layer Structure

**From `shape-layer-options.png`:**

```
▼ Contents                    Add: ○
  ▼ Ellipse 1           [Normal ▼]
      ═══
    ▼ Ellipse Path 1
      ○ Size          ∞ 212.2, 212.2
      ○ Position        0,0,0
    ▶ Stroke 1          [Normal ▼]
    ▶ Fill 1            [Normal ▼]
    ▼ Transform: Ellipse 1
      ○ Anchor Point    0,0,0
      ○ Position        -727.6, -329.1
      ○ Scale         ∞ 100.0, 100.0 %
      ○ Skew            0,0
      ○ Skew Axis       0x+0°
      ○ Rotation        0x+0°
      ○ Opacity         100%
▼ Transform
    Reset
  ○ Anchor Point       -727.6, -329.1
  ○ X Position         232.4
  ○ Y Position         37.1  (highlighted/selected)
  ○ Scale            ∞ 30.0, 30.0 %
  ○ Rotation           0x+0°
```

**Key Features:**
- Shape layers have "Contents" group
- Each shape (Ellipse, Rectangle, etc.) has its own Transform
- Layer-level Transform is separate
- X/Y Position can be split (separate dimensions)
- Graph editor shows position curves (red=X, green=Y)

---

### 1.8 Speed Graph Reference

**From `speed-graph-reference-1.jpg`:**

Easing types available:
- **Hold**: Flat line (no interpolation)
- **Linear**: Straight diagonal
- **Easy Ease**: S-curve
- **Easy Ease In**: Curve starts slow
- **Easy Ease Out**: Curve ends slow

---

## PART 2: Current Weyl Implementation Gaps

### 2.1 Critical Missing Features

| Feature | AE Ground Truth | Weyl Current | Priority |
|---------|----------------|--------------|----------|
| Timecode Display | HH;MM;SS;FF format | Frame number only | HIGH |
| Layer Duration Bar | Extends full comp length | Bug: not reaching end | CRITICAL |
| 3D Z-Position | Shows when 3D enabled | Bug: not appearing | CRITICAL |
| Blend Modes | 38 modes | 4 modes (Normal, Add, Multiply, Screen) | MEDIUM |
| Property Values | Cyan colored numbers | Generic styling | LOW |
| Rotation Format | "0x+0.0°" (revs + degrees) | Degrees only | LOW |
| Scale Link | Chain icon to link X/Y | Not implemented | MEDIUM |
| Transform Reset | "Reset" link in header | Not implemented | LOW |

### 2.2 Timeline Issues

1. **Frame Count Bug**: Ruler showing 170+ frames instead of 81
2. **Layer outPoint**: Defaulting to frameCount-1 instead of frameCount
3. **Playhead**: Hit area too small (fixed in recent commit)
4. **Zoom Scaling**: When zoomed out, timeline should fill viewport (partially fixed)

### 2.3 Properties Panel Issues

1. **Text Properties**:
   - Font family selector: EXISTS but needs more fonts
   - Font size: EXISTS but not syncing to renderer
   - Fill/Stroke colors: EXISTS but not syncing
   - Tracking: EXISTS but not syncing
   - Missing: Paragraph options, Text Animators

2. **Light Properties**:
   - Missing: Point of Interest (for Spot lights)
   - Missing: Shadow Darkness
   - Missing: Shadow Diffusion
   - Falloff options: Only "quadratic", AE has None/Smooth/Inverse Square Clamped

3. **Solid Creation**:
   - Missing: "Make Comp Size" button
   - Missing: Lock Aspect Ratio
   - Missing: Preview checkbox

### 2.4 3D Layer System

**AE 3D Transform (when 3D enabled):**
```
○ Anchor Point    X, Y, Z
○ Position        X, Y, Z
○ Scale           X, Y, Z %
○ Orientation     X°, Y°, Z°
○ X Rotation      0x+0°
○ Y Rotation      0x+0°
○ Z Rotation      0x+0°
○ Opacity         100%
```

**Weyl Issues:**
- Z values not appearing in timeline (BUG - supposedly fixed but not working)
- Orientation not editable
- Rotation format wrong

---

## PART 3: Implementation To-Do List

### Phase 1: Critical Bug Fixes (IMMEDIATE)

- [ ] **FIX: Layer outPoint defaulting correctly**
  - File: `compositorStore.ts`
  - Change: `outPoint: this.project.composition.frameCount`

- [ ] **FIX: Timeline ruler stops at exact frameCount**
  - File: `TimelinePanel.vue`
  - Change: Loop `for (let f = 0; f <= store.frameCount; f++)`

- [ ] **FIX: 3D Z-Position appearing in timeline**
  - File: `EnhancedLayerTrack.vue`
  - Change: Trust `layer.threeD` flag, not value existence

- [ ] **FIX: toggleLayer3D forcing Vue reactivity**
  - File: `compositorStore.ts`
  - Change: Replace entire value objects, set type='vector3'

- [ ] **FIX: Text property sync to renderer**
  - File: `TextProperties.vue`
  - Ensure `updateAnimatable` syncs both `layer.data` AND `layer.properties`

### Phase 2: UI/UX Alignment

- [ ] **Timecode Display**: Add HH;MM;SS;FF format option
- [ ] **Property Value Colors**: Cyan for numeric values (#3498db)
- [ ] **Blend Modes**: Add full 38-mode list
- [ ] **Scale Link Icon**: Add chain icon to link/unlink X/Y/Z
- [ ] **Rotation Format**: Display as "Xx+Y.Y°"
- [ ] **Transform Reset**: Add "Reset" link to Transform section header

### Phase 3: Light Layer Enhancements

- [ ] **Point of Interest**: Add for Spot and Directional lights
- [ ] **Falloff Types**: Add None, Smooth, Inverse Square Clamped
- [ ] **Shadow Settings**: Add Darkness and Diffusion controls
- [ ] **Light Settings Dialog**: Create popup for new light creation

### Phase 4: Shape Layer System

- [ ] **Contents Group**: Implement shape hierarchy
- [ ] **Per-Shape Transform**: Each shape gets its own transform
- [ ] **Add Menu**: "+ Add" button for shapes, strokes, fills
- [ ] **Separate Position Dimensions**: Allow X/Y split

### Phase 5: Text Animation System

- [ ] **Text Animators**: Add animator system
- [ ] **Per-Character Properties**: Position, Scale, Rotation, Opacity
- [ ] **Range Selectors**: Based on characters, words, lines
- [ ] **Wiggly Selector**: Random animation

---

## PART 4: File-by-File Changes Required

### 4.1 `compositorStore.ts`

```typescript
// Line ~XXX: createLayer function
outPoint: this.project.composition.frameCount, // Was frameCount - 1

// Line ~XXX: toggleLayer3D function
// Replace entire value objects to force reactivity
t.position.value = { x: pos.x, y: pos.y, z: pos.z ?? 0 };
t.position.type = 'vector3';
```

### 4.2 `TimelinePanel.vue`

```typescript
// trackContentWidth - use exact frame count
const computedWidthStyle = computed(() => {
  const frameWidth = store.frameCount * pixelsPerFrame.value;
  return Math.max(frameWidth, viewportWidth.value) + 'px';
});

// drawRuler - loop to exact frameCount
for (let f = 0; f <= store.frameCount; f++) { ... }
```

### 4.3 `EnhancedLayerTrack.vue`

```typescript
// Z Position - trust layer.threeD flag
if (props.layer.threeD) {
  transformProps.push({
    path: 'transform.position.z',
    name: 'Z Position',
    property: t.position // Pass full position, PropertyTrack extracts .z
  });
}
```

### 4.4 `PropertyTrack.vue`

```typescript
// Handle Z Position as special case
<template v-if="name === 'Z Position'">
  <ScrubableNumber
    :modelValue="property.value?.z ?? 0"
    @update:modelValue="v => updateValByIndex('z', v)"
  />
</template>
```

### 4.5 `TextProperties.vue`

```typescript
// Ensure dual sync in updateAnimatable
function updateAnimatable(name: string, val: number) {
  const prop = getProperty(name);
  if (prop) {
    prop.value = val;
    store.project.meta.modified = new Date().toISOString();
  }
  // ALSO update layer.data for immediate render
  const keyMap = {
    'Font Size': 'fontSize',
    'Fill Color': 'fill',
    'Stroke Color': 'stroke',
    // ... etc
  };
  if (keyMap[name]) {
    textData.value[keyMap[name]] = val;
  }
}
```

### 4.6 `LightProperties.vue`

Add missing properties:
- Point of Interest (vec3) for Spot/Directional
- Shadow Darkness (0-100%)
- Shadow Diffusion (0+ px)
- Falloff dropdown: None, Smooth, Inverse Square Clamped

---

## PART 5: Verification Checklist

After implementing changes, verify:

- [ ] New layer extends to full timeline (outPoint = frameCount)
- [ ] Timeline ruler shows exactly frameCount frames (e.g., 0-81, not 170+)
- [ ] Clicking 3D toggle (⬡) shows Z Position in Transform
- [ ] Z Position input actually changes Z value
- [ ] Text font size changes reflect on canvas
- [ ] Text fill color changes reflect on canvas
- [ ] Middle mouse button pans composition canvas
- [ ] Playhead is easy to grab (20px hit area)
- [ ] Light Falloff dropdown has 3 options

---

## Summary

The Weyl Compositor has solid foundations but several critical bugs prevent basic functionality:

1. **Timeline math errors** (wrong frame counts, layer duration)
2. **Vue reactivity failures** (3D toggle not updating UI)
3. **Data sync gaps** (properties not reaching renderer)

The Ground Truth analysis reveals AE's meticulous attention to:
- Consistent value formatting (cyan numbers, rotation format)
- Comprehensive blend mode support
- Hierarchical property organization
- Context-sensitive panels

Priority should be: Fix critical bugs first, then UI polish, then feature parity.
