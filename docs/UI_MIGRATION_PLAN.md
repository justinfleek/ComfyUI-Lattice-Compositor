# Weyl Compositor UI Migration Plan

## Reference Analysis

### Primary References
- **ref-2.png**: "Jane/Mike" floating panel interface
- **original-5d0a56a0844a97b4f6b1703890289d40.webp**: Component details and keyframe shapes

### Design Philosophy: "Dense Islands, Empty Ocean"
High density **inside** panels, high breathability **between** them.

---

## Part 1: Design System Foundation

### 1.1 Color Palette (Sampled from References)

| Role | Current | New | Hex | Usage |
|------|---------|-----|-----|-------|
| App Canvas | `#1a1a1a` | Void Black | `#050505` | Gap between panels |
| Panel BG | `#1e1e1e` | Oil Grey | `#121212` | Main panel backgrounds |
| Panel Surface | `#252525` | Charcoal | `#1a1a1a` | Headers, tabs |
| Input Well | `#2a2a2a` | Graphite | `#1E1E1E` | Input fields, dropdowns |
| Accent Primary | `#4a90d9` | Vivid Violet | `#8B5CF6` | Active states, selections |
| Accent Secondary | - | Purple→Pink | `linear-gradient(135deg, #8B5CF6, #EC4899)` | Progress bars, curves |
| Text Primary | `#e0e0e0` | Mist White | `#E5E5E5` | Labels (not pure white) |
| Text Secondary | `#888` | Ash | `#6B7280` | Hints, placeholders |
| Success | `#4ab14a` | Emerald | `#10B981` | Confirmations |
| Warning | `#f59e0b` | Amber | `#F59E0B` | Warnings |
| Error | `#d94a4a` | Rose | `#F43F5E` | Errors |

### 1.2 Typography

| Element | Current | New |
|---------|---------|-----|
| Font Family | System UI | `'Inter', 'Plus Jakarta Sans', system-ui` |
| Panel Headers | 13px, #888 | 11px, #6B7280, uppercase, 600 weight |
| Labels | 12px | 12px, #9CA3AF |
| Values | 12px | 12px, #E5E5E5, right-aligned |
| Inputs | 12px | 13px, #E5E5E5 |
| Monospace | Monaco | `'JetBrains Mono', 'SF Mono', monospace` |

### 1.3 Spacing & Sizing

| Element | Current | New |
|---------|---------|-----|
| Panel Gutter | 0px (edge-to-edge) | **20px** (floating) |
| Panel Radius | 0-4px | **16px** |
| Button Radius | 4px | **8px** (rect) or **999px** (pill) |
| Input Radius | 4px | **8px** |
| Component Gap | 8px | **12px** |
| Section Gap | 16px | **20px** |

### 1.4 Shadows & Borders

| Element | Current | New |
|---------|---------|-----|
| Panel Border | 1px solid #2a2a2a | **None** (use surface brightness) |
| Panel Shadow | None | `0 8px 32px rgba(0,0,0,0.4)` |
| Input Border | 1px solid #444 | `1px solid transparent` (border on focus only) |
| Focus Ring | None | `0 0 0 2px #8B5CF6` |

---

## Part 2: Layout Architecture

### 2.1 Current Layout (Edge-to-Edge Tiled)
```
┌──────────────────────────────────────────────────────────────┐
│ TOOLBAR                                                      │
├────────┬───────────────────────────────────────────┬─────────┤
│ LEFT   │ VIEWPORT                                  │ RIGHT   │
│ PANEL  ├───────────────────────────────────────────┤ PANEL   │
│        │ TIMELINE                                  │         │
├────────┴───────────────────────────────────────────┴─────────┤
│ STATUS BAR                                                   │
└──────────────────────────────────────────────────────────────┘
```

### 2.2 New Layout (Floating Island)
```
┌──────────────────────────────────────────────────────────────┐
│                                                              │
│   ┌─────────┐  ┌────────────────────────┐  ┌──────────────┐ │
│   │ PROJECT │  │                        │  │  PROPERTIES  │ │
│   │ VIDEO   │  │                        │  │              │ │
│   │         │  │      VIEWPORT          │  ├──────────────┤ │
│   └─────────┘  │                        │  │  AI AGENT    │ │
│                │                        │  │  "Hi! How    │ │
│   ┌─────────┐  └────────────────────────┘  │  can I help?"│ │
│   │ EFFECTS │                              └──────────────┘ │
│   └─────────┘  ┌────────────────────────────────────────┐   │
│                │ TIMELINE                               │   │
│                └────────────────────────────────────────┘   │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### 2.3 Floating Panel CSS Pattern
```css
.floating-panel {
  background: #121212;
  border-radius: 16px;
  box-shadow: 0 8px 32px rgba(0,0,0,0.4);
  border: none;
  overflow: hidden;
}

.workspace-layout {
  background: #050505;  /* Void between panels */
  padding: 20px;
  gap: 20px;
  display: grid;
  grid-template-columns: 240px 1fr 300px;
  grid-template-rows: auto 1fr auto;
}
```

---

## Part 3: Component Migration Map

### 3.1 WorkspaceLayout.vue

| Element | Current State | Target State | Priority |
|---------|---------------|--------------|----------|
| Root background | `#1a1a1a` | `#050505` (void black) | P0 |
| Panel borders | `1px solid #2a2a2a` | Remove, use shadow | P0 |
| Panel corners | `0px` | `16px radius` | P0 |
| Splitpanes | Vue Splitpanes | CSS Grid with gaps | P1 |
| Toolbar | Edge-to-edge bar | Floating pill toolbar | P1 |
| Status bar | Bottom bar | Floating status pill | P2 |

**Structural Changes:**
1. Replace `Splitpanes` with CSS Grid for consistent gutters
2. Wrap each major panel in `.floating-panel` class
3. Add 20px padding to workspace container
4. Remove all `border-left`, `border-right` from panels

### 3.2 Toolbar (Top Bar)

| Element | Current | Target | Notes |
|---------|---------|--------|-------|
| Container | Full-width bar | Floating rounded bar | Center in viewport |
| Tool buttons | Square icons | Pill buttons with icons | Group by function |
| Dividers | 1px lines | Subtle gaps | 12px spacing |
| Timecode | Monospace box | Floating pill display | Match ref time display |
| Play controls | Inline buttons | Centered floating group | ⏮ ⏪ ⏸ ⏩ ⏭ |

**Reference Pattern (from component details):**
```
┌──────────────────────────────────────────────────────┐
│  ⏮  ▶  ↻  ●  [≋]  ⟡  ▷    00:00:000 ∨              │
│                    ↑                                 │
│               "Easings" dropdown                     │
└──────────────────────────────────────────────────────┘
```

### 3.3 Left Sidebar: ProjectPanel.vue

| Element | Current | Target | Notes |
|---------|---------|--------|-------|
| Tabs | Text tabs with border-bottom | Pill segment control | Project / Effects / Assets |
| Search | Input with border | Borderless with icon | 🔍 placeholder |
| Media grid | List view | Thumbnail grid | Match ref layout |
| Item hover | Background change | Subtle glow + lift | Purple accent |
| Thumbnails | Square | 16:9 with rounded corners | 8px radius |

**Reference Pattern:**
```
┌─────────────────────────────┐
│  Project Video              │
│  ┌─────────────────────────┐│
│  │ 🔍 Search                ││
│  └─────────────────────────┘│
│  ┌──────┐  ┌──────┐        │
│  │ 🖼️   │  │ 🖼️   │        │
│  │ 0:21 │  │ 0:39 │        │
│  └──────┘  └──────┘        │
└─────────────────────────────┘
```

### 3.4 Right Sidebar: PropertiesPanel.vue

| Element | Current | Target | Notes |
|---------|---------|--------|-------|
| Tabs | Many text tabs | Scrollable icon tabs | Use icons not text |
| Section headers | Text + border | Collapsible with chevron | No borders |
| Property rows | Label + input | Label-as-input pattern | "X: 1920" not "X Position: [1920]" |
| Sliders | Standard range | Purple gradient track | Match volume slider |
| Keyframe toggle | Diamond icon | Contextual shape | See keyframe system |

**Space-Saving Patterns:**
1. **Scrubber Input**: Click-drag on values to change (eliminates separate slider)
2. **Combined Labels**: "X: 100" instead of "X Position" + input
3. **Collapsible Sections**: Default collapsed, expand on click
4. **Icon Labels**: Use icons instead of text where possible

**Reference Pattern (from ref-2):**
```
┌────────────────────────────────┐
│  Animation  │  Tracking        │  ← Segmented tabs
├────────────────────────────────┤
│  🔊 Volume ═══════════●══ 75%  │  ← Purple gradient slider
│                                │
│  Media Background              │
│  ┌─────┬─────┬─────┬─────┐    │
│  │Curve│ HSL │Wheel│Basic│    │  ← Sub-tabs
│  └─────┴─────┴─────┴─────┘    │
│  [Purple curve visualization]  │
└────────────────────────────────┘
```

### 3.5 AI Chat Panel: AIChatPanel.vue

| Element | Current | Target | Notes |
|---------|---------|--------|-------|
| Position | Tab in right panel | **Dedicated floating widget** | Bottom-right corner |
| Greeting | Generic | "Hi [User]! How can I help you?" | Personalized |
| Actions | Text input | Action pill buttons | "Generate Text", "Generate Avatar" |
| Style | Form-like | Conversational | Card-based actions |

**Reference Pattern:**
```
┌─────────────────────────────┐
│  Hi Mike!                   │
│  How can I help you?        │
│                             │
│  ┌──────────────────────┐   │
│  │ 📝 Generate Text      │   │
│  └──────────────────────┘   │
│  ┌──────────────────────┐   │
│  │ 👤 Generate Avatar    │   │
│  └──────────────────────┘   │
│                             │
│  ┌───────────────────┐      │
│  │ Type a message... │ ➤    │
│  └───────────────────┘      │
└─────────────────────────────┘
```

### 3.6 TimelinePanel.vue

| Element | Current | Target | Notes |
|---------|---------|--------|-------|
| Track headers | Text labels | Compact with icons | Layer type icon + name |
| Layer bars | Solid rectangles | **Pill shapes with thumbnails** | Rounded ends |
| Connections | None | **Bezier node lines** | Purple curves between related clips |
| Waveforms | Basic | Detailed with purple tint | Match ref audio track |
| Playhead | Thin line | Rounded cap with glow | Purple accent |

**Node Connection System:**
In the reference, timeline clips show curved lines connecting related elements (e.g., Text → Effect). Implementation:
```
┌────────────────────────────────────────────────────────────────┐
│  │ 0s   │ 1s   │ 2s   │ 3s   │ 4s   │ 5s   │ 6s   │ 7s │     │
│  ├──────┴──────┴──────┴──────┴──────┴──────┴──────┴────┴─────┤
│  │  ╭──────────────────────────────────────╮                  │
│  │  │ 📺 Video                           ▼│  ← Pill shape    │
│  │  ╰──────────────────────────────────────╯                  │
│  │           ╲                                                │
│  │            ╲ ← Bezier connection (purple)                  │
│  │             ╲                                              │
│  │  ╭───────────╲──────╮                                      │
│  │  │ 🔊 Sound   ▼    │                                      │
│  │  ╰──────────────────╯                                      │
└────────────────────────────────────────────────────────────────┘
```

### 3.7 GraphEditor.vue / GraphEditorCanvas.vue

| Element | Current | Target | Notes |
|---------|---------|--------|-------|
| Background | Grid | Subtle dot grid | Less visual noise |
| Curves | Blue lines | **Purple-pink gradient** | Match ref curves |
| Keyframes | Diamonds | **Semantic shapes** | See keyframe system |
| Handles | Small squares | Larger circles | Easier to grab |
| Easing dropdown | Basic select | **Styled dropdown** | With curve preview |

**Easing Dropdown (from reference):**
```
┌──────────────────────────────┐
│  ╭═ Graph Editor             │
│  │                           │
│  │  ─ Linear                 │
│  │                           │
│  │  ⬚ Hold                   │
│  │                           │
│  │  ∫ Quad                   │
│  │  ∫ Cubic                  │
│  │  ∫ Quart                  │
│  │  ∫ Quint                  │
│  │  ∫ Sine                   │
│  │  ✓ ∫ Expo  │In│Out│Both│  │  ← Selected with options
│  │  ∫ Circ                   │
│  │  ∫ Back                   │
│  │                           │
│  │  ∿ Elastic                │
│  │  ⌢ Bounce                 │
└──────────────────────────────┘
```

### 3.8 Snapping Options Panel (New Component)

**Based on reference, add a floating snapping options panel:**
```
┌─────────────────────────────┐
│  Toggle Snapping         ✓  │
│  ─────────────────────────  │
│  ✓ Grid                     │
│  ✓ Playhead                 │
│  ✓ Keyframes, Layers, Triggers │
│  ─────────────────────────  │
│  Show Grid               ✓  │
│  ✓ 1 / second               │
│    2 / second               │
│    4 / second               │
│    10 / second              │
│  ─────────────────────────  │
│  Show Thumbnail          ✓  │
│  ─────────────────────────  │
│  ──────────●──────  + 🔗 ⚙  │
└─────────────────────────────┘
```

---

## Part 4: Semantic Keyframe Shape System

### 4.1 Shape Definitions (from reference)

The reference shows **16 distinct keyframe shapes** with semantic meaning:

| Shape | Name | SVG Path | Usage |
|-------|------|----------|-------|
| ▎ | Mini | Short vertical bar | Subtle/micro keyframes |
| █ | Extend | Taller bar | Extended hold |
| ║ | Long | Full height bar | Long duration marker |
| ● | Round Head | Circle top | Smooth start |
| ●═ | RH Extend | Circle + bar | Smooth with hold |
| ●║ | RH Long | Circle + long bar | Smooth with long hold |
| ○║ | RH L/Outline | Outline circle + bar | Outline variant |
| ═ | Wide | Horizontal bar | Wide timing window |
| ═▌ | Wide Hammer | Bar + end cap | Hard stop after wide |
| ⬭ | Pill | Rounded rectangle | Eased transition |
| ⌚ | Watch | Hourglass shape | Time-based (ease in-out) |
| ▲ | Triangle | Triangle | Directional/ramp |
| ◆ | Diamond | Diamond | Standard keyframe |
| 🍸 | Martini | Inverted triangle | Ease-out with hold |
| ◉ | Radio | Filled circle | Point keyframe |
| ◉═ | Radio Long | Circle + long bar | Point with extension |

### 4.2 Shape-to-Easing Mapping

| Easing Type | Shape | Rationale |
|-------------|-------|-----------|
| Linear | ◆ Diamond | Standard, neutral |
| Hold | █ Extend / ═▌ Hammer | Visual "stop" |
| Ease In | ▲ Triangle (pointing right) | Accelerating |
| Ease Out | 🍸 Martini | Decelerating |
| Ease In-Out | ⌚ Watch / ⬭ Pill | Symmetrical |
| Elastic | ∿ Wave shape | Bouncy |
| Bounce | ⌢ Arc shape | Bouncing |
| Step | ▎ Mini | Discrete jump |

### 4.3 Implementation

Create `KeyframeShapes.ts`:
```typescript
export const KEYFRAME_SHAPES = {
  mini: { path: 'M0,8 L0,16', width: 2, height: 24 },
  extend: { path: 'M0,4 L0,20', width: 4, height: 24 },
  long: { path: 'M0,0 L0,24', width: 4, height: 24 },
  roundHead: { path: 'M4,4 A4,4 0 1,1 4,4.01 M4,8 L4,20', width: 8, height: 24 },
  // ... etc
  diamond: { path: 'M6,0 L12,12 L6,24 L0,12 Z', width: 12, height: 24 },
  martini: { path: 'M0,0 L12,0 L6,20 L6,24 L6,20 Z', width: 12, height: 24 },
  // ... etc
} as const;

export function getShapeForEasing(easing: string): keyof typeof KEYFRAME_SHAPES {
  switch (easing) {
    case 'linear': return 'diamond';
    case 'hold': return 'extend';
    case 'easeIn': return 'triangle';
    case 'easeOut': return 'martini';
    case 'easeInOut': return 'pill';
    // ... etc
    default: return 'diamond';
  }
}
```

---

## Part 5: Control Components

### 5.1 ScrubableNumber.vue (Enhanced)

**Current**: Number input with optional slider
**Target**: Click-drag on value itself to scrub

```vue
<!-- Before -->
<div class="property-row">
  <label>Opacity</label>
  <input type="range" /> <input type="number" />
</div>

<!-- After -->
<div class="scrub-value" @mousedown="startScrub">
  <span class="label">Opacity</span>
  <span class="value">{{ value }}%</span>
</div>
```

### 5.2 SliderInput.vue (Purple Gradient)

**Target Style:**
```css
.slider-track {
  background: linear-gradient(90deg, #8B5CF6, #EC4899);
  height: 4px;
  border-radius: 2px;
}

.slider-thumb {
  width: 12px;
  height: 12px;
  background: #fff;
  border-radius: 50%;
  box-shadow: 0 2px 4px rgba(0,0,0,0.3);
}
```

### 5.3 ColorPicker.vue

**Target**: Add purple accent, match ref "Media Background" color tools
- Curves tab
- HSL tab
- Color Wheel tab
- Basic (simple picker) tab

### 5.4 CurveEditor.vue

**Target Style:**
- Background: `#121212` with subtle grid
- Curve: Purple-pink gradient stroke (`stroke: url(#purplePinkGradient)`)
- Control points: White circles with purple glow on hover
- Handles: Smaller, connected with thin lines

---

## Part 6: Dialog Components

### 6.1 All Dialogs

| Property | Current | Target |
|----------|---------|--------|
| Overlay | `rgba(0,0,0,0.7)` | `rgba(0,0,0,0.8)` with blur |
| Container | `#2a2a2a` | `#121212` |
| Radius | 6px | 16px |
| Header | Gradient bar | Minimal text header |
| Close button | × in corner | Subtle icon or swipe |
| Buttons | Rectangular | Pill-shaped |

### 6.2 ExportDialog.vue

Match ref "Export" button style:
```css
.export-btn {
  background: linear-gradient(135deg, #8B5CF6, #EC4899);
  color: white;
  padding: 12px 32px;
  border-radius: 999px;
  font-weight: 600;
}
```

---

## Part 7: Implementation Phases

### Phase 1: Foundation (Design Tokens)
1. Create `ui/src/styles/design-tokens.css` with new color palette
2. Create `ui/src/styles/floating-panel.css` with panel styles
3. Update global CSS variables

### Phase 2: Layout Restructure
1. Replace Splitpanes with CSS Grid in WorkspaceLayout
2. Add floating panel wrappers
3. Implement 20px gutter system
4. Test responsive behavior

### Phase 3: Core Components
1. Update ScrubableNumber with scrub-on-value
2. Update SliderInput with purple gradient
3. Create KeyframeShapes system
4. Update ColorPicker with tabs

### Phase 4: Panels
1. ProjectPanel (thumbnails, search)
2. PropertiesPanel (dense layout)
3. TimelinePanel (pill clips, node lines)
4. AIChatPanel (conversational widget)

### Phase 5: Graph Editor
1. Purple-pink curves
2. Easing dropdown with previews
3. Semantic keyframe shapes
4. Snapping options panel

### Phase 6: Polish
1. Animations and transitions
2. Hover states and focus rings
3. Loading states
4. Dark mode refinements

---

## Part 8: Component File Changes Summary

| File | Changes | Priority |
|------|---------|----------|
| `WorkspaceLayout.vue` | Grid layout, floating panels, void background | P0 |
| `TimelinePanel.vue` | Pill clips, node connections, purple playhead | P0 |
| `GraphEditorCanvas.vue` | Purple curves, semantic shapes | P0 |
| `PropertiesPanel.vue` | Dense layout, scrub values | P1 |
| `AIChatPanel.vue` | Conversational widget style | P1 |
| `ProjectPanel.vue` | Thumbnail grid, search | P1 |
| `ScrubableNumber.vue` | Scrub on value | P1 |
| `SliderInput.vue` | Purple gradient | P2 |
| `ColorPicker.vue` | Tabbed interface | P2 |
| `KeyframeToggle.vue` | Semantic shapes | P2 |
| `ExportDialog.vue` | Pill buttons, rounded | P2 |
| `PathSuggestionDialog.vue` | New dialog style | P2 |
| `CompositionSettingsDialog.vue` | New dialog style | P2 |

---

## Part 9: New Components Needed

| Component | Purpose | Reference |
|-----------|---------|-----------|
| `FloatingPanel.vue` | Wrapper for floating island style | ref-2 |
| `SegmentedControl.vue` | Pill-style tab switcher | ref-2 tabs |
| `SnappingOptionsPanel.vue` | Grid/snap settings | component details |
| `TimeDisplayWidget.vue` | Current/Duration/FPS display | component details |
| `AIActionCard.vue` | "Generate Text" style cards | ref-2 AI widget |
| `NodeConnection.vue` | Bezier lines between clips | ref-2 timeline |
| `KeyframeShape.vue` | SVG keyframe renderer | component details bottom |

---

## Part 10: CSS Variables (New)

```css
:root {
  /* Colors */
  --weyl-void: #050505;
  --weyl-surface-1: #0a0a0a;
  --weyl-surface-2: #121212;
  --weyl-surface-3: #1a1a1a;
  --weyl-surface-4: #222222;

  --weyl-accent: #8B5CF6;
  --weyl-accent-secondary: #EC4899;
  --weyl-accent-gradient: linear-gradient(135deg, #8B5CF6, #EC4899);

  --weyl-text-primary: #E5E5E5;
  --weyl-text-secondary: #9CA3AF;
  --weyl-text-muted: #6B7280;

  /* Spacing */
  --weyl-gutter: 20px;
  --weyl-radius-sm: 8px;
  --weyl-radius-md: 12px;
  --weyl-radius-lg: 16px;
  --weyl-radius-full: 999px;

  /* Shadows */
  --weyl-shadow-panel: 0 8px 32px rgba(0,0,0,0.4);
  --weyl-shadow-dropdown: 0 4px 16px rgba(0,0,0,0.3);

  /* Transitions */
  --weyl-transition-fast: 150ms ease;
  --weyl-transition-normal: 250ms ease;
}
```

---

## Appendix A: Density Strategies

### A.1 Zero-UI Containers
- Remove panel headers (use inline labels)
- Remove internal borders (use spacing)
- Remove divider lines (use surface tone changes)

### A.2 Progressive Disclosure
- Collapse property groups by default
- Show context-sensitive controls only
- Use "..." menus for advanced options

### A.3 Combined Controls
- Label + value in one element: "X: 100"
- Slider + input in one control (scrub on value)
- Icon buttons instead of text buttons

### A.4 Bento Grid
- Fixed module sizes for major panels
- Allow only timeline to be resizable
- Viewport takes remaining space

---

## Appendix B: Accessibility Notes

- Maintain 4.5:1 contrast ratio for text
- Focus rings visible (purple glow)
- Keyboard navigation preserved
- Screen reader labels on icon-only buttons
- Reduced motion option for animations
