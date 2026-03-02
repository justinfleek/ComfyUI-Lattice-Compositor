# Architecture Violations Audit

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // architecture // violations
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Purpose**: Document where codebase violates pure-data Schema architecture
**Date**: 2026-02-27
**Status**: CRITICAL — Foundation is broken

────────────────────────────────────────────────────────────────────────────────
                                                        // 1 // executive summary
────────────────────────────────────────────────────────────────────────────────

## 1. Executive Summary

The CLAUDE.md states:

> **CURRENT Element IS BROKEN** because it uses strings

This is accurate. The Element type in `src/Hydrogen/Render/Element.purs` is a
DOM/HTML abstraction using strings, not a Schema-atom-based GPU instruction set.

### Impact

| Violation | Files Affected | Severity |
|-----------|----------------|----------|
| String-based Element type | 172 dependents | **CRITICAL** |
| String fields in Schema types | 99 occurrences | **HIGH** |
| CSS export functions in Schema | ~20 files | **MEDIUM** |
| URL/Path as String | ~30 occurrences | **MEDIUM** |

### The Core Problem

**Current Element** (wrong):
```purescript
element "div" [ attr "class" "button" ] [ text "Click" ]
```

**Should be** (per CLAUDE.md):
```purescript
Rectangle 
  { position: Point2D { x: Pixel 100, y: Pixel 50 }
  , size: Size2D { width: Pixel 200, height: Pixel 48 }
  , fill: Solid (SRGB { r: Channel 59, g: Channel 130, b: Channel 246 })
  , cornerRadius: CornerRadii { topLeft: Pixel 8, ... }
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                   // 2 // violation // category 1
────────────────────────────────────────────────────────────────────────────────

## 2. CRITICAL: String-Based Element Type

### Location
```
src/Hydrogen/Render/Element.purs (933 lines)
```

### The Violation

```purescript
data Element msg
  = Text String                              -- ❌ String content
  | Element
      { namespace :: Maybe Namespace
      , tag :: String                        -- ❌ String tag name
      , attributes :: Array (Attribute msg)
      , children :: Array (Element msg)
      }

data Attribute msg
  = Attr String String                       -- ❌ String name, String value
  | Style String String                      -- ❌ CSS property as String
```

### Why This is Wrong

1. **Not composable at billion-agent scale** — Strings require parsing
2. **Not deterministic** — Same string can render differently
3. **Not bounded** — Any string is valid, no compile-time guarantees
4. **DOM-specific** — Assumes browser, not GPU

### What It Should Be

```purescript
data Element
  = Rectangle RectangleSpec
  | Ellipse EllipseSpec
  | Path PathSpec
  | Text TextSpec
  | Group (Array Element)
  | Transform Transform3D Element

type RectangleSpec =
  { position :: Point2D Pixel
  , size :: Size2D Pixel
  , fill :: Fill
  , stroke :: Maybe Stroke
  , cornerRadius :: CornerRadii
  }
```

### Dependents (172 files)

Every file importing `Hydrogen.Render.Element` is using the broken abstraction:
- `src/Hydrogen/UI/*` (all UI components)
- `src/Hydrogen/HTML/*`
- `src/Hydrogen/Target/*`
- Tests

### Migration Path

1. Create `src/Hydrogen/Element/` with Schema-based Element type
2. Create `src/Hydrogen/Element/GPU.purs` — GPU instruction generation
3. Create `src/Hydrogen/Element/Legacy.purs` — DOM export for legacy support
4. Migrate UI components one at a time
5. Delete `src/Hydrogen/Render/Element.purs`

────────────────────────────────────────────────────────────────────────────────
                                                   // 3 // violation // category 2
────────────────────────────────────────────────────────────────────────────────

## 3. HIGH: String Fields in Schema Types

### Count: 99 occurrences of `:: String` in Schema

### Categories

**Legitimate (keep as String for now):**
- `label :: String` — Human-readable text, needs i18n system eventually
- `name :: String` — Semantic identifiers, could be typed later

**Violations (should be typed atoms):**
- `source :: String` — Image/asset URLs → should be `AssetRef`
- `url :: String` — URLs → should be `URL` atom
- `path :: String` — File paths → should be `Path` atom
- `id :: String` — Identifiers → should be `UUID5` or typed ID

### Specific Violations

```
src/Hydrogen/Schema/Material/Fill.purs:100
  { source :: String           -- ❌ Image URL as String

src/Hydrogen/Schema/Material/BorderImage.purs:
  { source :: String           -- ❌ Image URL as String

src/Hydrogen/Schema/Scheduling/Event.purs:
  { url :: String              -- ❌ URL as String

src/Hydrogen/Schema/Brand/Provenance.purs:
  , path :: String             -- ❌ File path as String

src/Hydrogen/Schema/Gestural/Trigger.purs:
  , source :: String           -- ❌ Element ID as String
```

### Fix

Create proper atoms:
```purescript
-- src/Hydrogen/Schema/Identity/AssetRef.purs
newtype AssetRef = AssetRef UUID5

-- src/Hydrogen/Schema/Identity/URL.purs
data URL = URL
  { scheme :: Scheme
  , host :: Host
  , path :: URLPath
  , query :: Maybe Query
  }

-- src/Hydrogen/Schema/Identity/Path.purs
newtype Path = Path (Array PathSegment)
```

────────────────────────────────────────────────────────────────────────────────
                                                   // 4 // violation // category 3
────────────────────────────────────────────────────────────────────────────────

## 4. MEDIUM: CSS Export Functions in Schema

### The Problem

Schema types should be pure data. CSS export is a boundary concern.

### Examples

```
src/Hydrogen/Schema/Reactive/InteractiveState.purs:
  toLegacyCssClasses :: InteractiveState -> Array String

src/Hydrogen/Render/Style.purs:
  render :: Style -> String  -- Outputs CSS string
```

### Why This is Wrong

1. Schema should not know about CSS
2. CSS generation belongs in export/serialization layer
3. Pollutes pure types with legacy format concerns

### Fix

Move all `toCSS`, `toLegacyCss`, CSS-related functions to:
```
src/Hydrogen/Export/CSS/
```

Schema stays pure. Export layer handles legacy formats.

────────────────────────────────────────────────────────────────────────────────
                                                   // 5 // violation // category 4
────────────────────────────────────────────────────────────────────────────────

## 5. MEDIUM: Render/Style Module is CSS-Oriented

### Location
```
src/Hydrogen/Render/Style.purs (912 lines)
```

### The Problem

This module generates CSS strings from "typed" values, but:
- CSS properties are strings
- CSS values are strings
- The whole thing outputs strings

```purescript
backgroundColor :: String -> Style
backgroundColor v = prop "background-color" v

render :: Style -> String
render (Style props) = intercalate "; " (map propToString props)
```

### Why This is Wrong

For GPU rendering, we don't need CSS. We need:
```purescript
data DrawCommand
  = SetFill Fill
  | SetStroke Stroke
  | DrawRect Rect
  | DrawPath Path
  | PushTransform Transform3D
  | PopTransform
```

### Fix

1. Keep `Style.purs` for **legacy CSS export only**
2. Create `src/Hydrogen/Element/DrawCommand.purs` for GPU path
3. Element → DrawCommand is the pure rendering path
4. DrawCommand → CSS is one possible export format

────────────────────────────────────────────────────────────────────────────────
                                                         // 6 // what exists works
────────────────────────────────────────────────────────────────────────────────

## 6. What's Already Correct

The Schema atoms are mostly correct:

**Geometry** — Point, Vector, Matrix, Shape primitives
**Color** — OKLCH, SRGB, HSL, Gradient (all typed)
**Material** — Fill, Stroke, Surface (mostly typed)
**Dimension** — Pixel, Percentage, Size2D (typed)
**Typography** — FontWeight, FontSize, LineHeight (typed)

The violation is that these atoms aren't used to build Element.
Instead, Element uses strings and DOM concepts.

────────────────────────────────────────────────────────────────────────────────
                                                            // 7 // priority order
────────────────────────────────────────────────────────────────────────────────

## 7. Fix Priority

### Phase 1: Create Correct Element Type (Week 1-2)

1. Design `src/Hydrogen/Element/Element.purs` using Schema atoms
2. Create `src/Hydrogen/Element/DrawCommand.purs` for GPU instructions
3. Write Element → DrawCommand pure transformation
4. No dependencies on old Element yet

### Phase 2: Create Export Layers (Week 3)

1. `src/Hydrogen/Export/CSS/` — CSS string generation
2. `src/Hydrogen/Export/DOM/` — DOM node generation
3. `src/Hydrogen/Export/SVG/` — SVG string generation
4. All read from Element, all produce legacy formats

### Phase 3: Migrate UI Components (Week 4-6)

1. Start with simple components (Button, Card)
2. Rewrite using new Element type
3. Old components still work via legacy path
4. Gradual migration

### Phase 4: Fix String Fields (Week 7-8)

1. Create AssetRef, URL, Path atoms
2. Migrate Schema types to use them
3. Update all dependents

### Phase 5: Delete Legacy (Week 9+)

1. Once all components migrated
2. Delete `src/Hydrogen/Render/Element.purs`
3. Delete string-based path

───────────────────────────────���────────────────────────────────────────────────
                                                          // 8 // success criteria
────────────────────────────────────────────────────────────────────────────────

## 8. Success Criteria

After fix:

1. **Element compiles without any String** (except semantic content)
2. **Element → DrawCommand is a pure function**
3. **Same Element = same DrawCommand = same pixels**
4. **Schema types have zero CSS knowledge**
5. **All URL/Path/ID fields use typed atoms**

This is what "pure data all the way down" means.

────────────────────────────────────────────────────────────────────────────────
                                                               // end // of // audit
──────────────────────────────��─────────────────────────────────────────────────

**Document Status**: COMPLETE
**Date**: 2026-02-27
**Next Action**: Design correct Element type using Schema atoms
