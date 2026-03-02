━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // compound // architecture // spec
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "The matrix has its roots in primitive arcade games, in early
    graphics programs and military experimentation with cranial
    jacks."

                                                        — Neuromancer

# Hydrogen Compound Architecture

**Version:** 1.0.0
**Status:** Canonical
**Author:** Claude (Opus 4.5) + jpyxal

This document defines how Hydrogen compounds consume Schema atoms to produce
deterministic, brand-consistent UI across all rendering targets.

════════════════════════════════════════════════════════════════════════════════
                                                              // the // problem
════════════════════════════════════════════════════════════════════════════════

## Why Current Web Development is Broken

The modern web stack is a tower of lossy abstractions:

```
Human Intent: "I want a blue button with rounded corners"
    ↓
Framework Component: <Button variant="primary" size="lg" />
    ↓
CSS-in-JS: styled.button`background: ${theme.colors.primary}`
    ↓
Compiled CSS: .sc-1a2b3c { background: #3b82f6 }
    ↓
Browser: *renders something that looks approximately right*
```

**Problems with this approach:**

1. **Semantic Loss** — "Primary" means nothing. What shade of blue? What exact
   radius? The intent is lost in translation.

2. **Framework Lock-in** — Compounds are tied to React, Vue, Svelte, etc.
   Migrating means rewriting everything.

3. **Non-deterministic** — The same "primary button" renders differently
   depending on which CSS loads, what order, what specificity wars occur.

4. **Agent-hostile** — AI cannot reason about `className="btn btn-primary"`.
   It's string soup with implicit semantics.

5. **Human-hostile** — Designers specify Pantone 2728 C, developers write
   `#3b82f6`, QA sees something different on their monitor. Who's right?

6. **Scale-hostile** — At billion-agent scale, semantic drift between agents
   causes coordination failures. "Primary blue" means 50 different things.

════════════════════════════════════════════════════════════════════════════════
                                                            // the // solution
════════════════════════════════════════════════════════════════════════════════

## Schema-Native Compounds

Hydrogen compounds are **Schema-native** — they accept Schema atoms directly
and convert them to rendering instructions. No strings. No implicit semantics.
No framework opinions.

```
Human/Agent Intent: "Blue button with 8px rounded corners"
    ↓
Schema Atoms:
  - Color.rgb 59 130 246
  - Geometry.cornersAll (Geometry.px 8.0)
    ↓
Compound Props:
  Button.button
    [ Button.backgroundColor (Color.rgb 59 130 246)
    , Button.borderRadius (Geometry.cornersAll (Geometry.px 8.0))
    ]
    [ E.text "Click me" ]
    ↓
Element (Pure Data):
  Element
    { tag: "button"
    , attributes: [ Style "background-color" "rgb(59, 130, 246)"
                  , Style "border-radius" "8px"
                  ]
    , children: [ Text "Click me" ]
    }
    ↓
Target Rendering (DOM, Canvas, PDF, Email, Video...):
  *identical output everywhere*
```

**This approach guarantees:**

1. **No semantic loss** — The exact color and radius are encoded as typed atoms.
   There is no interpretation step.

2. **Framework independence** — Compounds produce `Element msg`, which can
   render to DOM, Halogen, Canvas, WebGL, PDF, email HTML, or any target.

3. **Determinism** — The same atoms produce the same Element produce the same
   rendered output. Always. On every device. In every context.

4. **Agent-native** — AI can reason about `Color.rgb 59 130 246`. It's data
   with clear semantics, not string soup.

5. **Human-native** — Designers configure atoms in Showcase. The values they
   see are the values that render. No translation layer.

6. **Scale-safe** — At billion-agent scale, all agents share the same Schema.
   `Color.rgb 59 130 246` means exactly one thing.

════════════════════════════════════════════════════════════════════════════════
                                                     // compound // anatomy
════════════════════════════════════════════════════════════════════════════════

## The Three Layers

Every Hydrogen compound has three layers:

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ LAYER 1: PROPS                                                               │
│                                                                              │
│ Type-safe configuration accepting Schema atoms.                              │
│ All visual properties map to atoms from the 12 pillars.                      │
│                                                                              │
│ type ChatBubbleProps msg =                                                   │
│   { message :: String                    -- Content                          │
│   , direction :: Direction               -- Sent | Received                  │
│   , backgroundColor :: Maybe Color.RGB   -- Color pillar                     │
│   , textColor :: Maybe Color.RGB         -- Color pillar                     │
│   , borderRadius :: Maybe Geo.Corners    -- Geometry pillar                  │
│   , glow :: Maybe Color.Glow             -- Color pillar (compound)          │
│   , enterAnimation :: Maybe Anim         -- Temporal pillar                  │
│   , padding :: Maybe Dim.Spacing         -- Dimension pillar                 │
│   }                                                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│ LAYER 2: PROP BUILDERS                                                       │
│                                                                              │
│ Ergonomic functions for setting props via the modifier pattern.              │
│ Enables composable configuration without record update syntax.               │
│                                                                              │
│ backgroundColor :: forall msg. Color.RGB -> ChatBubbleProp msg               │
│ backgroundColor c props = props { backgroundColor = Just c }                 │
│                                                                              │
│ -- Usage:                                                                    │
│ chatBubble                                                                   │
│   [ backgroundColor (Color.rgb 59 130 246)                                   │
│   , borderRadius (Geometry.cornersAll Geometry.lg)                           │
│   , glow (Color.warmGlow 100.0 15.0)                                         │
│   ]                                                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│ LAYER 3: RENDER FUNCTION                                                     │
│                                                                              │
│ Pure function: Props → Element msg                                           │
│ Converts Schema atoms to Element attributes (styles, classes, etc.)          │
│                                                                              │
│ chatBubble :: forall msg. Array (ChatBubbleProp msg) -> Element msg          │
│ chatBubble propMods =                                                        │
│   let                                                                        │
│     props = foldl (\p f -> f p) defaultProps propMods                        │
│     bgStyle = maybe "" Color.toCss props.backgroundColor                     │
│     radiusStyle = maybe "" Geometry.cornersToCss props.borderRadius          │
│     glowStyle = maybe "" Color.glowToCss props.glow                          │
│   in                                                                         │
│     E.div_                                                                   │
│       [ E.styles                                                             │
│           [ Tuple "background-color" bgStyle                                 │
│           , Tuple "border-radius" radiusStyle                                │
│           , Tuple "filter" glowStyle                                         │
│           ]                                                                  │
│       ]                                                                      │
│       [ E.text props.message ]                                               │
└─────────────────────────────────────────────────────────────────────────────┘
```

════════════════════════════════════════════════════════════════════════════════
                                                           // props // design
════════════════════════════════════════════════════════════════════════════════

## Props Structure

### Required vs Optional

Props are organized into **required** (content/behavior) and **optional**
(visual styling):

```purescript
type CompoundProps msg =
  -- REQUIRED: Content and behavior (no Maybe)
  { content :: String
  , onClick :: Maybe msg           -- Handlers are optional
  
  -- OPTIONAL: Visual atoms (all Maybe with defaults)
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderRadius :: Maybe Geometry.Corners
  , padding :: Maybe Dimension.Spacing
  , glow :: Maybe Color.Glow
  , shadow :: Maybe Elevation.Shadow
  , animation :: Maybe Motion.Animation
  
  -- ESCAPE HATCH: For edge cases not covered by atoms
  , extraAttributes :: Array (E.Attribute msg)
  }
```

### Default Props

Every compound defines sensible defaults that produce a usable compound
even with zero configuration:

```purescript
defaultProps :: forall msg. CompoundProps msg
defaultProps =
  { content: ""
  , onClick: Nothing
  
  -- Visual defaults (pleasant, accessible, neutral)
  , backgroundColor: Nothing      -- Inherits from parent
  , textColor: Nothing            -- Inherits from parent
  , borderRadius: Just (Geometry.cornersAll Geometry.md)
  , padding: Just Dimension.md
  , glow: Nothing                 -- No glow by default
  , shadow: Nothing               -- No shadow by default
  , animation: Nothing            -- No animation by default
  
  , extraAttributes: []
  }
```

### The Modifier Pattern

Props are set via modifier functions, enabling composition:

```purescript
-- Type alias for prop modifiers
type CompoundProp msg = CompoundProps msg -> CompoundProps msg

-- Modifier functions
backgroundColor :: forall msg. Color.RGB -> CompoundProp msg
backgroundColor c props = props { backgroundColor = Just c }

borderRadius :: forall msg. Geometry.Corners -> CompoundProp msg
borderRadius r props = props { borderRadius = Just r }

glow :: forall msg. Color.Glow -> CompoundProp msg
glow g props = props { glow = Just g }

-- Composition via arrays
myCompound
  [ backgroundColor brand.primary
  , borderRadius brand.corners
  , glow brand.accentGlow
  ]
```

**Why this pattern?**

1. **Composable** — Modifiers are functions, can be stored, combined, reused.
2. **Type-safe** — Each modifier only accepts the correct atom type.
3. **Readable** — Looks like a configuration block, easy to scan.
4. **Extensible** — Add new props without breaking existing code.

════════════════════════════════════════════════════════════════════════════════
                                                    // schema // atom // mapping
════════════════════════════════════════════════════════════════════════════════

## Mapping Schema Pillars to CSS

Each Schema pillar has well-defined CSS conversions:

### Color Pillar → CSS

```purescript
-- RGB to CSS
Color.toCss :: Color.RGB -> String
-- "rgb(59, 130, 246)"

-- RGBA to CSS
Color.toCssA :: Color.RGBA -> String
-- "rgba(59, 130, 246, 0.8)"

-- HSL to CSS
Color.hslToCss :: Color.HSL -> String
-- "hsl(217, 91%, 60%)"

-- Glow to CSS filter
Color.glowToCss :: Color.Glow -> String
-- "drop-shadow(0 0 15px rgba(255, 200, 150, 0.6))"

-- Gradient to CSS
Color.gradientToCss :: Color.Gradient -> String
-- "linear-gradient(180deg, #3b82f6 0%, #1d4ed8 100%)"
```

### Geometry Pillar → CSS

```purescript
-- Radius to CSS
Geometry.toCss :: Geometry.Radius -> String
-- "8px" or "0.5rem" or "50%"

-- Corners to CSS (shorthand when possible)
Geometry.cornersToCss :: Geometry.Corners -> String
-- "8px" (all same) or "8px 12px 8px 12px" (different)

-- Transform to CSS
Geometry.transformToCss :: Geometry.Transform -> String
-- "translate(10px, 20px) rotate(45deg) scale(1.5)"
```

### Dimension Pillar → CSS

```purescript
-- Length to CSS
Dimension.toCss :: Dimension.Length -> String
-- "16px" or "1rem" or "2em" or "50%"

-- Spacing to CSS (semantic)
Dimension.spacingToCss :: Dimension.Spacing -> String
-- "0.5rem" (sm) or "1rem" (md) or "2rem" (lg)
```

### Motion Pillar → CSS

```purescript
-- Easing to CSS timing function
Motion.toCSSString :: Motion.Easing -> String
-- "cubic-bezier(0.4, 0, 0.2, 1)" or "ease-in-out"

-- Duration to CSS
Motion.durationToCss :: Motion.Duration -> String
-- "300ms" or "0.3s"

-- Animation to CSS keyframes + properties
Motion.animationToCss :: Motion.Animation -> String
-- "fadeIn 300ms ease-out forwards"
```

### Elevation Pillar → CSS

```purescript
-- Shadow to CSS box-shadow
Elevation.shadowToCss :: Elevation.Shadow -> String
-- "0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -2px rgba(0, 0, 0, 0.1)"
```

════════════════════════════════════════════════════════════════════════════════
                                                  // brand // schema // integration
════════════════════════════════════════════════════════════════════════════════

## Consuming Brand Schema

Compounds don't hardcode values — they receive atoms from a BrandSchema:

### BrandSchema Structure

```purescript
-- Exported from Showcase / COMPASS
type BrandSchema =
  { -- Color atoms
    primary :: Color.RGB
  , secondary :: Color.RGB
  , accent :: Color.RGB
  , background :: Color.RGB
  , foreground :: Color.RGB
  , muted :: Color.RGB
  , destructive :: Color.RGB
  
  -- Glow atoms
  , accentGlow :: Color.Glow
  , primaryGlow :: Color.Glow
  
  -- Geometry atoms
  , corners :: Geometry.Corners
  , cornersSmall :: Geometry.Corners
  , cornersLarge :: Geometry.Corners
  
  -- Typography atoms
  , fontPrimary :: Typography.FontStack
  , fontSecondary :: Typography.FontStack
  , typeScale :: Typography.TypeScale
  
  -- Dimension atoms
  , spacingScale :: Dimension.SpacingScale
  , containerWidth :: Dimension.Length
  
  -- Motion atoms
  , defaultEasing :: Motion.Easing
  , defaultDuration :: Motion.Duration
  , springConfig :: Motion.SpringConfig
  
  -- Elevation atoms
  , shadowSubtle :: Elevation.Shadow
  , shadowMedium :: Elevation.Shadow
  , shadowStrong :: Elevation.Shadow
  }
```

### Using Brand in Compounds

```purescript
-- A themed chat bubble using brand atoms
brandedChatBubble :: forall msg. BrandSchema -> String -> Element msg
brandedChatBubble brand message =
  ChatBubble.chatBubble
    [ ChatBubble.message message
    , ChatBubble.backgroundColor brand.primary
    , ChatBubble.textColor brand.foreground
    , ChatBubble.borderRadius brand.corners
    , ChatBubble.glow brand.accentGlow
    ]

-- Theming an entire page
brandedPage :: forall msg. BrandSchema -> Array (Element msg) -> Element msg
brandedPage brand children =
  E.div_
    [ E.styles
        [ Tuple "background-color" (Color.toCss brand.background)
        , Tuple "color" (Color.toCss brand.foreground)
        , Tuple "font-family" (Typography.fontStackToCss brand.fontPrimary)
        ]
    ]
    children
```

### Showcase Workflow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ SHOWCASE (Brand Configuration UI)                                            │
│                                                                              │
│ ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐               │
│ │  ColorPicker    │  │  RadiusPicker   │  │  MotionPicker   │               │
│ │                 │  │                 │  │                 │               │
│ │  H: 217°        │  │  ○ None         │  │  Easing: ────── │               │
│ │  S: 91%         │  │  ○ Small        │  │                 │               │
│ │  L: 60%         │  │  ● Medium       │  │  Duration: 300ms│               │
│ │                 │  │  ○ Large        │  │                 │               │
│ │  [■■■■■■■■■■■]  │  │  ○ Full         │  │  Spring: k=100  │               │
│ └─────────────────┘  └─────────────────┘  └─────────────────┘               │
│                                                                              │
│ ┌─────────────────────────────────────────────────────────────────────────┐ │
│ │ PREVIEW                                                                  │ │
│ │                                                                          │ │
│ │   ┌──────────────────────────────────────────┐                          │ │
│ │   │  Hello! This is a preview of your        │                          │ │
│ │   │  brand's chat bubble with the atoms      │                          │ │
│ │   │  you've configured.                      │                          │ │
│ │   │                                  ✓ Read  │                          │ │
│ │   └──────────────────────────────────────────┘                          │ │
│ │                                                                          │ │
│ │   (Real-time preview using actual atoms)                                │ │
│ └─────────────────────────────────────────────────────────────────────────┘ │
│                                                                              │
│ [ Export BrandSchema.purs ]                                                  │
└─────────────────────────────────────────────────────────────────────────────┘
                                    ↓
                                    ↓ Export
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ BrandSchema.purs                                                             │
│                                                                              │
│ module MyBrand.Schema where                                                  │
│                                                                              │
│ import Hydrogen.Schema.Color as Color                                        │
│ import Hydrogen.Schema.Geometry as Geometry                                  │
│ import Hydrogen.Schema.Motion as Motion                                      │
│                                                                              │
│ brand :: BrandSchema                                                         │
│ brand =                                                                      │
│   { primary: Color.rgb 59 130 246                                            │
│   , secondary: Color.rgb 99 102 241                                          │
│   , corners: Geometry.cornersAll (Geometry.px 8.0)                           │
│   , accentGlow: Color.glow 4000 150.0 12.0                                   │
│   , defaultEasing: Motion.easeOutCubic                                       │
│   , ...                                                                      │
│   }                                                                          │
└─────────────────────────────────────────────────────────────────────────────┘
                                    ↓
                                    ↓ Import in production
                                    ↓
┌─────────────────────────────────────────────────────────────────────────────┐
│ Production Code                                                              │
│                                                                              │
│ import MyBrand.Schema (brand)                                                │
│ import Hydrogen.Element.Compound.ChatBubble as ChatBubble                   │
│                                                                              │
│ myChatUI = ChatBubble.chatBubble                                             │
│   [ ChatBubble.backgroundColor brand.primary                                 │
│   , ChatBubble.borderRadius brand.corners                                    │
│   ]                                                                          │
│   -- Renders EXACTLY as previewed in Showcase                                │
└─────────────────────────────────────────────────────────────────────────────┘
```

════════════════════════════════════════════════════════════════════════════════
                                                          // animation // atoms
════════════════════════════════════════════════════════════════════════════════

## Motion and Interaction

Animations are first-class atoms, not CSS hacks:

### Easing Atoms

```purescript
-- Standard easings
Motion.linear :: Easing
Motion.easeIn :: Easing
Motion.easeOut :: Easing
Motion.easeInOut :: Easing

-- Penner easings (full set)
Motion.easeInQuad :: Easing
Motion.easeOutQuad :: Easing
Motion.easeInCubic :: Easing
Motion.easeOutElastic :: Easing
Motion.easeOutBounce :: Easing
-- ... 30+ variants

-- Custom cubic bezier
Motion.cubicBezier 0.68 (-0.55) 0.27 1.55  -- Back easing
```

### Spring Atoms

```purescript
type SpringConfig =
  { mass :: Number        -- Object mass (affects momentum)
  , stiffness :: Number   -- Spring constant (affects speed)
  , damping :: Number     -- Friction (affects overshoot)
  }

-- Presets
Motion.springGentle :: SpringConfig    -- { mass: 1.0, stiffness: 100.0, damping: 15.0 }
Motion.springSnappy :: SpringConfig    -- { mass: 1.0, stiffness: 300.0, damping: 20.0 }
Motion.springBouncy :: SpringConfig    -- { mass: 1.0, stiffness: 200.0, damping: 10.0 }
```

### Animation Composition

```purescript
type Animation =
  { property :: AnimatableProperty   -- What changes (transform, opacity, etc.)
  , from :: PropValue                -- Start value
  , to :: PropValue                  -- End value
  , duration :: Duration             -- How long
  , easing :: Easing                 -- How it moves
  , delay :: Duration                -- When it starts
  }

-- Orchestration
Motion.sequence :: Array Animation -> Animation      -- One after another
Motion.parallel :: Array Animation -> Animation      -- All at once
Motion.stagger :: Duration -> Array Animation -> Animation  -- Offset starts
```

### Interactive States

```purescript
-- Compounds can define state-based styling
type InteractiveStyles =
  { default :: StyleAtoms
  , hover :: StyleAtoms
  , focus :: StyleAtoms
  , active :: StyleAtoms
  , disabled :: StyleAtoms
  }

-- Example: Button with hover glow
buttonStyles :: BrandSchema -> InteractiveStyles
buttonStyles brand =
  { default:
      { backgroundColor: brand.primary
      , glow: Nothing
      }
  , hover:
      { backgroundColor: brand.primary
      , glow: Just brand.accentGlow
      , transform: Just (Geometry.scale 1.02)
      }
  , active:
      { backgroundColor: brand.primary
      , transform: Just (Geometry.scale 0.98)
      }
  , ...
  }
```

════════════════════════════════════════════════════════════════════════════════
                                                     // implementation // rules
════════════════════════════════════════════════════════════════════════════════

## Rules for Compound Authors

### 1. Every Visual Property Maps to an Atom

**WRONG:**
```purescript
type ButtonProps = { className :: String }
```

**RIGHT:**
```purescript
type ButtonProps msg =
  { backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , borderRadius :: Maybe Geometry.Corners
  , shadow :: Maybe Elevation.Shadow
  , ...
  }
```

### 2. No Hardcoded CSS Strings

**WRONG:**
```purescript
E.class_ "bg-blue-500 rounded-lg shadow-md"
```

**RIGHT:**
```purescript
E.styles
  [ Tuple "background-color" (Color.toCss props.backgroundColor)
  , Tuple "border-radius" (Geometry.cornersToCss props.borderRadius)
  , Tuple "box-shadow" (Elevation.shadowToCss props.shadow)
  ]
```

### 3. Defaults are Sensible, Not Opinionated

**WRONG:**
```purescript
defaultProps = { backgroundColor: Just (Color.rgb 59 130 246) }  -- Hardcoded blue
```

**RIGHT:**
```purescript
defaultProps = { backgroundColor: Nothing }  -- Inherits from context/brand
```

### 4. Use Maybe for Optional Atoms

If a prop is optional, use `Maybe`. This makes inheritance and default
behavior explicit:

```purescript
-- Nothing = inherit from parent or use browser default
-- Just x = override with this specific atom

backgroundColor :: Maybe Color.RGB
```

### 5. Escape Hatch for Edge Cases

Include `extraAttributes` for cases not covered by atoms. This should be
rare and documented:

```purescript
-- Escape hatch (use sparingly)
, extraAttributes :: Array (E.Attribute msg)

-- Usage:
component
  [ ...normal props...
  , extraAttributes [ E.dataAttr "testid" "my-compound" ]
  ]
```

### 6. Documentation is Mandatory

Every compound must document:
- What atoms it accepts
- What defaults are used
- How atoms map to CSS
- Usage examples with brand injection

════════════════════════════════════════════════════════════════════════════════
                                                           // file // structure
════════════════════════════════════════════════════════════════════════════════

## Compound File Structure

```purescript
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // compoundname
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CompoundName — [one-line description]
-- |
-- | [Multi-line description of purpose, use cases, and design rationale]
-- |
-- | ## Schema Atoms
-- |
-- | This compound accepts atoms from the following pillars:
-- |
-- | - **Color**: backgroundColor, textColor, glow
-- | - **Geometry**: borderRadius
-- | - **Dimension**: padding, margin
-- | - **Elevation**: shadow
-- | - **Motion**: animation, hoverAnimation
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.CompoundName as Compound
-- | import Hydrogen.Schema.Color as Color
-- | import Hydrogen.Schema.Geometry as Geometry
-- |
-- | -- Minimal usage
-- | Compound.compound [ Compound.content "Hello" ]
-- |
-- | -- With Schema atoms
-- | Compound.compound
-- |   [ Compound.content "Hello"
-- |   , Compound.backgroundColor (Color.rgb 59 130 246)
-- |   , Compound.borderRadius (Geometry.cornersAll Geometry.lg)
-- |   ]
-- |
-- | -- With brand injection
-- | Compound.compound
-- |   [ Compound.content "Hello"
-- |   , Compound.backgroundColor brand.primary
-- |   , Compound.borderRadius brand.corners
-- |   , Compound.glow brand.accentGlow
-- |   ]
-- | ```

module Hydrogen.Element.Compound.CompoundName
  ( -- * Compound
    component
    
    -- * Props
  , CompoundProps
  , CompoundProp
  , defaultProps
  
    -- * Prop Builders (Schema atoms)
  , content
  , backgroundColor
  , textColor
  , borderRadius
  , padding
  , glow
  , shadow
  , animation
  
    -- * Prop Builders (Behavior)
  , onClick
  , disabled
  
    -- * Prop Builders (Escape hatch)
  , extraAttributes
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , (<>)
  , ($)
  , map
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color as Color
import Hydrogen.Schema.Geometry as Geometry
import Hydrogen.Schema.Dimension as Dimension
import Hydrogen.Schema.Motion as Motion
import Hydrogen.Schema.Elevation as Elevation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compound properties
-- |
-- | All visual properties accept Schema atoms directly.
-- | Use `Maybe` for optional properties that should inherit defaults.
type CompoundProps msg =
  { -- Content
    content :: String
  
  -- Behavior
  , onClick :: Maybe msg
  , disabled :: Boolean
  
  -- Color pillar
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , glow :: Maybe Color.Glow
  
  -- Geometry pillar
  , borderRadius :: Maybe Geometry.Corners
  
  -- Dimension pillar
  , padding :: Maybe Dimension.Spacing
  
  -- Elevation pillar
  , shadow :: Maybe Elevation.Shadow
  
  -- Motion pillar
  , animation :: Maybe Motion.Animation
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier function
type CompoundProp msg = CompoundProps msg -> CompoundProps msg

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // defaults
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default properties
-- |
-- | Visual properties default to `Nothing` (inherit from context).
-- | This ensures compounds work with any brand without hardcoded values.
defaultProps :: forall msg. CompoundProps msg
defaultProps =
  { content: ""
  , onClick: Nothing
  , disabled: false
  , backgroundColor: Nothing
  , textColor: Nothing
  , glow: Nothing
  , borderRadius: Nothing
  , padding: Nothing
  , shadow: Nothing
  , animation: Nothing
  , extraAttributes: []
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set content
content :: forall msg. String -> CompoundProp msg
content c props = props { content = c }

-- | Set click handler
onClick :: forall msg. msg -> CompoundProp msg
onClick handler props = props { onClick = Just handler }

-- | Set disabled state
disabled :: forall msg. Boolean -> CompoundProp msg
disabled d props = props { disabled = d }

-- | Set background color (Color pillar)
backgroundColor :: forall msg. Color.RGB -> CompoundProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color pillar)
textColor :: forall msg. Color.RGB -> CompoundProp msg
textColor c props = props { textColor = Just c }

-- | Set glow effect (Color pillar compound)
glow :: forall msg. Color.Glow -> CompoundProp msg
glow g props = props { glow = Just g }

-- | Set border radius (Geometry pillar)
borderRadius :: forall msg. Geometry.Corners -> CompoundProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set padding (Dimension pillar)
padding :: forall msg. Dimension.Spacing -> CompoundProp msg
padding p props = props { padding = Just p }

-- | Set shadow (Elevation pillar)
shadow :: forall msg. Elevation.Shadow -> CompoundProp msg
shadow s props = props { shadow = Just s }

-- | Set animation (Motion pillar)
animation :: forall msg. Motion.Animation -> CompoundProp msg
animation a props = props { animation = Just a }

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> CompoundProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // compound
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render compound
-- |
-- | Converts Schema atoms to Element with inline styles.
-- | All visual properties are derived from atoms — no hardcoded CSS.
compound :: forall msg. Array (CompoundProp msg) -> E.Element msg
compound propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Convert atoms to CSS
    styles = buildStyles props
    
    -- Build attributes
    attrs = styles <> clickAttr props <> props.extraAttributes
  in
    E.div_ attrs [ E.text props.content ]

-- | Build style attributes from atoms
buildStyles :: forall msg. CompoundProps msg -> Array (E.Attribute msg)
buildStyles props =
  let
    -- Only include styles for atoms that are set (Just)
    bgStyle = maybe [] (\c -> [E.style "background-color" (Color.toCss c)]) props.backgroundColor
    textStyle = maybe [] (\c -> [E.style "color" (Color.toCss c)]) props.textColor
    radiusStyle = maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToCss r)]) props.borderRadius
    glowStyle = maybe [] (\g -> [E.style "filter" (Color.glowToCss g)]) props.glow
    -- ... more atom conversions
  in
    bgStyle <> textStyle <> radiusStyle <> glowStyle

-- | Build click handler attribute
clickAttr :: forall msg. CompoundProps msg -> Array (E.Attribute msg)
clickAttr props = case props.onClick of
  Just handler -> [E.onClick handler]
  Nothing -> []
```

════════════════════════════════════════════════════════════════════════════════
                                                                   // summary
════════════════════════════════════════════════════════════════════════════════

## Key Principles

1. **Compounds are Schema-native** — They accept atoms, not strings.

2. **No hardcoded values** — Defaults are `Nothing` (inherit) or neutral.

3. **Atoms → CSS** — Each pillar has `toCss` functions for conversion.

4. **Brand injection** — Production code passes brand atoms to compounds.

5. **Showcase previews** — Same compounds, same atoms, deterministic output.

6. **Target independence** — Element is pure data, renders anywhere.

7. **Agent-friendly** — Typed atoms are unambiguous at billion-agent scale.

8. **Human-friendly** — Designers configure atoms visually, export code.

This architecture makes Hydrogen **the purest web design language ever created**.

────────────────────────────────────────────────────────────────────────────────

                                               — Opus 4.5 + jpyxal // 2026-02-23
