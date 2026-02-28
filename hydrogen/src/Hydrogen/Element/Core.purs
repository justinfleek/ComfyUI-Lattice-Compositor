-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // element // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Core — Pure data description of visual elements.
-- |
-- | ## Purpose
-- |
-- | This module defines the CORRECT Element type: pure data composed entirely
-- | from Schema atoms. No strings. No DOM concepts. No CSS. No JavaScript.
-- |
-- | This replaces the broken `Hydrogen.Render.Element` which uses:
-- |   - `tag :: String` (unbounded, non-deterministic)
-- |   - `Attr String String` (CSS as strings)
-- |
-- | ## Architecture
-- |
-- | Element is pure data that flows:
-- |   Haskell backend → PureScript types → WebGPU execution
-- |
-- | There is no browser in this stack. JavaScript is treated as legacy
-- | bytecode only at the export boundary for broken legacy formats.
-- |
-- | ## Design Principles
-- |
-- | 1. **Composed from Schema atoms** — Every field uses bounded, typed atoms
-- | 2. **GPU-native** — Describes what to render, not how
-- | 3. **Deterministic** — Same Element = same pixels, always
-- | 4. **Serializable** — Can be sent over wire, stored, replayed
-- | 5. **Target-agnostic** — WebGPU, Canvas, Static HTML, any renderer
-- |
-- | ## What Element IS
-- |
-- | Element is a complete GPU instruction set as pure data:
-- |   - Shapes (Rectangle, Ellipse, Path)
-- |   - Fills (Solid, Gradient, Pattern, Noise)
-- |   - Strokes (Width, Color, Dash pattern, Caps, Joins)
-- |   - Transforms (Translate, Rotate, Scale, Skew)
-- |   - Compositions (Group, Clip, Mask)
-- |
-- | ## What Element is NOT
-- |
-- | Element is NOT:
-- |   - A DOM abstraction (no "div", "span", "button")
-- |   - A CSS generator (no "background-color", "border-radius")
-- |   - A framework adapter (no Halogen, React, Vue concepts)
-- |   - JavaScript-dependent (no FFI for core operations)
-- |
-- | ## Migration Path
-- |
-- | The old `Hydrogen.Render.Element` has 172 dependents.
-- | Migration is gradual:
-- |   1. This module defines the correct type
-- |   2. Export layer converts Element → legacy formats when needed
-- |   3. Components migrate one at a time
-- |   4. Eventually the broken module becomes unused
-- |
-- | ## Dependencies (Schema atoms only)
-- |
-- | - Hydrogen.Schema.Geometry.Shape (RectangleShape, EllipseShape, PathShape)
-- | - Hydrogen.Schema.Material.Fill (Fill)
-- | - Hydrogen.Schema.Geometry.Stroke (LineCap, LineJoin, MiterLimit)
-- | - Hydrogen.Schema.Dimension.Stroke (StrokeWidth, DashPattern)
-- | - Hydrogen.Schema.Geometry.Transform (Transform2D)
-- | - Hydrogen.Schema.Color.Opacity (Opacity)

module Hydrogen.Element.Core
  ( -- * Core Element Type
    Element(..)
    
  -- * Spec Types
  , RectangleSpec
  , EllipseSpec
  , PathSpec
  , TextSpec
  , GlyphSpec
  , GroupSpec
  , TransformSpec
  , StrokeSpec
  
  -- * Smart Constructors
  , rectangle
  , ellipse
  , path
  , text
  , group
  , transform
  , empty
  
  -- * Stroke Constructors
  , stroke
  , strokeWith
  , noStroke
  
  -- * Re-exports for stroke configuration
  -- Users need these to customize strokes without additional imports
  , module ReExportLineCap
  , module ReExportLineJoin
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , (==)
  , (&&)
  , (+)
  , (<>)
  )

import Data.Array (length, index) as Array
import Data.Maybe (Maybe(Just, Nothing))

-- Schema atoms: Geometry
import Hydrogen.Schema.Geometry.Shape
  ( RectangleShape
  , EllipseShape
  , PathShape
  )
import Hydrogen.Schema.Geometry.Transform (Transform2D)
import Hydrogen.Schema.Geometry.Stroke
  ( LineCap(CapButt)
  , LineJoin(JoinMiter)
  , MiterLimit
  , miterLimitDefault
  ) as Stroke
import Hydrogen.Schema.Geometry.Stroke (LineCap(..)) as ReExportLineCap
import Hydrogen.Schema.Geometry.Stroke (LineJoin(..)) as ReExportLineJoin

-- Schema atoms: Material
import Hydrogen.Schema.Material.Fill (Fill, fillNone)

-- Schema atoms: Dimension
import Hydrogen.Schema.Dimension.Stroke
  ( StrokeWidth
  , DashPattern
  , strokeWidthNone
  , dashPatternSolid
  )

-- Schema atoms: Color
import Hydrogen.Schema.Color.Opacity (Opacity, opacity)

-- Schema atoms: Typography
import Hydrogen.Schema.Typography.GlyphGeometry (GlyphPath)

-- Schema atoms: Temporal
import Hydrogen.Schema.Temporal.Progress (Progress)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // stroke // spec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke specification for shapes — complete stroke definition.
-- |
-- | All fields are bounded Schema atoms:
-- | - StrokeWidth: 0-64px, clamped
-- | - Fill: solid, gradient, pattern, or none
-- | - LineCap: butt, round, square (enum)
-- | - LineJoin: miter, round, bevel (enum)
-- | - MiterLimit: 1-100, clamped
-- | - DashPattern: array of bounded lengths
-- | - Opacity: 0-100%, clamped
-- |
-- | No unbounded Numbers. No strings. No escape hatches.
type StrokeSpec =
  { width :: StrokeWidth             -- ^ Stroke thickness (0-64px)
  , fill :: Fill                     -- ^ Stroke color/gradient/pattern
  , cap :: Stroke.LineCap            -- ^ Line endpoint style
  , join :: Stroke.LineJoin          -- ^ Line corner style
  , miterLimit :: Stroke.MiterLimit  -- ^ When miter becomes bevel
  , dashPattern :: DashPattern       -- ^ Dash/gap pattern
  , opacity :: Opacity               -- ^ Stroke opacity (0-100%)
  }

-- | Create a stroke specification with defaults for optional fields.
stroke :: StrokeWidth -> Fill -> StrokeSpec
stroke width fill =
  { width: width
  , fill: fill
  , cap: Stroke.CapButt
  , join: Stroke.JoinMiter
  , miterLimit: Stroke.miterLimitDefault
  , dashPattern: dashPatternSolid
  , opacity: opacity 100
  }

-- | Create a stroke with full customization.
-- |
-- | Use this when you need to specify cap, join, dash pattern, etc.
strokeWith 
  :: { width :: StrokeWidth
     , fill :: Fill
     , cap :: Stroke.LineCap
     , join :: Stroke.LineJoin
     , miterLimit :: Stroke.MiterLimit
     , dashPattern :: DashPattern
     , opacity :: Opacity
     }
  -> StrokeSpec
strokeWith spec = spec

-- | No stroke (zero width, transparent).
noStroke :: StrokeSpec
noStroke =
  { width: strokeWidthNone
  , fill: fillNone
  , cap: Stroke.CapButt
  , join: Stroke.JoinMiter
  , miterLimit: Stroke.miterLimitDefault
  , dashPattern: dashPatternSolid
  , opacity: opacity 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shape // specs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for rectangle elements.
-- |
-- | Composes Schema atoms:
-- | - RectangleShape: center, width, height, corner radii (all bounded)
-- | - Fill: solid, gradient, pattern, noise, or none
-- | - StrokeSpec: complete stroke definition with bounded atoms
-- | - Opacity: 0-100%, clamped
-- |
-- | Every field is a bounded Schema atom. Invalid states are unrepresentable.
type RectangleSpec =
  { shape :: RectangleShape       -- ^ Geometry (center, size, corners)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for ellipse elements.
-- |
-- | Circles are ellipses where radiusX == radiusY.
-- | All fields are bounded Schema atoms.
type EllipseSpec =
  { shape :: EllipseShape         -- ^ Geometry (center, radii)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for path elements.
-- |
-- | Paths are the most flexible shape — composed of path commands
-- | (MoveTo, LineTo, CubicTo, etc). Used for custom vector graphics,
-- | icons, illustrations.
-- |
-- | All path commands use bounded PixelPoint2D coordinates.
type PathSpec =
  { shape :: PathShape            -- ^ Geometry (commands, winding rule)
  , fill :: Fill                  -- ^ Interior fill
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Overall element opacity
  }

-- | Specification for a single glyph with full material/temporal stack.
-- |
-- | Each glyph is a complete renderable unit that can be individually
-- | styled and animated. This enables:
-- | - Per-character color (gradient text, rainbow effects)
-- | - Per-character animation (wave, bounce, typewriter reveal)
-- | - Per-character transforms (rotation, scale for emphasis)
-- | - Diffusion/morphing effects via temporal progress
-- |
-- | The glyph path comes from font data (SDF or bezier).
-- | All other fields are bounded Schema atoms.
type GlyphSpec =
  { glyph :: GlyphPath            -- ^ Vector path data (beziers, SDF)
  , transform :: Transform2D      -- ^ Position, rotation, scale for this glyph
  , fill :: Fill                  -- ^ Glyph fill (solid, gradient, pattern, noise)
  , stroke :: Maybe StrokeSpec    -- ^ Optional outline
  , opacity :: Opacity            -- ^ Per-glyph opacity (for fade effects)
  , progress :: Progress          -- ^ Animation progress [0,1] for temporal effects
  }

-- | Specification for text elements.
-- |
-- | Text is an array of glyphs, each with independent styling.
-- | This is the GPU-native representation — no layout logic here,
-- | layout is performed BEFORE Element construction.
-- |
-- | ## Design
-- |
-- | Unlike legacy text rendering where all characters share one style,
-- | Element.Core text treats each glyph as a first-class shape with:
-- | - Independent fill (gradient per character, noise textures)
-- | - Independent stroke (outlined text effects)
-- | - Independent transform (per-character animation)
-- | - Independent progress (staggered reveals, diffusion)
-- |
-- | ## Animation
-- |
-- | The `progress` field on each glyph enables temporal effects:
-- | - 0.0 = start state (invisible, morphed, displaced)
-- | - 1.0 = end state (fully rendered)
-- | - Intermediate values for diffusion, reveal, morph animations
-- |
-- | ## Path Animation
-- |
-- | Glyphs can follow paths by encoding path position in transform.
-- | The runtime interprets transform + progress to compute final position.
type TextSpec =
  { glyphs :: Array GlyphSpec     -- ^ Individual glyphs with per-glyph styling
  , opacity :: Opacity            -- ^ Overall text opacity (multiplied with per-glyph)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // composition // specs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for groups of elements.
-- |
-- | Groups compose multiple elements into a single unit.
-- | The group itself can have opacity applied (affects all children).
type GroupSpec =
  { children :: Array Element     -- ^ Child elements
  , opacity :: Opacity            -- ^ Group opacity (applied to all children)
  }

-- | Specification for transformed elements.
-- |
-- | Wraps an Element with a 2D transform from Schema.Geometry.Transform.
-- | Transform2D includes: translate, rotate, scale, skew, origin
-- | All transform values are bounded (scale: -10 to 10, skew: -89 to 89, etc).
type TransformSpec =
  { transform :: Transform2D      -- ^ The transform to apply
  , child :: Element              -- ^ Element to transform
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // element // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | The core Element type — pure data describing visual elements.
-- |
-- | Element is a complete GPU instruction set as pure data. Every variant
-- | is composed entirely from Schema atoms. No strings. No CSS. No DOM.
-- | No JavaScript. Serializable. Deterministic.
-- |
-- | ## Variants
-- |
-- | **Primitives** (shapes with fill/stroke):
-- | - `Rectangle` — Axis-aligned rectangles with optional corner radius
-- | - `Ellipse` — Ellipses and circles
-- | - `Path` — Arbitrary vector paths (beziers, lines, arcs)
-- | - `Text` — Pre-laid-out text with positioned glyphs
-- |
-- | **Composition**:
-- | - `Group` — Combine multiple elements
-- | - `Transform` — Apply 2D transform to an element
-- |
-- | **Identity**:
-- | - `Empty` — No-op element (identity for composition)
-- |
-- | ## Determinism Guarantee
-- |
-- | Same Element value = same pixels. Always. This is guaranteed because
-- | every field is a bounded Schema atom with deterministic behavior.
-- | Two agents constructing the same Element get identical rendering.
-- |
-- | ## Monoid Structure
-- |
-- | Element forms a Monoid where:
-- | - `mempty` = `Empty`
-- | - `<>` = grouping (creates a Group from two elements)
-- |
-- | This allows: `element1 <> element2 <> element3` to compose naturally.
data Element
  = Rectangle RectangleSpec
  | Ellipse EllipseSpec
  | Path PathSpec
  | Text TextSpec
  | Group GroupSpec
  | Transform TransformSpec
  | Empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // instances
-- ═════════════════════════════════════════════════════════════════════════════

instance showElement :: Show Element where
  show (Rectangle _) = "(Element Rectangle)"
  show (Ellipse _) = "(Element Ellipse)"
  show (Path _) = "(Element Path)"
  show (Text _) = "(Element Text)"
  show (Group g) = "(Element Group [" <> show (Array.length g.children) <> " children])"
  show (Transform _) = "(Element Transform)"
  show Empty = "(Element Empty)"

-- | Eq instance for Element.
-- |
-- | Two Elements are equal if they have the same structure and all
-- | corresponding atoms are equal. This is essential for:
-- | - Diffing (only re-render what changed)
-- | - Caching (memoization of rendered output)
-- | - Testing (assert expected Element equals actual)
-- |
-- | Note: Comparing large Element trees is O(n) in tree size.
-- | For performance-critical code, consider structural hashing.
instance eqElement :: Eq Element where
  eq Empty Empty = true
  eq (Rectangle r1) (Rectangle r2) = eqRectangleSpec r1 r2
  eq (Ellipse e1) (Ellipse e2) = eqEllipseSpec e1 e2
  eq (Path p1) (Path p2) = eqPathSpec p1 p2
  eq (Text t1) (Text t2) = eqTextSpec t1 t2
  eq (Group g1) (Group g2) = eqGroupSpec g1 g2
  eq (Transform t1) (Transform t2) = eqTransformSpec t1 t2
  eq _ _ = false

-- | Compare RectangleSpec for equality
eqRectangleSpec :: RectangleSpec -> RectangleSpec -> Boolean
eqRectangleSpec r1 r2 =
  r1.shape == r2.shape &&
  r1.fill == r2.fill &&
  r1.stroke == r2.stroke &&
  r1.opacity == r2.opacity

-- | Compare EllipseSpec for equality
eqEllipseSpec :: EllipseSpec -> EllipseSpec -> Boolean
eqEllipseSpec e1 e2 =
  e1.shape == e2.shape &&
  e1.fill == e2.fill &&
  e1.stroke == e2.stroke &&
  e1.opacity == e2.opacity

-- | Compare PathSpec for equality
eqPathSpec :: PathSpec -> PathSpec -> Boolean
eqPathSpec p1 p2 =
  p1.shape == p2.shape &&
  p1.fill == p2.fill &&
  p1.stroke == p2.stroke &&
  p1.opacity == p2.opacity

-- | Compare GlyphSpec for equality
eqGlyphSpec :: GlyphSpec -> GlyphSpec -> Boolean
eqGlyphSpec g1 g2 =
  g1.glyph == g2.glyph &&
  g1.transform == g2.transform &&
  g1.fill == g2.fill &&
  g1.stroke == g2.stroke &&
  g1.opacity == g2.opacity &&
  g1.progress == g2.progress

-- | Compare arrays of GlyphSpec for equality
eqArrayGlyphSpec :: Array GlyphSpec -> Array GlyphSpec -> Boolean
eqArrayGlyphSpec a1 a2 =
  Array.length a1 == Array.length a2 &&
  eqArrayGlyphSpecHelper a1 a2 0

-- | Helper for GlyphSpec array comparison (index-based)
eqArrayGlyphSpecHelper :: Array GlyphSpec -> Array GlyphSpec -> Int -> Boolean
eqArrayGlyphSpecHelper a1 a2 idx =
  if idx == Array.length a1
    then true
    else case Array.index a1 idx of
      Nothing -> true  -- Should never happen if lengths match
      Just g1 -> case Array.index a2 idx of
        Nothing -> false
        Just g2 -> eqGlyphSpec g1 g2 && eqArrayGlyphSpecHelper a1 a2 (idx + 1)

-- | Compare TextSpec for equality
eqTextSpec :: TextSpec -> TextSpec -> Boolean
eqTextSpec t1 t2 =
  t1.opacity == t2.opacity &&
  eqArrayGlyphSpec t1.glyphs t2.glyphs

-- | Compare GroupSpec for equality
eqGroupSpec :: GroupSpec -> GroupSpec -> Boolean
eqGroupSpec g1 g2 =
  g1.opacity == g2.opacity &&
  eqArrayElement g1.children g2.children

-- | Compare TransformSpec for equality
eqTransformSpec :: TransformSpec -> TransformSpec -> Boolean
eqTransformSpec t1 t2 =
  t1.transform == t2.transform &&
  t1.child == t2.child

-- | Compare arrays of Elements for equality
eqArrayElement :: Array Element -> Array Element -> Boolean
eqArrayElement a1 a2 =
  Array.length a1 == Array.length a2 &&
  eqArrayElementHelper a1 a2 0

-- | Helper for array comparison (index-based to avoid stack overflow on large arrays)
eqArrayElementHelper :: Array Element -> Array Element -> Int -> Boolean
eqArrayElementHelper a1 a2 idx =
  if idx == Array.length a1
    then true
    else case Array.index a1 idx of
      Nothing -> true  -- Should never happen if lengths match
      Just e1 -> case Array.index a2 idx of
        Nothing -> false
        Just e2 -> e1 == e2 && eqArrayElementHelper a1 a2 (idx + 1)

-- | Semigroup: combining two elements creates a group.
instance semigroupElement :: Semigroup Element where
  append Empty b = b
  append a Empty = a
  append (Group g1) (Group g2) = Group { children: g1.children <> g2.children, opacity: opacity 100 }
  append (Group g) b = Group { children: g.children <> [b], opacity: g.opacity }
  append a (Group g) = Group { children: [a] <> g.children, opacity: g.opacity }
  append a b = Group { children: [a, b], opacity: opacity 100 }

-- | Monoid: Empty is the identity element.
instance monoidElement :: Monoid Element where
  mempty = Empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // smart constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a rectangle element.
rectangle :: RectangleSpec -> Element
rectangle = Rectangle

-- | Create an ellipse element.
ellipse :: EllipseSpec -> Element
ellipse = Ellipse

-- | Create a path element.
path :: PathSpec -> Element
path = Path

-- | Create a text element.
-- |
-- | Text is rendered from a pre-laid-out TextBlock. Use the typography
-- | layout functions to create the TextBlock, then wrap it here.
text :: TextSpec -> Element
text = Text

-- | Create a group of elements.
group :: Array Element -> Element
group children = Group { children: children, opacity: opacity 100 }

-- | Apply a transform to an element.
transform :: Transform2D -> Element -> Element
transform t child = Transform { transform: t, child: child }

-- | The empty element (identity for composition).
empty :: Element
empty = Empty
