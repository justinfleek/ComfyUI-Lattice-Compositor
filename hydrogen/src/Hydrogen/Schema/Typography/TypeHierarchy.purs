-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // typography // type-hierarchy
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TypeHierarchy - semantic typographic levels mapped to TypeStyles.
-- |
-- | A complete typographic system for an application or brand:
-- | - **Hero (HL)**: Largest display text, marketing headlines
-- | - **H1-H6**: Standard heading hierarchy
-- | - **Body**: Primary reading text
-- | - **Small**: Secondary/supporting text
-- | - **Caption**: Labels, metadata
-- | - **Overline**: Category labels, eyebrow text
-- |
-- | Example from Sentience brand:
-- | - HL-H3: Archivo ExtraBold, UPPERCASE, tracking 25, line-height 1.3
-- | - H4-H6: Poppins Bold, Normal case, tracking 40, line-height 1.3
-- | - Body: Poppins Regular, Normal case, tracking 40, line-height 1.6

module Hydrogen.Schema.Typography.TypeHierarchy
  ( TypeHierarchy
  , HierarchyLevel(..)
  , typeHierarchy
  -- Accessors
  , hero
  , h1
  , h2
  , h3
  , h4
  , h5
  , h6
  , body
  , small
  , caption
  , overline
  , styleFor
  -- Generation
  , generate
  , GenerateConfig
  -- CSS
  , toLegacyCss
  ) where

import Prelude

import Hydrogen.Schema.Typography.FontWeight (FontWeight)
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Typography.LetterSpacing (LetterSpacing)
import Hydrogen.Schema.Typography.LetterSpacing as LetterSpacing
import Hydrogen.Schema.Typography.LineHeight (LineHeight)
import Hydrogen.Schema.Typography.TextTransform (TextTransform(None, Uppercase))
import Hydrogen.Schema.Typography.TypeScale (TypeScale)
import Hydrogen.Schema.Typography.TypeScale as TypeScale
import Hydrogen.Schema.Typography.TypeStyle (TypeStyle, FontStack)
import Hydrogen.Schema.Typography.TypeStyle as TypeStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hierarchy level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic hierarchy levels
-- |
-- | These represent the roles text plays, not just sizes.
data HierarchyLevel
  = Hero     -- ^ Largest display, marketing headlines
  | H1       -- ^ Primary heading
  | H2       -- ^ Secondary heading
  | H3       -- ^ Tertiary heading
  | H4       -- ^ Quaternary heading
  | H5       -- ^ Quinary heading
  | H6       -- ^ Senary heading
  | Body     -- ^ Primary reading text
  | Small    -- ^ Secondary text
  | Caption  -- ^ Labels, metadata
  | Overline -- ^ Category labels, eyebrow text

derive instance eqHierarchyLevel :: Eq HierarchyLevel
derive instance ordHierarchyLevel :: Ord HierarchyLevel

instance showHierarchyLevel :: Show HierarchyLevel where
  show Hero = "hero"
  show H1 = "h1"
  show H2 = "h2"
  show H3 = "h3"
  show H4 = "h4"
  show H5 = "h5"
  show H6 = "h6"
  show Body = "body"
  show Small = "small"
  show Caption = "caption"
  show Overline = "overline"

-- | Get the scale step for each hierarchy level
-- |
-- | Step 0 = body size. Positive = larger, negative = smaller.
levelStep :: HierarchyLevel -> Int
levelStep Hero = 7
levelStep H1 = 6
levelStep H2 = 5
levelStep H3 = 4
levelStep H4 = 3
levelStep H5 = 2
levelStep H6 = 1
levelStep Body = 0
levelStep Small = -1
levelStep Caption = -2
levelStep Overline = -2  -- Same size as caption, but different styling

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // type hierarchy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete typographic hierarchy
-- |
-- | Maps each semantic level to a complete TypeStyle.
newtype TypeHierarchy = TypeHierarchy
  { hero :: TypeStyle
  , h1 :: TypeStyle
  , h2 :: TypeStyle
  , h3 :: TypeStyle
  , h4 :: TypeStyle
  , h5 :: TypeStyle
  , h6 :: TypeStyle
  , body :: TypeStyle
  , small :: TypeStyle
  , caption :: TypeStyle
  , overline :: TypeStyle
  }

derive instance eqTypeHierarchy :: Eq TypeHierarchy

instance showTypeHierarchy :: Show TypeHierarchy where
  show _ = "TypeHierarchy {...}"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a type hierarchy from explicit styles
typeHierarchy
  :: { hero :: TypeStyle
     , h1 :: TypeStyle
     , h2 :: TypeStyle
     , h3 :: TypeStyle
     , h4 :: TypeStyle
     , h5 :: TypeStyle
     , h6 :: TypeStyle
     , body :: TypeStyle
     , small :: TypeStyle
     , caption :: TypeStyle
     , overline :: TypeStyle
     }
  -> TypeHierarchy
typeHierarchy = TypeHierarchy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the hero (display) style
hero :: TypeHierarchy -> TypeStyle
hero (TypeHierarchy th) = th.hero

-- | Get the H1 style
h1 :: TypeHierarchy -> TypeStyle
h1 (TypeHierarchy th) = th.h1

-- | Get the H2 style
h2 :: TypeHierarchy -> TypeStyle
h2 (TypeHierarchy th) = th.h2

-- | Get the H3 style
h3 :: TypeHierarchy -> TypeStyle
h3 (TypeHierarchy th) = th.h3

-- | Get the H4 style
h4 :: TypeHierarchy -> TypeStyle
h4 (TypeHierarchy th) = th.h4

-- | Get the H5 style
h5 :: TypeHierarchy -> TypeStyle
h5 (TypeHierarchy th) = th.h5

-- | Get the H6 style
h6 :: TypeHierarchy -> TypeStyle
h6 (TypeHierarchy th) = th.h6

-- | Get the body style
body :: TypeHierarchy -> TypeStyle
body (TypeHierarchy th) = th.body

-- | Get the small text style
small :: TypeHierarchy -> TypeStyle
small (TypeHierarchy th) = th.small

-- | Get the caption style
caption :: TypeHierarchy -> TypeStyle
caption (TypeHierarchy th) = th.caption

-- | Get the overline style
overline :: TypeHierarchy -> TypeStyle
overline (TypeHierarchy th) = th.overline

-- | Get style for a specific level
styleFor :: HierarchyLevel -> TypeHierarchy -> TypeStyle
styleFor Hero th = hero th
styleFor H1 th = h1 th
styleFor H2 th = h2 th
styleFor H3 th = h3 th
styleFor H4 th = h4 th
styleFor H5 th = h5 th
styleFor H6 th = h6 th
styleFor Body th = body th
styleFor Small th = small th
styleFor Caption th = caption th
styleFor Overline th = overline th

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for generating a type hierarchy
type GenerateConfig =
  { scale :: TypeScale
  , headingStack :: FontStack
  , bodyStack :: FontStack
  , headingWeight :: FontWeight
  , bodyWeight :: FontWeight
  , headingLineHeight :: LineHeight
  , bodyLineHeight :: LineHeight
  , headingLetterSpacing :: LetterSpacing
  , bodyLetterSpacing :: LetterSpacing
  , useUppercaseHeadings :: Boolean  -- Apply to Hero-H3
  }

-- | Generate a type hierarchy from a scale and configuration
-- |
-- | Automatically calculates font sizes from the scale and applies
-- | appropriate styles to each level.
generate :: GenerateConfig -> TypeHierarchy
generate cfg = TypeHierarchy
  { hero: makeHeading Hero
  , h1: makeHeading H1
  , h2: makeHeading H2
  , h3: makeHeading H3
  , h4: makeSubheading H4
  , h5: makeSubheading H5
  , h6: makeSubheading H6
  , body: makeBody Body
  , small: makeBody Small
  , caption: makeCaption
  , overline: makeOverline
  }
  where
  -- Large headings (Hero-H3): potentially uppercase, heading font
  makeHeading :: HierarchyLevel -> TypeStyle
  makeHeading level = TypeStyle.typeStyleWithStack
    cfg.headingStack
    cfg.headingWeight
    (TypeScale.sizeAt (levelStep level) cfg.scale)
    cfg.headingLineHeight
    (if cfg.useUppercaseHeadings then LetterSpacing.uppercase else cfg.headingLetterSpacing)
    (if cfg.useUppercaseHeadings then Uppercase else None)

  -- Smaller headings (H4-H6): normal case, heading font
  makeSubheading :: HierarchyLevel -> TypeStyle
  makeSubheading level = TypeStyle.typeStyleWithStack
    cfg.headingStack
    cfg.headingWeight
    (TypeScale.sizeAt (levelStep level) cfg.scale)
    cfg.headingLineHeight
    cfg.headingLetterSpacing
    None

  -- Body text levels
  makeBody :: HierarchyLevel -> TypeStyle
  makeBody level = TypeStyle.typeStyleWithStack
    cfg.bodyStack
    cfg.bodyWeight
    (TypeScale.sizeAt (levelStep level) cfg.scale)
    cfg.bodyLineHeight
    cfg.bodyLetterSpacing
    None

  -- Caption: smaller body font
  makeCaption :: TypeStyle
  makeCaption = TypeStyle.typeStyleWithStack
    cfg.bodyStack
    cfg.bodyWeight
    (TypeScale.sizeAt (levelStep Caption) cfg.scale)
    cfg.bodyLineHeight
    cfg.bodyLetterSpacing
    None

  -- Overline: uppercase caption
  makeOverline :: TypeStyle
  makeOverline = TypeStyle.typeStyleWithStack
    cfg.bodyStack
    FontWeight.semiBold
    (TypeScale.sizeAt (levelStep Overline) cfg.scale)
    cfg.bodyLineHeight
    LetterSpacing.uppercase
    Uppercase

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary - pure string generation.
-- | Generate CSS custom properties for the hierarchy
toLegacyCss :: TypeHierarchy -> String
toLegacyCss th = 
  ".hero {\n" <> TypeStyle.toLegacyCss (hero th) <> "\n}\n\n" <>
  "h1, .h1 {\n" <> TypeStyle.toLegacyCss (h1 th) <> "\n}\n\n" <>
  "h2, .h2 {\n" <> TypeStyle.toLegacyCss (h2 th) <> "\n}\n\n" <>
  "h3, .h3 {\n" <> TypeStyle.toLegacyCss (h3 th) <> "\n}\n\n" <>
  "h4, .h4 {\n" <> TypeStyle.toLegacyCss (h4 th) <> "\n}\n\n" <>
  "h5, .h5 {\n" <> TypeStyle.toLegacyCss (h5 th) <> "\n}\n\n" <>
  "h6, .h6 {\n" <> TypeStyle.toLegacyCss (h6 th) <> "\n}\n\n" <>
  "body, .body {\n" <> TypeStyle.toLegacyCss (body th) <> "\n}\n\n" <>
  ".small {\n" <> TypeStyle.toLegacyCss (small th) <> "\n}\n\n" <>
  ".caption {\n" <> TypeStyle.toLegacyCss (caption th) <> "\n}\n\n" <>
  ".overline {\n" <> TypeStyle.toLegacyCss (overline th) <> "\n}"
