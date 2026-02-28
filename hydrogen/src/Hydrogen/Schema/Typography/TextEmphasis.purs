-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // typography // text-emphasis
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextEmphasis - CJK emphasis marks and typographic stress.
-- |
-- | In East Asian typography, emphasis is typically indicated by small marks
-- | placed above (horizontal) or beside (vertical) characters, rather than
-- | using italics or bold (which are Western conventions).
-- |
-- | ## Mark shapes
-- |
-- | - **Dot**: Solid circle (●) — most common in Simplified Chinese
-- | - **Circle**: Hollow circle (○) — common in Traditional Chinese
-- | - **DoubleCircle**: Bullseye (◎) — strong emphasis
-- | - **Triangle**: Solid triangle (▲) — used in some publications
-- | - **Sesame**: Sesame seed shape (﹅) — traditional Japanese emphasis
-- |
-- | ## Position
-- |
-- | - **Over**: Marks above text (default for horizontal writing)
-- | - **Under**: Marks below text (common in Traditional Chinese)
-- |
-- | For vertical writing, "over" means to the right and "under" means to the left.
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `text-emphasis`, `text-emphasis-style`, `text-emphasis-color`,
-- | `text-emphasis-position`.

module Hydrogen.Schema.Typography.TextEmphasis
  ( -- * Atoms
    EmphasisShape(..)
  , EmphasisFill(..)
  , EmphasisPosition(..)
  
  -- * Compound
  , TextEmphasis(..)
  
  -- * Constructors
  , none
  , dot
  , circle
  , doubleCircle
  , triangle
  , sesame
  , filledDot
  , openDot
  , filledCircle
  , openCircle
  , filledSesame
  , openSesame
  , custom
  
  -- * Modifiers
  , withPosition
  , withColor
  , over
  , under
  
  -- * Predicates
  , isVisible
  , isFilled
  , isOpen
  , isOverText
  , isUnderText
  
  -- * CSS Output
  , toLegacyCss
  , toShorthand
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // emphasis shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of emphasis mark
-- |
-- | The specific glyph used to mark emphasized text.
data EmphasisShape
  = ShapeNone         -- ^ No emphasis marks
  | ShapeDot          -- ^ Dot (● or ○)
  | ShapeCircle       -- ^ Circle (○ or ●)
  | ShapeDoubleCircle -- ^ Bullseye/double circle (◎)
  | ShapeTriangle     -- ^ Triangle (▲ or △)
  | ShapeSesame       -- ^ Sesame seed (﹅ or ﹆)

derive instance eqEmphasisShape :: Eq EmphasisShape
derive instance ordEmphasisShape :: Ord EmphasisShape

instance showEmphasisShape :: Show EmphasisShape where
  show ShapeNone = "ShapeNone"
  show ShapeDot = "ShapeDot"
  show ShapeCircle = "ShapeCircle"
  show ShapeDoubleCircle = "ShapeDoubleCircle"
  show ShapeTriangle = "ShapeTriangle"
  show ShapeSesame = "ShapeSesame"

-- | Convert shape to CSS value
shapeToLegacyCss :: EmphasisShape -> String
shapeToLegacyCss ShapeNone = "none"
shapeToLegacyCss ShapeDot = "dot"
shapeToLegacyCss ShapeCircle = "circle"
shapeToLegacyCss ShapeDoubleCircle = "double-circle"
shapeToLegacyCss ShapeTriangle = "triangle"
shapeToLegacyCss ShapeSesame = "sesame"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // emphasis fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill style of emphasis mark
-- |
-- | Whether the mark is filled (solid) or open (outline).
data EmphasisFill
  = Filled -- ^ Solid/filled mark (default)
  | Open   -- ^ Outline/hollow mark

derive instance eqEmphasisFill :: Eq EmphasisFill
derive instance ordEmphasisFill :: Ord EmphasisFill

instance showEmphasisFill :: Show EmphasisFill where
  show Filled = "Filled"
  show Open = "Open"

-- | Convert fill to CSS value
fillToLegacyCss :: EmphasisFill -> String
fillToLegacyCss Filled = "filled"
fillToLegacyCss Open = "open"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // emphasis position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of emphasis marks relative to text
-- |
-- | In horizontal writing:
-- | - Over: marks appear above text
-- | - Under: marks appear below text
-- |
-- | In vertical writing:
-- | - Over: marks appear to the right of text
-- | - Under: marks appear to the left of text
data EmphasisPosition
  = PositionOver  -- ^ Above (horizontal) or right (vertical)
  | PositionUnder -- ^ Below (horizontal) or left (vertical)

derive instance eqEmphasisPosition :: Eq EmphasisPosition
derive instance ordEmphasisPosition :: Ord EmphasisPosition

instance showEmphasisPosition :: Show EmphasisPosition where
  show PositionOver = "PositionOver"
  show PositionUnder = "PositionUnder"

-- | Convert position to CSS value
-- |
-- | Note: CSS also requires writing mode context (over right, under left)
-- | but for simplicity we default to standard horizontal mode positions.
positionToLegacyCss :: EmphasisPosition -> String
positionToLegacyCss PositionOver = "over right"
positionToLegacyCss PositionUnder = "under left"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // text emphasis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete text emphasis specification
-- |
-- | Combines shape, fill, position, and color into a complete emphasis style.
newtype TextEmphasis = TextEmphasis
  { shape :: EmphasisShape
  , fill :: EmphasisFill
  , position :: EmphasisPosition
  , color :: Maybe String  -- CSS color string (or Nothing for currentColor)
  }

derive instance eqTextEmphasis :: Eq TextEmphasis

instance showTextEmphasis :: Show TextEmphasis where
  show (TextEmphasis te) =
    "TextEmphasis { shape: " <> show te.shape <>
    ", fill: " <> show te.fill <>
    ", position: " <> show te.position <>
    ", color: " <> show te.color <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | No emphasis marks
none :: TextEmphasis
none = TextEmphasis
  { shape: ShapeNone
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Filled dot emphasis (default Simplified Chinese style)
dot :: TextEmphasis
dot = TextEmphasis
  { shape: ShapeDot
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Circle emphasis (default Traditional Chinese style)
circle :: TextEmphasis
circle = TextEmphasis
  { shape: ShapeCircle
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Double circle emphasis (strong emphasis)
doubleCircle :: TextEmphasis
doubleCircle = TextEmphasis
  { shape: ShapeDoubleCircle
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Triangle emphasis
triangle :: TextEmphasis
triangle = TextEmphasis
  { shape: ShapeTriangle
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Sesame emphasis (traditional Japanese style)
sesame :: TextEmphasis
sesame = TextEmphasis
  { shape: ShapeSesame
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Filled dot (explicit)
filledDot :: TextEmphasis
filledDot = TextEmphasis
  { shape: ShapeDot
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Open dot (hollow)
openDot :: TextEmphasis
openDot = TextEmphasis
  { shape: ShapeDot
  , fill: Open
  , position: PositionOver
  , color: Nothing
  }

-- | Filled circle (explicit)
filledCircle :: TextEmphasis
filledCircle = TextEmphasis
  { shape: ShapeCircle
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Open circle (hollow)
openCircle :: TextEmphasis
openCircle = TextEmphasis
  { shape: ShapeCircle
  , fill: Open
  , position: PositionOver
  , color: Nothing
  }

-- | Filled sesame
filledSesame :: TextEmphasis
filledSesame = TextEmphasis
  { shape: ShapeSesame
  , fill: Filled
  , position: PositionOver
  , color: Nothing
  }

-- | Open sesame (hollow)
openSesame :: TextEmphasis
openSesame = TextEmphasis
  { shape: ShapeSesame
  , fill: Open
  , position: PositionOver
  , color: Nothing
  }

-- | Custom emphasis with all parameters
custom :: EmphasisShape -> EmphasisFill -> EmphasisPosition -> Maybe String -> TextEmphasis
custom sh fi po co = TextEmphasis
  { shape: sh
  , fill: fi
  , position: po
  , color: co
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Change the position
withPosition :: EmphasisPosition -> TextEmphasis -> TextEmphasis
withPosition p (TextEmphasis te) = TextEmphasis te { position = p }

-- | Change the color
withColor :: String -> TextEmphasis -> TextEmphasis
withColor c (TextEmphasis te) = TextEmphasis te { color = Just c }

-- | Position marks over (above) text
over :: TextEmphasis -> TextEmphasis
over = withPosition PositionOver

-- | Position marks under (below) text
under :: TextEmphasis -> TextEmphasis
under = withPosition PositionUnder

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this emphasis visible (not none)?
isVisible :: TextEmphasis -> Boolean
isVisible (TextEmphasis { shape: ShapeNone }) = false
isVisible _ = true

-- | Is this a filled (solid) style?
isFilled :: TextEmphasis -> Boolean
isFilled (TextEmphasis { fill: Filled }) = true
isFilled _ = false

-- | Is this an open (outline) style?
isOpen :: TextEmphasis -> Boolean
isOpen (TextEmphasis { fill: Open }) = true
isOpen _ = false

-- | Are marks positioned over (above) text?
isOverText :: TextEmphasis -> Boolean
isOverText (TextEmphasis { position: PositionOver }) = true
isOverText _ = false

-- | Are marks positioned under (below) text?
isUnderText :: TextEmphasis -> Boolean
isUnderText (TextEmphasis { position: PositionUnder }) = true
isUnderText _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to full CSS declarations
toLegacyCss :: TextEmphasis -> String
toLegacyCss (TextEmphasis te) = case te.shape of
  ShapeNone -> "text-emphasis: none;"
  _ ->
    "text-emphasis-style: " <> fillToLegacyCss te.fill <> " " <> shapeToLegacyCss te.shape <> ";\n" <>
    "text-emphasis-position: " <> positionToLegacyCss te.position <> ";" <>
    case te.color of
      Nothing -> ""
      Just c -> "\ntext-emphasis-color: " <> c <> ";"

-- | Convert to text-emphasis shorthand
toShorthand :: TextEmphasis -> String
toShorthand (TextEmphasis te) = case te.shape of
  ShapeNone -> "text-emphasis: none;"
  _ ->
    "text-emphasis: " <>
    fillToLegacyCss te.fill <> " " <>
    shapeToLegacyCss te.shape <>
    case te.color of
      Nothing -> ";"
      Just c -> " " <> c <> ";"
