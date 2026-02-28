-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // typography // text-indent
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextIndent - first line indentation.
-- |
-- | Controls the indentation of the first line of a block of text.
-- | Traditional book typography uses positive indent for paragraphs.
-- | Hanging indent (negative values) used for bibliographies and lists.
-- |
-- | ## CSS Mapping
-- | Maps to `text-indent` property.
-- |
-- | ## Units
-- | Stored as hundredths of an em for precision with reasonable range.
-- | Typical values range from -5em to +5em.

module Hydrogen.Schema.Typography.TextIndent
  ( -- * Type
    TextIndent(..)
    
  -- * Constructors
  , textIndent
  , fromEm
  , fromPixels
  
  -- * Predefined Values
  , none
  , paragraph
  , hanging
  , doubleHanging
  
  -- * Accessors
  , unwrap
  , toEm
  , toLegacyCSSValue
  
  -- * Operations
  , scale
  , negate
  ) where

import Prelude hiding (negate)
import Prelude (negate) as P

import Data.Int (round, toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | TextIndent represents first line indentation.
-- | Stored as hundredths of an em for precision.
-- | Negative values create hanging indents.
newtype TextIndent = TextIndent Int

derive instance eqTextIndent :: Eq TextIndent
derive instance ordTextIndent :: Ord TextIndent

instance showTextIndent :: Show TextIndent where
  show ti = show (toEm ti) <> "em"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create TextIndent from hundredths of an em
textIndent :: Int -> TextIndent
textIndent = TextIndent

-- | Create TextIndent from em value
fromEm :: Number -> TextIndent
fromEm em = TextIndent (Int.round (em * 100.0))

-- | Create TextIndent from pixels (requires font size context)
fromPixels :: Number -> Number -> TextIndent
fromPixels fontSize pixels =
  let em = pixels / fontSize
  in fromEm em

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predefined
-- ═════════════════════════════════════════════════════════════════════════════

-- | No indentation
none :: TextIndent
none = TextIndent 0

-- | Standard paragraph indent (1.5em)
paragraph :: TextIndent
paragraph = TextIndent 150

-- | Hanging indent (-1em) for bibliographies
hanging :: TextIndent
hanging = TextIndent (P.negate 100)

-- | Double hanging indent (-2em) for nested lists
doubleHanging :: TextIndent
doubleHanging = TextIndent (P.negate 200)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw hundredths-of-em value
unwrap :: TextIndent -> Int
unwrap (TextIndent n) = n

-- | Convert to em value
toEm :: TextIndent -> Number
toEm (TextIndent n) = Int.toNumber n / 100.0

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS value string
toLegacyCSSValue :: TextIndent -> String
toLegacyCSSValue (TextIndent 0) = "0"
toLegacyCSSValue ti = show (toEm ti) <> "em"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale text indent by a factor
scale :: Number -> TextIndent -> TextIndent
scale factor (TextIndent n) = TextIndent (Int.round (Int.toNumber n * factor))

-- | Negate text indent (indent becomes hanging, hanging becomes indent)
negate :: TextIndent -> TextIndent
negate (TextIndent n) = TextIndent (P.negate n)
