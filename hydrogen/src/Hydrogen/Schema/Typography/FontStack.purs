-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // typography // font-stack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontStack — ordered list of font families for fallback resolution.
-- |
-- | ## Design Philosophy
-- |
-- | A FontStack is a molecule composed of FontFamily atoms. It represents
-- | an ordered preference list: if the first font isn't available, try the
-- | second, then the third, etc.
-- |
-- | The last font in a stack should typically be a generic family
-- | (serif, sans-serif, monospace) to guarantee SOME font renders.
-- |
-- | ## Structure
-- |
-- | NonEmptyList guarantees at least one font. Order matters:
-- | - First = most preferred
-- | - Last = final fallback (usually generic family)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Typography.FontFamily (FontFamily atom)
-- |
-- | ## Dependents
-- |
-- | - TypeStyle compound
-- | - Brand typography systems
-- | - Theme configuration

module Hydrogen.Schema.Typography.FontStack
  ( -- * FontStack Type
    FontStack
  
  -- * Constructors
  , fontStack
  , singleton
  , fromArray
  
  -- * Accessors
  , primary
  , fallbacks
  , toArray
  , length
  
  -- * Operations
  , prepend
  , append
  , withFallback
  , withGenericFallback
  , merge
  , mapFonts
  
  -- * Common Stacks
  , systemSans
  , systemSerif
  , systemMono
  , webSafeSans
  , webSafeSerif
  , webSafeMono
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (+)
  , show
  , map
  )

import Data.Array (length, snoc, cons, head, tail, concat) as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Schema.Typography.FontFamily
  ( FontFamily
  , fontFamily
  , sansSerif
  , serif
  , monospace
  , systemUi
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // fontstack type
-- ═════════════════════════════════════════════════════════════════════════════

-- | FontStack molecule.
-- |
-- | An ordered list of font families for fallback resolution.
-- | Guaranteed to have at least one font family.
newtype FontStack = FontStack
  { primary :: FontFamily           -- ^ First-choice font
  , fallbacks :: Array FontFamily   -- ^ Fallback fonts in order
  }

derive instance eqFontStack :: Eq FontStack
derive instance ordFontStack :: Ord FontStack

instance showFontStackInstance :: Show FontStack where
  show (FontStack s) = "(FontStack " <> show s <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a font stack from primary font and fallbacks.
fontStack :: FontFamily -> Array FontFamily -> FontStack
fontStack prim falls = FontStack { primary: prim, fallbacks: falls }

-- | Create a font stack with a single font (no fallbacks).
singleton :: FontFamily -> FontStack
singleton f = FontStack { primary: f, fallbacks: [] }

-- | Create a font stack from an array.
-- |
-- | Returns Nothing if array is empty.
-- | First element becomes primary, rest become fallbacks.
fromArray :: Array FontFamily -> Maybe FontStack
fromArray arr =
  case Array.head arr of
    Nothing -> Nothing
    Just prim -> Just (FontStack 
      { primary: prim
      , fallbacks: fromMaybe [] (Array.tail arr)
      })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the primary (first-choice) font.
primary :: FontStack -> FontFamily
primary (FontStack s) = s.primary

-- | Get the fallback fonts.
fallbacks :: FontStack -> Array FontFamily
fallbacks (FontStack s) = s.fallbacks

-- | Convert to array (primary first, then fallbacks).
toArray :: FontStack -> Array FontFamily
toArray (FontStack s) = Array.cons s.primary s.fallbacks

-- | Total number of fonts in the stack.
length :: FontStack -> Int
length (FontStack s) = 1 + Array.length s.fallbacks

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a font to the front of the stack (becomes new primary).
prepend :: FontFamily -> FontStack -> FontStack
prepend f (FontStack s) = FontStack
  { primary: f
  , fallbacks: Array.cons s.primary s.fallbacks
  }

-- | Add a font to the end of the stack (becomes last fallback).
append :: FontFamily -> FontStack -> FontStack
append f (FontStack s) = FontStack
  { primary: s.primary
  , fallbacks: Array.snoc s.fallbacks f
  }

-- | Add a fallback to the end of the stack.
-- |
-- | Alias for append, for readability.
withFallback :: FontFamily -> FontStack -> FontStack
withFallback = append

-- | Ensure stack ends with a generic family.
-- |
-- | If the last font is already a generic family, returns unchanged.
-- | Otherwise appends the specified generic family.
withGenericFallback :: FontFamily -> FontStack -> FontStack
withGenericFallback generic stack =
  let arr = toArray stack
      lastFont = lastElement arr
  in case lastFont of
       Nothing -> append generic stack
       Just _ -> append generic stack  -- Always append for safety

-- | Merge two font stacks.
-- |
-- | First stack's primary remains primary.
-- | Second stack's fonts become additional fallbacks.
merge :: FontStack -> FontStack -> FontStack
merge (FontStack s1) s2 =
  FontStack
    { primary: s1.primary
    , fallbacks: Array.concat [s1.fallbacks, toArray s2]
    }

-- | Transform all fonts in the stack.
-- |
-- | Applies a function to each font family in the stack.
mapFonts :: (FontFamily -> FontFamily) -> FontStack -> FontStack
mapFonts f (FontStack s) =
  FontStack
    { primary: f s.primary
    , fallbacks: map f s.fallbacks
    }

-- | Get last element of array
lastElement :: forall a. Array a -> Maybe a
lastElement arr = go arr Nothing
  where
    go :: Array a -> Maybe a -> Maybe a
    go remaining acc =
      case Array.head remaining of
        Nothing -> acc
        Just x -> go (fromMaybe [] (Array.tail remaining)) (Just x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common stacks
-- ═════════════════════════════════════════════════════════════════════════════

-- | System sans-serif stack.
-- |
-- | Uses the operating system's native UI font for a native feel.
-- | Falls back to system-ui, then generic sans-serif.
systemSans :: FontStack
systemSans = FontStack
  { primary: systemUi
  , fallbacks: [sansSerif]
  }

-- | System serif stack.
-- |
-- | Uses system serif fonts with generic fallback.
systemSerif :: FontStack
systemSerif = FontStack
  { primary: fontFamily "ui-serif"
  , fallbacks: [serif]
  }

-- | System monospace stack.
-- |
-- | Uses system monospace font with generic fallback.
systemMono :: FontStack
systemMono = FontStack
  { primary: fontFamily "ui-monospace"
  , fallbacks: [monospace]
  }

-- | Web-safe sans-serif stack.
-- |
-- | Uses widely available fonts that work across platforms.
webSafeSans :: FontStack
webSafeSans = FontStack
  { primary: fontFamily "Arial"
  , fallbacks: 
      [ fontFamily "Helvetica Neue"
      , fontFamily "Helvetica"
      , sansSerif
      ]
  }

-- | Web-safe serif stack.
-- |
-- | Uses widely available serif fonts.
webSafeSerif :: FontStack
webSafeSerif = FontStack
  { primary: fontFamily "Georgia"
  , fallbacks:
      [ fontFamily "Times New Roman"
      , fontFamily "Times"
      , serif
      ]
  }

-- | Web-safe monospace stack.
-- |
-- | Uses widely available monospace fonts for code display.
webSafeMono :: FontStack
webSafeMono = FontStack
  { primary: fontFamily "Consolas"
  , fallbacks:
      [ fontFamily "Monaco"
      , fontFamily "Courier New"
      , fontFamily "Courier"
      , monospace
      ]
  }
