-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // typography // tabsize
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TabSize — width of tab characters in monospace character units.
-- |
-- | ## Design Philosophy
-- |
-- | TabSize is a bounded integer atom representing how many character widths
-- | a tab character occupies. This is pure data — no CSS, no runtime concerns.
-- |
-- | The renderer (WebGPU, terminal emulator, etc.) interprets this value
-- | when laying out text containing tab characters.
-- |
-- | ## Bounds
-- |
-- | Range: 1 to 32 character widths
-- | - 1: Minimum meaningful tab (rare)
-- | - 2: Modern JS/TS convention
-- | - 4: Python/Java convention  
-- | - 8: Unix/terminal convention
-- | - 32: Practical maximum
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded
-- |
-- | ## Dependents
-- |
-- | - Text layout engine
-- | - Code block rendering
-- | - Terminal emulation

module Hydrogen.Schema.Typography.TabSize
  ( -- * TabSize Type
    TabSize
  
  -- * Constructors
  , tabSize
  , unsafeTabSize
  
  -- * Accessors
  , unwrap
  
  -- * Common Presets
  , two
  , four
  , eight
  
  -- * Bounds
  , bounds
  , minValue
  , maxValue
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , show
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tabsize type
-- ═════════════════════════════════════════════════════════════════════════════

-- | TabSize atom.
-- |
-- | Width of tab characters measured in monospace character units.
-- | Bounded to practical range 1-32.
newtype TabSize = TabSize Int

derive instance eqTabSize :: Eq TabSize
derive instance ordTabSize :: Ord TabSize

instance showTabSizeInstance :: Show TabSize where
  show (TabSize n) = "(TabSize " <> show n <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create tab size with clamping to bounds.
-- |
-- | Values outside 1-32 are clamped.
tabSize :: Int -> TabSize
tabSize n = TabSize (Bounded.clampInt minValue maxValue n)

-- | Create tab size without validation.
-- |
-- | Use only when value is known to be in bounds.
unsafeTabSize :: Int -> TabSize
unsafeTabSize = TabSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the underlying value.
unwrap :: TabSize -> Int
unwrap (TabSize n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Two-character tab width.
-- |
-- | Modern convention for JavaScript, TypeScript, Ruby.
two :: TabSize
two = TabSize 2

-- | Four-character tab width.
-- |
-- | Convention for Python (PEP 8), Java, C++.
four :: TabSize
four = TabSize 4

-- | Eight-character tab width.
-- |
-- | Historical Unix/terminal convention.
eight :: TabSize
eight = TabSize 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum valid tab size.
minValue :: Int
minValue = 1

-- | Maximum valid tab size.
maxValue :: Int
maxValue = 32

-- | Bounds documentation for this type.
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds minValue maxValue "tabSize" "Tab width in character units"
