-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                            // hydrogen // css
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS class utilities and combinators
-- |
-- | This module provides utilities for building Tailwind class strings
-- | in a type-safe, composable way.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Style.Css as Css
-- |
-- | -- Combine classes
-- | Css.cx [ "flex", "items-center", "gap-4" ]  -- "flex items-center gap-4"
-- |
-- | -- Conditional classes
-- | Css.cx [ "btn", Css.when isActive "btn-active" ]
-- |
-- | -- Responsive variants
-- | Css.sm "hidden"   -- "sm:hidden"
-- | Css.md "flex"     -- "md:flex"
-- |
-- | -- State variants
-- | Css.hover "bg-primary"    -- "hover:bg-primary"
-- | Css.focus "ring-2"        -- "focus:ring-2"
-- | ```
module Hydrogen.Style.LegacyCss
  ( -- * Class Combinators
    cx
  , classes
  , when
  , unless
  , maybe
  , either
    -- * Responsive Variants
  , sm
  , md
  , lg
  , xl
  , xxl
    -- * State Variants
  , hover
  , focus
  , active
  , disabled
  , focusVisible
  , focusWithin
  , groupHover
  , groupFocus
  , peerHover
  , peerFocus
    -- * Pseudo Elements
  , before
  , after
  , placeholder
  , selection
  , firstLetter
  , firstLine
    -- * Pseudo Classes
  , first
  , last
  , odd
  , even
  , empty
    -- * Form States
  , checked
  , indeterminate
  , required
  , invalid
  , valid
    -- * Reduced Motion
  , motionSafe
  , motionReduce
    -- * Print
  , print
    -- * Arbitrary Values
  , arbitrary
  , arbitraryProperty
  ) where

import Prelude hiding (when)

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Maybe as M
import Data.Either (Either(Left, Right))
import Data.String as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // class combinators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine multiple class strings, filtering empty ones
-- |
-- | ```purescript
-- | cx [ "flex", "items-center", "", "gap-4" ]
-- | -- "flex items-center gap-4"
-- | ```
cx :: Array String -> String
cx = String.joinWith " " <<< Array.filter (not <<< String.null)

-- | Alias for cx
classes :: Array String -> String
classes = cx

-- | Conditionally include a class
-- |
-- | ```purescript
-- | cx [ "btn", when isActive "btn-active" ]
-- | ```
when :: Boolean -> String -> String
when true cls = cls
when false _ = ""

-- | Conditionally include a class (inverse of when)
unless :: Boolean -> String -> String
unless cond = when (not cond)

-- | Include a class based on Maybe
-- |
-- | ```purescript
-- | cx [ "base", maybe "" identity maybeClass ]
-- | ```
maybe :: forall a. String -> (a -> String) -> Maybe a -> String
maybe default f = M.maybe default f

-- | Include a class based on Either
either :: forall a b. (a -> String) -> (b -> String) -> Either a b -> String
either f _ (Left a) = f a
either _ g (Right b) = g b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // responsive variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small breakpoint (640px)
sm :: String -> String
sm cls = "sm:" <> cls

-- | Medium breakpoint (768px)
md :: String -> String
md cls = "md:" <> cls

-- | Large breakpoint (1024px)
lg :: String -> String
lg cls = "lg:" <> cls

-- | Extra large breakpoint (1280px)
xl :: String -> String
xl cls = "xl:" <> cls

-- | 2XL breakpoint (1536px)
xxl :: String -> String
xxl cls = "2xl:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // state variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hover state
hover :: String -> String
hover cls = "hover:" <> cls

-- | Focus state
focus :: String -> String
focus cls = "focus:" <> cls

-- | Active (pressed) state
active :: String -> String
active cls = "active:" <> cls

-- | Disabled state
disabled :: String -> String
disabled cls = "disabled:" <> cls

-- | Focus visible (keyboard focus)
focusVisible :: String -> String
focusVisible cls = "focus-visible:" <> cls

-- | Focus within (child focused)
focusWithin :: String -> String
focusWithin cls = "focus-within:" <> cls

-- | When parent with .group is hovered
groupHover :: String -> String
groupHover cls = "group-hover:" <> cls

-- | When parent with .group is focused
groupFocus :: String -> String
groupFocus cls = "group-focus:" <> cls

-- | When sibling with .peer is hovered
peerHover :: String -> String
peerHover cls = "peer-hover:" <> cls

-- | When sibling with .peer is focused
peerFocus :: String -> String
peerFocus cls = "peer-focus:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pseudo elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | ::before pseudo element
before :: String -> String
before cls = "before:" <> cls

-- | ::after pseudo element
after :: String -> String
after cls = "after:" <> cls

-- | ::placeholder pseudo element
placeholder :: String -> String
placeholder cls = "placeholder:" <> cls

-- | ::selection pseudo element
selection :: String -> String
selection cls = "selection:" <> cls

-- | ::first-letter pseudo element
firstLetter :: String -> String
firstLetter cls = "first-letter:" <> cls

-- | ::first-line pseudo element
firstLine :: String -> String
firstLine cls = "first-line:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pseudo classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | :first-child
first :: String -> String
first cls = "first:" <> cls

-- | :last-child
last :: String -> String
last cls = "last:" <> cls

-- | :nth-child(odd)
odd :: String -> String
odd cls = "odd:" <> cls

-- | :nth-child(even)
even :: String -> String
even cls = "even:" <> cls

-- | :empty
empty :: String -> String
empty cls = "empty:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // form states
-- ═════════════════════════════════════════════════════════════════════════════

-- | :checked
checked :: String -> String
checked cls = "checked:" <> cls

-- | :indeterminate
indeterminate :: String -> String
indeterminate cls = "indeterminate:" <> cls

-- | :required
required :: String -> String
required cls = "required:" <> cls

-- | :invalid
invalid :: String -> String
invalid cls = "invalid:" <> cls

-- | :valid
valid :: String -> String
valid cls = "valid:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // reduced motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | @media (prefers-reduced-motion: no-preference)
motionSafe :: String -> String
motionSafe cls = "motion-safe:" <> cls

-- | @media (prefers-reduced-motion: reduce)
motionReduce :: String -> String
motionReduce cls = "motion-reduce:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // print
-- ═════════════════════════════════════════════════════════════════════════════

-- | @media print
print :: String -> String
print cls = "print:" <> cls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // arbitrary values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Arbitrary value
-- |
-- | ```purescript
-- | arbitrary "w" "137px"  -- "w-[137px]"
-- | ```
arbitrary :: String -> String -> String
arbitrary property value = property <> "-[" <> value <> "]"

-- | Arbitrary property (for uncommon CSS)
-- |
-- | ```purescript
-- | arbitraryProperty "clip-path" "polygon(...)"
-- | -- "[clip-path:polygon(...)]"
-- | ```
arbitraryProperty :: String -> String -> String
arbitraryProperty property value = "[" <> property <> ":" <> value <> "]"
