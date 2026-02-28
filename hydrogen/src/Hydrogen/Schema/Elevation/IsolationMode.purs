-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // elevation // isolation-mode
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | IsolationMode Atom — Stacking context isolation control.
-- |
-- | ## Stacking Contexts
-- |
-- | In compositing, elements are grouped into stacking contexts. Within a
-- | context, elements are z-ordered relative to each other. Creating a new
-- | stacking context isolates the element's children from the parent context.
-- |
-- | ## Modes
-- |
-- | - **Auto**: Element inherits stacking context behavior from ancestors.
-- |   May or may not create a new context depending on other properties.
-- |
-- | - **Isolate**: Element explicitly creates a new stacking context.
-- |   Children are isolated from parent context's z-ordering.
-- |
-- | ## When Isolation Matters
-- |
-- | Isolation is required when:
-- | - Using blend modes (children should blend with each other, not background)
-- | - Complex z-ordering (prevent children from escaping parent bounds)
-- | - Compositing groups (treat subtree as single unit for effects)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.IsolationMode as Iso
-- |
-- | -- Create isolated container
-- | blendContainer = Iso.isolate
-- |
-- | -- Default behavior
-- | normalElement = Iso.auto
-- | ```

module Hydrogen.Schema.Elevation.IsolationMode
  ( IsolationMode(..)
  , auto
  , isolate
  , isIsolated
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Generic.Rep (class Generic)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // isolation mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stacking context isolation mode
-- |
-- | Controls whether an element creates a new stacking context.
data IsolationMode
  = Auto     -- ^ Inherit behavior from ancestors
  | Isolate  -- ^ Explicitly create new stacking context

derive instance eqIsolationMode :: Eq IsolationMode
derive instance ordIsolationMode :: Ord IsolationMode
derive instance genericIsolationMode :: Generic IsolationMode _

instance showIsolationMode :: Show IsolationMode where
  show Auto = "Auto"
  show Isolate = "Isolate"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Auto isolation (inherit from ancestors)
auto :: IsolationMode
auto = Auto

-- | Explicit isolation (create new stacking context)
isolate :: IsolationMode
isolate = Isolate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if isolation mode creates a new stacking context
isIsolated :: IsolationMode -> Boolean
isIsolated Isolate = true
isIsolated Auto = false
