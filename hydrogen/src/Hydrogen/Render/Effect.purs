-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // render // effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect Algebra — What an Element can produce.
-- |
-- | Effects track the capabilities of an Element:
-- | - Can it emit click events?
-- | - Can it animate?
-- | - Can it emit sound?
-- | - Can it request data?
-- |
-- | Effects form a **join-semilattice** (monoid with idempotent join):
-- | - `pure` is the identity (no effects)
-- | - `combine` merges effects (a button inside a div makes the div clickable)
-- | - Effects compose upward through the tree
-- |
-- | ## Design Philosophy
-- |
-- | At billion-agent scale, knowing what an Element can DO is critical:
-- | - A pure element can be statically rendered
-- | - A clickable element needs event wiring
-- | - An animating element needs a frame loop
-- | - A data-requesting element needs async handling
-- |
-- | The type system proves these properties. No runtime checks needed.

module Hydrogen.Render.Effect
  ( Effect
  -- * Constructors
  , pure
  , click
  , hover
  , focus
  , input
  , drag
  , scroll
  , touch
  , animate
  , sound
  , requestData
  , interactive
  , effectful
  -- * Algebra
  , combine
  , combineAll
  -- * Predicates
  , isPure
  , isInteractive
  , canClick
  , canHover
  , canFocus
  , canInput
  , canDrag
  , canScroll
  , canTouch
  , canAnimate
  , canEmitSound
  , canRequestData
  -- * Lattice operations
  , join
  , meet
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Semigroup
  , class Monoid
  , class Show
  , compare
  , (==)
  , (||)
  , (&&)
  , (<>)
  )

import Data.Foldable (class Foldable, foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect algebra for Elements.
-- |
-- | Represents what an Element can produce/do. Encoded as a record of
-- | booleans for clarity and type safety.
-- |
-- | The structure forms a join-semilattice where:
-- | - All false is the bottom element (pure)
-- | - All true is the top element (effectful)
-- | - `combine` is the join operation (boolean OR per field)
newtype Effect = Effect
  { click :: Boolean
  , hover :: Boolean
  , focus :: Boolean
  , input :: Boolean
  , drag :: Boolean
  , scroll :: Boolean
  , touch :: Boolean
  , animate :: Boolean
  , sound :: Boolean
  , requestData :: Boolean
  }

derive instance eqEffect :: Eq Effect

instance ordEffect :: Ord Effect where
  compare (Effect a) (Effect b) = compare (toList a) (toList b)
    where
    toList r = 
      [ r.click, r.hover, r.focus, r.input, r.drag
      , r.scroll, r.touch, r.animate, r.sound, r.requestData
      ]

instance showEffect :: Show Effect where
  show eff
    | isPure eff = "Pure"
    | eff == interactive = "Interactive"
    | eff == effectful = "Effectful"
    | true = "Effect{" <> showFields eff <> "}"

showFields :: Effect -> String
showFields (Effect r) =
  let
    fields = 
      (if r.click then ["click"] else []) <>
      (if r.hover then ["hover"] else []) <>
      (if r.focus then ["focus"] else []) <>
      (if r.input then ["input"] else []) <>
      (if r.drag then ["drag"] else []) <>
      (if r.scroll then ["scroll"] else []) <>
      (if r.touch then ["touch"] else []) <>
      (if r.animate then ["animate"] else []) <>
      (if r.sound then ["sound"] else []) <>
      (if r.requestData then ["data"] else [])
  in
    joinStrings ", " fields

joinStrings :: String -> Array String -> String
joinStrings _ [] = ""
joinStrings _ [x] = x
joinStrings sep xs = foldl (\acc s -> if acc == "" then s else acc <> sep <> s) "" xs

instance semigroupEffect :: Semigroup Effect where
  append = combine

instance monoidEffect :: Monoid Effect where
  mempty = pure

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // effect // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure element — no effects, can be statically rendered
pure :: Effect
pure = Effect
  { click: false
  , hover: false
  , focus: false
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can emit click events
click :: Effect
click = Effect
  { click: true
  , hover: false
  , focus: false
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can emit hover events
hover :: Effect
hover = Effect
  { click: false
  , hover: true
  , focus: false
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can receive focus
focus :: Effect
focus = Effect
  { click: false
  , hover: false
  , focus: true
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can receive text input
input :: Effect
input = Effect
  { click: false
  , hover: false
  , focus: false
  , input: true
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can be dragged
drag :: Effect
drag = Effect
  { click: false
  , hover: false
  , focus: false
  , input: false
  , drag: true
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can emit scroll events
scroll :: Effect
scroll = Effect
  { click: false
  , hover: false
  , focus: false
  , input: false
  , drag: false
  , scroll: true
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can receive touch events
touch :: Effect
touch = Effect
  { click: false
  , hover: false
  , focus: false
  , input: false
  , drag: false
  , scroll: false
  , touch: true
  , animate: false
  , sound: false
  , requestData: false
  }

-- | Element can animate (needs frame loop)
animate :: Effect
animate = Effect
  { click: false
  , hover: false
  , focus: false
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: true
  , sound: false
  , requestData: false
  }

-- | Element can emit sound
sound :: Effect
sound = Effect
  { click: false
  , hover: false
  , focus: false
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: true
  , requestData: false
  }

-- | Element can request data (async)
requestData :: Effect
requestData = Effect
  { click: false
  , hover: false
  , focus: false
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: true
  }

-- | Common combination: basic interactive element
-- | (click + hover + focus)
interactive :: Effect
interactive = Effect
  { click: true
  , hover: true
  , focus: true
  , input: false
  , drag: false
  , scroll: false
  , touch: false
  , animate: false
  , sound: false
  , requestData: false
  }

-- | All effects (top of lattice)
effectful :: Effect
effectful = Effect
  { click: true
  , hover: true
  , focus: true
  , input: true
  , drag: true
  , scroll: true
  , touch: true
  , animate: true
  , sound: true
  , requestData: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // algebra
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two effects (join in the semilattice)
-- |
-- | This is the monoidal operation. When a child element has an effect,
-- | the parent inherits it. Effects flow upward through composition.
combine :: Effect -> Effect -> Effect
combine (Effect a) (Effect b) = Effect
  { click: a.click || b.click
  , hover: a.hover || b.hover
  , focus: a.focus || b.focus
  , input: a.input || b.input
  , drag: a.drag || b.drag
  , scroll: a.scroll || b.scroll
  , touch: a.touch || b.touch
  , animate: a.animate || b.animate
  , sound: a.sound || b.sound
  , requestData: a.requestData || b.requestData
  }

-- | Combine a collection of effects
combineAll :: forall f. Foldable f => f Effect -> Effect
combineAll = foldl combine pure

-- | Join operation (same as combine, lattice terminology)
join :: Effect -> Effect -> Effect
join = combine

-- | Meet operation (intersection of effects)
meet :: Effect -> Effect -> Effect
meet (Effect a) (Effect b) = Effect
  { click: a.click && b.click
  , hover: a.hover && b.hover
  , focus: a.focus && b.focus
  , input: a.input && b.input
  , drag: a.drag && b.drag
  , scroll: a.scroll && b.scroll
  , touch: a.touch && b.touch
  , animate: a.animate && b.animate
  , sound: a.sound && b.sound
  , requestData: a.requestData && b.requestData
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this a pure element with no effects?
isPure :: Effect -> Boolean
isPure (Effect r) =
  (r.click == false) &&
  (r.hover == false) &&
  (r.focus == false) &&
  (r.input == false) &&
  (r.drag == false) &&
  (r.scroll == false) &&
  (r.touch == false) &&
  (r.animate == false) &&
  (r.sound == false) &&
  (r.requestData == false)

-- | Does this element have basic interactive effects?
isInteractive :: Effect -> Boolean
isInteractive (Effect r) = r.click && r.hover && r.focus

-- | Can this element emit click events?
canClick :: Effect -> Boolean
canClick (Effect r) = r.click

-- | Can this element emit hover events?
canHover :: Effect -> Boolean
canHover (Effect r) = r.hover

-- | Can this element receive focus?
canFocus :: Effect -> Boolean
canFocus (Effect r) = r.focus

-- | Can this element receive input?
canInput :: Effect -> Boolean
canInput (Effect r) = r.input

-- | Can this element be dragged?
canDrag :: Effect -> Boolean
canDrag (Effect r) = r.drag

-- | Can this element scroll?
canScroll :: Effect -> Boolean
canScroll (Effect r) = r.scroll

-- | Can this element receive touch?
canTouch :: Effect -> Boolean
canTouch (Effect r) = r.touch

-- | Can this element animate?
canAnimate :: Effect -> Boolean
canAnimate (Effect r) = r.animate

-- | Can this element emit sound?
canEmitSound :: Effect -> Boolean
canEmitSound (Effect r) = r.sound

-- | Can this element request data?
canRequestData :: Effect -> Boolean
canRequestData (Effect r) = r.requestData
