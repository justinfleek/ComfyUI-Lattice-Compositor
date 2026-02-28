-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // brand // values
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand values: Core principles that inform every decision.
-- |
-- | From SMART Brand Ingestion Framework:
-- |   - Ordered list of stated values
-- |   - Inform design, communication, and interaction
-- |
-- | PURE DATA: Values are atoms in an ordered collection.

module Hydrogen.Schema.Brand.Values
  ( -- * Value Atom
    Value
  , mkValue
  , unValue
  , compareValues
  
  -- * Value Set
  , ValueSet
  , mkValueSet
  , valuesToArray
  , valueCount
  , hasValue
  , primaryValue
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , (>)
  , (<=)
  , (&&)
  , (<>)
  , compare
  )

import Data.Array (length, nub, elem, head) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, trim) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Value atom.
-- |
-- | A single brand value (e.g., "Innovation", "Security", "Accessibility").
-- | Bounded: 1-100 characters.
newtype Value = Value String

derive instance eqValue :: Eq Value
derive instance ordValue :: Ord Value

instance showValue :: Show Value where
  show (Value v) = "Value(" <> v <> ")"

-- | Smart constructor with validation.
mkValue :: String -> Maybe Value
mkValue s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 100
     then Just (Value trimmed)
     else Nothing

-- | Unwrap value.
unValue :: Value -> String
unValue (Value v) = v

-- | Compare two values alphabetically.
compareValues :: Value -> Value -> Ordering
compareValues (Value v1) (Value v2) = compare v1 v2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // value set
-- ═════════════════════════════════════════════════════════════════════════════

-- | ValueSet molecule.
-- |
-- | An ordered, non-empty, unique list of brand values.
-- | Order matters — first value is most important.
type ValueSet =
  { values :: Array Value
  }

-- | Create a value set (deduplicates, ensures non-empty).
-- |
-- | Returns Nothing if empty after deduplication.
mkValueSet :: Array Value -> Maybe ValueSet
mkValueSet vs =
  let deduped = Array.nub vs
  in if Array.length deduped > 0
     then Just { values: deduped }
     else Nothing

-- | Get values as ordered array.
valuesToArray :: ValueSet -> Array Value
valuesToArray vs = vs.values

-- | Get number of values.
valueCount :: ValueSet -> Int
valueCount vs = Array.length vs.values

-- | Check if a value is in the set.
hasValue :: Value -> ValueSet -> Boolean
hasValue v vs = Array.elem v vs.values

-- | Get the primary (first) value.
-- |
-- | Returns Nothing only if the set is somehow empty (shouldn't happen
-- | with proper construction via mkValueSet).
primaryValue :: ValueSet -> Maybe Value
primaryValue vs = Array.head vs.values
