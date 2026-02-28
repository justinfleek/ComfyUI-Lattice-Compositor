-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // schema // diff
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diff — Structural comparison and patch generation for Schema values.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, efficient updates require knowing exactly what
-- | changed between two versions of a value. Instead of replacing entire
-- | structures, we compute and apply minimal patches.
-- |
-- | ## Design
-- |
-- | The Diff system provides:
-- | 1. **Change detection** — Did anything change?
-- | 2. **Structural comparison** — What specifically changed?
-- | 3. **Patch generation** — Minimal operations to transform old → new
-- | 4. **Patch application** — Apply patches to reconstruct values
-- |
-- | ## Invariants
-- |
-- | ```
-- | ∀ a b. apply (diff a b) a ≡ b    -- Correctness
-- | ∀ a b. diff a a ≡ NoChange       -- Identity
-- | ∀ a b c. apply (diff b c) (apply (diff a b) a) ≡ apply (diff a c) a  -- Composition
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | let old = Point2D { x: 100.0, y: 200.0 }
-- | let new = Point2D { x: 150.0, y: 200.0 }
-- | let patch = diff old new
-- | -- patch = FieldChange "x" (NumberDelta 50.0)
-- | 
-- | apply patch old == new  -- true
-- | ```
-- |
-- | ## Lean4 Proof
-- |
-- | ```lean
-- | theorem diff_apply_identity : ∀ old new, apply (diff old new) old = new
-- | ```

module Hydrogen.Schema.Diff
  ( -- * Core Types
    Diff(NoChange, Replace, Delta)
  , FieldDiff(FieldChange, FieldAdd, FieldRemove)
  , ArrayDiff(ArrayReplace, ArrayPatch)
  , ArrayOp(Insert, Delete, Move, Update)
  
  -- * Diffable Typeclass
  , class Diffable
  , diff
  , apply
  , isNoChange
  
  -- * Primitive Diffs
  , NumberDelta(NumberDelta)
  , IntDelta(IntDelta)
  , StringDelta(StringReplace, StringPatch)
  , StringPatchOp(InsertChars, DeleteChars, ReplaceChars)
  
  -- * Diff Utilities
  , diffNumbers
  , diffInts
  , diffStrings
  , diffBooleans
  , diffMaybes
  
  -- * Statistics
  , DiffStats
  , diffStats
  , isMinimal
  , changeCount
  
  -- * Apply Functions
  , applyNumberDiff
  , applyIntDiff
  , applyStringDiff
  , applyBooleanDiff
  , applyMaybeDiff
  , applyStringOps
  , applyStringOp
  , applyArrayDiff
  , applyArrayOp
  
  -- * Unwrap Functions
  , unwrapNumberDelta
  , unwrapIntDelta
  , unwrapStringDelta
  
  -- * Array Helpers
  , takeChars
  , dropChars
  , makeRange
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , negate
  , pure
  , map
  , ($)
  , (+)
  , (-)
  , (*)
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (<>)
  , (<<<)
  )

import Data.Array (length, index, foldl, snoc, zipWith, take, drop, insertAt, deleteAt, modifyAt) as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.String.CodeUnits (length, toCharArray, fromCharArray) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // core diff types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Core diff type — represents the difference between two values.
-- |
-- | - `NoChange` — Values are identical
-- | - `Replace` — Complete replacement (old → new)
-- | - `Delta` — Incremental change with patch data
data Diff a
  = NoChange
  | Replace a a      -- old, new
  | Delta a          -- patch data specific to type

derive instance eqDiff :: Eq a => Eq (Diff a)

instance showDiff :: Show a => Show (Diff a) where
  show NoChange = "NoChange"
  show (Replace old new) = "Replace(" <> show old <> " → " <> show new <> ")"
  show (Delta patch) = "Delta(" <> show patch <> ")"

-- | Check if a diff represents no change
isNoChange :: forall a. Diff a -> Boolean
isNoChange NoChange = true
isNoChange _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // primitive deltas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Delta for Number values — stores the difference.
-- |
-- | Applying: newValue = oldValue + delta
newtype NumberDelta = NumberDelta Number

derive instance eqNumberDelta :: Eq NumberDelta
derive instance ordNumberDelta :: Ord NumberDelta

instance showNumberDelta :: Show NumberDelta where
  show (NumberDelta d) = "Δ" <> show d

-- | Delta for Int values — stores the difference.
newtype IntDelta = IntDelta Int

derive instance eqIntDelta :: Eq IntDelta
derive instance ordIntDelta :: Ord IntDelta

instance showIntDelta :: Show IntDelta where
  show (IntDelta d) = "Δ" <> show d

-- | Delta for String values — either full replace or patch operations.
data StringDelta
  = StringReplace String    -- Full replacement with new string
  | StringPatch (Array StringPatchOp)  -- Sequence of patch operations

derive instance eqStringDelta :: Eq StringDelta

instance showStringDelta :: Show StringDelta where
  show (StringReplace s) = "Replace(\"" <> s <> "\")"
  show (StringPatch ops) = "Patch[" <> show (Array.length ops) <> " ops]"

-- | Individual string patch operation
data StringPatchOp
  = InsertChars Int String   -- Insert string at position
  | DeleteChars Int Int      -- Delete n chars starting at position
  | ReplaceChars Int Int String  -- Replace n chars at position with string

derive instance eqStringPatchOp :: Eq StringPatchOp

instance showStringPatchOp :: Show StringPatchOp where
  show (InsertChars pos str) = "Insert@" <> show pos <> "(\"" <> str <> "\")"
  show (DeleteChars pos n) = "Delete@" <> show pos <> "(" <> show n <> ")"
  show (ReplaceChars pos n str) = "Replace@" <> show pos <> "(" <> show n <> ",\"" <> str <> "\")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // field changes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Change to a single field in a record.
-- |
-- | For record diffing, each field produces a FieldDiff.
data FieldDiff a
  = FieldChange String (Diff a)  -- Field name + its diff
  | FieldAdd String a            -- Field was added with value
  | FieldRemove String a         -- Field was removed (had value)

derive instance eqFieldDiff :: Eq a => Eq (FieldDiff a)

instance showFieldDiff :: Show a => Show (FieldDiff a) where
  show (FieldChange name d) = name <> ": " <> show d
  show (FieldAdd name v) = "+" <> name <> ": " <> show v
  show (FieldRemove name v) = "-" <> name <> ": " <> show v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // array changes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diff for arrays — either full replace or sequence of operations.
data ArrayDiff a
  = ArrayReplace (Array a)        -- Full replacement
  | ArrayPatch (Array (ArrayOp a))  -- Sequence of operations

derive instance eqArrayDiff :: Eq a => Eq (ArrayDiff a)

instance showArrayDiff :: Show a => Show (ArrayDiff a) where
  show (ArrayReplace arr) = "Replace[" <> show (Array.length arr) <> "]"
  show (ArrayPatch ops) = "Patch[" <> show (Array.length ops) <> " ops]"

-- | Individual array operation
data ArrayOp a
  = Insert Int a        -- Insert value at index
  | Delete Int          -- Delete element at index
  | Move Int Int        -- Move element from index to index
  | Update Int (Diff a) -- Update element at index with diff

derive instance eqArrayOp :: Eq a => Eq (ArrayOp a)

instance showArrayOp :: Show a => Show (ArrayOp a) where
  show (Insert idx v) = "Insert@" <> show idx
  show (Delete idx) = "Delete@" <> show idx
  show (Move from to) = "Move(" <> show from <> "→" <> show to <> ")"
  show (Update idx d) = "Update@" <> show idx <> ":" <> show d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // diffable typeclass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Typeclass for values that can be diffed and patched.
-- |
-- | Laws:
-- | - Identity: `diff a a ≡ NoChange`
-- | - Correctness: `apply (diff a b) a ≡ b`
class Eq a <= Diffable a where
  diff :: a -> a -> Diff a
  apply :: Diff a -> a -> a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // diffable instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diffable instance for Number.
-- |
-- | Uses additive delta: new = old + delta
-- | This is the most efficient representation for numeric changes.
instance diffableNumber :: Diffable Number where
  diff old new
    | old == new = NoChange
    | otherwise = Delta (new - old)
  apply NoChange n = n
  apply (Replace _ new) _ = new
  apply (Delta delta) n = n + delta

-- | Diffable instance for Int.
-- |
-- | Uses additive delta: new = old + delta
instance diffableInt :: Diffable Int where
  diff old new
    | old == new = NoChange
    | otherwise = Delta (new - old)
  apply NoChange n = n
  apply (Replace _ new) _ = new
  apply (Delta delta) n = n + delta

-- | Diffable instance for Boolean.
-- |
-- | Uses Replace since there are only two states.
instance diffableBoolean :: Diffable Boolean where
  diff old new
    | old == new = NoChange
    | otherwise = Replace old new
  apply NoChange b = b
  apply (Replace _ new) _ = new
  apply (Delta new) _ = new

-- | Diffable instance for String.
-- |
-- | Uses Replace for simplicity. A more sophisticated implementation
-- | could use edit distance algorithms for patch-based diffs.
instance diffableString :: Diffable String where
  diff old new
    | old == new = NoChange
    | otherwise = Replace old new
  apply NoChange s = s
  apply (Replace _ new) _ = new
  apply (Delta new) _ = new

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // primitive diffs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diff two numbers, producing a delta if different.
diffNumbers :: Number -> Number -> Diff NumberDelta
diffNumbers old new
  | old == new = NoChange
  | otherwise = Delta (NumberDelta (new - old))

-- | Apply a number diff
applyNumberDiff :: Diff NumberDelta -> Number -> Number
applyNumberDiff NoChange n = n
applyNumberDiff (Replace _ new) _ = unwrapNumberDelta new
applyNumberDiff (Delta (NumberDelta d)) n = n + d

-- | Unwrap NumberDelta (for Replace case where it holds the new value)
unwrapNumberDelta :: NumberDelta -> Number
unwrapNumberDelta (NumberDelta d) = d

-- | Diff two integers
diffInts :: Int -> Int -> Diff IntDelta
diffInts old new
  | old == new = NoChange
  | otherwise = Delta (IntDelta (new - old))

-- | Apply an int diff
applyIntDiff :: Diff IntDelta -> Int -> Int
applyIntDiff NoChange n = n
applyIntDiff (Replace _ new) _ = unwrapIntDelta new
applyIntDiff (Delta (IntDelta d)) n = n + d

-- | Unwrap IntDelta
unwrapIntDelta :: IntDelta -> Int
unwrapIntDelta (IntDelta d) = d

-- | Diff two strings
-- |
-- | For short strings or when the strings are very different, uses Replace.
-- | For similar strings, could use patch operations (simplified here).
diffStrings :: String -> String -> Diff StringDelta
diffStrings old new
  | old == new = NoChange
  | otherwise = Delta (StringReplace new)

-- | Apply a string diff
applyStringDiff :: Diff StringDelta -> String -> String
applyStringDiff NoChange s = s
applyStringDiff (Replace _ new) _ = unwrapStringDelta new
applyStringDiff (Delta (StringReplace new)) _ = new
applyStringDiff (Delta (StringPatch ops)) s = applyStringOps ops s

-- | Unwrap StringDelta for Replace case
unwrapStringDelta :: StringDelta -> String
unwrapStringDelta (StringReplace s) = s
unwrapStringDelta (StringPatch _) = ""  -- Patches require apply

-- | Apply string patch operations
applyStringOps :: Array StringPatchOp -> String -> String
applyStringOps ops initial =
  Array.foldl applyStringOp initial ops

-- | Apply a single string patch operation
applyStringOp :: String -> StringPatchOp -> String
applyStringOp str (InsertChars pos insert) =
  let chars = String.toCharArray str
      before = takeChars pos chars
      after = dropChars pos chars
  in String.fromCharArray before <> insert <> String.fromCharArray after

applyStringOp str (DeleteChars pos n) =
  let chars = String.toCharArray str
      before = takeChars pos chars
      after = dropChars (pos + n) chars
  in String.fromCharArray before <> String.fromCharArray after

applyStringOp str (ReplaceChars pos n replacement) =
  let chars = String.toCharArray str
      before = takeChars pos chars
      after = dropChars (pos + n) chars
  in String.fromCharArray before <> replacement <> String.fromCharArray after

-- | Take first n characters as array
takeChars :: Int -> Array Char -> Array Char
takeChars n chars =
  Array.foldl (\acc i ->
    case Array.index chars i of
      Nothing -> acc
      Just c -> if i < n then Array.snoc acc c else acc
  ) [] (makeRange 0 (Array.length chars - 1))

-- | Drop first n characters as array
dropChars :: Int -> Array Char -> Array Char
dropChars n chars =
  Array.foldl (\acc i ->
    case Array.index chars i of
      Nothing -> acc
      Just c -> if i >= n then Array.snoc acc c else acc
  ) [] (makeRange 0 (Array.length chars - 1))

-- | Make a range of integers (helper)
makeRange :: Int -> Int -> Array Int
makeRange start end =
  if start > end then []
  else buildRange start end []

buildRange :: Int -> Int -> Array Int -> Array Int
buildRange current end acc =
  if current > end then acc
  else buildRange (current + 1) end (Array.snoc acc current)

-- | Diff two booleans
diffBooleans :: Boolean -> Boolean -> Diff Boolean
diffBooleans old new
  | old == new = NoChange
  | otherwise = Replace old new

-- | Apply boolean diff
applyBooleanDiff :: Diff Boolean -> Boolean -> Boolean
applyBooleanDiff NoChange b = b
applyBooleanDiff (Replace _ new) _ = new
applyBooleanDiff (Delta new) _ = new

-- | Diff two Maybe values
diffMaybes :: forall a. Eq a => Maybe a -> Maybe a -> Diff (Maybe a)
diffMaybes Nothing Nothing = NoChange
diffMaybes (Just a) (Just b)
  | a == b = NoChange
  | otherwise = Replace (Just a) (Just b)
diffMaybes old new = Replace old new

-- | Apply Maybe diff
applyMaybeDiff :: forall a. Diff (Maybe a) -> Maybe a -> Maybe a
applyMaybeDiff NoChange m = m
applyMaybeDiff (Replace _ new) _ = new
applyMaybeDiff (Delta new) _ = new

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // array diff apply
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply an array diff to an array.
-- |
-- | For `ArrayReplace`, returns the new array directly.
-- | For `ArrayPatch`, applies operations in sequence.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | let original = [1, 2, 3, 4, 5]
-- | let patch = ArrayPatch [Delete 2, Insert 0 99]
-- | applyArrayDiff patch original  -- [99, 1, 2, 4, 5]
-- | ```
applyArrayDiff :: forall a. Diffable a => ArrayDiff a -> Array a -> Array a
applyArrayDiff (ArrayReplace newArray) _ = newArray
applyArrayDiff (ArrayPatch ops) arr = Array.foldl applyArrayOp arr ops

-- | Apply a single array operation.
-- |
-- | Operations:
-- | - `Insert idx value` — Insert value at index, shifting elements right
-- | - `Delete idx` — Remove element at index, shifting elements left
-- | - `Move from to` — Move element from one index to another
-- | - `Update idx diff` — Apply diff to element at index
applyArrayOp :: forall a. Diffable a => Array a -> ArrayOp a -> Array a
applyArrayOp arr (Insert idx value) =
  fromMaybe arr (Array.insertAt idx value arr)

applyArrayOp arr (Delete idx) =
  fromMaybe arr (Array.deleteAt idx arr)

applyArrayOp arr (Move fromIdx toIdx) =
  case Array.index arr fromIdx of
    Nothing -> arr
    Just value ->
      let afterDelete = fromMaybe arr (Array.deleteAt fromIdx arr)
          adjustedTo = if fromIdx < toIdx then toIdx - 1 else toIdx
      in fromMaybe afterDelete (Array.insertAt adjustedTo value afterDelete)

applyArrayOp arr (Update idx elementDiff) =
  fromMaybe arr (Array.modifyAt idx (apply elementDiff) arr)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // diff statistics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Statistics about a diff for analysis.
-- |
-- | Useful for:
-- | - Performance monitoring (how much is changing?)
-- | - Optimization decisions (is a full replace cheaper?)
-- | - Debugging (what's causing frequent updates?)
type DiffStats =
  { totalChanges :: Int
  , fieldChanges :: Int
  , arrayOps :: Int
  , isFullReplace :: Boolean
  }

-- | Generate stats from basic counts
diffStats :: Int -> Int -> Int -> Boolean -> DiffStats
diffStats total fields arrays fullReplace =
  { totalChanges: total
  , fieldChanges: fields
  , arrayOps: arrays
  , isFullReplace: fullReplace
  }

-- | Check if a diff is minimal (single change or small number)
isMinimal :: DiffStats -> Boolean
isMinimal stats = stats.totalChanges <= 3 && not stats.isFullReplace

-- | Get total change count from stats
changeCount :: DiffStats -> Int
changeCount stats = stats.totalChanges
