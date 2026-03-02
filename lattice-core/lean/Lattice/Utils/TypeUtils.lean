/-
  Lattice.Utils.TypeUtils - Type utility functions

  Reusable type-safe utility functions for object manipulation.

  Source: ui/src/utils/typeUtils.ts
-/

namespace Lattice.Utils.TypeUtils

/-! ## Key Omission -/

/-- Type-safe key omission from a list
    Filters out specified keys from a list of key-value pairs -/
def omitKeys {α β : Type} [BEq α] (kvs : List (α × β)) (keysToOmit : List α) : List (α × β) :=
  kvs.filter fun (k, _) => !keysToOmit.contains k

/-- Pick only specified keys from a list of key-value pairs -/
def pickKeys {α β : Type} [BEq α] (kvs : List (α × β)) (keysToPick : List α) : List (α × β) :=
  kvs.filter fun (k, _) => keysToPick.contains k

/-- Merge two lists of key-value pairs (second overrides first) -/
def mergeKVs {α β : Type} [BEq α] (first second : List (α × β)) : List (α × β) :=
  let secondKeys := second.map Prod.fst
  let filteredFirst := first.filter fun (k, _) => !secondKeys.contains k
  filteredFirst ++ second

/-- Get value by key from a list of key-value pairs -/
def getByKey {α β : Type} [BEq α] (kvs : List (α × β)) (key : α) : Option β :=
  kvs.find? (fun (k, _) => k == key) |>.map Prod.snd

/-- Set or update a key-value pair -/
def setByKey {α β : Type} [BEq α] (kvs : List (α × β)) (key : α) (value : β) : List (α × β) :=
  let filtered := kvs.filter fun (k, _) => k != key
  filtered ++ [(key, value)]

/-- Check if key exists in list -/
def hasKey {α β : Type} [BEq α] (kvs : List (α × β)) (key : α) : Bool :=
  kvs.any fun (k, _) => k == key

/-- Get all keys from a list of key-value pairs -/
def keys {α β : Type} (kvs : List (α × β)) : List α :=
  kvs.map Prod.fst

/-- Get all values from a list of key-value pairs -/
def values {α β : Type} (kvs : List (α × β)) : List β :=
  kvs.map Prod.snd

end Lattice.Utils.TypeUtils
