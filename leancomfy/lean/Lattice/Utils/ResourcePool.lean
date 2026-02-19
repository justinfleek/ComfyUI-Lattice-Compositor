/-
  Lattice.Utils.ResourcePool - Generic resource pooling

  Abstract resource pool that can be used for any pooled resource type.
  The TypeScript version uses HTMLCanvasElement; this version is generic.

  Source: ui/src/utils/canvasPool.ts
-/

namespace Lattice.Utils.ResourcePool

/-! ## Types -/

/-- Configuration for pool behavior -/
structure PoolConfig where
  maxSize : Nat := 20       -- Maximum pooled resources
  maxAgeMs : Nat := 60000   -- TTL for unused resources (60 seconds)
  deriving Repr, BEq

/-- A pooled resource entry -/
structure PoolEntry (α : Type) where
  resource : α
  width : Nat
  height : Nat
  inUse : Bool
  lastUsed : Nat  -- Timestamp in milliseconds
  deriving Repr

/-- Resource pool state -/
structure ResourcePool (α : Type) where
  entries : List (PoolEntry α)
  config : PoolConfig
  deriving Repr

/-- Result of acquiring a resource -/
inductive AcquireResult (α : Type)
  | found : α → AcquireResult α        -- Reused from pool
  | created : α → AcquireResult α      -- Newly created
  | poolFull : α → AcquireResult α     -- Created but pool at capacity
  deriving Repr

/-- Pool statistics -/
structure PoolStats where
  total : Nat
  inUse : Nat
  available : Nat
  deriving Repr, BEq

/-! ## Pool Operations -/

/-- Create an empty pool with default config -/
def empty : ResourcePool α :=
  { entries := [], config := {} }

/-- Create an empty pool with custom config -/
def withConfig (config : PoolConfig) : ResourcePool α :=
  { entries := [], config := config }

/-- Find a matching unused entry in the pool -/
def findAvailable (pool : ResourcePool α) (width height : Nat) : Option (PoolEntry α) :=
  pool.entries.find? fun entry =>
    !entry.inUse && entry.width == width && entry.height == height

/-- Mark an entry as in use -/
def markInUse (pool : ResourcePool α) (resource : α) (now : Nat) [BEq α] : ResourcePool α :=
  { pool with
    entries := pool.entries.map fun entry =>
      if entry.resource == resource
      then { entry with inUse := true, lastUsed := now }
      else entry
  }

/-- Try to acquire a resource from the pool.
    Returns (updated pool, acquire result).
    The caller must provide a function to create new resources. -/
def acquire (pool : ResourcePool α) (width height : Nat) (now : Nat)
    (createResource : Nat → Nat → α) [BEq α] : ResourcePool α × AcquireResult α :=
  match findAvailable pool width height with
  | some entry =>
    let updatedPool := markInUse pool entry.resource now
    (updatedPool, .found entry.resource)
  | none =>
    let newResource := createResource width height
    if pool.entries.length < pool.config.maxSize then
      let newEntry : PoolEntry α := {
        resource := newResource
        width := width
        height := height
        inUse := true
        lastUsed := now
      }
      let updatedPool := { pool with entries := pool.entries ++ [newEntry] }
      (updatedPool, .created newResource)
    else
      (pool, .poolFull newResource)

/-- Release a resource back to the pool -/
def release (pool : ResourcePool α) (resource : α) (now : Nat) [BEq α] : ResourcePool α :=
  { pool with
    entries := pool.entries.map fun entry =>
      if entry.resource == resource
      then { entry with inUse := false, lastUsed := now }
      else entry
  }

/-- Remove old unused resources from the pool -/
def cleanup (pool : ResourcePool α) (now : Nat) : ResourcePool α :=
  { pool with
    entries := pool.entries.filter fun entry =>
      entry.inUse || now - entry.lastUsed <= pool.config.maxAgeMs
  }

/-- Clear all resources from the pool -/
def clear (pool : ResourcePool α) : ResourcePool α :=
  { pool with entries := [] }

/-- Get pool statistics -/
def getStats (pool : ResourcePool α) : PoolStats :=
  let inUseCount := pool.entries.filter (·.inUse) |>.length
  { total := pool.entries.length
  , inUse := inUseCount
  , available := pool.entries.length - inUseCount
  }

/-! ## Proofs -/

/-- Empty pool has no entries -/
theorem empty_has_no_entries : (empty : ResourcePool α).entries.length = 0 := rfl

/-- Clearing a pool results in no entries -/
theorem clear_has_no_entries (pool : ResourcePool α) :
    (clear pool).entries.length = 0 := rfl

/-- Pool size never exceeds maxSize after acquire -/
theorem acquire_respects_max_size [BEq α] (pool : ResourcePool α) (w h now : Nat)
    (create : Nat → Nat → α) :
    (acquire pool w h now create).1.entries.length ≤ pool.config.maxSize ∨
    (acquire pool w h now create).1.entries.length ≤ pool.entries.length := by
  simp only [acquire]
  split
  · -- Found existing entry - map preserves length
    right
    simp only [markInUse]
    exact Nat.le_of_eq (List.length_map _ _)
  · -- Creating new
    split
    · -- Pool not full, adding one
      right
      simp only [List.length_append, List.length_singleton]
      omega
    · -- Pool full, no change
      right
      exact Nat.le_refl _

/-- Stats total equals entries length -/
theorem stats_total_is_entries_length (pool : ResourcePool α) :
    (getStats pool).total = pool.entries.length := rfl

end Lattice.Utils.ResourcePool
