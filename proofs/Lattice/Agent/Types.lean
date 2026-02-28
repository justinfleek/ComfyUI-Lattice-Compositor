/-
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // lattice // agent // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  AGENT TYPES — THE BOUNDS THAT DEFINE AGENT EXISTENCE

  "A pixel is not just a color. A pixel is a potential location for an
   agent's body."

  Every autonomous AI agent operating in the Lattice world model has:
  1. Position — WHERE it exists in the world
  2. Bounds — WHAT space it occupies
  3. Capabilities — WHAT actions it can perform
  4. State — WHAT it currently is

  These types are the immutable definitions. The proofs in other modules
  guarantee that agents cannot violate these definitions.

-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Lattice.Math.Vec3
import Lattice.Math.Bounded

namespace Lattice.Agent.Types

open Lattice.Math.Vec3
open Lattice.Math.Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // agent id
-- ═══════════════════════════════════════════════════════════════════════════════

/--
AgentId: A unique, deterministic identifier for an agent.

In the full system, this would be UUID5 (content-addressed).
For proofs, we model it as a natural number.
-/
structure AgentId where
  id : ℕ
  deriving Repr, DecidableEq, Hashable

namespace AgentId

/-- AgentIds are totally ordered -/
instance : LT AgentId := ⟨fun a b => a.id < b.id⟩
instance : LE AgentId := ⟨fun a b => a.id ≤ b.id⟩

end AgentId

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // bounding box
-- ═══════════════════════════════════════════════════════════════════════════════

/--
BoundingBox: The region of space an agent occupies.

Agents cannot overlap arbitrarily — the world model enforces rules about
what occupancy patterns are valid.
-/
structure BoundingBox where
  min : Vec3  -- Minimum corner (x, y, z)
  max : Vec3  -- Maximum corner (x, y, z)
  valid : min.x ≤ max.x ∧ min.y ≤ max.y ∧ min.z ≤ max.z
  deriving Repr

namespace BoundingBox

/-- Check if a point is inside the bounding box -/
def contains (box : BoundingBox) (p : Vec3) : Prop :=
  box.min.x ≤ p.x ∧ p.x ≤ box.max.x ∧
  box.min.y ≤ p.y ∧ p.y ≤ box.max.y ∧
  box.min.z ≤ p.z ∧ p.z ≤ box.max.z

/-- Check if two bounding boxes overlap -/
def overlaps (a b : BoundingBox) : Prop :=
  a.min.x ≤ b.max.x ∧ a.max.x ≥ b.min.x ∧
  a.min.y ≤ b.max.y ∧ a.max.y ≥ b.min.y ∧
  a.min.z ≤ b.max.z ∧ a.max.z ≥ b.min.z

/-- Overlapping is symmetric -/
theorem overlaps_symm (a b : BoundingBox) : overlaps a b ↔ overlaps b a := by
  simp only [overlaps]
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6⟩ <;> exact ⟨h2, h1, h4, h3, h6, h5⟩

/-- Center of bounding box -/
def center (box : BoundingBox) : Vec3 :=
  ⟨(box.min.x + box.max.x) / 2,
   (box.min.y + box.max.y) / 2,
   (box.min.z + box.max.z) / 2⟩

/-- Size of bounding box -/
def size (box : BoundingBox) : Vec3 :=
  Vec3.sub box.max box.min

/-- Size is non-negative in all dimensions -/
theorem size_nonneg (box : BoundingBox) :
    (size box).x ≥ 0 ∧ (size box).y ≥ 0 ∧ (size box).z ≥ 0 := by
  simp only [size, Vec3.sub]
  obtain ⟨hx, hy, hz⟩ := box.valid
  exact ⟨by linarith, by linarith, by linarith⟩

end BoundingBox

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // action types
-- ═══════════════════════════════════════════════════════════════════════════════

/--
ActionType: What kinds of actions an agent can perform.

Each action type has different capability requirements and world effects.
-/
inductive ActionType where
  | read      -- Observe without modification
  | write     -- Modify owned state
  | delete    -- Remove owned objects
  | create    -- Instantiate new objects
  | transfer  -- Give capabilities to others
  | move      -- Change position
  | admin     -- Full control (restricted)
  deriving Repr, DecidableEq, Hashable

namespace ActionType

/-- Some actions are more dangerous than others -/
def dangerLevel : ActionType → ℕ
  | .read => 0
  | .write => 1
  | .move => 1
  | .create => 2
  | .delete => 3
  | .transfer => 4
  | .admin => 5

/-- Admin is most dangerous -/
theorem admin_most_dangerous (a : ActionType) : dangerLevel a ≤ dangerLevel .admin := by
  cases a <;> simp [dangerLevel]

end ActionType

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // target refs
-- ═══════════════════════════════════════════════════════════════════════════════

/--
TargetRef: What an action targets.

Agents can only reference targets they have capabilities for.
This is enforced by the capability system.
-/
inductive TargetRef where
  | self                      -- Own agent state
  | agent (id : AgentId)      -- Another agent (requires consent)
  | region (box : BoundingBox) -- A spatial region
  | object (id : ℕ)            -- A world object
  | global                    -- World-level (admin only)
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // agent state
-- ═══════════════════════════════════════════════════════════════════════════════

/--
AgentState: The complete state of an agent at a moment in time.

This is the "body" of the agent — its position, bounds, and properties.
Every field is bounded and typed. Invalid states are unrepresentable.
-/
structure AgentState where
  -- Identity
  id : AgentId

  -- Spatial embodiment
  position : Vec3
  velocity : Vec3
  bounds : BoundingBox

  -- Visual expression (simplified)
  opacity : UnitInterval

  -- Temporal state
  frameAge : ℕ  -- Frames since creation

  -- Validity: position must be inside bounds
  position_in_bounds : bounds.contains position
  deriving Repr

namespace AgentState

/-- An agent's position is always valid (within its bounds) -/
theorem position_valid (agent : AgentState) : agent.bounds.contains agent.position :=
  agent.position_in_bounds

/-- Agents with same ID are the same agent -/
def sameAgent (a b : AgentState) : Prop := a.id = b.id

end AgentState

end Lattice.Agent.Types
