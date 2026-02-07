/-
  Compass.Flags - Flag exclusivity proof
  
  Contains Grok-provided theorem:
  - P0-F1: Flags Mutually Exclusive
-/

import Compass.Core

namespace Compass.Flags

open Compass.Core

/-! ## Flag Types -/

inductive Flag where
  | exclusiveA : Flag
  | exclusiveB : Flag
  | shared : Flag
  deriving DecidableEq, Repr, Inhabited

def Flag.toString : Flag → String
  | .exclusiveA => "exclusiveA"
  | .exclusiveB => "exclusiveB"
  | .shared => "shared"

def Flag.fromString : String → Option Flag
  | "exclusiveA" => some .exclusiveA
  | "exclusiveB" => some .exclusiveB
  | "shared" => some .shared
  | _ => none

theorem flag_roundtrip (f : Flag) :
    Flag.fromString (Flag.toString f) = some f := by
  cases f <;> rfl

/-! ## Extractable Instance -/

instance : Extractable Flag where
  encode f := .str (Flag.toString f)
  decode j := do
    let s ← j.asString
    Flag.fromString s
  roundtrip f := by simp [Json.asString, flag_roundtrip]

/-! ## Mutually Exclusive Predicate (using List instead of Set) -/

/-- Two flags are mutually exclusive if they cannot both appear in a list -/
def flagsMutuallyExclusive (flags : List Flag) : Prop :=
  ∀ f1 f2 : Flag, f1 ∈ flags → f2 ∈ flags → f1 = .exclusiveA → f2 ≠ .exclusiveB

/-! ## THEOREM P0-F1: Flags Mutually Exclusive

    If flags satisfy the mutual exclusivity predicate, then having exclusiveA
    in the list implies exclusiveB is NOT in the list.
-/

theorem flags_mutually_exclusive {flags : List Flag} (h_excl : flagsMutuallyExclusive flags) :
    .exclusiveA ∈ flags → .exclusiveB ∉ flags := by
  intro h_a_in h_b_in
  exact h_excl .exclusiveA .exclusiveB h_a_in h_b_in rfl rfl

/-! ## THEOREM P0-F2: Exclusive flags are distinct -/

theorem exclusive_flags_distinct : Flag.exclusiveA ≠ Flag.exclusiveB := by
  intro h
  cases h

/-! ## Alternative: Boolean Flag Set -/

structure FlagSet where
  hasExclusiveA : Bool
  hasExclusiveB : Bool
  hasShared : Bool
  deriving Repr, DecidableEq

def FlagSet.isValid (fs : FlagSet) : Bool :=
  ¬(fs.hasExclusiveA && fs.hasExclusiveB)

/-! ## THEOREM P0-F3: Valid flag sets respect exclusivity -/

theorem valid_flagset_exclusive (fs : FlagSet) (h : fs.isValid = true) :
    ¬(fs.hasExclusiveA = true ∧ fs.hasExclusiveB = true) := by
  simp [FlagSet.isValid] at h
  intro ⟨ha, hb⟩
  simp [ha, hb] at h

/-! ## Extractable Instance for FlagSet -/

instance : Extractable FlagSet where
  encode fs := .obj [
    ("hasExclusiveA", .bool fs.hasExclusiveA),
    ("hasExclusiveB", .bool fs.hasExclusiveB),
    ("hasShared", .bool fs.hasShared)
  ]
  decode j := do
    let a ← Json.fieldN 0 j >>= Json.asBool
    let b ← Json.fieldN 1 j >>= Json.asBool
    let s ← Json.fieldN 2 j >>= Json.asBool
    some ⟨a, b, s⟩
  roundtrip fs := by cases fs; rfl

/-! ## Flag Operations -/

def FlagSet.empty : FlagSet := ⟨false, false, false⟩

def FlagSet.addFlag (fs : FlagSet) (f : Flag) : Option FlagSet :=
  match f with
  | .exclusiveA => 
    if fs.hasExclusiveB then none 
    else some { fs with hasExclusiveA := true }
  | .exclusiveB => 
    if fs.hasExclusiveA then none 
    else some { fs with hasExclusiveB := true }
  | .shared => some { fs with hasShared := true }

/-! ## THEOREM P0-F4: Adding exclusive to conflicting returns none -/

theorem add_exclusive_conflict (fs : FlagSet) :
    fs.hasExclusiveB = true → fs.addFlag .exclusiveA = none := by
  intro h
  simp [FlagSet.addFlag, h]

theorem add_exclusive_conflict' (fs : FlagSet) :
    fs.hasExclusiveA = true → fs.addFlag .exclusiveB = none := by
  intro h
  simp [FlagSet.addFlag, h]

/-! ## THEOREM P0-F5: addFlag preserves validity -/

-- If addFlag succeeds (returns some), the result is still valid
theorem add_flag_preserves_valid (fs : FlagSet) (f : Flag) (newFs : FlagSet)
    (h_valid : fs.isValid = true)
    (h_add : fs.addFlag f = some newFs) :
    newFs.isValid = true := by
  -- Case split on the flag type
  cases f with
  | exclusiveA =>
    -- addFlag for exclusiveA: if fs.hasExclusiveB then none else some {fs with hasExclusiveA := true}
    simp only [FlagSet.addFlag] at h_add
    split at h_add
    case isTrue hB =>
      -- If hasExclusiveB, returns none, contradicts h_add
      contradiction
    case isFalse hB =>
      -- Returns some, so newFs = {fs with hasExclusiveA := true}
      simp only [Option.some.injEq] at h_add
      rw [← h_add]
      -- Need to show: isValid {fs with hasExclusiveA := true} = true
      -- isValid = ¬(hasExclusiveA && hasExclusiveB) = ¬(true && fs.hasExclusiveB)
      -- Since hB : ¬(fs.hasExclusiveB = true), we have fs.hasExclusiveB = false
      simp only [FlagSet.isValid]
      -- ¬(true && fs.hasExclusiveB) = ¬fs.hasExclusiveB = true iff fs.hasExclusiveB = false
      cases hBval : fs.hasExclusiveB with
      | true => exact absurd hBval hB
      | false => rfl
  | exclusiveB =>
    simp only [FlagSet.addFlag] at h_add
    split at h_add
    case isTrue hA =>
      contradiction
    case isFalse hA =>
      simp only [Option.some.injEq] at h_add
      rw [← h_add]
      simp only [FlagSet.isValid]
      -- ¬(fs.hasExclusiveA && true) = ¬fs.hasExclusiveA
      cases hAval : fs.hasExclusiveA with
      | true => exact absurd hAval hA
      | false => rfl
  | shared =>
    -- addFlag for shared always succeeds and doesn't affect exclusivity
    simp only [FlagSet.addFlag, Option.some.injEq] at h_add
    rw [← h_add]
    -- isValid {fs with hasShared := true} = fs.isValid (shared doesn't affect A/B)
    simp only [FlagSet.isValid]
    exact h_valid

end Compass.Flags
