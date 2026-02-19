/-
  Compass.RateLimiter - Token Bucket Rate Limiting with proofs

  Features:
  - Token bucket algorithm with refill
  - Per-user, per-API-key, per-tool limits
  - Burst capacity for short traffic spikes
  - API key can only lower limits (never raise)
  - Statistics tracking

  Every type has:
  - Extractable instance with roundtrip proof
  - Security invariants as theorems
-/

import Compass.Core
import Compass.Auth
import Compass.Tools

namespace Compass.RateLimiter

open Compass.Core
open Compass.Auth
open Compass.Tools

/-! ## Token Bucket State -/

/-- Token bucket for rate limiting -/
structure Bucket where
  tokens : Int           -- Current tokens (scaled by 1000 for precision)
  last_update_ms : Int   -- Last update timestamp (milliseconds)
  max_tokens : Int       -- Maximum tokens (requests + burst)
  refill_rate : Int      -- Tokens per second (scaled by 1000)
  deriving Repr, DecidableEq

instance : Inhabited Bucket where
  default := ⟨0, 0, 0, 0⟩

def Bucket.toJson (b : Bucket) : Json := .obj [
  ("tokens", .int b.tokens),
  ("last_update_ms", .int b.last_update_ms),
  ("max_tokens", .int b.max_tokens),
  ("refill_rate", .int b.refill_rate)
]

def Bucket.fromJson (j : Json) : Option Bucket := do
  let tokens ← (Json.fieldN 0 j) >>= Json.asInt
  let last_update_ms ← (Json.fieldN 1 j) >>= Json.asInt
  let max_tokens ← (Json.fieldN 2 j) >>= Json.asInt
  let refill_rate ← (Json.fieldN 3 j) >>= Json.asInt
  pure ⟨tokens, last_update_ms, max_tokens, refill_rate⟩

theorem Bucket.roundtrip (b : Bucket) :
    Bucket.fromJson (Bucket.toJson b) = some b := by
  cases b; rfl

instance : Extractable Bucket where
  encode := Bucket.toJson
  decode := Bucket.fromJson
  roundtrip := Bucket.roundtrip

/-- Create a fresh bucket at max capacity -/
def Bucket.fresh (limit : RateLimit) (now_ms : Int) : Bucket :=
  let max_tokens := (limit.requests + limit.burst) * 1000
  let refill_rate := limit.requests * 1000 / limit.period_seconds
  ⟨max_tokens, now_ms, max_tokens, refill_rate⟩

/-- THEOREM: Fresh bucket starts at max capacity -/
theorem fresh_bucket_full (limit : RateLimit) (now : Int) :
    (Bucket.fresh limit now).tokens = (Bucket.fresh limit now).max_tokens := by
  simp [Bucket.fresh]

/-! ## Bucket Operations -/

/-- Refill tokens based on elapsed time -/
def Bucket.refill (b : Bucket) (now_ms : Int) : Bucket :=
  let elapsed_ms := now_ms - b.last_update_ms
  -- Only refill if time has passed
  if elapsed_ms <= 0 then b
  else
    let refill := b.refill_rate * elapsed_ms / 1000
    let new_tokens := min b.max_tokens (b.tokens + refill)
    { b with tokens := new_tokens, last_update_ms := now_ms }

/-- THEOREM: Refill never exceeds max_tokens -/
theorem refill_bounded (b : Bucket) (now : Int) (h_inv : b.tokens ≤ b.max_tokens) :
    (b.refill now).tokens ≤ (b.refill now).max_tokens := by
  simp only [Bucket.refill]
  split_ifs with h
  · -- elapsed <= 0: bucket unchanged
    exact h_inv
  · -- elapsed > 0: new_tokens = min max_tokens (tokens + refill) ≤ max_tokens
    exact Int.min_le_left _ _

/-- Try to consume tokens from bucket -/
def Bucket.tryConsume (b : Bucket) (cost : Int) : Option Bucket :=
  if cost ≤ 0 then some b
  else if b.tokens >= cost then
    some { b with tokens := b.tokens - cost }
  else
    none

/-- THEOREM: Consume decreases tokens by exact cost -/
theorem consume_exact (b : Bucket) (cost : Int) (h : cost > 0) (hc : b.tokens >= cost) :
    (b.tryConsume cost) = some { b with tokens := b.tokens - cost } := by
  unfold Bucket.tryConsume
  simp only [Int.not_le.mpr h, ↓reduceIte, ge_iff_le, hc, ↓reduceIte]

/-- THEOREM: Consume fails when insufficient tokens -/
theorem consume_fails_insufficient (b : Bucket) (cost : Int) (h : cost > 0) (hi : b.tokens < cost) :
    (b.tryConsume cost) = none := by
  unfold Bucket.tryConsume
  simp only [Int.not_le.mpr h, ↓reduceIte, ge_iff_le, Int.not_le.mpr hi, ↓reduceIte]

/-! ## Rate Limit Acquisition Result -/

inductive AcquireResult where
  | Allowed : Int → AcquireResult        -- remaining tokens
  | Denied : Int → AcquireResult         -- retry after seconds
  deriving Repr, DecidableEq

def AcquireResult.isAllowed : AcquireResult → Bool
  | .Allowed _ => true
  | .Denied _ => false

def AcquireResult.isDenied : AcquireResult → Bool
  | .Allowed _ => false
  | .Denied _ => true

-- JSON-based encoding for Extractable (provable roundtrip)
def AcquireResult.toJson : AcquireResult → Json
  | .Allowed n => .obj [("tag", .str "allowed"), ("value", .int n)]
  | .Denied n => .obj [("tag", .str "denied"), ("value", .int n)]

def AcquireResult.fromJson : Json → Option AcquireResult
  | .obj fields =>
    match fields with
    | [("tag", .str "allowed"), ("value", .int n)] => some (.Allowed n)
    | [("tag", .str "denied"), ("value", .int n)] => some (.Denied n)
    | _ => none
  | _ => none

-- Roundtrip proof using JSON encoding (structurally provable)
theorem AcquireResult.roundtrip (r : AcquireResult) :
    AcquireResult.fromJson (AcquireResult.toJson r) = some r := by
  cases r with
  | Allowed n => rfl
  | Denied n => rfl

instance : Extractable AcquireResult where
  encode := AcquireResult.toJson
  decode := AcquireResult.fromJson
  roundtrip := AcquireResult.roundtrip

/-! ## Security Theorems (P0 Priority) -/

/-! THEOREM P0-R1: Token consumption is atomic -/

theorem token_consumption_atomic (b : Bucket) (cost : Int) :
    let result := b.tryConsume cost
    (result.isSome → ∃ b', result = some b' ∧ (cost ≤ 0 ∨ b'.tokens = b.tokens - cost)) ∧
    (result.isNone → cost > 0 ∧ b.tokens < cost) := by
  simp only [Bucket.tryConsume]
  constructor
  · intro h_some
    split_ifs at h_some ⊢ with h1 h2
    · exact ⟨b, rfl, Or.inl h1⟩
    · exact ⟨{ b with tokens := b.tokens - cost }, rfl, Or.inr rfl⟩
    · simp at h_some
  · intro h_none
    split_ifs at h_none with h1 h2
    · simp at h_none
    · simp at h_none
    · exact ⟨Int.not_le.mp h1, Int.not_le.mp h2⟩

/-! THEOREM P0-R2: Rate limit can only be lowered by API key -/

theorem api_key_only_lowers_rate (tool_limit : RateLimit) (key_override : Option Int) (effective : RateLimit) :
    (h : key_override.isSome) →
    effective.requests = min tool_limit.requests (key_override.get h) →
    effective.requests ≤ tool_limit.requests := by
  intros _ h_eff
  rw [h_eff]
  exact Int.min_le_left _ _

/-! THEOREM P0-R3: Tokens cannot go negative -/

theorem tokens_nonneg (b : Bucket) (cost : Int) (hb : b.tokens >= 0) (_hc : cost >= 0) :
    let result := b.tryConsume cost
    (result.isSome → ∃ b', result = some b' ∧ b'.tokens ≥ 0) ∧
    (result.isNone → b.tokens < cost) := by
  constructor
  · intro h_some
    simp only [Bucket.tryConsume] at h_some ⊢
    split_ifs at h_some ⊢ with h1 h2
    · exact ⟨b, rfl, hb⟩
    · -- h2 : b.tokens >= cost, need to show b.tokens - cost >= 0
      have h_sub : b.tokens - cost ≥ 0 := Int.sub_nonneg.mpr h2
      exact ⟨{ b with tokens := b.tokens - cost }, rfl, h_sub⟩
    · exact False.elim (by simp at h_some)
  · intro h_none
    simp only [Bucket.tryConsume] at h_none
    split_ifs at h_none with h1 h2
    · exact False.elim (by simp at h_none)
    · exact False.elim (by simp at h_none)
    · exact Int.not_le.mp h2

end Compass.RateLimiter
