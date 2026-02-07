/-
  Compass.Router - Security proofs for API key scope and privilege escalation
  
  Contains proven theorems:
  - P0-R1: API Key Scope Restriction
  - P0-R2: No Empty Scope Violation  
  - P0-R3: No Privilege Escalation
-/

import Compass.Core

namespace Compass.Router

open Compass.Core

/-! ## Operations and Scopes -/

inductive Operation where
  | read : Operation
  | write : Operation
  | admin : Operation
  deriving DecidableEq, Repr, Inhabited

def Operation.toString : Operation → String
  | .read => "read"
  | .write => "write"
  | .admin => "admin"

def Operation.fromString : String → Option Operation
  | "read" => some .read
  | "write" => some .write
  | "admin" => some .admin
  | _ => none

theorem operation_roundtrip (op : Operation) :
    Operation.fromString (Operation.toString op) = some op := by
  cases op <;> rfl

instance : Extractable Operation where
  encode op := .str (Operation.toString op)
  decode j := do
    let s ← j.asString
    Operation.fromString s
  roundtrip op := by simp [Json.asString, operation_roundtrip]

/-! ## Scope -/

structure Scope where
  allowedOps : List Operation
  invariant : allowedOps ≠ []
  deriving Repr

def restricts (keyScope : Scope) (op : Operation) : Prop :=
  op ∈ keyScope.allowedOps

/-! ## THEOREM P0-R1: API Key Scope Restriction
    
    If an operation is allowed by a key's scope, then any operation NOT in the
    scope cannot be aliased to the allowed operation. This prevents scope bypass.
-/

theorem api_key_scope_restriction {keyScope : Scope} {op : Operation} :
    restricts keyScope op → 
    ∀ otherOp : Operation, otherOp ∉ keyScope.allowedOps → otherOp ≠ op := by
  intro h_restrict otherOp h_not_in h_eq
  rw [h_eq] at h_not_in
  exact h_not_in h_restrict

/-! ## THEOREM P0-R2: No Empty Scope Violation

    A Scope cannot have an empty allowedOps list. This is enforced by the
    `invariant` field which proves `allowedOps ≠ []`.
-/

theorem no_empty_scope_violation (keyScope : Scope) :
    keyScope.allowedOps = [] → False := by
  intro h_empty
  exact keyScope.invariant h_empty

/-! ## THEOREM P0-R3: No Privilege Escalation

    If an operation is NOT allowed by a base scope, and the base scope is a 
    subset of an elevated scope, then the operation is also NOT allowed by
    the elevated scope. This prevents privilege escalation attacks.
-/

def listSubset (xs ys : List Operation) : Prop :=
  ∀ x, x ∈ xs → x ∈ ys

/-! ## THEOREM P0-R3: No Privilege Escalation

    If a derived scope is a SUBSET of the base scope (can only restrict, not expand),
    then any operation not in the base is also not in the derived.
    
    This is the core security invariant: API keys cannot have more permissions
    than the user who created them.
-/

theorem no_privilege_escalation {baseScope derivedScope : Scope} {op : Operation} :
    listSubset derivedScope.allowedOps baseScope.allowedOps →
    ¬ restricts baseScope op → 
    ¬ restricts derivedScope op := by
  intro h_subset h_not_base h_derived
  apply h_not_base
  exact h_subset op h_derived

/-! ## THEOREM P0-R4: Scope Intersection Safety

    The intersection of two scopes is always a subset of each original scope.
-/

def scopeIntersect (s1 s2 : List Operation) : List Operation :=
  s1.filter (· ∈ s2)

theorem scope_intersect_subset_left (s1 s2 : List Operation) :
    listSubset (scopeIntersect s1 s2) s1 := by
  intro op h_in
  simp [scopeIntersect] at h_in
  exact h_in.1

theorem scope_intersect_subset_right (s1 s2 : List Operation) :
    listSubset (scopeIntersect s1 s2) s2 := by
  intro op h_in
  simp [scopeIntersect] at h_in
  exact h_in.2

/-! ## Circuit Breaker State Machine -/

inductive CircuitState where
  | Closed : CircuitState      -- Normal operation
  | Open : CircuitState        -- Failing, reject requests
  | HalfOpen : CircuitState    -- Testing if recovered
  deriving DecidableEq, Repr, Inhabited

def CircuitState.toString : CircuitState → String
  | .Closed => "closed"
  | .Open => "open"
  | .HalfOpen => "half_open"

def CircuitState.fromString : String → Option CircuitState
  | "closed" => some .Closed
  | "open" => some .Open
  | "half_open" => some .HalfOpen
  | _ => none

theorem circuit_state_roundtrip (s : CircuitState) :
    CircuitState.fromString (CircuitState.toString s) = some s := by
  cases s <;> rfl

instance : Extractable CircuitState where
  encode s := .str (CircuitState.toString s)
  decode j := do
    let str ← j.asString
    CircuitState.fromString str
  roundtrip s := by simp [Json.asString, circuit_state_roundtrip]

/-! ## Circuit Breaker -/

structure CircuitBreaker where
  state : CircuitState
  failure_count : Nat
  success_count : Nat
  failure_threshold : Nat
  success_threshold : Nat
  deriving Repr

def CircuitBreaker.allowsRequest (cb : CircuitBreaker) : Bool :=
  match cb.state with
  | .Closed => true
  | .Open => false
  | .HalfOpen => true

/-! ## THEOREM: Closed circuit always allows requests -/

theorem closed_always_allows (cb : CircuitBreaker) (h : cb.state = .Closed) :
    cb.allowsRequest = true := by
  simp [CircuitBreaker.allowsRequest, h]

/-! ## THEOREM: Open circuit never allows requests -/

theorem open_never_allows (cb : CircuitBreaker) (h : cb.state = .Open) :
    cb.allowsRequest = false := by
  simp [CircuitBreaker.allowsRequest, h]

/-! ## Router Result -/

inductive RouterResult where
  | Success : String → RouterResult
  | PermissionDenied : String → RouterResult
  | RateLimitExceeded : Nat → RouterResult
  | BudgetExceeded : Float → RouterResult
  | ValidationFailed : String → RouterResult
  | CircuitOpen : RouterResult
  deriving Repr

def RouterResult.isSuccess : RouterResult → Bool
  | .Success _ => true
  | _ => false

/-! ## THEOREM: Non-success results indicate specific failures -/

theorem non_success_has_reason (r : RouterResult) (h : ¬ r.isSuccess) :
    (∃ msg, r = .PermissionDenied msg) ∨
    (∃ n, r = .RateLimitExceeded n) ∨
    (∃ f, r = .BudgetExceeded f) ∨
    (∃ msg, r = .ValidationFailed msg) ∨
    r = .CircuitOpen := by
  cases r with
  | Success _ => simp [RouterResult.isSuccess] at h
  | PermissionDenied msg => exact Or.inl ⟨msg, rfl⟩
  | RateLimitExceeded n => exact Or.inr (Or.inl ⟨n, rfl⟩)
  | BudgetExceeded f => exact Or.inr (Or.inr (Or.inl ⟨f, rfl⟩))
  | ValidationFailed msg => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨msg, rfl⟩)))
  | CircuitOpen => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-! ## Circuit Breaker State Machine Recovery -/

/-- Transition circuit breaker on success -/
def CircuitBreaker.onSuccess (cb : CircuitBreaker) : CircuitBreaker :=
  match cb.state with
  | .Closed => { cb with failure_count := 0 }
  | .HalfOpen => 
    if cb.success_count + 1 ≥ cb.success_threshold then
      { cb with state := .Closed, success_count := 0, failure_count := 0 }
    else
      { cb with success_count := cb.success_count + 1 }
  | .Open => cb  -- Open state doesn't process successes

/-- Transition circuit breaker on failure -/
def CircuitBreaker.onFailure (cb : CircuitBreaker) : CircuitBreaker :=
  match cb.state with
  | .Closed =>
    if cb.failure_count + 1 ≥ cb.failure_threshold then
      { cb with state := .Open, failure_count := 0 }
    else
      { cb with failure_count := cb.failure_count + 1 }
  | .HalfOpen => { cb with state := .Open, success_count := 0 }
  | .Open => cb

/-! ## THEOREM: Circuit breaker eventually closes after enough successes -/

/-- After enough successes in HalfOpen state, circuit closes -/
theorem circuit_eventually_closes_spec (cb : CircuitBreaker) :
    cb.state = .HalfOpen →
    cb.success_count + 1 ≥ cb.success_threshold →
    (cb.onSuccess).state = .Closed := by
  intro h_half h_thresh
  simp [CircuitBreaker.onSuccess, h_half, h_thresh]

/-- Single success in HalfOpen increments count or closes -/
theorem halfopen_success_progress (cb : CircuitBreaker) (h : cb.state = .HalfOpen) :
    (cb.onSuccess).state = .Closed ∨ 
    (cb.onSuccess).success_count = cb.success_count + 1 := by
  simp [CircuitBreaker.onSuccess, h]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end Compass.Router
