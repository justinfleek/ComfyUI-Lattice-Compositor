/-
  ParticleSim.Forces
  
  Forces between particles and Newton's laws.
  Key theorem: If forces satisfy Newton's third law, momentum is conserved.
-/
import ParticleSim.Particle
import Mathlib.Tactic

namespace ParticleSim

/-- An internal force between particles i and j -/
structure InternalForce (n : ℕ) where
  i : Fin n
  j : Fin n
  force : Vec3  -- Force on particle i from particle j
  
/-- Newton's third law: force from i on j equals negative of force from j on i -/
def newton3 {n : ℕ} (f_ij f_ji : InternalForce n) : Prop :=
  f_ij.i = f_ji.j ∧ f_ij.j = f_ji.i ∧ f_ij.force + f_ji.force = 0

/-- A force configuration is a list of internal forces -/
def ForceConfig (n : ℕ) := List (InternalForce n)

/-- 
A force configuration satisfies Newton's third law if for every force f_ij,
there exists a corresponding force f_ji such that they sum to zero.

For simplicity, we represent this as the sum of all forces being zero.
-/
def satisfiesNewton3 {n : ℕ} (forces : ForceConfig n) : Prop :=
  (forces.map InternalForce.force).foldl (· + ·) 0 = 0

-- ============================================================================
-- TIME EVOLUTION
-- ============================================================================

/-- 
Apply a force to a particle for time dt (impulse changes momentum).
New velocity = old velocity + (force/mass) * dt
Using exact rational arithmetic.
-/
def applyImpulse (p : Particle) (f : Vec3) (dt : ℚ) (dt_pos : 0 < dt) : Particle where
  pos := p.pos + dt * p.vel  -- Simple Euler position update
  vel := p.vel + (dt / p.mass) * f  -- Velocity change from impulse
  mass := p.mass
  mass_pos := p.mass_pos

/-- 
Net force on particle i from a force configuration.
Sum of all forces where the target is i.
-/
def netForceOn {n : ℕ} (i : Fin n) (forces : ForceConfig n) : Vec3 :=
  (forces.filter (fun f => f.i = i)).foldl (fun acc f => acc + f.force) 0

/--
Apply forces to an indexed particle system represented as a function.
-/
def applyForcesIndexed {n : ℕ} (particles : Fin n → Particle) 
    (forces : ForceConfig n) (dt : ℚ) (dt_pos : 0 < dt) : Fin n → Particle :=
  fun i => applyImpulse (particles i) (netForceOn i forces) dt dt_pos

-- ============================================================================
-- MOMENTUM CONSERVATION THEOREM
-- ============================================================================

/-- Sum of vectors in a list -/
def sumVec3 (vs : List Vec3) : Vec3 := vs.foldl (· + ·) 0

theorem sumVec3_nil : sumVec3 [] = 0 := by
  unfold sumVec3
  simp [List.foldl]

theorem sumVec3_cons (v : Vec3) (vs : List Vec3) : 
    sumVec3 (v :: vs) = v + sumVec3 vs := by
  unfold sumVec3
  simp only [List.foldl]
  induction vs generalizing v with
  | nil => simp [List.foldl, Vec3.zero_add, Vec3.add_zero]
  | cons w ws ih =>
    simp only [List.foldl]
    have gen : ∀ (a b : Vec3) (xs : List Vec3),
        xs.foldl (· + ·) (a + b) = a + xs.foldl (· + ·) b := by
      intro a b xs
      induction xs generalizing a b with
      | nil => simp [List.foldl]
      | cons y ys ihy =>
        simp only [List.foldl]
        rw [Vec3.add_assoc]
        exact ihy a (b + y)
    simp only [Vec3.zero_add]
    rw [gen]

theorem sumVec3_append (vs ws : List Vec3) : 
    sumVec3 (vs ++ ws) = sumVec3 vs + sumVec3 ws := by
  induction vs with
  | nil => simp [sumVec3_nil, Vec3.zero_add]
  | cons v vs' ih =>
    simp only [List.cons_append]
    rw [sumVec3_cons, sumVec3_cons, ih, Vec3.add_assoc]

/-- 
Momentum of a particle after impulse.
Key lemma: momentum changes by exactly f * dt
-/
theorem momentum_after_impulse (p : Particle) (f : Vec3) (dt : ℚ) (dt_pos : 0 < dt) :
    (applyImpulse p f dt dt_pos).momentum = p.momentum + dt * f := by
  unfold applyImpulse Particle.momentum
  simp only [Vec3.smul_def, Vec3.add_def]
  ext <;> field_simp <;> ring

/--
Total momentum of indexed system
-/
def totalMomentumIndexed {n : ℕ} (particles : Fin n → Particle) : Vec3 :=
  Finset.univ.sum (fun i => (particles i).momentum)

/-- 
Change in momentum equals sum of all impulses.
If forces satisfy Newton's third law (sum to zero), momentum is conserved.
-/
theorem momentum_change_eq_impulse_sum {n : ℕ} 
    (particles : Fin n → Particle)
    (forces : ForceConfig n) 
    (dt : ℚ) (dt_pos : 0 < dt) :
    let particles' := applyForcesIndexed particles forces dt dt_pos
    totalMomentumIndexed particles' = 
      totalMomentumIndexed particles + dt * sumVec3 (forces.map InternalForce.force) := by
  intro particles'
  unfold totalMomentumIndexed applyForcesIndexed
  -- This requires more machinery to prove properly
  -- The key insight is that each particle's momentum change is (netForceOn i) * dt
  -- and the sum of all netForceOn equals sumVec3 (forces.map force)
  sorry -- TODO: complete this proof with proper Finset manipulation

/--
MAIN THEOREM: Conservation of momentum under Newton's third law.

If all internal forces satisfy Newton's third law (i.e., they sum to zero),
then total momentum is conserved.
-/
theorem momentum_conserved {n : ℕ} 
    (particles : Fin n → Particle)
    (forces : ForceConfig n) 
    (n3 : satisfiesNewton3 forces)
    (dt : ℚ) (dt_pos : 0 < dt) :
    let particles' := applyForcesIndexed particles forces dt dt_pos
    totalMomentumIndexed particles' = totalMomentumIndexed particles := by
  intro particles'
  -- We would use momentum_change_eq_impulse_sum here
  -- Then use n3 to show the impulse sum is zero
  -- For now, let's prove it directly for the simplified case
  unfold satisfiesNewton3 at n3
  -- sumVec3 and the foldl are equivalent
  have h_sum : sumVec3 (forces.map InternalForce.force) = 0 := by
    unfold sumVec3
    exact n3
  -- Using the previous theorem (once proven):
  -- rw [momentum_change_eq_impulse_sum]
  -- rw [h_sum, Vec3.smul_zero, Vec3.add_zero]
  sorry -- Completes once momentum_change_eq_impulse_sum is proven

end ParticleSim
