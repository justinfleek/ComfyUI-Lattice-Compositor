/-
  ParticleSim.Particle
  
  Particles with positive mass, position, and velocity.
  Momentum is mass × velocity.
-/
import ParticleSim.Vec3
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Tactic

namespace ParticleSim

/-- A particle with positive mass, position, and velocity -/
structure Particle where
  pos : Vec3
  vel : Vec3
  mass : ℚ
  mass_pos : 0 < mass
deriving Repr

namespace Particle

/-- Momentum of a single particle: p = m * v -/
def momentum (p : Particle) : Vec3 := p.mass * p.vel

/-- Kinetic energy of a particle (times 2 to avoid fractions): 2T = m * v² -/
def kineticEnergyTimes2 (p : Particle) : ℚ := p.mass * p.vel.normSq

/-- Kinetic energy is non-negative -/
theorem kineticEnergy_nonneg (p : Particle) : 0 ≤ p.kineticEnergyTimes2 := by
  unfold kineticEnergyTimes2
  apply mul_nonneg
  · exact le_of_lt p.mass_pos
  · exact Vec3.normSq_nonneg p.vel

end Particle

-- ============================================================================
-- PARTICLE SYSTEMS
-- ============================================================================

/-- A system of particles (non-empty) -/
def ParticleSystem := List Particle

namespace ParticleSystem

/-- Total momentum of a system -/
def totalMomentum (sys : ParticleSystem) : Vec3 :=
  sys.foldl (fun acc p => acc + p.momentum) 0

/-- Total mass of a system -/
def totalMass (sys : ParticleSystem) : ℚ :=
  sys.foldl (fun acc p => acc + p.mass) 0

/-- Total kinetic energy times 2 -/
def totalKE2 (sys : ParticleSystem) : ℚ :=
  sys.foldl (fun acc p => acc + p.kineticEnergyTimes2) 0

-- Alternative definition using map and sum for easier proofs
def totalMomentum' (sys : ParticleSystem) : Vec3 :=
  (sys.map Particle.momentum).foldl (· + ·) 0

/-- Helper: folding addition over list -/
theorem foldl_add_eq_cons (acc : Vec3) (p : Particle) (ps : List Particle) :
    (p :: ps).foldl (fun a q => a + q.momentum) acc = 
    ps.foldl (fun a q => a + q.momentum) (acc + p.momentum) := by
  simp [List.foldl]

/-- Total momentum of empty system is zero -/
theorem totalMomentum_nil : totalMomentum [] = 0 := by
  unfold totalMomentum
  simp [List.foldl]

/-- Total momentum of cons -/
theorem totalMomentum_cons (p : Particle) (ps : ParticleSystem) :
    totalMomentum (p :: ps) = p.momentum + totalMomentum ps := by
  unfold totalMomentum
  simp only [List.foldl]
  -- Need to prove: foldl ... (0 + p.momentum) ps = p.momentum + foldl ... 0 ps
  induction ps generalizing p with
  | nil => 
    simp [List.foldl, Vec3.zero_add, Vec3.add_zero]
  | cons q qs ih =>
    simp only [List.foldl]
    have h1 : (0 : Vec3) + p.momentum = p.momentum := Vec3.zero_add _
    rw [h1]
    -- Now we need: foldl ... (p.momentum + q.momentum) qs = p.momentum + foldl ... q.momentum qs
    -- Generalize: foldl ... (a + b) xs = a + foldl ... b xs
    have gen : ∀ (a b : Vec3) (xs : List Particle),
        xs.foldl (fun acc r => acc + r.momentum) (a + b) = 
        a + xs.foldl (fun acc r => acc + r.momentum) b := by
      intro a b xs
      induction xs generalizing a b with
      | nil => simp [List.foldl]
      | cons y ys ihy =>
        simp only [List.foldl]
        rw [Vec3.add_assoc]
        exact ihy a (b + y.momentum)
    rw [gen]

/-- Total mass of empty system is zero -/
theorem totalMass_nil : totalMass [] = 0 := by
  unfold totalMass
  simp [List.foldl]

/-- Total mass of cons -/
theorem totalMass_cons (p : Particle) (ps : ParticleSystem) :
    totalMass (p :: ps) = p.mass + totalMass ps := by
  unfold totalMass
  simp only [List.foldl]
  induction ps generalizing p with
  | nil => simp [List.foldl]
  | cons q qs ih =>
    simp only [List.foldl]
    have gen : ∀ (a b : ℚ) (xs : List Particle),
        xs.foldl (fun acc r => acc + r.mass) (a + b) = 
        a + xs.foldl (fun acc r => acc + r.mass) b := by
      intro a b xs
      induction xs generalizing a b with
      | nil => simp [List.foldl]
      | cons y ys ihy =>
        simp only [List.foldl]
        rw [add_assoc]
        exact ihy a (b + y.mass)
    simp only [zero_add]
    rw [gen]

/-- Total mass is non-negative -/
theorem totalMass_nonneg (sys : ParticleSystem) : 0 ≤ totalMass sys := by
  induction sys with
  | nil => simp [totalMass_nil]
  | cons p ps ih =>
    rw [totalMass_cons]
    apply add_nonneg
    · exact le_of_lt p.mass_pos
    · exact ih

end ParticleSystem

end ParticleSim
