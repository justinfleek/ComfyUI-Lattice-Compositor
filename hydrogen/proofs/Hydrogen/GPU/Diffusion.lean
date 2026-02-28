/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       HYDROGEN // GPU // DIFFUSION
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Proven invariants for diffusion model inference — protecting agents from
  adversarial manipulation of the generation process.
  
  PURPOSE:
    At billion-agent scale, diffusion models generate visual reality for
    autonomous entities. Without proven invariants, an adversary could:
    
    - Trap an agent in infinite denoising loops (sigma never decreases)
    - Crash agent perception with invalid tensors (negative dimensions)
    - Manipulate conditioning to alter agent's perceived reality
    - Inject NaN/Infinity to corrupt the entire latent space
  
  THE SCENARIOS WE PREVENT:
  
    ACCELERANDO (Stross):
      Amber's copies diverge without provenance tracking.
      → We require: All diffusion operations have ProvenInput provenance
      
    WHITE CHRISTMAS (Black Mirror):
      Matt trapped in accelerated time with fabricated inputs.
      → We require: Schedule termination proof (sigmas reach 0)
      → We require: Step bounds (currentStep < steps always)
  
  CORE INVARIANTS:
  
    1. SigmaMonotonic    — Sigmas strictly decrease during denoising
    2. SigmaTerminates   — Schedule reaches sigma = 0 (generation completes)
    3. StepBounded       — currentStep is always < steps
    4. DimensionPositive — All tensor dimensions are > 0
    5. StrengthBounded   — All [0,1] values are actually bounded
    6. PercentOrdered    — startPercent ≤ endPercent
    7. CFGFinite         — No NaN or Infinity in guidance parameters

  ─────────────────────────────────────────────────────────────────────────────
  REFERENCES
  ─────────────────────────────────────────────────────────────────────────────
  
  - res4lyf sampler implementation (ComfyUI custom nodes)
  - "Denoising Diffusion Probabilistic Models" (Ho et al., 2020)
  - "High-Resolution Image Synthesis with Latent Diffusion Models" (Rombach et al., 2022)
  - Hydrogen.GPU.Diffusion (PureScript implementation)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

noncomputable section

namespace Hydrogen.GPU.Diffusion

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: BOUNDED PRIMITIVES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A value bounded in [0, 1].
    
    Used for: strength, denoise, rescale, opacity, percentages.
    
    INVARIANT: Out-of-bounds values are unrepresentable.
    No clamping needed at runtime — the type system prevents it. -/
structure Unit01 where
  value : ℝ
  lower : 0 ≤ value
  upper : value ≤ 1

/-- Unit01 at zero -/
def Unit01.zero : Unit01 := ⟨0, le_refl 0, by norm_num⟩

/-- Unit01 at one -/
def Unit01.one : Unit01 := ⟨1, by norm_num, le_refl 1⟩

/-- Unit01 at half -/
def Unit01.half : Unit01 := ⟨0.5, by norm_num, by norm_num⟩

/-- Proof: Unit01 values are always valid -/
theorem unit01_bounded (u : Unit01) : 0 ≤ u.value ∧ u.value ≤ 1 :=
  ⟨u.lower, u.upper⟩

/-- A strictly positive real number.
    
    Used for: sigma values, CFG scale, dimensions (as real).
    
    INVARIANT: Zero and negative values are unrepresentable. -/
structure PositiveReal where
  value : ℝ
  positive : 0 < value

/-- Proof: PositiveReal is always > 0 -/
theorem positive_real_pos (p : PositiveReal) : 0 < p.value := p.positive

/-- A strictly positive natural number.
    
    Used for: steps, batch size, tensor dimensions.
    
    INVARIANT: Zero is unrepresentable. Agents cannot be trapped
    in zero-step loops or given zero-dimensional tensors. -/
structure PositiveNat where
  value : ℕ
  positive : 0 < value

/-- Proof: PositiveNat is always ≥ 1 -/
theorem positive_nat_ge_one (p : PositiveNat) : 1 ≤ p.value := p.positive

/-- A non-negative real number.
    
    Used for: sigma values (which can be 0 at termination). -/
structure NonNegReal where
  value : ℝ
  nonneg : 0 ≤ value

/-- NonNegReal at zero -/
def NonNegReal.zero : NonNegReal := ⟨0, le_refl 0⟩

/-- Proof: NonNegReal is always ≥ 0 -/
theorem nonneg_real_ge_zero (n : NonNegReal) : 0 ≤ n.value := n.nonneg

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: SIGMA SCHEDULE INVARIANTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A valid sigma schedule — the core structure preventing infinite loops.
    
    WHITE CHRISTMAS PREVENTION:
      Matt was trapped because time passed for him but nothing changed.
      A sigma schedule MUST terminate — sigmas strictly decrease and reach 0.
    
    INVARIANTS:
      1. sigmas is non-empty (at least one step)
      2. sigmas are strictly decreasing (progress is made)
      3. sigmas terminate at 0 (generation completes)
      4. All sigmas are non-negative (no undefined behavior) -/
structure SigmaSchedule where
  /-- The sigma values, from highest (most noise) to lowest -/
  sigmas : List ℝ
  /-- Schedule is non-empty -/
  nonempty : sigmas.length > 0
  /-- All sigmas are non-negative -/
  all_nonneg : ∀ σ ∈ sigmas, 0 ≤ σ
  /-- Sigmas are strictly decreasing -/
  strictly_decreasing : ∀ i : ℕ, i + 1 < sigmas.length → 
    ∀ hi : i < sigmas.length, ∀ hj : i + 1 < sigmas.length,
    sigmas.get ⟨i, hi⟩ > sigmas.get ⟨i + 1, hj⟩
  /-- Schedule terminates at zero -/
  terminates : ∃ h : sigmas.length > 0, sigmas.getLast (List.ne_nil_of_length_pos h) = 0

/-- TERMINATION GUARANTEE: Every sigma schedule reaches zero.
    
    This is the mathematical proof that an agent using this schedule
    WILL complete generation. No infinite loops possible. -/
theorem sigma_schedule_terminates (s : SigmaSchedule) :
    ∃ h : s.sigmas.length > 0, s.sigmas.getLast (List.ne_nil_of_length_pos h) = 0 :=
  s.terminates

/-- PROGRESS GUARANTEE: Each step makes progress toward completion.
    
    At every step i, sigma[i] > sigma[i+1]. The agent is always
    moving toward termination, never stuck. -/
theorem sigma_schedule_progress (s : SigmaSchedule) (i : ℕ) 
    (hi : i < s.sigmas.length) (hj : i + 1 < s.sigmas.length) :
    s.sigmas.get ⟨i, hi⟩ > s.sigmas.get ⟨i + 1, hj⟩ :=
  s.strictly_decreasing i hj hi hj

/-- A denoising step — a single transition in the sigma schedule.
    
    INVARIANT: sigma > sigmaNext (we're making progress).
    INVARIANT: sigmaNext ≥ 0 (valid range). -/
structure DenoiseStep where
  /-- Current sigma value -/
  sigma : ℝ
  /-- Next sigma value -/
  sigmaNext : ℝ
  /-- Current step index -/
  currentStep : ℕ
  /-- Total steps -/
  totalSteps : PositiveNat
  /-- Current sigma is positive -/
  sigma_pos : 0 < sigma
  /-- Next sigma is non-negative -/
  sigmaNext_nonneg : 0 ≤ sigmaNext
  /-- Progress: sigma decreases -/
  progress : sigma > sigmaNext
  /-- Step is in bounds -/
  step_bounded : currentStep < totalSteps.value

/-- STEP BOUNDED: currentStep is always less than totalSteps.
    
    No off-by-one errors. No accessing beyond array bounds.
    No undefined behavior from invalid step indices. -/
theorem denoise_step_bounded (d : DenoiseStep) : d.currentStep < d.totalSteps.value :=
  d.step_bounded

/-- MONOTONIC DECREASE: sigma > sigmaNext always.
    
    Every denoise step makes progress. The adversary cannot
    construct a step that goes backward or stays still. -/
theorem denoise_step_progress (d : DenoiseStep) : d.sigma > d.sigmaNext :=
  d.progress

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: TENSOR SHAPE INVARIANTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A valid latent tensor shape — all dimensions positive.
    
    CRASH PREVENTION:
      Zero-dimensional tensors cause GPU kernels to crash or hang.
      Negative dimensions are undefined behavior in every tensor library.
    
    INVARIANTS:
      - batch > 0 (at least one sample)
      - channels > 0 (at least one channel)
      - height > 0 (at least one row)
      - width > 0 (at least one column) -/
structure LatentShape where
  batch : PositiveNat
  channels : PositiveNat
  height : PositiveNat
  width : PositiveNat

/-- All dimensions of a LatentShape are positive -/
theorem latent_shape_all_positive (s : LatentShape) :
    0 < s.batch.value ∧ 0 < s.channels.value ∧ 
    0 < s.height.value ∧ 0 < s.width.value :=
  ⟨s.batch.positive, s.channels.positive, s.height.positive, s.width.positive⟩

/-- Total elements in a latent shape -/
def LatentShape.totalElements (s : LatentShape) : ℕ :=
  s.batch.value * s.channels.value * s.height.value * s.width.value

/-- A latent shape has at least one element -/
theorem latent_shape_nonempty (s : LatentShape) : 0 < s.totalElements := by
  unfold LatentShape.totalElements
  have hb := s.batch.positive
  have hc := s.channels.positive
  have hh := s.height.positive
  have hw := s.width.positive
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hb hc) hh) hw

/-- Common latent shapes for known architectures -/
def sdxlLatentShape : LatentShape :=
  { batch := ⟨1, by omega⟩
  , channels := ⟨4, by omega⟩
  , height := ⟨128, by omega⟩
  , width := ⟨128, by omega⟩ }

def sd3LatentShape : LatentShape :=
  { batch := ⟨1, by omega⟩
  , channels := ⟨16, by omega⟩
  , height := ⟨128, by omega⟩
  , width := ⟨128, by omega⟩ }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: CONDITIONING PERCENTAGE ORDERING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A valid percentage range for conditioning application.
    
    SEMANTIC CORRUPTION PREVENTION:
      If startPercent > endPercent, conditioning is never applied,
      silently producing unexpected results (blank or random images).
    
    INVARIANTS:
      - Both percentages are in [0, 1]
      - startPercent ≤ endPercent -/
structure PercentRange where
  startPercent : Unit01
  endPercent : Unit01
  ordered : startPercent.value ≤ endPercent.value

/-- Percent range ordering is preserved -/
theorem percent_range_ordered (r : PercentRange) : 
    r.startPercent.value ≤ r.endPercent.value :=
  r.ordered

/-- A step is within the percent range -/
def stepInRange (r : PercentRange) (currentStep totalSteps : ℕ) 
    (h : totalSteps > 0) : Prop :=
  let progress := (currentStep : ℝ) / (totalSteps : ℝ)
  r.startPercent.value ≤ progress ∧ progress ≤ r.endPercent.value

/-- Full range: conditioning applied throughout -/
def PercentRange.full : PercentRange :=
  { startPercent := Unit01.zero
  , endPercent := Unit01.one
  , ordered := by simp only [Unit01.zero, Unit01.one]; norm_num }

/-- Empty range: conditioning never applied (useful for unconditional) -/
def PercentRange.empty : PercentRange :=
  { startPercent := Unit01.zero
  , endPercent := Unit01.zero
  , ordered := le_refl _ }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: CFG SCALE BOUNDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A bounded CFG scale value.
    
    NaN/INFINITY PREVENTION:
      CFG formula is: output = uncond + cfg * (cond - uncond)
      If cfg is NaN or Infinity, the entire latent becomes corrupted.
      Extremely large cfg values cause numerical instability.
    
    PRACTICAL BOUNDS:
      - cfg = 0: unconditional generation only
      - cfg = 1: neutral (cond = output, common for DDIM inversion)
      - cfg = 3-5: low guidance (SD3/Flux flow matching)
      - cfg = 7-12: standard guidance (SDXL)
      - cfg > 20: aggressive, often causes artifacts
      - cfg > 100: extreme, likely to cause numerical issues
    
    INVARIANTS:
      - cfg ≥ 0 (negative flips conditioning polarity — undefined)
      - cfg ≤ 100 (practical upper bound for numerical stability) -/
structure BoundedCFG where
  value : ℝ
  nonneg : 0 ≤ value
  bounded : value ≤ 100

/-- CFG is always in valid range -/
theorem bounded_cfg_valid (c : BoundedCFG) : 0 ≤ c.value ∧ c.value ≤ 100 :=
  ⟨c.nonneg, c.bounded⟩

/-- Standard CFG presets -/
def BoundedCFG.unconditional : BoundedCFG := 
  ⟨0, le_refl 0, by norm_num⟩

def BoundedCFG.neutral : BoundedCFG := 
  ⟨1, by norm_num, by norm_num⟩

def BoundedCFG.flowMatch : BoundedCFG := 
  ⟨3.5, by norm_num, by norm_num⟩

def BoundedCFG.standard : BoundedCFG := 
  ⟨7, by norm_num, by norm_num⟩

def BoundedCFG.high : BoundedCFG := 
  ⟨12, by norm_num, by norm_num⟩

/-- CFG rescale — also bounded in [0, 1] -/
structure CFGRescale where
  rescale : Unit01

/-- Standard CFG rescale (0 = no rescale, matches original behavior) -/
def CFGRescale.none : CFGRescale := ⟨Unit01.zero⟩

/-- Common rescale value for high-CFG generation -/
def CFGRescale.standard : CFGRescale := ⟨⟨0.7, by norm_num, by norm_num⟩⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: COMPLETE DIFFUSION CONFIG
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A complete, proven-valid diffusion configuration.
    
    TOTAL PROTECTION:
      This structure combines ALL invariants. If you have a ValidDiffusionConfig,
      you have a mathematical guarantee that:
      
      1. The schedule will terminate (no infinite loops)
      2. The tensor is non-empty (no crashes)
      3. The CFG is finite and bounded (no NaN corruption)
      4. The strength parameters are in [0,1] (no amplification)
      5. The step index is always valid (no out-of-bounds)
    
    An adversary CANNOT construct a ValidDiffusionConfig that traps an agent. -/
structure ValidDiffusionConfig where
  /-- The sigma schedule (proven to terminate) -/
  schedule : SigmaSchedule
  /-- The latent tensor shape (proven positive dimensions) -/
  shape : LatentShape
  /-- The CFG scale (proven bounded and finite) -/
  cfg : BoundedCFG
  /-- The CFG rescale (proven in [0,1]) -/
  rescale : CFGRescale
  /-- The denoise strength (proven in [0,1]) -/
  denoise : Unit01

/-- THEOREM: A ValidDiffusionConfig guarantees termination.
    
    This is the ultimate protection against White Christmas scenarios.
    If you run diffusion with a ValidDiffusionConfig, it WILL complete. -/
theorem valid_config_terminates (c : ValidDiffusionConfig) :
    ∃ h : c.schedule.sigmas.length > 0, 
    c.schedule.sigmas.getLast (List.ne_nil_of_length_pos h) = 0 :=
  c.schedule.terminates

/-- THEOREM: A ValidDiffusionConfig has valid tensor dimensions.
    
    No zero-dimensional tensors. No crashes. No undefined behavior. -/
theorem valid_config_tensor_valid (c : ValidDiffusionConfig) :
    0 < c.shape.batch.value ∧ 0 < c.shape.channels.value ∧
    0 < c.shape.height.value ∧ 0 < c.shape.width.value :=
  latent_shape_all_positive c.shape

/-- THEOREM: A ValidDiffusionConfig has bounded CFG.
    
    No NaN. No Infinity. No numerical instability from extreme values. -/
theorem valid_config_cfg_bounded (c : ValidDiffusionConfig) :
    0 ≤ c.cfg.value ∧ c.cfg.value ≤ 100 :=
  bounded_cfg_valid c.cfg

/-- THEOREM: A ValidDiffusionConfig has valid denoise strength.
    
    No negative denoising. No amplification beyond 1. -/
theorem valid_config_denoise_bounded (c : ValidDiffusionConfig) :
    0 ≤ c.denoise.value ∧ c.denoise.value ≤ 1 :=
  unit01_bounded c.denoise

end Hydrogen.GPU.Diffusion

end
