/-
  Lattice.Particles.Audio - Particle audio bindings

  Part of Particles module. Max 500 lines.

  Source: ui/src/types/particles.ts (audio bindings)
-/

import Lattice.Primitives
import Lattice.Particles.Enums

namespace Lattice.Particles.Audio

open Lattice.Primitives
open Lattice.Particles.Enums

/-! ## Audio Binding Config -/

/-- Audio-reactive particle binding -/
structure AudioBindingConfig where
  id : NonEmptyString
  enabled : Bool
  feature : AudioFeatureName         -- Which audio feature to use
  smoothing : Float                  -- 0-1, temporal smoothing
  min : Float                        -- Feature value mapping input min
  max : Float                        -- Feature value mapping input max
  target : AudioTargetType           -- What to affect
  targetId : NonEmptyString          -- Emitter/force field ID, or 'system'
  parameter : NonEmptyString         -- Parameter name (e.g., 'emissionRate')
  outputMin : Float                  -- Output range min
  outputMax : Float                  -- Output range max
  curve : AudioCurveType             -- Response curve
  stepCount : Nat                    -- Steps for 'step' curve (default: 5)
  triggerMode : AudioTriggerMode     -- When to apply
  threshold : Float                  -- For 'onThreshold' mode (0-1)
  smoothing_ge_0 : smoothing ≥ 0
  smoothing_le_1 : smoothing ≤ 1
  smoothing_finite : smoothing.isFinite
  min_finite : min.isFinite
  max_finite : max.isFinite
  min_le_max : min ≤ max
  outputMin_finite : outputMin.isFinite
  outputMax_finite : outputMax.isFinite
  stepCount_positive : stepCount > 0
  threshold_ge_0 : threshold ≥ 0
  threshold_le_1 : threshold ≤ 1
  threshold_finite : threshold.isFinite
  deriving Repr

/-! ## Audio Particle Mapping -/

/-- Audio-to-particle parameter mapping -/
structure AudioParticleMapping where
  feature : AudioFeatureName
  parameter : AudioMappingParameter
  emitterId : Option NonEmptyString  -- Specific emitter or none for all
  sensitivity : Float
  smoothing : Float                  -- 0-1
  sensitivity_positive : sensitivity > 0
  sensitivity_finite : sensitivity.isFinite
  smoothing_ge_0 : smoothing ≥ 0
  smoothing_le_1 : smoothing ≤ 1
  smoothing_finite : smoothing.isFinite
  deriving Repr

end Lattice.Particles.Audio
