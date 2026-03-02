/-
  Lattice.Schemas.Settings.ValidationLimitsSchema - Validation limits schema

  Validates validation limits stored in localStorage.

  Source: ui/src/schemas/settings/validation-limits-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.Settings.ValidationLimitsSchema

open Lattice.Schemas.SharedValidation

/-! ## Absolute Maximums (Security Critical) -/

def MAX_DIMENSION_ABSOLUTE : Nat := 16384
def MAX_FRAME_COUNT_ABSOLUTE : Nat := 100000
def MAX_ARRAY_LENGTH_ABSOLUTE : Nat := 1000000
def MAX_PARTICLES_ABSOLUTE : Nat := 10000000
def MAX_LAYERS_ABSOLUTE : Nat := 10000
def MAX_KEYFRAMES_ABSOLUTE : Nat := 100000
def MAX_STRING_LENGTH_ABSOLUTE : Nat := 1000000
def MAX_FPS_ABSOLUTE : Nat := 120

/-! ## Validation Limits Structure -/

/-- Validation limits with configurable and absolute values -/
structure ValidationLimits where
  maxDimension : Nat
  maxDimensionAbsolute : Nat
  maxFrameCount : Nat
  maxFrameCountAbsolute : Nat
  maxArrayLength : Nat
  maxArrayLengthAbsolute : Nat
  maxParticles : Nat
  maxParticlesAbsolute : Nat
  maxLayers : Nat
  maxLayersAbsolute : Nat
  maxKeyframesPerProperty : Nat
  maxKeyframesPerPropertyAbsolute : Nat
  maxStringLength : Nat
  maxStringLengthAbsolute : Nat
  maxFPS : Nat
  maxFPSAbsolute : Nat
  deriving Repr, BEq

/-! ## Default Values -/

def defaultValidationLimits : ValidationLimits :=
  { maxDimension := 8192
  , maxDimensionAbsolute := MAX_DIMENSION_ABSOLUTE
  , maxFrameCount := 10000
  , maxFrameCountAbsolute := MAX_FRAME_COUNT_ABSOLUTE
  , maxArrayLength := 100000
  , maxArrayLengthAbsolute := MAX_ARRAY_LENGTH_ABSOLUTE
  , maxParticles := 1000000
  , maxParticlesAbsolute := MAX_PARTICLES_ABSOLUTE
  , maxLayers := 1000
  , maxLayersAbsolute := MAX_LAYERS_ABSOLUTE
  , maxKeyframesPerProperty := 10000
  , maxKeyframesPerPropertyAbsolute := MAX_KEYFRAMES_ABSOLUTE
  , maxStringLength := 100000
  , maxStringLengthAbsolute := MAX_STRING_LENGTH_ABSOLUTE
  , maxFPS := 120
  , maxFPSAbsolute := MAX_FPS_ABSOLUTE
  }

/-! ## Validation -/

/-- Validate that configurable limits don't exceed absolute limits -/
def validateLimitsConstraint (limits : ValidationLimits) : Except ValidationError Unit :=
  if limits.maxDimension > limits.maxDimensionAbsolute then
    throw (mkError "maxDimension" "must be <= maxDimensionAbsolute")
  else if limits.maxFrameCount > limits.maxFrameCountAbsolute then
    throw (mkError "maxFrameCount" "must be <= maxFrameCountAbsolute")
  else if limits.maxArrayLength > limits.maxArrayLengthAbsolute then
    throw (mkError "maxArrayLength" "must be <= maxArrayLengthAbsolute")
  else if limits.maxParticles > limits.maxParticlesAbsolute then
    throw (mkError "maxParticles" "must be <= maxParticlesAbsolute")
  else if limits.maxLayers > limits.maxLayersAbsolute then
    throw (mkError "maxLayers" "must be <= maxLayersAbsolute")
  else if limits.maxKeyframesPerProperty > limits.maxKeyframesPerPropertyAbsolute then
    throw (mkError "maxKeyframesPerProperty" "must be <= maxKeyframesPerPropertyAbsolute")
  else if limits.maxStringLength > limits.maxStringLengthAbsolute then
    throw (mkError "maxStringLength" "must be <= maxStringLengthAbsolute")
  else if limits.maxFPS > limits.maxFPSAbsolute then
    throw (mkError "maxFPS" "must be <= maxFPSAbsolute")
  else
    pure ()

/-- Validate individual field values -/
def validateFieldValues (limits : ValidationLimits) : Except ValidationError Unit := do
  let _ ← validatePositiveInt "maxDimension" MAX_DIMENSION_ABSOLUTE limits.maxDimension
  let _ ← validatePositiveInt "maxDimensionAbsolute" MAX_DIMENSION_ABSOLUTE limits.maxDimensionAbsolute
  let _ ← validatePositiveInt "maxFrameCount" MAX_FRAME_COUNT_ABSOLUTE limits.maxFrameCount
  let _ ← validatePositiveInt "maxFrameCountAbsolute" MAX_FRAME_COUNT_ABSOLUTE limits.maxFrameCountAbsolute
  let _ ← validatePositiveInt "maxArrayLength" MAX_ARRAY_LENGTH_ABSOLUTE limits.maxArrayLength
  let _ ← validatePositiveInt "maxArrayLengthAbsolute" MAX_ARRAY_LENGTH_ABSOLUTE limits.maxArrayLengthAbsolute
  let _ ← validatePositiveInt "maxParticles" MAX_PARTICLES_ABSOLUTE limits.maxParticles
  let _ ← validatePositiveInt "maxParticlesAbsolute" MAX_PARTICLES_ABSOLUTE limits.maxParticlesAbsolute
  let _ ← validatePositiveInt "maxLayers" MAX_LAYERS_ABSOLUTE limits.maxLayers
  let _ ← validatePositiveInt "maxLayersAbsolute" MAX_LAYERS_ABSOLUTE limits.maxLayersAbsolute
  let _ ← validatePositiveInt "maxKeyframesPerProperty" MAX_KEYFRAMES_ABSOLUTE limits.maxKeyframesPerProperty
  let _ ← validatePositiveInt "maxKeyframesPerPropertyAbsolute" MAX_KEYFRAMES_ABSOLUTE limits.maxKeyframesPerPropertyAbsolute
  let _ ← validatePositiveInt "maxStringLength" MAX_STRING_LENGTH_ABSOLUTE limits.maxStringLength
  let _ ← validatePositiveInt "maxStringLengthAbsolute" MAX_STRING_LENGTH_ABSOLUTE limits.maxStringLengthAbsolute
  let _ ← validatePositiveInt "maxFPS" MAX_FPS_ABSOLUTE limits.maxFPS
  let _ ← validatePositiveInt "maxFPSAbsolute" MAX_FPS_ABSOLUTE limits.maxFPSAbsolute
  pure ()

/-- Full validation of ValidationLimits -/
def validateValidationLimits (limits : ValidationLimits) : Except ValidationError ValidationLimits := do
  validateFieldValues limits
  validateLimitsConstraint limits
  pure limits

/-- Safe validation (returns Option) -/
def safeValidateValidationLimits (limits : ValidationLimits) : Option ValidationLimits :=
  match validateValidationLimits limits with
  | .ok l => some l
  | .error _ => none

end Lattice.Schemas.Settings.ValidationLimitsSchema
