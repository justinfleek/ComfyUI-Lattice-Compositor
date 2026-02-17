# Changelog

All notable changes to the Lattice Compositor will be documented in this file.

## [Unreleased]

### Fixed

#### 2026-01-05: math3d.ts Precision Fixes (5 bugs)

**Bugs Fixed:** BUG-054, BUG-055, BUG-056, BUG-057, BUG-058

**Problem:** 
- Float32Array precision loss during matrix operations
- Euler angle conversion numerical instability
- Gimbal lock producing NaN/undefined values
- Very small angle sign flip errors

**Solution:**
1. Added `Mat4_64` interface for high-precision (Float64) calculations
2. Rewrote `multiplyMat4()` to use Float64 intermediate calculations
3. Rewrote `quatToEuler()` using rotation-matrix decomposition algorithm (Three.js/Unity standard)
4. Added quaternion normalization before Euler extraction
5. Added explicit gimbal lock handling with stable fallback
6. Added precision constants and converter functions

**Files Changed:**
- `ui/src/services/math3d.ts`
- `ui/src/__tests__/properties/strict-transforms.property.test.ts`

**Verification:**
- All 33 property tests pass
- Scale composition error: < 1e-13 (was 1e-7)
- Euler angle error at 89.95°: 1.2e-13 (was failing)
- No NaN/Infinity edge cases

**Impact:**
- Camera matrices for AI model export (MotionCtrl, Uni3C, Wan-Move) now have ~15 digits precision
- Nested transform composition is stable
- Gimbal lock handled gracefully

---

## Version History

### v0.1.0 - Initial Development
- Core compositor functionality
- Layer system
- Effect pipeline
- Export system
