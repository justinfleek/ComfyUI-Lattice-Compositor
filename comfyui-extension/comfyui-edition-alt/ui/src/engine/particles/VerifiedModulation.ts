/**
 * VERIFIED LIFETIME MODULATION - Anti-Compounding
 * 
 * INVARIANT: Uses initialSize, never current size
 * This prevents exponential decay/compounding during modulation
 * 
 * Based on ParticleSystemVerified.ts from leanparticles/
 */

import type { ParticleBuffer } from "./VerifiedParticleBuffer";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                      // modulation // curves
// ════════════════════════════════════════════════════════════════════════════

export type ModulationCurve = 'linear' | 'easeIn' | 'easeOut' | 'easeInOut';

/**
 * Evaluate modulation curve at life ratio t ∈ [0, 1]
 * 
 * All curves map [0, 1] → [0, 1]
 * 
 * @param curve - Curve type
 * @param t - Life ratio in [0, 1]
 * @returns Curve value in [0, 1]
 */
function evalCurve(curve: ModulationCurve, t: number): number {
  // Clamp t to [0, 1]
  const clampedT = Math.max(0, Math.min(1, t));
  
  switch (curve) {
    case 'linear': 
      return clampedT;
    case 'easeIn': 
      return clampedT * clampedT;
    case 'easeOut': 
      return 1 - (1 - clampedT) * (1 - clampedT);
    case 'easeInOut': 
      return clampedT < 0.5 
        ? 2 * clampedT * clampedT 
        : 1 - 2 * (1 - clampedT) * (1 - clampedT);
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                    // lifetime // modulation
// ════════════════════════════════════════════════════════════════════════════

/**
 * Apply lifetime-based size modulation
 * 
 * INVARIANT: Uses initialSize, never current size
 * PROVEN: No compounding - always multiplies initialSize by curve value
 * 
 * @param particles - Particle buffer (SOA layout)
 * @param curve - Modulation curve type
 * @param startScale - Size scale at birth (lifeRatio = 0)
 * @param endScale - Size scale at death (lifeRatio = 1)
 */
export function applyLifetimeSizeModulation(
  particles: ParticleBuffer,
  curve: ModulationCurve,
  startScale: number,
  endScale: number
): void {
  const count = particles.count;
  const size = particles.size;
  const initialSize = particles.initialSize;
  const age = particles.age;
  const lifetime = particles.lifetime;
  
  // Validate scales
  const safeStartScale = Number.isFinite(startScale) && startScale >= 0 ? startScale : 1;
  const safeEndScale = Number.isFinite(endScale) && endScale >= 0 ? endScale : 1;
  
  for (let i = 0; i < count; i++) {
    // Calculate life ratio: age / lifetime
    const safeLifetime = Math.max(lifetime[i], 0.001); // Guard against zero lifetime
    const lifeRatio = Math.min(1, Math.max(0, age[i] / safeLifetime));
    
    // Evaluate curve at life ratio
    const curveVal = evalCurve(curve, lifeRatio);
    
    // Interpolate between start and end scale
    const scale = safeStartScale + (safeEndScale - safeStartScale) * curveVal;
    
    //                                                                  // critical
    //                                                                    // proven
    size[i] = initialSize[i] * scale;
    
    // Ensure result is finite and positive
    if (!Number.isFinite(size[i]) || size[i] <= 0) {
      size[i] = initialSize[i];
    }
  }
}

/**
 * Apply lifetime-based opacity modulation
 * 
 * Similar to size modulation but for opacity (alpha)
 * 
 * @param particles - Particle buffer (SOA layout)
 * @param curve - Modulation curve type
 * @param startOpacity - Opacity at birth [0, 1]
 * @param endOpacity - Opacity at death [0, 1]
 */
export function applyLifetimeOpacityModulation(
  particles: ParticleBuffer,
  curve: ModulationCurve,
  startOpacity: number,
  endOpacity: number
): void {
  const count = particles.count;
  const colorA = particles.colorA;
  const age = particles.age;
  const lifetime = particles.lifetime;
  
  // Validate opacities
  const safeStartOpacity = Math.max(0, Math.min(1, Number.isFinite(startOpacity) ? startOpacity : 1));
  const safeEndOpacity = Math.max(0, Math.min(1, Number.isFinite(endOpacity) ? endOpacity : 0));
  
  for (let i = 0; i < count; i++) {
    // Calculate life ratio
    const safeLifetime = Math.max(lifetime[i], 0.001);
    const lifeRatio = Math.min(1, Math.max(0, age[i] / safeLifetime));
    
    // Evaluate curve at life ratio
    const curveVal = evalCurve(curve, lifeRatio);
    
    // Interpolate opacity
    colorA[i] = Math.max(0, Math.min(1, safeStartOpacity + (safeEndOpacity - safeStartOpacity) * curveVal));
  }
}
