/**
 * VERIFIED PARTICLE SYSTEM - Property-Based Tests
 * 
 * Tests for Lean4-proven invariants:
 * - RNG determinism
 * - No compounding errors
 * - Drag physics (F·v ≤ 0)
 * - Verlet integration properties
 */

import { describe, it, expect } from "vitest";
import { SeededRandom } from "../VerifiedRNG";
import { AudioReactivitySystem } from "../VerifiedAudioReactivity";
import { accumulateForces, ForceType, type ForceField } from "../VerifiedForces";
import { ParticleBuffer } from "../VerifiedParticleBuffer";
import { integrateVerlet } from "../VerifiedIntegrator";
import { pos, unit } from "../VerifiedTypes";

describe("Verified Particle System - Property Tests", () => {
  describe("RNG Determinism", () => {
    it("same seed produces same sequence", () => {
      const rng1 = new SeededRandom(12345);
      const rng2 = new SeededRandom(12345);
      
      const seq1 = Array.from({ length: 100 }, () => rng1.next());
      const seq2 = Array.from({ length: 100 }, () => rng2.next());
      
      expect(seq1).toEqual(seq2);
    });
    
    it("different seeds produce different sequences", () => {
      const rng1 = new SeededRandom(12345);
      const rng2 = new SeededRandom(67890);
      
      const seq1 = Array.from({ length: 100 }, () => rng1.next());
      const seq2 = Array.from({ length: 100 }, () => rng2.next());
      
      expect(seq1).not.toEqual(seq2);
    });
  });
  
  describe("Audio Reactivity - No Compounding", () => {
    it("same audio input always produces same output", () => {
      const system = new AudioReactivitySystem();
      system.registerEmitter(1, 100, 10, 50);
      
      const result1 = system.getModulatedValues(1, unit(0.5));
      const result2 = system.getModulatedValues(1, unit(0.5));
      const result3 = system.getModulatedValues(1, unit(0.5));
      
      expect(result1).toEqual(result2);
      expect(result2).toEqual(result3);
    });
    
    it("modulation uses base values, not current values", () => {
      const system = new AudioReactivitySystem();
      system.registerEmitter(1, 100, 10, 50);
      
      // Apply modulation multiple times
      const result1 = system.getModulatedValues(1, unit(0.5));
      const result2 = system.getModulatedValues(1, unit(0.5));
      const result3 = system.getModulatedValues(1, unit(0.5));
      
      // All should be identical (no compounding)
      expect(result1?.speed).toBe(result2?.speed);
      expect(result2?.speed).toBe(result3?.speed);
    });
  });
  
  describe("Drag Force Physics", () => {
    it("drag force opposes velocity (F·v ≤ 0)", () => {
      const particles = new ParticleBuffer(100);
      particles.spawn(0, 0, 0, 10, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0);
      
      const accX = new Float32Array(100);
      const accY = new Float32Array(100);
      const accZ = new Float32Array(100);
      
      const dragField: ForceField = {
        type: ForceType.Drag,
        strength: 1,
        position: { x: 0, y: 0, z: 0 },
        direction: { x: 0, y: 0, z: 0 },
        falloffStart: 0,
        falloffEnd: 1000,
        linearDrag: 0.1,
        quadDrag: 0.01,
      };
      
      accumulateForces(particles, [dragField], accX, accY, accZ, 0);
      
      // Drag should oppose velocity: F·v ≤ 0
      const vx = particles.velX[0];
      const vy = particles.velY[0];
      const vz = particles.velZ[0];
      const fx = accX[0] * particles.mass[0];
      const fy = accY[0] * particles.mass[0];
      const fz = accZ[0] * particles.mass[0];
      
      const dotProduct = fx * vx + fy * vy + fz * vz;
      expect(dotProduct).toBeLessThanOrEqual(0);
    });
  });
  
  describe("Verlet Integration", () => {
    it("preserves finite values", () => {
      const particles = new ParticleBuffer(10);
      particles.spawn(0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0);
      
      const accX = new Float32Array(10);
      const accY = new Float32Array(10);
      const accZ = new Float32Array(10);
      
      integrateVerlet(particles, accX, accY, accZ, pos(1/60), pos(100));
      
      expect(Number.isFinite(particles.posX[0])).toBe(true);
      expect(Number.isFinite(particles.posY[0])).toBe(true);
      expect(Number.isFinite(particles.posZ[0])).toBe(true);
    });
    
    it("clamps velocity to maxSpeed", () => {
      const particles = new ParticleBuffer(10);
      particles.spawn(0, 0, 0, 1000, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0);
      
      const accX = new Float32Array(10);
      const accY = new Float32Array(10);
      const accZ = new Float32Array(10);
      
      const maxSpeed = 10;
      integrateVerlet(particles, accX, accY, accZ, pos(1/60), pos(maxSpeed));
      
      const speed = Math.sqrt(
        particles.velX[0]**2 + particles.velY[0]**2 + particles.velZ[0]**2
      );
      
      expect(speed).toBeLessThanOrEqual(maxSpeed * 1.01); // Allow small tolerance
    });
  });
});
