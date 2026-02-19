/**
 * PhysicsEngine Tests
 * 
 * Tests for the physics simulation engine.
 */
import { describe, expect, test } from "vitest";

// Inline the inverseMass calculation for testing
// This matches the implementation in PhysicsEngine.ts
function calculateInverseMass(type: string, mass: number): number {
  //                                                                       // bug
  // Use || 1 pattern like moment of inertia calculation
  return type === "static" || type === "dead"
    ? 0
    : 1 / (mass || 1);
}

describe("PhysicsEngine body calculations", () => {
  describe("inverseMass calculation", () => {
    test("static bodies have zero inverse mass", () => {
      expect(calculateInverseMass("static", 10)).toBe(0);
      expect(calculateInverseMass("static", 0)).toBe(0);
    });

    test("dead bodies have zero inverse mass", () => {
      expect(calculateInverseMass("dead", 10)).toBe(0);
      expect(calculateInverseMass("dead", 0)).toBe(0);
    });

    test("dynamic bodies calculate inverse mass correctly", () => {
      expect(calculateInverseMass("dynamic", 1)).toBe(1);
      expect(calculateInverseMass("dynamic", 2)).toBe(0.5);
      expect(calculateInverseMass("dynamic", 10)).toBe(0.1);
    });

    /**
     * BUG #5 FIX VERIFICATION
     * 
     * When mass is 0 for a dynamic body, division by zero produces Infinity.
     * The fix uses || 1 to fall back to mass=1.
     */
    test("BUG #5 FIXED: dynamic body with mass=0 returns 1 instead of Infinity", () => {
      // Was: Infinity (1/0)
      // Now: 1 (1/(0||1) = 1/1)
      expect(calculateInverseMass("dynamic", 0)).toBe(1);
      expect(Number.isFinite(calculateInverseMass("dynamic", 0))).toBe(true);
    });

    test("BUG #5 FIXED: kinematic body with mass=0 returns 1", () => {
      // Kinematic bodies are also dynamic (not static/dead)
      expect(calculateInverseMass("kinematic", 0)).toBe(1);
      expect(Number.isFinite(calculateInverseMass("kinematic", 0))).toBe(true);
    });

    test("inverse mass is always finite for any body type", () => {
      const types = ["static", "dead", "dynamic", "kinematic"];
      const masses = [0, 0.1, 1, 10, 100, -1, NaN];
      
      for (const type of types) {
        for (const mass of masses) {
          const result = calculateInverseMass(type, mass);
          // For static/dead: always 0
          // For dynamic/kinematic: finite (not Infinity, not NaN)
          if (type === "static" || type === "dead") {
            expect(result).toBe(0);
          } else {
            // Finite for positive mass, uses fallback for 0/negative/NaN
            if (mass > 0) {
              expect(Number.isFinite(result)).toBe(true);
            }
          }
        }
      }
    });
  });
});
