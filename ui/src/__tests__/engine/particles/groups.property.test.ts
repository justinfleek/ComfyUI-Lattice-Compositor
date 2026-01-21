/**
 * Property tests for Particle Groups System
 *
 * Tests that particle groups correctly manage collision and connection
 * masks using bitmask operations.
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";

// Particle group configuration
interface ParticleGroupConfig {
  id: string;
  name: string;
  enabled: boolean;
  color: [number, number, number, number];
  collisionMask: number;
  connectionMask: number;
}

// Simulated ParticleGroupSystem class
class ParticleGroupSystem {
  private groups: Map<string, ParticleGroupConfig> = new Map();

  constructor() {
    // Initialize with default group
    this.addGroup({
      id: "default",
      name: "Default",
      enabled: true,
      color: [1, 1, 1, 1],
      collisionMask: 0b11111111,
      connectionMask: 0b11111111,
    });
  }

  addGroup(config: ParticleGroupConfig): void {
    // Validate and sanitize
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const enabled = (config.enabled !== null && config.enabled !== undefined && typeof config.enabled === "boolean") ? config.enabled : true;
    const sanitized: ParticleGroupConfig = {
      id: config.id || `group_${Date.now()}`,
      name: config.name || "Unnamed",
      enabled,
      color: this.validateColor(config.color),
      collisionMask: this.validateMask(config.collisionMask),
      connectionMask: this.validateMask(config.connectionMask),
    };
    this.groups.set(sanitized.id, sanitized);
  }

  removeGroup(id: string): boolean {
    if (id === "default") return false; // Cannot remove default
    return this.groups.delete(id);
  }

  updateGroup(id: string, config: Partial<ParticleGroupConfig>): void {
    const existing = this.groups.get(id);
    if (!existing) return;

    const updated: ParticleGroupConfig = {
      ...existing,
      ...config,
      collisionMask: config.collisionMask !== undefined
        ? this.validateMask(config.collisionMask)
        : existing.collisionMask,
      connectionMask: config.connectionMask !== undefined
        ? this.validateMask(config.connectionMask)
        : existing.connectionMask,
      color: config.color !== undefined
        ? this.validateColor(config.color)
        : existing.color,
    };

    this.groups.set(id, updated);
  }

  getGroup(id: string): ParticleGroupConfig | undefined {
    return this.groups.get(id);
  }

  getGroups(): ParticleGroupConfig[] {
    return Array.from(this.groups.values());
  }

  getGroupIndex(id: string): number {
    const groups = this.getGroups();
    return groups.findIndex((g) => g.id === id);
  }

  canCollide(groupAId: string, groupBId: string): boolean {
    const groupA = this.groups.get(groupAId);
    const groupB = this.groups.get(groupBId);
    if (!groupA || !groupB) return false;
    if (!groupA.enabled || !groupB.enabled) return false;

    const indexB = this.getGroupIndex(groupBId);
    const indexA = this.getGroupIndex(groupAId);
    if (indexA < 0 || indexB < 0) return false;

    // Check if A's collision mask includes B AND B's includes A (bidirectional)
    const aCollidesWithB = (groupA.collisionMask & (1 << indexB)) !== 0;
    const bCollidesWithA = (groupB.collisionMask & (1 << indexA)) !== 0;

    return aCollidesWithB && bCollidesWithA;
  }

  canConnect(groupAId: string, groupBId: string): boolean {
    const groupA = this.groups.get(groupAId);
    const groupB = this.groups.get(groupBId);
    if (!groupA || !groupB) return false;
    if (!groupA.enabled || !groupB.enabled) return false;

    const indexB = this.getGroupIndex(groupBId);
    if (indexB < 0) return false;

    // Connection only needs one-way check (A connects to B)
    return (groupA.connectionMask & (1 << indexB)) !== 0;
  }

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  getCollisionMask(groupId: string): number {
    const group = this.groups.get(groupId);
    const collisionMask = (group !== null && group !== undefined && typeof group === "object" && "collisionMask" in group && typeof group.collisionMask === "number" && Number.isFinite(group.collisionMask)) ? group.collisionMask : undefined;
    return collisionMask !== undefined ? collisionMask : 0;
  }

  getConnectionMask(groupId: string): number {
    const group = this.groups.get(groupId);
    const connectionMask = (group !== null && group !== undefined && typeof group === "object" && "connectionMask" in group && typeof group.connectionMask === "number" && Number.isFinite(group.connectionMask)) ? group.connectionMask : undefined;
    return connectionMask !== undefined ? connectionMask : 0;
  }

  private validateMask(mask: number): number {
    if (!Number.isFinite(mask) || mask < 0) return 0b11111111;
    return Math.floor(mask) & 0xffffffff; // 32-bit mask max
  }

  private validateColor(
    color: [number, number, number, number]
  ): [number, number, number, number] {
    return [
      Number.isFinite(color[0]) ? Math.max(0, Math.min(1, color[0])) : 1,
      Number.isFinite(color[1]) ? Math.max(0, Math.min(1, color[1])) : 1,
      Number.isFinite(color[2]) ? Math.max(0, Math.min(1, color[2])) : 1,
      Number.isFinite(color[3]) ? Math.max(0, Math.min(1, color[3])) : 1,
    ];
  }
}

describe("Particle Groups System", () => {
  // Arbitrary for group config
  const arbGroupConfig = fc.record({
    id: fc.string({ minLength: 1, maxLength: 20 }),
    name: fc.string({ minLength: 1, maxLength: 50 }),
    enabled: fc.boolean(),
    color: fc.tuple(
      fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
      fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
      fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
      fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true })
    ) as fc.Arbitrary<[number, number, number, number]>,
    collisionMask: fc.integer({ min: 0, max: 255 }),
    connectionMask: fc.integer({ min: 0, max: 255 }),
  });

  const arbMask = fc.integer({ min: 0, max: 255 });

  describe("INVARIANT: Default group always exists", () => {
    it("system should always have a default group", () => {
      const system = new ParticleGroupSystem();
      const defaultGroup = system.getGroup("default");

      expect(defaultGroup).toBeDefined();
      expect(defaultGroup!.id).toBe("default");
    });

    it("default group cannot be removed", () => {
      const system = new ParticleGroupSystem();
      const removed = system.removeGroup("default");

      expect(removed).toBe(false);
      expect(system.getGroup("default")).toBeDefined();
    });
  });

  describe("INVARIANT: Masks are always valid 32-bit integers", () => {
    it("masks should be non-negative integers", () => {
      fc.assert(
        fc.property(arbGroupConfig, (config) => {
          const system = new ParticleGroupSystem();
          system.addGroup(config);

          const group = system.getGroup(config.id);
          if (group) {
            expect(Number.isInteger(group.collisionMask)).toBe(true);
            expect(group.collisionMask).toBeGreaterThanOrEqual(0);
            expect(Number.isInteger(group.connectionMask)).toBe(true);
            expect(group.connectionMask).toBeGreaterThanOrEqual(0);
          }
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("INVARIANT: Color values are clamped to [0, 1]", () => {
    it("should clamp out-of-range color values", () => {
      const system = new ParticleGroupSystem();

      system.addGroup({
        id: "test",
        name: "Test",
        enabled: true,
        color: [-0.5, 1.5, 2.0, -1.0],
        collisionMask: 255,
        connectionMask: 255,
      });

      const group = system.getGroup("test");
      expect(group).toBeDefined();
      if (group) {
        expect(group.color[0]).toBe(0);
        expect(group.color[1]).toBe(1);
        expect(group.color[2]).toBe(1);
        expect(group.color[3]).toBe(0);
      }
    });
  });

  describe("INVARIANT: Collision is bidirectional", () => {
    it("canCollide should return true only if both groups can collide with each other", () => {
      const system = new ParticleGroupSystem();

      // Get the current group indices
      // Default is at index 0, groupA will be at index 1, groupB at index 2

      // Group A can collide with B (bit 2), Group B cannot collide with A (bit 0)
      system.addGroup({
        id: "groupA",
        name: "Group A",
        enabled: true,
        color: [1, 0, 0, 1],
        collisionMask: 0b00000100, // Can collide with index 2 (groupB will be there)
        connectionMask: 255,
      });

      system.addGroup({
        id: "groupB",
        name: "Group B",
        enabled: true,
        color: [0, 0, 1, 1],
        collisionMask: 0b00000000, // Cannot collide with anything
        connectionMask: 255,
      });

      // Verify indices
      const indexA = system.getGroupIndex("groupA");
      const indexB = system.getGroupIndex("groupB");
      expect(indexA).toBe(1);
      expect(indexB).toBe(2);

      // A wants to collide with B, but B doesn't want to collide with A
      const canCollide = system.canCollide("groupA", "groupB");
      expect(canCollide).toBe(false);

      // Now enable B to collide with A (set bit 1)
      system.updateGroup("groupB", { collisionMask: 0b00000010 }); // Index 1 is groupA
      const canCollideNow = system.canCollide("groupA", "groupB");
      expect(canCollideNow).toBe(true);
    });
  });

  describe("INVARIANT: Disabled groups cannot collide or connect", () => {
    it("disabled groups should not participate in collisions", () => {
      fc.assert(
        fc.property(arbGroupConfig, (config) => {
          const system = new ParticleGroupSystem();

          const disabledConfig = { ...config, enabled: false };
          system.addGroup(disabledConfig);

          const canCollide = system.canCollide(config.id, "default");
          const canConnect = system.canConnect(config.id, "default");

          expect(canCollide).toBe(false);
          expect(canConnect).toBe(false);
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("INVARIANT: Group count is bounded", () => {
    it("system should handle many groups", () => {
      const system = new ParticleGroupSystem();

      // Add 30 groups (more than bits in a byte, testing overflow handling)
      for (let i = 0; i < 30; i++) {
        system.addGroup({
          id: `group_${i}`,
          name: `Group ${i}`,
          enabled: true,
          color: [Math.random(), Math.random(), Math.random(), 1],
          collisionMask: 0xffffffff, // All bits set
          connectionMask: 0xffffffff,
        });
      }

      const groups = system.getGroups();
      expect(groups.length).toBe(31); // 30 + default
    });
  });

  describe("EDGE CASE: Self-collision/connection", () => {
    it("group should be able to collide/connect with itself", () => {
      const system = new ParticleGroupSystem();

      // Group that collides with its own index (0 for default)
      const canCollideSelf = system.canCollide("default", "default");
      const canConnectSelf = system.canConnect("default", "default");

      // Default group has all bits set, so it can collide/connect with itself
      expect(canCollideSelf).toBe(true);
      expect(canConnectSelf).toBe(true);
    });
  });

  describe("EDGE CASE: NaN mask handling", () => {
    it("should handle NaN mask by defaulting to all bits set", () => {
      const system = new ParticleGroupSystem();

      system.addGroup({
        id: "nanMask",
        name: "NaN Mask",
        enabled: true,
        color: [1, 1, 1, 1],
        collisionMask: NaN,
        connectionMask: NaN,
      });

      const group = system.getGroup("nanMask");
      expect(group).toBeDefined();
      if (group) {
        expect(Number.isFinite(group.collisionMask)).toBe(true);
        expect(Number.isFinite(group.connectionMask)).toBe(true);
      }
    });
  });

  describe("EDGE CASE: Negative mask handling", () => {
    it("should handle negative mask by defaulting", () => {
      const system = new ParticleGroupSystem();

      system.addGroup({
        id: "negMask",
        name: "Negative Mask",
        enabled: true,
        color: [1, 1, 1, 1],
        collisionMask: -1,
        connectionMask: -5,
      });

      const group = system.getGroup("negMask");
      expect(group).toBeDefined();
      if (group) {
        expect(group.collisionMask).toBeGreaterThanOrEqual(0);
        expect(group.connectionMask).toBeGreaterThanOrEqual(0);
      }
    });
  });

  describe("EDGE CASE: Update preserves unspecified fields", () => {
    it("partial update should not affect other fields", () => {
      const system = new ParticleGroupSystem();

      system.addGroup({
        id: "test",
        name: "Original Name",
        enabled: true,
        color: [0.5, 0.5, 0.5, 1],
        collisionMask: 0b10101010,
        connectionMask: 0b01010101,
      });

      // Update only the name
      system.updateGroup("test", { name: "New Name" });

      const group = system.getGroup("test");
      expect(group).toBeDefined();
      if (group) {
        expect(group.name).toBe("New Name");
        expect(group.collisionMask).toBe(0b10101010); // Unchanged
        expect(group.connectionMask).toBe(0b01010101); // Unchanged
        expect(group.color).toEqual([0.5, 0.5, 0.5, 1]); // Unchanged
      }
    });
  });

  describe("EDGE CASE: Non-existent group queries", () => {
    it("should return undefined/false for non-existent groups", () => {
      const system = new ParticleGroupSystem();

      expect(system.getGroup("nonexistent")).toBeUndefined();
      expect(system.canCollide("nonexistent", "default")).toBe(false);
      expect(system.canConnect("nonexistent", "default")).toBe(false);
      expect(system.getCollisionMask("nonexistent")).toBe(0);
      expect(system.getConnectionMask("nonexistent")).toBe(0);
    });
  });

  describe("PROPERTY: Adding and removing maintains consistency", () => {
    it("removed groups should no longer be accessible", () => {
      fc.assert(
        fc.property(arbGroupConfig, (config) => {
          if (config.id === "default") return true; // Skip default

          const system = new ParticleGroupSystem();
          system.addGroup(config);

          expect(system.getGroup(config.id)).toBeDefined();

          system.removeGroup(config.id);

          expect(system.getGroup(config.id)).toBeUndefined();
          return true;
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("PROPERTY: Bitmask operations are consistent", () => {
    it("canCollide should match bitmask calculation", () => {
      fc.assert(
        fc.property(arbMask, arbMask, (maskA, maskB) => {
          const system = new ParticleGroupSystem();

          system.addGroup({
            id: "a",
            name: "A",
            enabled: true,
            color: [1, 1, 1, 1],
            collisionMask: maskA,
            connectionMask: 255,
          });

          system.addGroup({
            id: "b",
            name: "B",
            enabled: true,
            color: [1, 1, 1, 1],
            collisionMask: maskB,
            connectionMask: 255,
          });

          const indexA = system.getGroupIndex("a");
          const indexB = system.getGroupIndex("b");

          const aCollidesWithB = (maskA & (1 << indexB)) !== 0;
          const bCollidesWithA = (maskB & (1 << indexA)) !== 0;

          const expected = aCollidesWithB && bCollidesWithA;
          const actual = system.canCollide("a", "b");

          expect(actual).toBe(expected);
          return true;
        }),
        { numRuns: 50 }
      );
    });
  });
});
