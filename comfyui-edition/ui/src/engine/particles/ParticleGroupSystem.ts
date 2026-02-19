/**
 * Particle Group System
 *
 * Manages particle groups for selective interactions.
 * Groups allow organizing particles so that:
 * - Particles only collide with particles in specified groups
 * - Particles only connect with particles in specified groups
 * - Different rendering options per group
 *
 * Uses bitmask operations for efficient group checking.
 */

import { MAX_PARTICLE_GROUPS, type ParticleGroupConfig } from "./types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // particle // group // system
// ════════════════════════════════════════════════════════════════════════════

export class ParticleGroupSystem {
  /** Group configurations by ID */
  private groups: Map<string, ParticleGroupConfig> = new Map();

  /** Particle to group index mapping (by particle index) */
  private particleGroups: Uint8Array;

  /** Number of particles */
  private maxParticles: number;

  constructor(maxParticles: number) {
    // Validate maxParticles
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.min(Math.floor(maxParticles), 10_000_000)
      : 10000;

    // Initialize particle group assignments (0 = default group)
    this.particleGroups = new Uint8Array(this.maxParticles);

    // Create default group
    this.addGroup({
      id: "default",
      name: "Default",
      index: 0,
      color: [1, 1, 1],
      enableCollision: true,
      collisionMask: 0xFFFFFFFF, // Collide with all groups
      enableConnections: true,
      connectionMask: 0xFFFFFFFF, // Connect with all groups
    });
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // group // management
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Add a new particle group
   */
  addGroup(config: ParticleGroupConfig): void {
    // Validate index
    const index = Math.max(0, Math.min(MAX_PARTICLE_GROUPS - 1, config.index));

    // Check for index collision
    for (const existing of this.groups.values()) {
      if (existing.id !== config.id && existing.index === index) {
        console.warn(`ParticleGroupSystem: Group index ${index} already in use by "${existing.name}"`);
        return;
      }
    }

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const collisionMask = (typeof config.collisionMask === "number" && Number.isFinite(config.collisionMask)) ? config.collisionMask : 0xFFFFFFFF;
    const connectionMask = (typeof config.connectionMask === "number" && Number.isFinite(config.connectionMask)) ? config.connectionMask : 0xFFFFFFFF;
    this.groups.set(config.id, {
      ...config,
      index,
      collisionMask,
      connectionMask,
    });
  }

  /**
   * Remove a particle group
   */
  removeGroup(groupId: string): void {
    if (groupId === "default") {
      console.warn("ParticleGroupSystem: Cannot remove default group");
      return;
    }

    const group = this.groups.get(groupId);
    if (!group) return;

    // Reassign particles in this group to default
    for (let i = 0; i < this.maxParticles; i++) {
      if (this.particleGroups[i] === group.index) {
        this.particleGroups[i] = 0; // Default group
      }
    }

    this.groups.delete(groupId);
  }

  /**
   * Get a group by ID
   */
  getGroup(groupId: string): ParticleGroupConfig | undefined {
    return this.groups.get(groupId);
  }

  /**
   * Get all groups
   */
  getAllGroups(): ParticleGroupConfig[] {
    return Array.from(this.groups.values());
  }

  /**
   * Update group configuration
   */
  updateGroup(groupId: string, config: Partial<ParticleGroupConfig>): void {
    const existing = this.groups.get(groupId);
    if (!existing) return;

    this.groups.set(groupId, { ...existing, ...config, id: groupId });
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                    // particle // assignment
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Assign a particle to a group
   */
  setParticleGroup(particleIndex: number, groupId: string): void {
    if (particleIndex < 0 || particleIndex >= this.maxParticles) return;

    const group = this.groups.get(groupId);
    if (!group) return;

    this.particleGroups[particleIndex] = group.index;
  }

  /**
   * Assign a particle to a group by index
   */
  setParticleGroupIndex(particleIndex: number, groupIndex: number): void {
    if (particleIndex < 0 || particleIndex >= this.maxParticles) return;
    if (groupIndex < 0 || groupIndex >= MAX_PARTICLE_GROUPS) return;

    this.particleGroups[particleIndex] = groupIndex;
  }

  /**
   * Get the group index for a particle
   */
  getParticleGroupIndex(particleIndex: number): number {
    if (particleIndex < 0 || particleIndex >= this.maxParticles) return 0;
    return this.particleGroups[particleIndex];
  }

  /**
   * Get the group ID for a particle
   * 
   * System F/Omega proof: Explicit validation of group existence
   * Type proof: particleIndex ∈ number → string (non-nullable)
   * Mathematical proof: Group must exist for the particle's group index
   * Pattern proof: Missing group is an explicit failure condition, not a lazy undefined return
   */
  getParticleGroupId(particleIndex: number): string {
    const groupIndex = this.getParticleGroupIndex(particleIndex);
    
    for (const group of this.groups.values()) {
      if (group.index === groupIndex) {
        return group.id;
      }
    }
    
    // System F/Omega proof: Explicit validation of group existence
    // Type proof: groups.values() returns IterableIterator<Group>
    // Mathematical proof: Group must exist for the calculated group index
    throw new Error(
      `[ParticleGroupSystem] Cannot get particle group ID: Group not found. ` +
      `Particle index: ${particleIndex}, group index: ${groupIndex}, ` +
      `groups available: ${Array.from(this.groups.values()).map(g => `index=${g.index}, id=${g.id}`).join("; ") || "none"}. ` +
      `Group must exist for the particle's group index. ` +
      `Wrap in try/catch if "group not found" is an expected state.`
    );
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // interaction // checking
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Check if two particles can collide based on their groups
   */
  canCollide(particleIndexA: number, particleIndexB: number): boolean {
    const groupIndexA = this.particleGroups[particleIndexA];
    const groupIndexB = this.particleGroups[particleIndexB];

    // Find group configs
    let groupA: ParticleGroupConfig | undefined;
    let groupB: ParticleGroupConfig | undefined;
    for (const group of this.groups.values()) {
      if (group.index === groupIndexA) groupA = group;
      if (group.index === groupIndexB) groupB = group;
    }

    // Default to allowing collision
    if (!groupA || !groupB) return true;

    // Check if both groups have collision enabled and mask allows
    if (!groupA.enableCollision || !groupB.enableCollision) return false;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const maskA = (typeof groupA.collisionMask === "number" && Number.isFinite(groupA.collisionMask)) ? groupA.collisionMask : 0xFFFFFFFF;
    const maskB = (typeof groupB.collisionMask === "number" && Number.isFinite(groupB.collisionMask)) ? groupB.collisionMask : 0xFFFFFFFF;

    // Check if A's mask includes B's index AND B's mask includes A's index
    return ((maskA & (1 << groupIndexB)) !== 0) && ((maskB & (1 << groupIndexA)) !== 0);
  }

  /**
   * Check if two particles can connect based on their groups
   */
  canConnect(particleIndexA: number, particleIndexB: number): boolean {
    const groupIndexA = this.particleGroups[particleIndexA];
    const groupIndexB = this.particleGroups[particleIndexB];

    // Find group configs
    let groupA: ParticleGroupConfig | undefined;
    let groupB: ParticleGroupConfig | undefined;
    for (const group of this.groups.values()) {
      if (group.index === groupIndexA) groupA = group;
      if (group.index === groupIndexB) groupB = group;
    }

    // Default to allowing connection
    if (!groupA || !groupB) return true;

    // Check if both groups have connections enabled and mask allows
    if (!groupA.enableConnections || !groupB.enableConnections) return false;

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const maskA = (typeof groupA.connectionMask === "number" && Number.isFinite(groupA.connectionMask)) ? groupA.connectionMask : 0xFFFFFFFF;
    const maskB = (typeof groupB.connectionMask === "number" && Number.isFinite(groupB.connectionMask)) ? groupB.connectionMask : 0xFFFFFFFF;

    // Check if A's mask includes B's index AND B's mask includes A's index
    return ((maskA & (1 << groupIndexB)) !== 0) && ((maskB & (1 << groupIndexA)) !== 0);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                        // bitmask // helpers
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Create a collision mask from an array of group IDs
   */
  createMaskFromGroupIds(groupIds: string[]): number {
    let mask = 0;
    for (const id of groupIds) {
      const group = this.groups.get(id);
      if (group) {
        mask |= (1 << group.index);
      }
    }
    return mask;
  }

  /**
   * Create a collision mask from an array of group indices
   */
  static createMaskFromIndices(indices: number[]): number {
    let mask = 0;
    for (const idx of indices) {
      if (idx >= 0 && idx < MAX_PARTICLE_GROUPS) {
        mask |= (1 << idx);
      }
    }
    return mask;
  }

  /**
   * Get group indices that are set in a mask
   */
  static getIndicesFromMask(mask: number): number[] {
    const indices: number[] = [];
    for (let i = 0; i < MAX_PARTICLE_GROUPS; i++) {
      if ((mask & (1 << i)) !== 0) {
        indices.push(i);
      }
    }
    return indices;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                             // serialization
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Serialize the group system state
   */
  serialize(): object {
    return {
      groups: Array.from(this.groups.values()),
      particleGroups: Array.from(this.particleGroups),
    };
  }

  /**
   * Deserialize group system state
   */
  static deserialize(data: { groups?: ParticleGroupConfig[]; particleGroups?: number[] }, maxParticles: number): ParticleGroupSystem {
    const system = new ParticleGroupSystem(maxParticles);

    // Clear default group to avoid duplicates
    system.groups.clear();

    // Restore groups
    if (data.groups) {
      for (const group of data.groups) {
        system.groups.set(group.id, group);
      }
    }

    // Restore particle assignments
    if (data.particleGroups) {
      const len = Math.min(data.particleGroups.length, system.particleGroups.length);
      for (let i = 0; i < len; i++) {
        system.particleGroups[i] = data.particleGroups[i];
      }
    }

    return system;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // cleanup
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Reset all particle group assignments to default
   */
  reset(): void {
    this.particleGroups.fill(0);
  }

  /**
   * Dispose resources
   */
  dispose(): void {
    this.groups.clear();
  }
}
