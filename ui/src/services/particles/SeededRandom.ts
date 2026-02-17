/**
 * Seeded Random Number Generator
 *
 * Uses mulberry32 algorithm for deterministic, reproducible randomness.
 * This is CRITICAL for particle system determinism - same seed always
 * produces the same sequence of numbers.
 *
 * DETERMINISM NOTICE:
 * ===================
 * This class is used throughout the particle system to ensure that
 * the same seed + config + frame produces identical results.
 * Math.random() is NEVER used directly in particle simulation.
 */

export class SeededRandom {
  private state: number;
  private initialSeed: number;

  constructor(seed: number = 12345) {
    this.initialSeed = seed;
    this.state = seed;
  }

  /** Reset to initial seed */
  reset(): void {
    this.state = this.initialSeed;
  }

  /** Reset to a new seed */
  setSeed(seed: number): void {
    this.initialSeed = seed;
    this.state = seed;
  }

  /** Get current state for checkpointing */
  getState(): number {
    return this.state;
  }

  /** Restore state from checkpoint */
  setState(state: number): void {
    this.state = state;
  }

  /** Get initial seed */
  getSeed(): number {
    return this.initialSeed;
  }

  /**
   * Get next random number in [0, 1)
   * Uses mulberry32 algorithm
   */
  next(): number {
    let t = (this.state += 0x6d2b79f5);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  /** Get random in range [min, max] */
  range(min: number, max: number): number {
    return min + this.next() * (max - min);
  }

  /** Get random integer in range [min, max] inclusive */
  int(min: number, max: number): number {
    return Math.floor(this.range(min, max + 1));
  }

  /** Get random value with variance: base + random(-variance, +variance) */
  variance(base: number, variance: number): number {
    return base + (this.next() - 0.5) * 2 * variance;
  }

  /** Get random boolean with given probability of true */
  bool(probability: number = 0.5): boolean {
    return this.next() < probability;
  }

  /** Get random angle in radians [0, 2*PI) */
  angle(): number {
    return this.next() * Math.PI * 2;
  }

  /** Get random point in unit circle */
  inCircle(): { x: number; y: number } {
    const angle = this.angle();
    const r = Math.sqrt(this.next());
    return { x: r * Math.cos(angle), y: r * Math.sin(angle) };
  }

  /** Get random point on unit sphere */
  onSphere(): { x: number; y: number; z: number } {
    const theta = this.angle();
    const phi = Math.acos(2 * this.next() - 1);
    return {
      x: Math.sin(phi) * Math.cos(theta),
      y: Math.sin(phi) * Math.sin(theta),
      z: Math.cos(phi),
    };
  }

  /**
   * Get random number from Gaussian/normal distribution
   * Uses Box-Muller transform for deterministic gaussian sampling
   */
  gaussian(mean: number = 0, stdDev: number = 1): number {
    const u1 = this.next();
    const u2 = this.next();
    // Box-Muller transform
    const z = Math.sqrt(-2 * Math.log(u1 || 1e-10)) * Math.cos(2 * Math.PI * u2);
    return mean + z * stdDev;
  }
}
