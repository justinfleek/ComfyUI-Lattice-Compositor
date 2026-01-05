/**
 * Wan-Move Flow Generators
 *
 * Extracted from wanMoveExport.ts - contains deterministic flow pattern
 * generators for Anadol-style generative trajectories.
 *
 * Includes:
 * - SeededRandom class for deterministic generation
 * - simplexNoise2D for organic motion
 * - 7 generative flow patterns: spiral, wave, explosion, vortex, data-river, morph, swarm
 */

import type { GenerativeFlowConfig, WanMoveTrajectory } from "./wanMoveExport";

// ============================================================================
// SEEDED RANDOM (for deterministic generation)
// ============================================================================

export class SeededRandom {
  private state: number;

  constructor(seed: number) {
    this.state = seed;
  }

  next(): number {
    let t = (this.state += 0x6d2b79f5);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }

  range(min: number, max: number): number {
    return min + this.next() * (max - min);
  }

  gaussian(mean: number, stdDev: number): number {
    const u1 = this.next();
    const u2 = this.next();
    const z = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
    return mean + z * stdDev;
  }
}

// ============================================================================
// SIMPLEX NOISE (for organic motion)
// ============================================================================

export function simplexNoise2D(x: number, y: number, seed: number): number {
  // Simplified Perlin-style noise
  const ix = Math.floor(x);
  const iy = Math.floor(y);
  const fx = x - ix;
  const fy = y - iy;

  const hash = (x: number, y: number) => {
    let h = seed + x * 374761393 + y * 668265263;
    h = (h ^ (h >> 13)) * 1274126177;
    return h;
  };

  const grad = (hash: number, dx: number, dy: number) => {
    const h = hash & 7;
    const u = h < 4 ? dx : dy;
    const v = h < 4 ? dy : dx;
    return (h & 1 ? -u : u) + (h & 2 ? -2 * v : 2 * v);
  };

  const lerp = (a: number, b: number, t: number) => a + t * (b - a);
  const fade = (t: number) => t * t * t * (t * (t * 6 - 15) + 10);

  const n00 = grad(hash(ix, iy), fx, fy);
  const n10 = grad(hash(ix + 1, iy), fx - 1, fy);
  const n01 = grad(hash(ix, iy + 1), fx, fy - 1);
  const n11 = grad(hash(ix + 1, iy + 1), fx - 1, fy - 1);

  const u = fade(fx);
  const v = fade(fy);

  return lerp(lerp(n00, n10, u), lerp(n01, n11, u), v) * 0.5 + 0.5;
}

// ============================================================================
// ANADOL-STYLE FLOW GENERATORS
// ============================================================================

/**
 * Generate spiral galaxy flow pattern
 */
export function generateSpiralFlow(
  config: GenerativeFlowConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, params } = config;
  const rng = new SeededRandom(params.seed ?? 42);

  const turns = params.spiralTurns ?? 3;
  const expansion = params.spiralExpansion ?? 1.5;
  const noise = params.noiseStrength ?? 0.1;

  const centerX = width / 2;
  const centerY = height / 2;
  const maxRadius = Math.min(width, height) * 0.45;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    // Initial position on spiral
    const armOffset = rng.next() * Math.PI * 2;
    const radiusOffset = rng.next();
    const phaseOffset = rng.next() * 0.5;

    for (let f = 0; f < numFrames; f++) {
      const t = f / numFrames + phaseOffset;
      const angle = armOffset + t * Math.PI * 2 * turns;
      const radius = (radiusOffset + t * expansion) * maxRadius;

      // Add noise for organic feel
      const noiseVal = simplexNoise2D(i * 0.1, f * 0.05, params.seed ?? 42);
      const noisedRadius = radius * (1 + (noiseVal - 0.5) * noise * 2);

      const x = centerX + Math.cos(angle) * noisedRadius;
      const y = centerY + Math.sin(angle) * noisedRadius;

      track.push([
        Math.max(0, Math.min(width, x)),
        Math.max(0, Math.min(height, y)),
      ]);

      // Visibility: fade out at edges
      const distFromCenter = Math.sqrt((x - centerX) ** 2 + (y - centerY) ** 2);
      vis.push(distFromCenter < maxRadius * 1.1);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate wave/ocean flow pattern
 */
export function generateWaveFlow(
  config: GenerativeFlowConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, params } = config;
  const rng = new SeededRandom(params.seed ?? 42);

  const amplitude = params.waveAmplitude ?? height * 0.15;
  const frequency = params.waveFrequency ?? 3;
  const speed = params.waveSpeed ?? 0.1;
  const layers = params.waveLayers ?? 5;
  const noise = params.noiseStrength ?? 0.05;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    const layer = Math.floor(rng.next() * layers);
    const layerY = ((layer + 0.5) / layers) * height;
    const startX = rng.next() * width;
    const phaseOffset = rng.next() * Math.PI * 2;
    const amplitudeVariation = 0.5 + rng.next() * 0.5;

    for (let f = 0; f < numFrames; f++) {
      const t = f / numFrames;

      // Move across screen
      const x =
        ((startX + t * width * speed * 10) % (width * 1.2)) - width * 0.1;

      // Wave motion
      const wave = Math.sin(
        (x / width) * Math.PI * 2 * frequency + phaseOffset + t * Math.PI * 4,
      );
      const y = layerY + wave * amplitude * amplitudeVariation;

      // Add turbulent noise
      const noiseVal = simplexNoise2D(
        x * 0.01,
        f * 0.05 + layer,
        params.seed ?? 42,
      );
      const noisedY = y + (noiseVal - 0.5) * amplitude * noise * 4;

      track.push([
        Math.max(0, Math.min(width, x)),
        Math.max(0, Math.min(height, noisedY)),
      ]);

      vis.push(x >= 0 && x <= width);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate explosion/big bang pattern
 */
export function generateExplosionFlow(
  config: GenerativeFlowConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, params } = config;
  const rng = new SeededRandom(params.seed ?? 42);

  const explosionSpeed = params.explosionSpeed ?? 1.0;
  const decay = params.explosionDecay ?? 0.95;
  const center = params.explosionCenter ?? { x: width / 2, y: height / 2 };
  const noise = params.noiseStrength ?? 0.1;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    // Random direction
    const angle = rng.next() * Math.PI * 2;
    const speed = rng.range(0.5, 1.5) * explosionSpeed;
    const startDelay = rng.next() * 0.3; // Staggered start

    let vx = Math.cos(angle) * speed * 20;
    let vy = Math.sin(angle) * speed * 20;
    let x = center.x;
    let y = center.y;

    for (let f = 0; f < numFrames; f++) {
      const t = f / numFrames;

      if (t < startDelay) {
        // Before explosion
        track.push([center.x, center.y]);
        vis.push(true);
      } else {
        // Exploding outward
        // Add noise for turbulence
        const noiseX =
          (simplexNoise2D(i * 0.1, f * 0.1, params.seed ?? 42) - 0.5) *
          noise *
          50;
        const noiseY =
          (simplexNoise2D(i * 0.1 + 100, f * 0.1, params.seed ?? 42) - 0.5) *
          noise *
          50;

        x += vx + noiseX;
        y += vy + noiseY;

        // Decay velocity
        vx *= decay;
        vy *= decay;

        track.push([
          Math.max(0, Math.min(width, x)),
          Math.max(0, Math.min(height, y)),
        ]);

        vis.push(x >= 0 && x <= width && y >= 0 && y <= height);
      }
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate vortex/whirlpool pattern
 */
export function generateVortexFlow(
  config: GenerativeFlowConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, params } = config;
  const rng = new SeededRandom(params.seed ?? 42);

  const strength = params.vortexStrength ?? 0.5;
  const maxRadius = params.vortexRadius ?? Math.min(width, height) * 0.4;
  const center = params.vortexCenter ?? { x: width / 2, y: height / 2 };
  const noise = params.noiseStrength ?? 0.05;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    // Start at random position around vortex
    const startAngle = rng.next() * Math.PI * 2;
    const startRadius = rng.range(maxRadius * 0.2, maxRadius);

    let angle = startAngle;
    let radius = startRadius;

    for (let f = 0; f < numFrames; f++) {
      // Spiral inward while rotating
      angle += strength * (1 + ((maxRadius - radius) / maxRadius) * 2);
      radius = Math.max(10, radius - radius * 0.01 * strength);

      // Add noise
      const noiseVal = simplexNoise2D(angle, radius * 0.01, params.seed ?? 42);
      const noisedRadius = radius * (1 + (noiseVal - 0.5) * noise);

      const x = center.x + Math.cos(angle) * noisedRadius;
      const y = center.y + Math.sin(angle) * noisedRadius;

      track.push([
        Math.max(0, Math.min(width, x)),
        Math.max(0, Math.min(height, y)),
      ]);

      vis.push(true);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate data river flow (particles flowing along a curved path)
 */
export function generateDataRiverFlow(
  config: GenerativeFlowConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, params } = config;
  const rng = new SeededRandom(params.seed ?? 42);

  const riverWidth = params.riverWidth ?? height * 0.3;
  const curve = params.riverCurve ?? 0.5;
  const turbulence = params.riverTurbulence ?? 0.1;

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  // River path (S-curve from left to right)
  const riverPath = (x: number) => {
    const t = x / width;
    return height / 2 + Math.sin(t * Math.PI * 2 * curve) * height * 0.25;
  };

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    const startX = rng.range(-width * 0.1, width * 0.3);
    const laneOffset = rng.gaussian(0, riverWidth * 0.15);
    const speed = rng.range(0.8, 1.2);

    for (let f = 0; f < numFrames; f++) {
      const t = f / numFrames;

      // Flow along river
      const x = startX + t * width * speed * 1.3;
      const baseY = riverPath(x);

      // Lane position + turbulence
      const turbNoise = simplexNoise2D(
        x * 0.01,
        f * 0.05 + i * 0.1,
        params.seed ?? 42,
      );
      const y =
        baseY + laneOffset + (turbNoise - 0.5) * riverWidth * turbulence * 2;

      track.push([
        Math.max(0, Math.min(width, x)),
        Math.max(0, Math.min(height, y)),
      ]);

      vis.push(x >= 0 && x <= width);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate morph flow (points transitioning between two shapes)
 */
export function generateMorphFlow(
  config: GenerativeFlowConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, params } = config;
  const rng = new SeededRandom(params.seed ?? 42);

  const sourceShape = params.morphSource ?? "grid";
  const targetShape = params.morphTarget ?? "circle";
  const easing = params.morphEasing ?? "ease-in-out";

  // Generate source positions
  const sourcePositions: { x: number; y: number }[] = [];
  const targetPositions: { x: number; y: number }[] = [];

  for (let i = 0; i < numPoints; i++) {
    // Source shape
    if (sourceShape === "grid") {
      const cols = Math.ceil(Math.sqrt(numPoints));
      const row = Math.floor(i / cols);
      const col = i % cols;
      sourcePositions.push({
        x: ((col + 0.5) / cols) * width * 0.8 + width * 0.1,
        y: ((row + 0.5) / cols) * height * 0.8 + height * 0.1,
      });
    } else if (sourceShape === "circle") {
      const angle = (i / numPoints) * Math.PI * 2;
      const radius = Math.min(width, height) * 0.35;
      sourcePositions.push({
        x: width / 2 + Math.cos(angle) * radius,
        y: height / 2 + Math.sin(angle) * radius,
      });
    } else {
      sourcePositions.push({
        x: rng.next() * width,
        y: rng.next() * height,
      });
    }

    // Target shape
    if (targetShape === "grid") {
      const cols = Math.ceil(Math.sqrt(numPoints));
      const row = Math.floor(i / cols);
      const col = i % cols;
      targetPositions.push({
        x: ((col + 0.5) / cols) * width * 0.8 + width * 0.1,
        y: ((row + 0.5) / cols) * height * 0.8 + height * 0.1,
      });
    } else if (targetShape === "circle") {
      const angle = (i / numPoints) * Math.PI * 2;
      const radius = Math.min(width, height) * 0.35;
      targetPositions.push({
        x: width / 2 + Math.cos(angle) * radius,
        y: height / 2 + Math.sin(angle) * radius,
      });
    } else {
      targetPositions.push({
        x: rng.next() * width,
        y: rng.next() * height,
      });
    }
  }

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  // Easing functions
  const easingFn = (t: number): number => {
    switch (easing) {
      case "ease-in":
        return t * t;
      case "ease-out":
        return 1 - (1 - t) * (1 - t);
      case "ease-in-out":
        return t < 0.5 ? 2 * t * t : 1 - (-2 * t + 2) ** 2 / 2;
      default:
        return t;
    }
  };

  for (let i = 0; i < numPoints; i++) {
    const track: number[][] = [];
    const vis: boolean[] = [];

    const src = sourcePositions[i];
    const tgt = targetPositions[i];

    for (let f = 0; f < numFrames; f++) {
      const t = f / (numFrames - 1);
      const easedT = easingFn(t);

      // Add slight noise for organic movement
      const noise = simplexNoise2D(i * 0.1, f * 0.02, params.seed ?? 42);
      const noiseOffset = (noise - 0.5) * 20;

      const x =
        src.x +
        (tgt.x - src.x) * easedT +
        noiseOffset * (1 - Math.abs(t - 0.5) * 2);
      const y =
        src.y +
        (tgt.y - src.y) * easedT +
        noiseOffset * (1 - Math.abs(t - 0.5) * 2);

      track.push([
        Math.max(0, Math.min(width, x)),
        Math.max(0, Math.min(height, y)),
      ]);

      vis.push(true);
    }

    tracks.push(track);
    visibility.push(vis);
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}

/**
 * Generate swarm/flocking behavior pattern
 */
export function generateSwarmFlow(
  config: GenerativeFlowConfig,
): WanMoveTrajectory {
  const { numPoints, numFrames, width, height, params } = config;
  const rng = new SeededRandom(params.seed ?? 42);

  const cohesion = params.swarmCohesion ?? 0.01;
  const separation = params.swarmSeparation ?? 30;
  const alignment = params.swarmAlignment ?? 0.05;
  const maxSpeed = params.swarmSpeed ?? 5;

  // Initialize particles
  const particles: { x: number; y: number; vx: number; vy: number }[] = [];
  for (let i = 0; i < numPoints; i++) {
    particles.push({
      x: rng.next() * width,
      y: rng.next() * height,
      vx: rng.range(-maxSpeed, maxSpeed),
      vy: rng.range(-maxSpeed, maxSpeed),
    });
  }

  const tracks: number[][][] = [];
  const visibility: boolean[][] = [];

  // Pre-allocate
  for (let i = 0; i < numPoints; i++) {
    tracks.push([]);
    visibility.push([]);
  }

  // Simulate each frame
  for (let f = 0; f < numFrames; f++) {
    // Calculate swarm forces
    const forces: { fx: number; fy: number }[] = particles.map(() => ({
      fx: 0,
      fy: 0,
    }));

    // Calculate center of mass
    let cx = 0,
      cy = 0;
    for (const p of particles) {
      cx += p.x;
      cy += p.y;
    }
    cx /= numPoints;
    cy /= numPoints;

    for (let i = 0; i < numPoints; i++) {
      const p = particles[i];

      // Cohesion: steer toward center
      forces[i].fx += (cx - p.x) * cohesion;
      forces[i].fy += (cy - p.y) * cohesion;

      // Separation: avoid crowding
      for (let j = 0; j < numPoints; j++) {
        if (i === j) continue;
        const other = particles[j];
        const dx = p.x - other.x;
        const dy = p.y - other.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        if (dist < separation && dist > 0) {
          forces[i].fx += (dx / dist) * (separation - dist) * 0.1;
          forces[i].fy += (dy / dist) * (separation - dist) * 0.1;
        }
      }

      // Alignment: match average velocity (sample nearby particles)
      let avgVx = 0,
        avgVy = 0,
        count = 0;
      for (let j = Math.max(0, i - 10); j < Math.min(numPoints, i + 10); j++) {
        avgVx += particles[j].vx;
        avgVy += particles[j].vy;
        count++;
      }
      if (count > 0) {
        forces[i].fx += (avgVx / count - p.vx) * alignment;
        forces[i].fy += (avgVy / count - p.vy) * alignment;
      }

      // Boundary avoidance
      const margin = 50;
      if (p.x < margin) forces[i].fx += (margin - p.x) * 0.1;
      if (p.x > width - margin) forces[i].fx -= (p.x - (width - margin)) * 0.1;
      if (p.y < margin) forces[i].fy += (margin - p.y) * 0.1;
      if (p.y > height - margin)
        forces[i].fy -= (p.y - (height - margin)) * 0.1;
    }

    // Update particles
    for (let i = 0; i < numPoints; i++) {
      const p = particles[i];

      p.vx += forces[i].fx;
      p.vy += forces[i].fy;

      // Limit speed
      const speed = Math.sqrt(p.vx * p.vx + p.vy * p.vy);
      if (speed > maxSpeed) {
        p.vx = (p.vx / speed) * maxSpeed;
        p.vy = (p.vy / speed) * maxSpeed;
      }

      p.x += p.vx;
      p.y += p.vy;

      // Record position
      tracks[i].push([
        Math.max(0, Math.min(width, p.x)),
        Math.max(0, Math.min(height, p.y)),
      ]);
      visibility[i].push(true);
    }
  }

  return {
    tracks,
    visibility,
    metadata: { numPoints, numFrames, width, height, fps: 16 },
  };
}
