/**
 * Particle System Engine
 *
 * Comprehensive particle simulation matching RyanOnTheInside's implementation.
 * Supports emitters, gravity wells, vortices, modulations, and audio reactivity.
 * Extended with turbulence fields, particle connections, sub-emitters, and burst on beat.
 */
import { EASING_PRESETS, applyEasing } from './interpolation';
import { createNoise2D } from 'simplex-noise';

// ============================================================================
// Types
// ============================================================================

export interface Particle {
  id: number;
  x: number;
  y: number;
  prevX: number;
  prevY: number;
  vx: number;
  vy: number;
  age: number;
  lifetime: number;
  size: number;
  baseSize: number;
  color: [number, number, number, number];
  baseColor: [number, number, number, number];
  emitterId: string;
  isSubParticle: boolean;
}

export interface TurbulenceConfig {
  id: string;
  enabled: boolean;
  scale: number;              // Noise frequency, 0.001-0.01 (smaller = larger swirls)
  strength: number;           // Force magnitude, 0-500
  evolutionSpeed: number;     // How fast noise changes over time, 0-1
}

export interface ConnectionConfig {
  enabled: boolean;
  maxDistance: number;        // Pixels, connect if closer than this
  maxConnections: number;     // Per particle, 1-5 (HARD LIMIT for performance)
  lineWidth: number;          // 0.5-3
  lineOpacity: number;        // 0-1
  fadeByDistance: boolean;    // Opacity decreases with distance
}

export interface SubEmitterConfig {
  id: string;
  parentEmitterId: string;    // Which emitter's particles trigger this, or '*' for all
  trigger: 'death';           // Only death trigger for now
  spawnCount: number;         // 1-10 particles on trigger
  inheritVelocity: number;    // 0-1, how much parent velocity inherited
  size: number;
  sizeVariance: number;
  lifetime: number;           // Frames
  speed: number;
  spread: number;             // Degrees, emission cone
  color: [number, number, number];
  enabled: boolean;
}

interface SpatialGrid {
  cellSize: number;
  cells: Map<string, Particle[]>;
}

export interface EmitterConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  direction: number;
  spread: number;
  speed: number;
  speedVariance: number;
  size: number;
  sizeVariance: number;
  color: [number, number, number];
  emissionRate: number;
  initialBurst: number;
  particleLifetime: number;
  lifetimeVariance: number;
  enabled: boolean;
  burstOnBeat: boolean;
  burstCount: number;
}

export interface GravityWellConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  strength: number;
  radius: number;
  falloff: 'linear' | 'quadratic' | 'constant';
  enabled: boolean;
}

export interface VortexConfig {
  id: string;
  name: string;
  x: number;
  y: number;
  strength: number;
  radius: number;
  rotationSpeed: number;
  inwardPull: number;
  enabled: boolean;
}

export interface ParticleModulation {
  id: string;
  emitterId: string;
  property: 'size' | 'speed' | 'opacity' | 'colorR' | 'colorG' | 'colorB';
  startValue: number;
  endValue: number;
  easing: string;
}

export interface ParticleSystemConfig {
  maxParticles: number;
  gravity: number;
  windStrength: number;
  windDirection: number;
  warmupPeriod: number;
  respectMaskBoundary: boolean;
  boundaryBehavior: 'bounce' | 'kill' | 'wrap';
  friction: number;
  turbulenceFields: TurbulenceConfig[];
  subEmitters: SubEmitterConfig[];
}

export interface RenderOptions {
  blendMode: 'normal' | 'additive' | 'multiply' | 'screen';
  renderTrails: boolean;
  trailLength: number;
  trailOpacityFalloff: number;
  particleShape: 'circle' | 'square' | 'triangle' | 'star';
  glowEnabled: boolean;
  glowRadius: number;
  glowIntensity: number;
  // Motion blur settings
  motionBlur: boolean;
  motionBlurStrength: number;   // 0-1, how much to stretch based on velocity
  motionBlurSamples: number;    // Number of samples for blur (1-16)
  // Particle connection settings
  connections: ConnectionConfig;
}

// ============================================================================
// Default Configurations
// ============================================================================

export function createDefaultEmitterConfig(id?: string): EmitterConfig {
  return {
    id: id || `emitter_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    name: 'Emitter',
    x: 0.5,
    y: 0.5,
    direction: 270,
    spread: 30,
    speed: 330,
    speedVariance: 50,
    size: 17,
    sizeVariance: 5,
    color: [255, 255, 255],
    emissionRate: 10,
    initialBurst: 0,
    particleLifetime: 60,
    lifetimeVariance: 10,
    enabled: true,
    burstOnBeat: false,
    burstCount: 20
  };
}

export function createDefaultTurbulenceConfig(id?: string): TurbulenceConfig {
  return {
    id: id || `turb_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    enabled: true,
    scale: 0.005,
    strength: 100,
    evolutionSpeed: 0.3
  };
}

export function createDefaultConnectionConfig(): ConnectionConfig {
  return {
    enabled: false,
    maxDistance: 100,
    maxConnections: 3,
    lineWidth: 1,
    lineOpacity: 0.5,
    fadeByDistance: true
  };
}

export function createDefaultSubEmitterConfig(id?: string): SubEmitterConfig {
  return {
    id: id || `sub_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    parentEmitterId: '*',
    trigger: 'death',
    spawnCount: 3,
    inheritVelocity: 0.3,
    size: 8,
    sizeVariance: 2,
    lifetime: 30,
    speed: 0.1,
    spread: 180,
    color: [255, 200, 100],
    enabled: true
  };
}

export function createDefaultGravityWellConfig(id?: string): GravityWellConfig {
  return {
    id: id || `well_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    name: 'Gravity Well',
    x: 0.5,
    y: 0.5,
    strength: 100,
    radius: 0.3,
    falloff: 'quadratic',
    enabled: true
  };
}

export function createDefaultVortexConfig(id?: string): VortexConfig {
  return {
    id: id || `vortex_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    name: 'Vortex',
    x: 0.5,
    y: 0.5,
    strength: 200,
    radius: 0.3,
    rotationSpeed: 5,
    inwardPull: 10,
    enabled: true
  };
}

export function createDefaultSystemConfig(): ParticleSystemConfig {
  return {
    maxParticles: 10000,
    gravity: 0,
    windStrength: 0,
    windDirection: 0,
    warmupPeriod: 0,
    respectMaskBoundary: false,
    boundaryBehavior: 'kill',
    friction: 0.01,
    turbulenceFields: [],
    subEmitters: []
  };
}

export function createDefaultRenderOptions(): RenderOptions {
  return {
    blendMode: 'additive',
    renderTrails: false,
    trailLength: 5,
    trailOpacityFalloff: 0.7,
    particleShape: 'circle',
    glowEnabled: false,
    glowRadius: 10,
    glowIntensity: 0.5,
    motionBlur: false,
    motionBlurStrength: 0.5,
    motionBlurSamples: 8,
    connections: createDefaultConnectionConfig()
  };
}

// ============================================================================
// Particle System Class
// ============================================================================

export class ParticleSystem {
  private particles: Particle[] = [];
  private emitters: Map<string, EmitterConfig> = new Map();
  private gravityWells: Map<string, GravityWellConfig> = new Map();
  private vortices: Map<string, VortexConfig> = new Map();
  private modulations: ParticleModulation[] = [];
  private config: ParticleSystemConfig;
  private boundaryMask: ImageData | null = null;
  private frameCount: number = 0;
  private emissionAccumulators: Map<string, number> = new Map();
  private nextParticleId: number = 0;
  private trailHistory: Map<number, Array<{x: number; y: number}>> = new Map();

  // Audio reactivity state
  private featureOverrides: Map<string, number> = new Map();

  // Turbulence noise generator
  private noise2D: ReturnType<typeof createNoise2D>;
  private noiseTime: number = 0;

  // Render options cache for spatial grid
  private renderOptions: RenderOptions = createDefaultRenderOptions();

  constructor(config: Partial<ParticleSystemConfig> = {}) {
    this.config = { ...createDefaultSystemConfig(), ...config };
    this.noise2D = createNoise2D();
  }

  // ============================================================================
  // Emitter Management
  // ============================================================================

  addEmitter(config: EmitterConfig): void {
    this.emitters.set(config.id, { ...config });
    this.emissionAccumulators.set(config.id, 0);

    // Handle initial burst
    if (config.initialBurst > 0 && config.enabled) {
      const burstCount = Math.floor(config.emissionRate * config.initialBurst * 10);
      for (let i = 0; i < burstCount; i++) {
        this.spawnParticle(config);
      }
    }
  }

  updateEmitter(id: string, updates: Partial<EmitterConfig>): void {
    const emitter = this.emitters.get(id);
    if (emitter) {
      Object.assign(emitter, updates);
    }
  }

  removeEmitter(id: string): void {
    this.emitters.delete(id);
    this.emissionAccumulators.delete(id);
  }

  getEmitter(id: string): EmitterConfig | undefined {
    return this.emitters.get(id);
  }

  getEmitters(): EmitterConfig[] {
    return Array.from(this.emitters.values());
  }

  // ============================================================================
  // Gravity Well Management
  // ============================================================================

  addGravityWell(config: GravityWellConfig): void {
    this.gravityWells.set(config.id, { ...config });
  }

  updateGravityWell(id: string, updates: Partial<GravityWellConfig>): void {
    const well = this.gravityWells.get(id);
    if (well) {
      Object.assign(well, updates);
    }
  }

  removeGravityWell(id: string): void {
    this.gravityWells.delete(id);
  }

  getGravityWells(): GravityWellConfig[] {
    return Array.from(this.gravityWells.values());
  }

  // ============================================================================
  // Vortex Management
  // ============================================================================

  addVortex(config: VortexConfig): void {
    this.vortices.set(config.id, { ...config });
  }

  updateVortex(id: string, updates: Partial<VortexConfig>): void {
    const vortex = this.vortices.get(id);
    if (vortex) {
      Object.assign(vortex, updates);
    }
  }

  removeVortex(id: string): void {
    this.vortices.delete(id);
  }

  getVortices(): VortexConfig[] {
    return Array.from(this.vortices.values());
  }

  // ============================================================================
  // Modulation Management
  // ============================================================================

  addModulation(mod: ParticleModulation): void {
    this.modulations.push({ ...mod });
  }

  removeModulation(id: string): void {
    const index = this.modulations.findIndex(m => m.id === id);
    if (index >= 0) {
      this.modulations.splice(index, 1);
    }
  }

  getModulations(): ParticleModulation[] {
    return [...this.modulations];
  }

  // ============================================================================
  // Boundary Mask
  // ============================================================================

  setBoundaryMask(mask: ImageData | null): void {
    this.boundaryMask = mask;
  }

  // ============================================================================
  // Audio Reactivity
  // ============================================================================

  setFeatureValue(param: string, value: number, emitterId?: string): void {
    const key = emitterId ? `${emitterId}:${param}` : `*:${param}`;
    this.featureOverrides.set(key, value);
  }

  private getFeatureValue(param: string, emitterId: string): number | undefined {
    // Check specific emitter first, then global
    return this.featureOverrides.get(`${emitterId}:${param}`)
        ?? this.featureOverrides.get(`*:${param}`);
  }

  // ============================================================================
  // Simulation
  // ============================================================================

  step(deltaTime: number = 1): void {
    // 1. Spawn new particles from emitters
    this.emitters.forEach((emitter, id) => {
      if (!emitter.enabled) return;

      // Get potentially audio-modified emission rate
      const baseRate = this.getFeatureValue('emissionRate', id) ?? emitter.emissionRate;
      const particlesToEmit = baseRate * deltaTime;

      // Accumulate fractional particles
      let accumulated = (this.emissionAccumulators.get(id) || 0) + particlesToEmit;

      while (accumulated >= 1 && this.particles.length < this.config.maxParticles) {
        this.spawnParticle(emitter);
        accumulated -= 1;
      }

      this.emissionAccumulators.set(id, accumulated);
    });

    // 2. Update each particle
    const windRadians = (this.config.windDirection * Math.PI) / 180;
    const windX = Math.cos(windRadians) * this.config.windStrength * 0.001;
    const windY = Math.sin(windRadians) * this.config.windStrength * 0.001;

    // Get potentially audio-modified global values
    const gravity = this.getFeatureValue('gravity', '*') ?? this.config.gravity;
    const windStrength = this.getFeatureValue('windStrength', '*') ?? this.config.windStrength;
    const actualWindX = windX * (windStrength / Math.max(1, this.config.windStrength));
    const actualWindY = windY * (windStrength / Math.max(1, this.config.windStrength));

    for (let i = this.particles.length - 1; i >= 0; i--) {
      const p = this.particles[i];

      // Store previous position for trails
      p.prevX = p.x;
      p.prevY = p.y;

      // Update trail history
      if (this.trailHistory.has(p.id)) {
        const trail = this.trailHistory.get(p.id)!;
        trail.unshift({ x: p.x, y: p.y });
        if (trail.length > 20) trail.pop();
      }

      // a. Apply global gravity
      p.vy += gravity * 0.001 * deltaTime;

      // b. Apply wind
      p.vx += actualWindX * deltaTime;
      p.vy += actualWindY * deltaTime;

      // c. Apply gravity wells
      this.gravityWells.forEach(well => {
        if (!well.enabled) return;

        const dx = well.x - p.x;
        const dy = well.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < well.radius && dist > 0.001) {
          let force = well.strength * 0.0001;

          // Apply falloff
          switch (well.falloff) {
            case 'linear':
              force *= 1 - (dist / well.radius);
              break;
            case 'quadratic':
              force *= Math.pow(1 - (dist / well.radius), 2);
              break;
            case 'constant':
              // No falloff
              break;
          }

          // Normalize and apply force
          const nx = dx / dist;
          const ny = dy / dist;
          p.vx += nx * force * deltaTime;
          p.vy += ny * force * deltaTime;
        }
      });

      // d. Apply vortices
      this.vortices.forEach(vortex => {
        if (!vortex.enabled) return;

        const dx = vortex.x - p.x;
        const dy = vortex.y - p.y;
        const dist = Math.sqrt(dx * dx + dy * dy);

        if (dist < vortex.radius && dist > 0.001) {
          const influence = 1 - (dist / vortex.radius);
          const strength = vortex.strength * 0.0001 * influence;

          // Perpendicular force (tangential)
          const nx = dx / dist;
          const ny = dy / dist;
          const perpX = -ny;
          const perpY = nx;

          p.vx += perpX * strength * deltaTime;
          p.vy += perpY * strength * deltaTime;

          // Inward pull (spiral)
          const inward = vortex.inwardPull * 0.0001 * influence;
          p.vx += nx * inward * deltaTime;
          p.vy += ny * inward * deltaTime;
        }
      });

      // e. Apply turbulence fields
      this.applyTurbulence(p, deltaTime);

      // f. Apply friction
      const frictionFactor = 1 - this.config.friction;
      p.vx *= frictionFactor;
      p.vy *= frictionFactor;

      // g. Update position
      p.x += p.vx * deltaTime;
      p.y += p.vy * deltaTime;

      // g. Check boundary collision
      if (this.boundaryMask && this.config.respectMaskBoundary) {
        this.handleBoundaryCollision(p);
      }

      // Simple canvas boundary handling
      this.handleCanvasBoundary(p);

      // h. Apply modulations based on age/lifetime ratio
      this.applyModulations(p);

      // j. Increment age
      p.age += deltaTime;

      // k. Remove if age > lifetime, trigger sub-emitters on death
      if (p.age > p.lifetime) {
        // Trigger sub-emitters for non-sub particles
        if (!p.isSubParticle) {
          this.triggerSubEmitters(p);
        }
        this.particles.splice(i, 1);
        this.trailHistory.delete(p.id);
      }
    }

    // Increment noise time for turbulence evolution
    this.noiseTime += deltaTime;
    this.frameCount++;
  }

  private spawnParticle(emitter: EmitterConfig): void {
    if (this.particles.length >= this.config.maxParticles) return;

    // Calculate emission direction with spread
    const spreadRad = (emitter.spread * Math.PI) / 180;
    const baseRad = (emitter.direction * Math.PI) / 180;
    const angle = baseRad + (Math.random() - 0.5) * spreadRad;

    // Calculate speed with variance
    const speed = emitter.speed + (Math.random() - 0.5) * 2 * emitter.speedVariance;
    const speedNormalized = speed * 0.001;

    // Calculate size with variance
    const size = Math.max(1, emitter.size + (Math.random() - 0.5) * 2 * emitter.sizeVariance);

    // Calculate lifetime with variance
    const lifetime = Math.max(1, emitter.particleLifetime + (Math.random() - 0.5) * 2 * emitter.lifetimeVariance);

    const particle: Particle = {
      id: this.nextParticleId++,
      x: emitter.x,
      y: emitter.y,
      prevX: emitter.x,
      prevY: emitter.y,
      vx: Math.cos(angle) * speedNormalized,
      vy: Math.sin(angle) * speedNormalized,
      age: 0,
      lifetime,
      size,
      baseSize: size,
      color: [...emitter.color, 255] as [number, number, number, number],
      baseColor: [...emitter.color, 255] as [number, number, number, number],
      emitterId: emitter.id,
      isSubParticle: false
    };

    this.particles.push(particle);
    this.trailHistory.set(particle.id, [{ x: particle.x, y: particle.y }]);
  }

  private handleBoundaryCollision(p: Particle): void {
    if (!this.boundaryMask) return;

    const px = Math.floor(p.x * this.boundaryMask.width);
    const py = Math.floor(p.y * this.boundaryMask.height);

    if (px < 0 || px >= this.boundaryMask.width || py < 0 || py >= this.boundaryMask.height) {
      return;
    }

    const idx = (py * this.boundaryMask.width + px) * 4;
    const maskValue = this.boundaryMask.data[idx]; // Use red channel

    // If mask is black (0), particle is in restricted area
    if (maskValue < 128) {
      switch (this.config.boundaryBehavior) {
        case 'bounce':
          // Simple bounce - reverse velocity
          p.vx *= -0.8;
          p.vy *= -0.8;
          // Move back
          p.x = p.prevX;
          p.y = p.prevY;
          break;
        case 'kill':
          p.age = p.lifetime + 1;
          break;
        case 'wrap':
          // Find valid position (simplified)
          p.x = Math.random();
          p.y = Math.random();
          break;
      }
    }
  }

  private handleCanvasBoundary(p: Particle): void {
    switch (this.config.boundaryBehavior) {
      case 'bounce':
        if (p.x < 0) { p.x = 0; p.vx *= -0.8; }
        if (p.x > 1) { p.x = 1; p.vx *= -0.8; }
        if (p.y < 0) { p.y = 0; p.vy *= -0.8; }
        if (p.y > 1) { p.y = 1; p.vy *= -0.8; }
        break;
      case 'kill':
        if (p.x < -0.1 || p.x > 1.1 || p.y < -0.1 || p.y > 1.1) {
          p.age = p.lifetime + 1;
        }
        break;
      case 'wrap':
        if (p.x < 0) p.x += 1;
        if (p.x > 1) p.x -= 1;
        if (p.y < 0) p.y += 1;
        if (p.y > 1) p.y -= 1;
        break;
    }
  }

  private applyModulations(p: Particle): void {
    const lifeRatio = p.age / p.lifetime;

    for (const mod of this.modulations) {
      // Check if modulation applies to this particle's emitter
      if (mod.emitterId !== '*' && mod.emitterId !== p.emitterId) continue;

      // Get eased value
      const easingKey = mod.easing as keyof typeof EASING_PRESETS;
      const easing = EASING_PRESETS[easingKey] || EASING_PRESETS.linear;
      const easedRatio = applyEasing(lifeRatio, easing);
      const value = mod.startValue + (mod.endValue - mod.startValue) * easedRatio;

      switch (mod.property) {
        case 'size':
          p.size = p.baseSize * value;
          break;
        case 'speed':
          // Modulate current velocity magnitude
          const currentSpeed = Math.sqrt(p.vx * p.vx + p.vy * p.vy);
          if (currentSpeed > 0.0001) {
            const scale = value / Math.max(0.0001, currentSpeed * 1000);
            p.vx *= scale;
            p.vy *= scale;
          }
          break;
        case 'opacity':
          p.color[3] = Math.max(0, Math.min(255, p.baseColor[3] * value));
          break;
        case 'colorR':
          p.color[0] = Math.max(0, Math.min(255, value * 255));
          break;
        case 'colorG':
          p.color[1] = Math.max(0, Math.min(255, value * 255));
          break;
        case 'colorB':
          p.color[2] = Math.max(0, Math.min(255, value * 255));
          break;
      }
    }
  }

  // ============================================================================
  // Turbulence
  // ============================================================================

  private applyTurbulence(p: Particle, deltaTime: number): void {
    const turbFields = this.config.turbulenceFields || [];
    for (const turb of turbFields) {
      if (!turb.enabled) continue;
      const nx = p.x * turb.scale * 1000;  // Scale up for noise variation
      const ny = p.y * turb.scale * 1000;
      const nt = this.noiseTime * turb.evolutionSpeed;
      const angle = this.noise2D(nx + nt, ny + nt) * Math.PI * 2;
      const force = turb.strength * 0.00001;
      p.vx += Math.cos(angle) * force * deltaTime;
      p.vy += Math.sin(angle) * force * deltaTime;
    }
  }

  addTurbulence(config: TurbulenceConfig): void {
    if (!this.config.turbulenceFields) this.config.turbulenceFields = [];
    this.config.turbulenceFields.push(config);
  }

  updateTurbulence(id: string, updates: Partial<TurbulenceConfig>): void {
    const turb = this.config.turbulenceFields?.find(t => t.id === id);
    if (turb) Object.assign(turb, updates);
  }

  removeTurbulence(id: string): void {
    if (this.config.turbulenceFields) {
      this.config.turbulenceFields = this.config.turbulenceFields.filter(t => t.id !== id);
    }
  }

  getTurbulenceFields(): TurbulenceConfig[] {
    return this.config.turbulenceFields || [];
  }

  // ============================================================================
  // Sub-Emitters
  // ============================================================================

  private triggerSubEmitters(deadParticle: Particle): void {
    const subEmitters = this.config.subEmitters || [];
    for (const sub of subEmitters) {
      if (!sub.enabled) continue;
      if (sub.parentEmitterId !== '*' && sub.parentEmitterId !== deadParticle.emitterId) continue;

      for (let i = 0; i < sub.spawnCount; i++) {
        const angle = (Math.random() - 0.5) * sub.spread * Math.PI / 180;
        const baseAngle = Math.atan2(deadParticle.vy, deadParticle.vx);
        const emitAngle = baseAngle + angle;
        const inheritedSpeed = Math.sqrt(deadParticle.vx ** 2 + deadParticle.vy ** 2) * sub.inheritVelocity;
        const totalSpeed = sub.speed * 0.001 + inheritedSpeed;

        const particle: Particle = {
          id: this.nextParticleId++,
          x: deadParticle.x,
          y: deadParticle.y,
          prevX: deadParticle.x,
          prevY: deadParticle.y,
          vx: Math.cos(emitAngle) * totalSpeed + deadParticle.vx * sub.inheritVelocity,
          vy: Math.sin(emitAngle) * totalSpeed + deadParticle.vy * sub.inheritVelocity,
          age: 0,
          lifetime: sub.lifetime * (1 + (Math.random() - 0.5) * 0.2),
          size: sub.size * (1 + (Math.random() - 0.5) * sub.sizeVariance / sub.size),
          baseSize: sub.size,
          color: [...sub.color, 255] as [number, number, number, number],
          baseColor: [...sub.color, 255] as [number, number, number, number],
          emitterId: sub.id,
          isSubParticle: true
        };

        this.particles.push(particle);
        this.trailHistory.set(particle.id, [{ x: particle.x, y: particle.y }]);
      }
    }
  }

  addSubEmitter(config: SubEmitterConfig): void {
    if (!this.config.subEmitters) this.config.subEmitters = [];
    this.config.subEmitters.push(config);
  }

  updateSubEmitter(id: string, updates: Partial<SubEmitterConfig>): void {
    const sub = this.config.subEmitters?.find(s => s.id === id);
    if (sub) Object.assign(sub, updates);
  }

  removeSubEmitter(id: string): void {
    if (this.config.subEmitters) {
      this.config.subEmitters = this.config.subEmitters.filter(s => s.id !== id);
    }
  }

  getSubEmitters(): SubEmitterConfig[] {
    return this.config.subEmitters || [];
  }

  // ============================================================================
  // Burst on Beat
  // ============================================================================

  triggerBurst(emitterId: string, count?: number): void {
    const emitter = this.emitters.get(emitterId);
    if (!emitter || !emitter.enabled) return;
    const burstCount = count ?? emitter.burstCount ?? 20;
    for (let i = 0; i < burstCount; i++) {
      this.spawnParticle(emitter);
    }
  }

  triggerAllBursts(): void {
    for (const emitter of this.emitters.values()) {
      if (emitter.burstOnBeat && emitter.enabled) {
        this.triggerBurst(emitter.id);
      }
    }
  }

  // ============================================================================
  // Particle Connections - Spatial Grid
  // ============================================================================

  private buildSpatialGrid(): SpatialGrid {
    const cellSize = this.renderOptions.connections?.maxDistance || 100;
    const cells = new Map<string, Particle[]>();
    for (const p of this.particles) {
      const cellX = Math.floor(p.x * 1000 / cellSize);  // Scale normalized coords
      const cellY = Math.floor(p.y * 1000 / cellSize);
      const key = `${cellX},${cellY}`;
      if (!cells.has(key)) cells.set(key, []);
      cells.get(key)!.push(p);
    }
    return { cellSize, cells };
  }

  private getNeighborParticles(p: Particle, grid: SpatialGrid): Particle[] {
    const cellX = Math.floor(p.x * 1000 / grid.cellSize);
    const cellY = Math.floor(p.y * 1000 / grid.cellSize);
    const neighbors: Particle[] = [];
    for (let dx = -1; dx <= 1; dx++) {
      for (let dy = -1; dy <= 1; dy++) {
        const key = `${cellX + dx},${cellY + dy}`;
        const cell = grid.cells.get(key);
        if (cell) neighbors.push(...cell);
      }
    }
    return neighbors;
  }

  private renderConnections(
    ctx: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D,
    width: number,
    height: number
  ): void {
    const config = this.renderOptions.connections;
    if (!config?.enabled || this.particles.length < 2) return;

    const grid = this.buildSpatialGrid();
    const maxDist = config.maxDistance / 1000;  // Normalize to 0-1
    const maxDistSq = maxDist * maxDist;

    ctx.lineWidth = config.lineWidth;

    for (const p of this.particles) {
      const neighbors = this.getNeighborParticles(p, grid);
      let connectionCount = 0;

      for (const other of neighbors) {
        if (other.id <= p.id) continue;  // Only draw each connection once
        if (connectionCount >= config.maxConnections) break;

        const dx = other.x - p.x;
        const dy = other.y - p.y;
        const distSq = dx * dx + dy * dy;

        if (distSq < maxDistSq) {
          const dist = Math.sqrt(distSq);
          let opacity = config.lineOpacity;
          if (config.fadeByDistance) {
            opacity *= 1 - (dist / maxDist);
          }

          const r = Math.round((p.color[0] + other.color[0]) / 2);
          const g = Math.round((p.color[1] + other.color[1]) / 2);
          const b = Math.round((p.color[2] + other.color[2]) / 2);

          ctx.strokeStyle = `rgba(${r},${g},${b},${opacity})`;
          ctx.beginPath();
          ctx.moveTo(p.x * width, p.y * height);
          ctx.lineTo(other.x * width, other.y * height);
          ctx.stroke();

          connectionCount++;
        }
      }
    }
  }

  reset(): void {
    this.particles = [];
    this.frameCount = 0;
    this.trailHistory.clear();
    this.emissionAccumulators.forEach((_, key) => {
      this.emissionAccumulators.set(key, 0);
    });
    this.nextParticleId = 0;
  }

  warmup(): void {
    for (let i = 0; i < this.config.warmupPeriod; i++) {
      this.step(1);
    }
  }

  getParticles(): readonly Particle[] {
    return this.particles;
  }

  getParticleCount(): number {
    return this.particles.length;
  }

  getConfig(): ParticleSystemConfig {
    return { ...this.config };
  }

  setConfig(updates: Partial<ParticleSystemConfig>): void {
    Object.assign(this.config, updates);
  }

  // ============================================================================
  // Rendering
  // ============================================================================

  renderToCanvas(
    ctx: CanvasRenderingContext2D,
    width: number,
    height: number,
    options: RenderOptions = createDefaultRenderOptions()
  ): void {
    // Cache render options for spatial grid
    this.renderOptions = options;
    ctx.save();

    // Set blend mode
    switch (options.blendMode) {
      case 'additive':
        ctx.globalCompositeOperation = 'lighter';
        break;
      case 'multiply':
        ctx.globalCompositeOperation = 'multiply';
        break;
      case 'screen':
        ctx.globalCompositeOperation = 'screen';
        break;
      default:
        ctx.globalCompositeOperation = 'source-over';
    }

    // Render particle connections first, before particles
    this.renderConnections(ctx, width, height);

    for (const p of this.particles) {
      const x = p.x * width;
      const y = p.y * height;
      const size = p.size;

      // Render trails first
      if (options.renderTrails) {
        const trail = this.trailHistory.get(p.id);
        if (trail && trail.length > 1) {
          ctx.beginPath();
          ctx.moveTo(x, y);

          const trailLen = Math.min(trail.length, options.trailLength);
          for (let i = 0; i < trailLen; i++) {
            const tp = trail[i];
            const opacity = p.color[3] * Math.pow(options.trailOpacityFalloff, i + 1);
            ctx.strokeStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${opacity / 255})`;
            ctx.lineWidth = size * Math.pow(options.trailOpacityFalloff, i);
            ctx.lineTo(tp.x * width, tp.y * height);
          }
          ctx.stroke();
        }
      }

      // Apply glow
      if (options.glowEnabled) {
        ctx.shadowBlur = options.glowRadius;
        ctx.shadowColor = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${options.glowIntensity})`;
      } else {
        ctx.shadowBlur = 0;
      }

      // Motion blur rendering
      if (options.motionBlur && (p.vx !== 0 || p.vy !== 0)) {
        this.renderParticleWithMotionBlur(ctx, p, x, y, size, width, height, options);
      } else {
        // Standard particle rendering
        this.renderParticleShape(ctx, x, y, size, p.color, options.particleShape);
      }
    }

    ctx.restore();
  }

  /**
   * Render a single particle with motion blur effect
   */
  private renderParticleWithMotionBlur(
    ctx: CanvasRenderingContext2D,
    p: Particle,
    x: number,
    y: number,
    size: number,
    _width: number,
    _height: number,
    options: RenderOptions
  ): void {
    // Calculate velocity magnitude
    const velocityMag = Math.sqrt(p.vx * p.vx + p.vy * p.vy);

    // If velocity is too small, render normally
    if (velocityMag < 0.0001) {
      this.renderParticleShape(ctx, x, y, size, p.color, options.particleShape);
      return;
    }

    // Calculate blur stretch based on velocity
    const stretchFactor = options.motionBlurStrength * velocityMag * 500;
    const samples = Math.min(options.motionBlurSamples, 16);

    // Direction of motion
    const dirX = p.vx / velocityMag;
    const dirY = p.vy / velocityMag;

    // Calculate stretch distance in pixels
    const stretchDistance = Math.min(stretchFactor * size, size * 10);

    // Render multiple samples along the motion vector
    for (let i = 0; i < samples; i++) {
      const t = i / (samples - 1); // 0 to 1
      const sampleOpacity = (1 - t * 0.8) / samples; // Fade towards the back

      // Position along the blur streak (from current position to where we were)
      const sampleX = x - dirX * stretchDistance * t;
      const sampleY = y - dirY * stretchDistance * t;

      // Size reduces towards back of blur
      const sampleSize = size * (1 - t * 0.3);

      // Set color with adjusted opacity
      const alpha = (p.color[3] / 255) * sampleOpacity * samples;
      ctx.fillStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${Math.min(1, alpha)})`;

      // Draw sample
      this.renderParticleShape(ctx, sampleX, sampleY, sampleSize, null, options.particleShape);
    }

    // Draw the main particle at full opacity
    ctx.fillStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${p.color[3] / 255})`;
    this.renderParticleShape(ctx, x, y, size, p.color, options.particleShape);
  }

  /**
   * Render a particle shape at given position
   */
  private renderParticleShape(
    ctx: CanvasRenderingContext2D,
    x: number,
    y: number,
    size: number,
    color: [number, number, number, number] | null,
    shape: RenderOptions['particleShape']
  ): void {
    // Set fill color if provided
    if (color) {
      ctx.fillStyle = `rgba(${color[0]}, ${color[1]}, ${color[2]}, ${color[3] / 255})`;
    }

    // Draw particle shape
    switch (shape) {
      case 'circle':
        ctx.beginPath();
        ctx.arc(x, y, size / 2, 0, Math.PI * 2);
        ctx.fill();
        break;

      case 'square':
        ctx.fillRect(x - size / 2, y - size / 2, size, size);
        break;

      case 'triangle':
        ctx.beginPath();
        ctx.moveTo(x, y - size / 2);
        ctx.lineTo(x - size / 2, y + size / 2);
        ctx.lineTo(x + size / 2, y + size / 2);
        ctx.closePath();
        ctx.fill();
        break;

      case 'star':
        this.drawStar(ctx, x, y, 5, size / 2, size / 4);
        ctx.fill();
        break;
    }
  }

  private drawStar(
    ctx: CanvasRenderingContext2D,
    cx: number,
    cy: number,
    spikes: number,
    outerRadius: number,
    innerRadius: number
  ): void {
    ctx.beginPath();
    let rotation = -Math.PI / 2;

    for (let i = 0; i < spikes; i++) {
      const outerX = cx + Math.cos(rotation) * outerRadius;
      const outerY = cy + Math.sin(rotation) * outerRadius;

      if (i === 0) {
        ctx.moveTo(outerX, outerY);
      } else {
        ctx.lineTo(outerX, outerY);
      }

      rotation += Math.PI / spikes;

      const innerX = cx + Math.cos(rotation) * innerRadius;
      const innerY = cy + Math.sin(rotation) * innerRadius;
      ctx.lineTo(innerX, innerY);

      rotation += Math.PI / spikes;
    }

    ctx.closePath();
  }

  renderToMask(width: number, height: number): ImageData {
    const canvas = new OffscreenCanvas(width, height);
    const ctx = canvas.getContext('2d')!;

    // Start with white (include all)
    ctx.fillStyle = '#FFFFFF';
    ctx.fillRect(0, 0, width, height);

    // Draw connections as black (exclude) if enabled
    const connConfig = this.renderOptions.connections;
    if (connConfig?.enabled && this.particles.length >= 2) {
      ctx.strokeStyle = '#000000';
      ctx.lineWidth = connConfig.lineWidth * 2;  // Slightly thicker for matte
      this.renderConnections(ctx, width, height);
    }

    // Draw particles as black (exclude)
    ctx.fillStyle = '#000000';
    for (const p of this.particles) {
      const x = p.x * width;
      const y = p.y * height;
      const size = p.size * 1.5; // Slightly larger for matte

      ctx.beginPath();
      ctx.arc(x, y, size / 2, 0, Math.PI * 2);
      ctx.fill();
    }

    return ctx.getImageData(0, 0, width, height);
  }

  // ============================================================================
  // Serialization
  // ============================================================================

  serialize(): object {
    return {
      config: this.config,
      emitters: Array.from(this.emitters.values()),
      gravityWells: Array.from(this.gravityWells.values()),
      vortices: Array.from(this.vortices.values()),
      modulations: this.modulations,
      frameCount: this.frameCount
    };
  }

  static deserialize(data: any): ParticleSystem {
    const system = new ParticleSystem(data.config);

    if (data.emitters) {
      for (const emitter of data.emitters) {
        system.addEmitter(emitter);
      }
    }

    if (data.gravityWells) {
      for (const well of data.gravityWells) {
        system.addGravityWell(well);
      }
    }

    if (data.vortices) {
      for (const vortex of data.vortices) {
        system.addVortex(vortex);
      }
    }

    if (data.modulations) {
      for (const mod of data.modulations) {
        system.addModulation(mod);
      }
    }

    return system;
  }
}

export default ParticleSystem;
