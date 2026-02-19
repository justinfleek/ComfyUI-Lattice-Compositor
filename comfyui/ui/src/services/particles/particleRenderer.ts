/**
 * Particle Renderer
 *
 * Extracted rendering functions for the CPU-based particle system.
 * All functions are pure and receive particle state as parameters.
 */

import type {
  ConnectionConfig,
  EmitterConfig,
  Particle,
  RenderOptions,
  SpatialGrid,
} from "./particleTypes";
import { isFiniteNumber } from "@/utils/typeGuards";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ═══════════════════════════════════════════════════════════════════════════

export interface ParticleRenderContext {
  particles: Particle[];
  emitters: Map<string, EmitterConfig>;
  trailHistory: Map<number, Array<{ x: number; y: number }>>;
  spriteCache: Map<string, HTMLImageElement | ImageBitmap>;
  renderOptions: RenderOptions;
}

// ═══════════════════════════════════════════════════════════════════════════
// Main Render Functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Get neighbor particles from spatial grid
 * Uses a fixed scale of 1000 to match buildSpatialGrid() in ParticleSystem
 */
function getNeighborParticles(p: Particle, grid: SpatialGrid): Particle[] {
  const neighbors: Particle[] = [];
  // Guard against cellSize=0 to prevent division by zero
  const safeCellSize = grid.cellSize > 0 ? grid.cellSize : 100;
  const cellX = Math.floor((p.x * 1000) / safeCellSize);
  const cellY = Math.floor((p.y * 1000) / safeCellSize);

  for (let dx = -1; dx <= 1; dx++) {
    for (let dy = -1; dy <= 1; dy++) {
      const key = `${cellX + dx},${cellY + dy}`;
      const cell = grid.cells.get(key);
      if (cell) neighbors.push(...cell);
    }
  }
  return neighbors;
}

/**
 * Render all particles to a 2D canvas context
 */
export function renderParticlesToCanvas(
  ctx: CanvasRenderingContext2D,
  width: number,
  height: number,
  context: ParticleRenderContext,
  spatialGrid?: SpatialGrid,
): void {
  const {
    particles,
    renderOptions: options,
    trailHistory,
    emitters,
    spriteCache,
  } = context;

  ctx.save();

  // Set blend mode
  switch (options.blendMode) {
    case "additive":
      ctx.globalCompositeOperation = "lighter";
      break;
    case "multiply":
      ctx.globalCompositeOperation = "multiply";
      break;
    case "screen":
      ctx.globalCompositeOperation = "screen";
      break;
    default:
      ctx.globalCompositeOperation = "source-over";
  }

  // Render particle connections first, before particles
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const connections = (options != null && typeof options === "object" && "connections" in options && options.connections != null && typeof options.connections === "object") ? options.connections : undefined;
  const connectionsEnabled = (connections != null && typeof connections === "object" && "enabled" in connections && typeof connections.enabled === "boolean" && connections.enabled) ? true : false;
  if (connectionsEnabled && spatialGrid) {
    renderConnections(
      ctx,
      width,
      height,
      particles,
      options.connections,
      spatialGrid,
      getNeighborParticles,
    );
  }

  for (const p of particles) {
    const x = p.x * width;
    const y = p.y * height;
    const size = p.size;

    // Render trails first
    if (options.renderTrails) {
      const trail = trailHistory.get(p.id);
      if (trail && trail.length > 1) {
        ctx.beginPath();
        ctx.moveTo(x, y);

        const trailLen = Math.min(trail.length, options.trailLength);
        for (let i = 0; i < trailLen; i++) {
          const tp = trail[i];
          const opacity = p.color[3] * options.trailOpacityFalloff ** (i + 1);
          ctx.strokeStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${opacity / 255})`;
          ctx.lineWidth = size * options.trailOpacityFalloff ** i;
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
      renderParticleWithMotionBlur(
        ctx,
        p,
        x,
        y,
        size,
        options,
        emitters,
        spriteCache,
      );
    } else {
      // Standard particle rendering
      renderParticleShape(
        ctx,
        x,
        y,
        size,
        p.color,
        options.particleShape,
        p,
        options,
        emitters,
        spriteCache,
      );
    }
  }

  ctx.restore();
}

/**
 * Render a single particle with motion blur effect
 */
export function renderParticleWithMotionBlur(
  ctx: CanvasRenderingContext2D,
  p: Particle,
  x: number,
  y: number,
  size: number,
  options: RenderOptions,
  emitters: Map<string, EmitterConfig>,
  spriteCache: Map<string, HTMLImageElement | ImageBitmap>,
): void {
  // Calculate velocity magnitude
  const velocityMag = Math.sqrt(p.vx * p.vx + p.vy * p.vy);

  // If velocity is too small, render normally
  if (velocityMag < 0.0001) {
    renderParticleShape(
      ctx,
      x,
      y,
      size,
      p.color,
      options.particleShape,
      undefined,
      undefined,
      emitters,
      spriteCache,
    );
    return;
  }

  // Calculate blur stretch based on velocity
  const stretchFactor = options.motionBlurStrength * velocityMag * 500;
  // Ensure at least 2 samples to avoid division by zero
  // Type proof: number | undefined → number
  const motionBlurSamples = isFiniteNumber(options.motionBlurSamples) && options.motionBlurSamples >= 2 && options.motionBlurSamples <= 16
    ? options.motionBlurSamples
    : 4;
  const samples = Math.max(2, Math.min(motionBlurSamples, 16));

  // Direction of motion
  const dirX = p.vx / velocityMag;
  const dirY = p.vy / velocityMag;

  // Calculate stretch distance in pixels
  const stretchDistance = Math.min(stretchFactor * size, size * 10);

  // Render multiple samples along the motion vector
  for (let i = 0; i < samples; i++) {
    const t = i / (samples - 1); // 0 to 1 (safe: samples >= 2)
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
    renderParticleShape(
      ctx,
      sampleX,
      sampleY,
      sampleSize,
      null,
      options.particleShape,
      p,
      options,
      emitters,
      spriteCache,
    );
  }

  // Draw the main particle at full opacity
  ctx.fillStyle = `rgba(${p.color[0]}, ${p.color[1]}, ${p.color[2]}, ${p.color[3] / 255})`;
  renderParticleShape(
    ctx,
    x,
    y,
    size,
    p.color,
    options.particleShape,
    p,
    options,
    emitters,
    spriteCache,
  );
}

/**
 * Render a particle shape at given position
 */
export function renderParticleShape(
  ctx: CanvasRenderingContext2D,
  x: number,
  y: number,
  size: number,
  color: [number, number, number, number] | null,
  shape: RenderOptions["particleShape"],
  particle?: Particle,
  options?: RenderOptions,
  emitters?: Map<string, EmitterConfig>,
  spriteCache?: Map<string, HTMLImageElement | ImageBitmap>,
): void {
  // Set fill color if provided
  if (color) {
    ctx.fillStyle = `rgba(${color[0]}, ${color[1]}, ${color[2]}, ${color[3] / 255})`;
  }

  // Handle sprite rendering
  if (shape === "sprite" && particle && emitters && spriteCache) {
    renderSprite(ctx, x, y, size, particle, options, emitters, spriteCache);
    return;
  }

  // Check if this particle has rotation (for non-sprite shapes)
  const hasRotation = particle && particle.rotation !== 0;

  if (hasRotation && particle) {
    ctx.save();
    ctx.translate(x, y);
    ctx.rotate(particle.rotation);
    // Draw at origin since we've translated
    drawShapeAtOrigin(ctx, size, shape);
    ctx.restore();
  } else {
    // Draw particle shape without rotation
    switch (shape) {
      case "circle":
        ctx.beginPath();
        ctx.arc(x, y, size / 2, 0, Math.PI * 2);
        ctx.fill();
        break;

      case "square":
        ctx.fillRect(x - size / 2, y - size / 2, size, size);
        break;

      case "triangle":
        ctx.beginPath();
        ctx.moveTo(x, y - size / 2);
        ctx.lineTo(x - size / 2, y + size / 2);
        ctx.lineTo(x + size / 2, y + size / 2);
        ctx.closePath();
        ctx.fill();
        break;

      case "star":
        drawStar(ctx, x, y, 5, size / 2, size / 4);
        ctx.fill();
        break;
    }
  }
}

/**
 * Draw shape at origin (for rotated shapes)
 */
export function drawShapeAtOrigin(
  ctx: CanvasRenderingContext2D,
  size: number,
  shape: RenderOptions["particleShape"],
): void {
  switch (shape) {
    case "circle":
      ctx.beginPath();
      ctx.arc(0, 0, size / 2, 0, Math.PI * 2);
      ctx.fill();
      break;

    case "square":
      ctx.fillRect(-size / 2, -size / 2, size, size);
      break;

    case "triangle":
      ctx.beginPath();
      ctx.moveTo(0, -size / 2);
      ctx.lineTo(-size / 2, size / 2);
      ctx.lineTo(size / 2, size / 2);
      ctx.closePath();
      ctx.fill();
      break;

    case "star":
      drawStar(ctx, 0, 0, 5, size / 2, size / 4);
      ctx.fill();
      break;
  }
}

/**
 * Render a sprite/texture particle
 */
export function renderSprite(
  ctx: CanvasRenderingContext2D,
  x: number,
  y: number,
  size: number,
  particle: Particle,
  options: RenderOptions | undefined,
  emitters: Map<string, EmitterConfig>,
  spriteCache: Map<string, HTMLImageElement | ImageBitmap>,
): void {
  const emitter = emitters.get(particle.emitterId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const emitterSprite = (emitter != null && typeof emitter === "object" && "sprite" in emitter && emitter.sprite != null && typeof emitter.sprite === "object") ? emitter.sprite : undefined;
  const spriteEnabled = (emitterSprite != null && typeof emitterSprite === "object" && "enabled" in emitterSprite && typeof emitterSprite.enabled === "boolean" && emitterSprite.enabled) ? true : false;
  if (!spriteEnabled) {
    // Fallback to circle if no sprite
    ctx.beginPath();
    ctx.arc(x, y, size / 2, 0, Math.PI * 2);
    ctx.fill();
    return;
  }

  // emitter is guaranteed non-null here because spriteEnabled check above requires emitter.sprite
  if (emitter === undefined) return;
  const sprite = emitter.sprite;
  const image = sprite.imageData || spriteCache.get(particle.emitterId);
  if (!image) {
    // Fallback to circle if no image loaded
    ctx.beginPath();
    ctx.arc(x, y, size / 2, 0, Math.PI * 2);
    ctx.fill();
    return;
  }

  ctx.save();

  // Set image smoothing
  // Type proof: boolean | undefined → boolean
  const spriteSmoothing = options !== undefined && typeof options.spriteSmoothing === "boolean"
    ? options.spriteSmoothing
    : true;
  ctx.imageSmoothingEnabled = spriteSmoothing;

  // Apply opacity based on particle age if enabled
  let alpha = particle.color[3] / 255;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const spriteOpacityByAge = (options != null && typeof options === "object" && "spriteOpacityByAge" in options && typeof options.spriteOpacityByAge === "boolean" && options.spriteOpacityByAge) ? true : false;
  if (spriteOpacityByAge) {
    // Guard against lifetime=0 to prevent division by zero
    const safeLifetime = particle.lifetime > 0 ? particle.lifetime : 1;
    const lifeRatio = particle.age / safeLifetime;
    // Fade out in the last 20% of life
    if (lifeRatio > 0.8) {
      alpha *= 1 - (lifeRatio - 0.8) / 0.2;
    }
  }
  ctx.globalAlpha = alpha;

  // Calculate sprite sheet frame coordinates
  let sx = 0;
  let sy = 0;
  let sw = image.width;
  let sh = image.height;

  if ((sprite.isSheet && sprite.columns > 1) || sprite.rows > 1) {
    const frameWidth = image.width / sprite.columns;
    const frameHeight = image.height / sprite.rows;
    const col = particle.spriteIndex % sprite.columns;
    const row = Math.floor(particle.spriteIndex / sprite.columns) % sprite.rows;
    sx = col * frameWidth;
    sy = row * frameHeight;
    sw = frameWidth;
    sh = frameHeight;
  }

  // Translate to particle position
  ctx.translate(x, y);

  // Apply rotation
  if (particle.rotation !== 0) {
    ctx.rotate(particle.rotation);
  }

  // Draw the sprite centered at the particle position
  const halfSize = size / 2;
  ctx.drawImage(
    image,
    sx,
    sy,
    sw,
    sh, // Source rectangle
    -halfSize,
    -halfSize,
    size,
    size, // Destination rectangle
  );

  ctx.restore();
}

/**
 * Draw a star shape
 */
export function drawStar(
  ctx: CanvasRenderingContext2D,
  cx: number,
  cy: number,
  spikes: number,
  outerRadius: number,
  innerRadius: number,
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

/**
 * Render connections between nearby particles using spatial grid
 */
export function renderConnections(
  ctx: CanvasRenderingContext2D | OffscreenCanvasRenderingContext2D,
  width: number,
  height: number,
  particles: Particle[],
  config: ConnectionConfig,
  spatialGrid: SpatialGrid,
  getNeighbors: (p: Particle, grid: SpatialGrid) => Particle[],
): void {
  if (!config.enabled || particles.length < 2) {
    return;
  }

  // Guard against maxDistance=0 to prevent division by zero
  const safeMaxDistance = config.maxDistance > 0 ? config.maxDistance : 100;
  const maxDist = safeMaxDistance / 1000; // Normalize to 0-1
  const maxDistSq = maxDist * maxDist;

  ctx.lineWidth = config.lineWidth;

  for (const p of particles) {
    const neighbors = getNeighbors(p, spatialGrid);
    let connectionCount = 0;

    for (const other of neighbors) {
      if (other.id <= p.id) continue; // Only draw each connection once
      if (connectionCount >= config.maxConnections) break;

      const dx = other.x - p.x;
      const dy = other.y - p.y;
      const distSq = dx * dx + dy * dy;

      if (distSq < maxDistSq) {
        const dist = Math.sqrt(distSq);
        let opacity = config.lineOpacity;
        if (config.fadeByDistance) {
          opacity *= 1 - dist / maxDist;
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

/**
 * Render particles to a mask (white background, black particles)
 */
export function renderParticlesToMask(
  width: number,
  height: number,
  particles: Particle[],
  renderOptions: RenderOptions,
): ImageData {
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext("2d")!;

  // Start with white (include all)
  ctx.fillStyle = "#FFFFFF";
  ctx.fillRect(0, 0, width, height);

  // Draw connections as black (exclude) if enabled
  const connConfig = renderOptions.connections;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const connConfigEnabled = (connConfig != null && typeof connConfig === "object" && "enabled" in connConfig && typeof connConfig.enabled === "boolean" && connConfig.enabled) ? true : false;
  if (connConfigEnabled && particles.length >= 2) {
    ctx.strokeStyle = "#000000";
    ctx.lineWidth = connConfig.lineWidth * 2; // Slightly thicker for matte
    // Note: For mask rendering, we use a simplified connection approach
    // since we don't need colors
    const maxDist = connConfig.maxDistance;
    const maxDistSq = maxDist * maxDist;

    for (let i = 0; i < particles.length; i++) {
      for (let j = i + 1; j < particles.length; j++) {
        const p1 = particles[i];
        const p2 = particles[j];
        const dx = p2.x - p1.x;
        const dy = p2.y - p1.y;
        const distSq = dx * dx + dy * dy;

        if (distSq < maxDistSq) {
          ctx.beginPath();
          ctx.moveTo(p1.x * width, p1.y * height);
          ctx.lineTo(p2.x * width, p2.y * height);
          ctx.stroke();
        }
      }
    }
  }

  // Draw particles as black (exclude)
  ctx.fillStyle = "#000000";
  for (const p of particles) {
    const x = p.x * width;
    const y = p.y * height;
    const size = p.size * 1.5; // Slightly larger for matte

    ctx.beginPath();
    ctx.arc(x, y, size / 2, 0, Math.PI * 2);
    ctx.fill();
  }

  return ctx.getImageData(0, 0, width, height);
}
