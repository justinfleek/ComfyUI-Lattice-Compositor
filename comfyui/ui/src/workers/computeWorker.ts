/**
 * Compute Worker
 *
 * WebWorker for offloading heavy computations from the main thread.
 * Handles:
 * - Particle simulation steps
 * - Bezier curve evaluation
 * - Audio feature extraction
 * - Image processing (blur, segmentation prep)
 *
 * Communication via structured messages with typed payloads.
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                          // message // types
// ════════════════════════════════════════════════════════════════════════════

export type WorkerMessageType =
  | "PARTICLE_STEP"
  | "PARTICLE_INIT"
  | "BEZIER_EVALUATE"
  | "BEZIER_ARC_LENGTH"
  | "IMAGE_BLUR"
  | "IMAGE_THRESHOLD"
  | "COMPUTE_HASH";

import type { JSONValue } from "@/types/dataAsset";

export interface WorkerMessage<T extends JSONValue = JSONValue> {
  type: WorkerMessageType;
  id: string;
  payload: T;
}

export interface WorkerResponse<T = unknown> {
  type: WorkerMessageType;
  id: string;
  success: boolean;
  result?: T;
  error?: string;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                    // particle // simulation
// ════════════════════════════════════════════════════════════════════════════

interface WorkerParticle {
  id: number;
  x: number;
  y: number;
  vx: number;
  vy: number;
  age: number;
  lifetime: number;
  size: number;
  color: [number, number, number, number];
  rotation: number;
}

interface ParticleConfig {
  gravity: number;
  windX: number;
  windY: number;
  friction: number;
  boundaryBehavior: "bounce" | "kill" | "wrap";
}

interface GravityWell {
  x: number;
  y: number;
  strength: number;
  radius: number;
  falloff: "linear" | "quadratic" | "constant";
}

interface Vortex {
  x: number;
  y: number;
  strength: number;
  radius: number;
  inwardPull: number;
}

interface ParticleStepPayload {
  particles: WorkerParticle[];
  config: ParticleConfig;
  gravityWells: GravityWell[];
  vortices: Vortex[];
  deltaTime: number;
}

interface ParticleStepResult {
  particles: WorkerParticle[];
  removedIds: number[];
}

function stepParticles(payload: ParticleStepPayload): ParticleStepResult {
  const { particles, config, gravityWells, vortices, deltaTime } = payload;
  const removedIds: number[] = [];

  for (let i = particles.length - 1; i >= 0; i--) {
    const p = particles[i];

    // Apply gravity
    p.vy += config.gravity * 0.001 * deltaTime;

    // Apply wind
    p.vx += config.windX * deltaTime;
    p.vy += config.windY * deltaTime;

    // Apply gravity wells
    for (const well of gravityWells) {
      const dx = well.x - p.x;
      const dy = well.y - p.y;
      const dist = Math.sqrt(dx * dx + dy * dy);

      if (dist < well.radius && dist > 0.001) {
        let force = well.strength * 0.0001;

        switch (well.falloff) {
          case "linear":
            force *= 1 - dist / well.radius;
            break;
          case "quadratic":
            force *= (1 - dist / well.radius) ** 2;
            break;
        }

        const nx = dx / dist;
        const ny = dy / dist;
        p.vx += nx * force * deltaTime;
        p.vy += ny * force * deltaTime;
      }
    }

    // Apply vortices
    for (const vortex of vortices) {
      const dx = vortex.x - p.x;
      const dy = vortex.y - p.y;
      const dist = Math.sqrt(dx * dx + dy * dy);

      if (dist < vortex.radius && dist > 0.001) {
        const influence = 1 - dist / vortex.radius;
        const strength = vortex.strength * 0.0001 * influence;

        const nx = dx / dist;
        const ny = dy / dist;
        const perpX = -ny;
        const perpY = nx;

        p.vx += perpX * strength * deltaTime;
        p.vy += perpY * strength * deltaTime;

        const inward = vortex.inwardPull * 0.0001 * influence;
        p.vx += nx * inward * deltaTime;
        p.vy += ny * inward * deltaTime;
      }
    }

    // Apply friction
    const frictionFactor = 1 - config.friction;
    p.vx *= frictionFactor;
    p.vy *= frictionFactor;

    // Update position
    p.x += p.vx * deltaTime;
    p.y += p.vy * deltaTime;

    // Handle boundaries
    switch (config.boundaryBehavior) {
      case "bounce":
        if (p.x < 0) {
          p.x = 0;
          p.vx *= -0.8;
        }
        if (p.x > 1) {
          p.x = 1;
          p.vx *= -0.8;
        }
        if (p.y < 0) {
          p.y = 0;
          p.vy *= -0.8;
        }
        if (p.y > 1) {
          p.y = 1;
          p.vy *= -0.8;
        }
        break;
      case "kill":
        if (p.x < -0.1 || p.x > 1.1 || p.y < -0.1 || p.y > 1.1) {
          p.age = p.lifetime + 1;
        }
        break;
      case "wrap":
        if (p.x < 0) p.x += 1;
        if (p.x > 1) p.x -= 1;
        if (p.y < 0) p.y += 1;
        if (p.y > 1) p.y -= 1;
        break;
    }

    // Increment age
    p.age += deltaTime;

    // Check lifetime
    if (p.age > p.lifetime) {
      removedIds.push(p.id);
      particles.splice(i, 1);
    }
  }

  return { particles, removedIds };
}

// ════════════════════════════════════════════════════════════════════════════
//                                             // bezier // curve // evaluation
// ════════════════════════════════════════════════════════════════════════════

interface BezierPoint {
  x: number;
  y: number;
}

interface BezierEvaluatePayload {
  points: BezierPoint[];
  t: number;
}

interface BezierArcLengthPayload {
  points: BezierPoint[];
  samples: number;
}

function evaluateBezier(points: BezierPoint[], t: number): BezierPoint {
  if (points.length === 1) return points[0];

  const newPoints: BezierPoint[] = [];
  for (let i = 0; i < points.length - 1; i++) {
    newPoints.push({
      x: points[i].x + (points[i + 1].x - points[i].x) * t,
      y: points[i].y + (points[i + 1].y - points[i].y) * t,
    });
  }

  return evaluateBezier(newPoints, t);
}

function computeArcLengthTable(
  points: BezierPoint[],
  samples: number,
): number[] {
  const lengths: number[] = [0];
  let totalLength = 0;
  let prevPoint = evaluateBezier(points, 0);

  for (let i = 1; i <= samples; i++) {
    const t = i / samples;
    const point = evaluateBezier(points, t);
    const dx = point.x - prevPoint.x;
    const dy = point.y - prevPoint.y;
    totalLength += Math.sqrt(dx * dx + dy * dy);
    lengths.push(totalLength);
    prevPoint = point;
  }

  return lengths;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                       // image // processing
// ════════════════════════════════════════════════════════════════════════════

interface ImageBlurPayload {
  imageData: ImageData;
  radius: number;
}

function boxBlur(imageData: ImageData, radius: number): ImageData {
  const { width, height, data } = imageData;
  const output = new Uint8ClampedArray(data.length);
  const size = radius * 2 + 1;
  const area = size * size;

  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      let r = 0,
        g = 0,
        b = 0,
        a = 0;

      for (let ky = -radius; ky <= radius; ky++) {
        for (let kx = -radius; kx <= radius; kx++) {
          const px = Math.min(width - 1, Math.max(0, x + kx));
          const py = Math.min(height - 1, Math.max(0, y + ky));
          const i = (py * width + px) * 4;
          r += data[i];
          g += data[i + 1];
          b += data[i + 2];
          a += data[i + 3];
        }
      }

      const i = (y * width + x) * 4;
      output[i] = r / area;
      output[i + 1] = g / area;
      output[i + 2] = b / area;
      output[i + 3] = a / area;
    }
  }

  return new ImageData(output, width, height);
}

interface ImageThresholdPayload {
  imageData: ImageData;
  threshold: number;
}

function threshold(imageData: ImageData, thresh: number): ImageData {
  const { width, height, data } = imageData;
  const output = new Uint8ClampedArray(data.length);

  for (let i = 0; i < data.length; i += 4) {
    const gray = (data[i] + data[i + 1] + data[i + 2]) / 3;
    const value = gray > thresh ? 255 : 0;
    output[i] = value;
    output[i + 1] = value;
    output[i + 2] = value;
    output[i + 3] = data[i + 3];
  }

  return new ImageData(output, width, height);
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                   // hashing
// ════════════════════════════════════════════════════════════════════════════

interface ComputeHashPayload {
  data: string | ArrayBuffer;
}

async function computeHash(data: string | ArrayBuffer): Promise<string> {
  const encoder = new TextEncoder();
  const buffer = typeof data === "string" ? encoder.encode(data) : data;
  const hashBuffer = await crypto.subtle.digest("SHA-256", buffer);
  const hashArray = Array.from(new Uint8Array(hashBuffer));
  return hashArray.map((b) => b.toString(16).padStart(2, "0")).join("");
}

// ════════════════════════════════════════════════════════════════════════════
//                                                        // message // handler
// ════════════════════════════════════════════════════════════════════════════

self.onmessage = async (event: MessageEvent<WorkerMessage>) => {
  const { type, id, payload } = event.data;

  try {
    // Result can be various types (ImageData, arrays, objects) - use unknown
    // WorkerResponse already has result?: T with T = unknown
    let result: unknown;

    switch (type) {
      case "PARTICLE_STEP": {
        const stepPayload = payload as unknown as ParticleStepPayload;
        result = stepParticles(stepPayload);
        break;
      }

      case "BEZIER_EVALUATE": {
        const evalPayload = payload as unknown as BezierEvaluatePayload;
        result = evaluateBezier(evalPayload.points, evalPayload.t);
        break;
      }

      case "BEZIER_ARC_LENGTH": {
        const arcPayload = payload as unknown as BezierArcLengthPayload;
        result = computeArcLengthTable(arcPayload.points, arcPayload.samples);
        break;
      }

      case "IMAGE_BLUR": {
        const blurPayload = payload as unknown as ImageBlurPayload;
        result = boxBlur(blurPayload.imageData, blurPayload.radius);
        break;
      }

      case "IMAGE_THRESHOLD": {
        const threshPayload = payload as unknown as ImageThresholdPayload;
        result = threshold(threshPayload.imageData, threshPayload.threshold);
        break;
      }

      case "COMPUTE_HASH": {
        const hashPayload = payload as unknown as ComputeHashPayload;
        result = await computeHash(hashPayload.data);
        break;
      }

      default:
        throw new Error(`Unknown message type: ${type}`);
    }

    const response: WorkerResponse = {
      type,
      id,
      success: true,
      result,
    };

    self.postMessage(response);
  } catch (error) {
    const response: WorkerResponse = {
      type,
      id,
      success: false,
      error: error instanceof Error ? error.message : String(error),
    };

    self.postMessage(response);
  }
};

// Export types for main thread
export type {
  WorkerParticle,
  ParticleConfig,
  ParticleStepPayload,
  ParticleStepResult,
};
