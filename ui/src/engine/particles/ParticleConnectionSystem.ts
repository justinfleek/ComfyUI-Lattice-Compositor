/**
 * Particle Connection System
 *
 * Handles rendering lines between nearby particles.
 * Uses spatial hash for efficient O(n) neighbor queries.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import * as THREE from 'three';
import { PARTICLE_STRIDE, type ConnectionConfig } from './types';

// ============================================================================
// PARTICLE CONNECTION SYSTEM CLASS
// ============================================================================

export class ParticleConnectionSystem {
  private readonly maxParticles: number;

  // Connection rendering
  private connectionMesh: THREE.LineSegments | null = null;
  private connectionGeometry: THREE.BufferGeometry | null = null;
  private connectionMaterial: THREE.LineBasicMaterial | null = null;

  // Configuration
  private config: ConnectionConfig;

  constructor(maxParticles: number, config: ConnectionConfig) {
    this.maxParticles = maxParticles;
    this.config = config;
  }

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  /**
   * Initialize connection rendering resources
   */
  initialize(): void {
    // Estimate max connections (each particle can connect to maxConnections neighbors)
    const maxLines = this.maxParticles * this.config.maxConnections;
    const maxVertices = maxLines * 2;

    this.connectionGeometry = new THREE.BufferGeometry();
    const positions = new Float32Array(maxVertices * 3);
    const colors = new Float32Array(maxVertices * 4);

    this.connectionGeometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
    this.connectionGeometry.setAttribute('color', new THREE.BufferAttribute(colors, 4));
    (this.connectionGeometry.getAttribute('position') as THREE.BufferAttribute).setUsage(THREE.DynamicDrawUsage);
    (this.connectionGeometry.getAttribute('color') as THREE.BufferAttribute).setUsage(THREE.DynamicDrawUsage);

    this.connectionMaterial = new THREE.LineBasicMaterial({
      vertexColors: true,
      transparent: true,
      blending: THREE.AdditiveBlending,
      depthWrite: false,
      linewidth: this.config.lineWidth, // Note: linewidth only works in some WebGL contexts
    });

    this.connectionMesh = new THREE.LineSegments(this.connectionGeometry, this.connectionMaterial);
    this.connectionMesh.frustumCulled = false;
  }

  // ============================================================================
  // UPDATE
  // ============================================================================

  /**
   * Update particle connections
   * Uses spatial hash for efficient neighbor queries
   * @param particleBuffer - The current particle data buffer
   */
  update(particleBuffer: Float32Array): void {
    if (!this.config.enabled || !this.connectionGeometry) return;

    const posAttr = this.connectionGeometry.getAttribute('position') as THREE.BufferAttribute;
    const colorAttr = this.connectionGeometry.getAttribute('color') as THREE.BufferAttribute;

    const maxDistSq = this.config.maxDistance * this.config.maxDistance;
    let vertexIndex = 0;

    // Build a list of active particle positions
    const activeParticles: Array<{ index: number; x: number; y: number; z: number; color: number[] }> = [];

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = particleBuffer[offset + 7];
      const age = particleBuffer[offset + 6];

      if (lifetime > 0 && age < lifetime) {
        activeParticles.push({
          index: i,
          x: particleBuffer[offset + 0],
          y: particleBuffer[offset + 1],
          z: particleBuffer[offset + 2],
          color: [
            particleBuffer[offset + 12],
            particleBuffer[offset + 13],
            particleBuffer[offset + 14],
            particleBuffer[offset + 15],
          ],
        });
      }
    }

    // Build spatial hash grid for O(n) neighbor queries instead of O(n^2)
    const cellSize = this.config.maxDistance;
    const grid = new Map<string, typeof activeParticles>();
    for (const p of activeParticles) {
      const cellX = Math.floor(p.x / cellSize);
      const cellY = Math.floor(p.y / cellSize);
      const cellZ = Math.floor(p.z / cellSize);
      const key = `${cellX},${cellY},${cellZ}`;
      if (!grid.has(key)) grid.set(key, []);
      grid.get(key)!.push(p);
    }

    // For each particle, find nearby particles using spatial hash
    const connectionCount = new Map<number, number>();
    const processedPairs = new Set<string>();

    for (const p1 of activeParticles) {
      const p1Connections = connectionCount.get(p1.index) ?? 0;
      if (p1Connections >= this.config.maxConnections) continue;

      // Query 3x3x3 neighborhood of cells
      const cellX = Math.floor(p1.x / cellSize);
      const cellY = Math.floor(p1.y / cellSize);
      const cellZ = Math.floor(p1.z / cellSize);

      for (let dx = -1; dx <= 1; dx++) {
        for (let dy = -1; dy <= 1; dy++) {
          for (let dz = -1; dz <= 1; dz++) {
            const key = `${cellX + dx},${cellY + dy},${cellZ + dz}`;
            const cellParticles = grid.get(key);
            if (!cellParticles) continue;

            for (const p2 of cellParticles) {
              // Skip self and already-processed pairs
              if (p2.index <= p1.index) continue;
              const pairKey = `${p1.index}-${p2.index}`;
              if (processedPairs.has(pairKey)) continue;
              processedPairs.add(pairKey);

              const p2Connections = connectionCount.get(p2.index) ?? 0;
              if (p2Connections >= this.config.maxConnections) continue;

              // Calculate distance
              const ddx = p2.x - p1.x;
              const ddy = p2.y - p1.y;
              const ddz = p2.z - p1.z;
              const distSq = ddx * ddx + ddy * ddy + ddz * ddz;

              if (distSq < maxDistSq) {
                // Calculate opacity based on distance
                let opacity = this.config.lineOpacity;
                if (this.config.fadeByDistance) {
                  const dist = Math.sqrt(distSq);
                  opacity *= 1 - (dist / this.config.maxDistance);
                }

                // Blend colors from both particles
                const color = this.config.color ?? [
                  (p1.color[0] + p2.color[0]) / 2,
                  (p1.color[1] + p2.color[1]) / 2,
                  (p1.color[2] + p2.color[2]) / 2,
                ];

                // Add line vertices
                posAttr.setXYZ(vertexIndex, p1.x, p1.y, p1.z);
                colorAttr.setXYZW(vertexIndex, color[0], color[1], color[2], opacity);
                vertexIndex++;

                posAttr.setXYZ(vertexIndex, p2.x, p2.y, p2.z);
                colorAttr.setXYZW(vertexIndex, color[0], color[1], color[2], opacity);
                vertexIndex++;

                // Update connection counts
                connectionCount.set(p1.index, (connectionCount.get(p1.index) ?? 0) + 1);
                connectionCount.set(p2.index, p2Connections + 1);

                // Check if we've maxed out this particle's connections
                if ((connectionCount.get(p1.index) ?? 0) >= this.config.maxConnections) break;
              }
            }
            if ((connectionCount.get(p1.index) ?? 0) >= this.config.maxConnections) break;
          }
          if ((connectionCount.get(p1.index) ?? 0) >= this.config.maxConnections) break;
        }
        if ((connectionCount.get(p1.index) ?? 0) >= this.config.maxConnections) break;
      }
    }

    // Update draw range
    this.connectionGeometry.setDrawRange(0, vertexIndex);
    posAttr.needsUpdate = true;
    colorAttr.needsUpdate = true;
  }

  // ============================================================================
  // ACCESSORS
  // ============================================================================

  /**
   * Get the connection mesh for adding to scene
   */
  getMesh(): THREE.LineSegments | null {
    return this.connectionMesh;
  }

  /**
   * Check if connection system is initialized
   */
  isInitialized(): boolean {
    return this.connectionMesh !== null;
  }

  /**
   * Enable or disable particle connections
   */
  setEnabled(enabled: boolean): void {
    this.config.enabled = enabled;
  }

  /**
   * Check if connections are enabled
   */
  isEnabled(): boolean {
    return this.config.enabled;
  }

  /**
   * Update connection configuration
   */
  updateConfig(config: Partial<ConnectionConfig>): void {
    Object.assign(this.config, config);
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Reset connection state
   */
  reset(): void {
    if (this.connectionGeometry) {
      this.connectionGeometry.setDrawRange(0, 0);
    }
  }

  /**
   * Dispose of all resources
   */
  dispose(): void {
    if (this.connectionGeometry) {
      this.connectionGeometry.dispose();
      this.connectionGeometry = null;
    }
    if (this.connectionMaterial) {
      this.connectionMaterial.dispose();
      this.connectionMaterial = null;
    }
    this.connectionMesh = null;
  }
}
