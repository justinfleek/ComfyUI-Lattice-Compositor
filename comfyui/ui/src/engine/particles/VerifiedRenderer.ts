/**
 * VERIFIED RENDERER - SOA to AOS Converter
 * 
 * Converts ParticleBuffer (SOA) to Three.js instanced attributes (AOS)
 * 
 * Performance: Batch conversion, minimize allocations
 */

import * as THREE from "three";
import type { ParticleBuffer } from "./VerifiedParticleBuffer";

/**
 * Convert SOA ParticleBuffer to Three.js instanced attributes
 * 
 * Three.js expects Array-of-Structures (AOS) layout for instanced rendering
 * This function converts Structure-of-Arrays (SOA) to AOS format
 * 
 * @param particles - Particle buffer (SOA layout)
 * @param instancedGeometry - Three.js instanced buffer geometry to update
 */
export function updateInstanceBuffers(
  particles: ParticleBuffer,
  instancedGeometry: THREE.InstancedBufferGeometry
): void {
  const count = particles.count;
  
  // Get or create instanced attributes
  let posAttr = instancedGeometry.getAttribute("i_position") as THREE.InstancedBufferAttribute;
  let velAttr = instancedGeometry.getAttribute("i_velocity") as THREE.InstancedBufferAttribute;
  let lifeAttr = instancedGeometry.getAttribute("i_life") as THREE.InstancedBufferAttribute;
  let physAttr = instancedGeometry.getAttribute("i_physical") as THREE.InstancedBufferAttribute;
  let rotAttr = instancedGeometry.getAttribute("i_rotation") as THREE.InstancedBufferAttribute;
  let colAttr = instancedGeometry.getAttribute("i_color") as THREE.InstancedBufferAttribute;
  
  // Ensure attributes exist and have correct size
  if (!posAttr || posAttr.count < count) {
    posAttr = new THREE.InstancedBufferAttribute(new Float32Array(count * 3), 3);
    instancedGeometry.setAttribute("i_position", posAttr);
  }
  
  if (!velAttr || velAttr.count < count) {
    velAttr = new THREE.InstancedBufferAttribute(new Float32Array(count * 3), 3);
    instancedGeometry.setAttribute("i_velocity", velAttr);
  }
  
  if (!lifeAttr || lifeAttr.count < count) {
    lifeAttr = new THREE.InstancedBufferAttribute(new Float32Array(count * 2), 2);
    instancedGeometry.setAttribute("i_life", lifeAttr);
  }
  
  if (!physAttr || physAttr.count < count) {
    physAttr = new THREE.InstancedBufferAttribute(new Float32Array(count * 2), 2);
    instancedGeometry.setAttribute("i_physical", physAttr);
  }
  
  if (!rotAttr || rotAttr.count < count) {
    rotAttr = new THREE.InstancedBufferAttribute(new Float32Array(count * 2), 2);
    instancedGeometry.setAttribute("i_rotation", rotAttr);
  }
  
  if (!colAttr || colAttr.count < count) {
    colAttr = new THREE.InstancedBufferAttribute(new Float32Array(count * 4), 4);
    instancedGeometry.setAttribute("i_color", colAttr);
  }
  
  // Batch copy from SOA to AOS
  // Position (vec3)
  for (let i = 0; i < count; i++) {
    posAttr.setXYZ(i, particles.posX[i], particles.posY[i], particles.posZ[i]);
  }
  
  // Velocity (vec3)
  for (let i = 0; i < count; i++) {
    velAttr.setXYZ(i, particles.velX[i], particles.velY[i], particles.velZ[i]);
  }
  
  // Life (vec2: age, lifetime)
  for (let i = 0; i < count; i++) {
    lifeAttr.setXY(i, particles.age[i], particles.lifetime[i]);
  }
  
  // Physical (vec2: mass, size)
  for (let i = 0; i < count; i++) {
    physAttr.setXY(i, particles.mass[i], particles.size[i]);
  }
  
  // Rotation (vec2: rotation, rotationSpeed)
  // Note: ParticleBuffer doesn't have rotation yet, using 0 for now
  for (let i = 0; i < count; i++) {
    rotAttr.setXY(i, 0, 0);
  }
  
  // Color (vec4: r, g, b, a)
  for (let i = 0; i < count; i++) {
    colAttr.setXYZW(
      i,
      particles.colorR[i],
      particles.colorG[i],
      particles.colorB[i],
      particles.colorA[i]
    );
  }
  
  // Mark attributes as needing update
  posAttr.needsUpdate = true;
  velAttr.needsUpdate = true;
  lifeAttr.needsUpdate = true;
  physAttr.needsUpdate = true;
  rotAttr.needsUpdate = true;
  colAttr.needsUpdate = true;
  
  // Update instance count
  instancedGeometry.instanceCount = count;
}

/**
 * Create Three.js instanced buffer geometry for particles
 * 
 * @param maxParticles - Maximum particle count
 * @returns Instanced buffer geometry ready for particle rendering
 */
export function createInstancedGeometry(maxParticles: number): THREE.InstancedBufferGeometry {
  const geometry = new THREE.InstancedBufferGeometry();
  
  // Base geometry (billboard quad)
  const positions = new Float32Array([
    -0.5, -0.5, 0,
    0.5, -0.5, 0,
    0.5, 0.5, 0,
    -0.5, 0.5, 0,
  ]);
  
  const uvs = new Float32Array([
    0, 0,
    1, 0,
    1, 1,
    0, 1,
  ]);
  
  const indices = new Uint16Array([
    0, 1, 2,
    0, 2, 3,
  ]);
  
  geometry.setAttribute("position", new THREE.BufferAttribute(positions, 3));
  geometry.setAttribute("uv", new THREE.BufferAttribute(uvs, 2));
  geometry.setIndex(new THREE.BufferAttribute(indices, 1));
  
  // Instanced attributes will be added by updateInstanceBuffers
  // These are updated each frame from ParticleBuffer
  
  return geometry;
}
