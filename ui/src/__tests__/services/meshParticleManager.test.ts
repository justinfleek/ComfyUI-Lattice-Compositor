/**
 * Mesh Particle Manager Tests
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { MeshParticleManager } from '@/services/meshParticleManager';
import * as THREE from 'three';

describe('MeshParticleManager', () => {
  let manager: MeshParticleManager;

  beforeEach(() => {
    manager = new MeshParticleManager();
  });

  describe('registerPrimitive', () => {
    it('should register a cube primitive', () => {
      const registration = manager.registerPrimitive('cube', 'Test Cube', 10);

      expect(registration).toBeDefined();
      expect(registration.source).toBe('primitive');
      expect(registration.geometry).toBeInstanceOf(THREE.BufferGeometry);
      expect(registration.vertexCount).toBeGreaterThan(0);
    });

    it('should register a sphere primitive', () => {
      const registration = manager.registerPrimitive('sphere', 'Test Sphere', 5);

      expect(registration).toBeDefined();
      expect(registration.name).toBe('Test Sphere');
      expect(registration.boundingSphere.radius).toBeGreaterThan(0);
    });

    it('should register all primitive types', () => {
      const types: Array<'cube' | 'sphere' | 'cone' | 'cylinder' | 'torus' | 'tetrahedron' | 'octahedron' | 'icosahedron'> = [
        'cube', 'sphere', 'cone', 'cylinder', 'torus', 'tetrahedron', 'octahedron', 'icosahedron'
      ];

      for (const type of types) {
        const reg = manager.registerPrimitive(type);
        expect(reg).toBeDefined();
        expect(reg.geometry).toBeInstanceOf(THREE.BufferGeometry);
      }
    });
  });

  describe('registerCustom', () => {
    it('should register custom geometry', () => {
      const geometry = new THREE.BoxGeometry(10, 10, 10);
      const registration = manager.registerCustom('custom-box', 'Custom Box', geometry);

      expect(registration).toBeDefined();
      expect(registration.source).toBe('custom');
      expect(manager.hasMesh('custom-box')).toBe(true);
    });
  });

  describe('getEmitterShapeConfig', () => {
    it('should return mesh vertices for emitter config', () => {
      manager.registerPrimitive('cube', 'Emitter Cube', 10);
      const id = manager.getAllMeshes()[0].id;
      const config = manager.getEmitterShapeConfig(id);

      expect(config).toBeDefined();
      expect(config?.type).toBe('mesh');
      expect(config?.meshVertices).toBeInstanceOf(Float32Array);
      expect(config?.meshVertices?.length).toBeGreaterThan(0);
    });
  });

  describe('createInstancedMesh', () => {
    it('should create instanced mesh for particles', () => {
      manager.registerPrimitive('sphere', 'Instance Sphere', 1);
      const id = manager.getAllMeshes()[0].id;
      const instanced = manager.createInstancedMesh(id, 1000);

      expect(instanced).toBeDefined();
      expect(instanced?.mesh).toBeInstanceOf(THREE.InstancedMesh);
      expect(instanced?.maxInstances).toBe(1000);
      expect(instanced?.mesh.count).toBe(0); // No active instances initially
    });

    it('should return null for non-existent mesh', () => {
      const instanced = manager.createInstancedMesh('non-existent', 1000);
      expect(instanced).toBeNull();
    });
  });

  describe('updateInstancedMesh', () => {
    it('should update instance transforms', () => {
      manager.registerPrimitive('cube', 'Update Test', 1);
      const id = manager.getAllMeshes()[0].id;
      manager.createInstancedMesh(id, 100);

      const particles = [
        { position: new THREE.Vector3(0, 0, 0), rotation: new THREE.Quaternion(), scale: 1 },
        { position: new THREE.Vector3(10, 0, 0), rotation: new THREE.Quaternion(), scale: 2 },
        { position: new THREE.Vector3(20, 0, 0), rotation: new THREE.Quaternion(), scale: 0.5 },
      ];

      manager.updateInstancedMesh(id, particles);

      const instance = manager.getInstancedMesh(id);
      expect(instance?.activeInstances).toBe(3);
      expect(instance?.mesh.count).toBe(3);
    });
  });

  describe('LOD', () => {
    it('should add and retrieve LOD levels', () => {
      manager.registerPrimitive('sphere', 'LOD Sphere', 5, 3);
      const id = manager.getAllMeshes()[0].id;

      const lod1 = new THREE.SphereGeometry(2.5, 8, 6);
      const lod2 = new THREE.SphereGeometry(2.5, 4, 4);

      manager.addLODLevels(id, [lod1, lod2], [50, 100]);

      // Near distance should return base geometry
      const nearGeom = manager.getLODGeometry(id, 10);
      expect(nearGeom).toBeDefined();

      // Far distance should return LOD geometry
      const farGeom = manager.getLODGeometry(id, 150);
      expect(farGeom).toBe(lod2);
    });
  });

  describe('cleanup', () => {
    it('should unregister mesh and dispose resources', () => {
      manager.registerPrimitive('cube');
      const id = manager.getAllMeshes()[0].id;

      expect(manager.hasMesh(id)).toBe(true);
      manager.unregisterMesh(id);
      expect(manager.hasMesh(id)).toBe(false);
    });

    it('should dispose all resources on dispose()', () => {
      manager.registerPrimitive('cube');
      manager.registerPrimitive('sphere');
      manager.registerPrimitive('cone');

      expect(manager.getAllMeshes().length).toBe(3);
      manager.dispose();
      expect(manager.getAllMeshes().length).toBe(0);
    });
  });
});
