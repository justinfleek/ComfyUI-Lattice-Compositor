/**
 * SVG Extrusion Service Tests
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { SVGExtrusionService } from '@/services/svgExtrusion';
import * as THREE from 'three';

describe('SVGExtrusionService', () => {
  let service: SVGExtrusionService;

  beforeEach(() => {
    service = new SVGExtrusionService();
  });

  describe('loadFromString', () => {
    it('should parse a simple SVG with one path', () => {
      const svg = `
        <svg width="100" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="10" y="10" width="80" height="80" fill="#ff0000"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'test-rect');

      expect(doc).toBeDefined();
      expect(doc.name).toBe('test-rect');
      expect(doc.paths.length).toBeGreaterThan(0);
    });

    it('should parse SVG with multiple paths', () => {
      const svg = `
        <svg width="200" height="200" xmlns="http://www.w3.org/2000/svg">
          <circle cx="50" cy="50" r="40" fill="#ff0000"/>
          <circle cx="150" cy="50" r="40" fill="#00ff00"/>
          <rect x="50" y="100" width="100" height="80" fill="#0000ff"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'multi-shape');

      expect(doc.paths.length).toBeGreaterThanOrEqual(1);
    });

    it('should calculate bounds correctly', () => {
      const svg = `
        <svg width="100" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="0" y="0" width="100" height="100" fill="#fff"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'bounds-test');

      expect(doc.bounds.width).toBeGreaterThan(0);
      expect(doc.bounds.height).toBeGreaterThan(0);
    });
  });

  describe('createExtrudedGeometry', () => {
    it('should create valid geometry from SVG path', () => {
      const svg = `
        <svg width="100" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="10" y="10" width="80" height="80" fill="#fff"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'extrude-test');

      if (doc.paths.length > 0) {
        const geometry = service.createExtrudedGeometry(doc.paths[0], {
          depth: 10,
          bevelEnabled: false,
        });

        expect(geometry).toBeInstanceOf(THREE.BufferGeometry);
        expect(geometry.getAttribute('position')).toBeDefined();
        expect(geometry.getAttribute('position').count).toBeGreaterThan(0);

        geometry.dispose();
      }
    });

    it('should apply bevel settings', () => {
      const svg = `
        <svg width="100" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="10" y="10" width="80" height="80" fill="#fff"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'bevel-test');

      if (doc.paths.length > 0) {
        const noBevel = service.createExtrudedGeometry(doc.paths[0], {
          depth: 10,
          bevelEnabled: false,
        });

        const withBevel = service.createExtrudedGeometry(doc.paths[0], {
          depth: 10,
          bevelEnabled: true,
          bevelSize: 2,
          bevelSegments: 3,
        });

        // Bevel adds more vertices
        expect(withBevel.getAttribute('position').count)
          .toBeGreaterThan(noBevel.getAttribute('position').count);

        noBevel.dispose();
        withBevel.dispose();
      }
    });
  });

  describe('createParticleMesh', () => {
    it('should create centered particle mesh', () => {
      const svg = `
        <svg width="100" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="10" y="10" width="80" height="80" fill="#fff"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'particle-test');

      if (doc.paths.length > 0) {
        const geometry = service.createParticleMesh(doc.paths[0], {
          extrusionDepth: 1,
          scale: 0.01,
          centerOrigin: true,
        });

        expect(geometry).toBeInstanceOf(THREE.BufferGeometry);

        // Check that it's centered (bounding box center near origin)
        geometry.computeBoundingBox();
        const center = new THREE.Vector3();
        geometry.boundingBox!.getCenter(center);

        expect(Math.abs(center.x)).toBeLessThan(1);
        expect(Math.abs(center.y)).toBeLessThan(1);

        geometry.dispose();
      }
    });
  });

  describe('generateAutoLayerConfigs', () => {
    it('should generate config for each path', () => {
      const svg = `
        <svg width="200" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="0" y="0" width="50" height="100" fill="#f00"/>
          <rect x="50" y="0" width="50" height="100" fill="#0f0"/>
          <rect x="100" y="0" width="50" height="100" fill="#00f"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'layer-test');
      const configs = service.generateAutoLayerConfigs(doc, 0, 5, 2);

      expect(configs.length).toBe(doc.paths.length);

      // Check depth increments
      for (let i = 1; i < configs.length; i++) {
        expect(configs[i].depth).toBeGreaterThan(configs[i - 1].depth);
      }
    });
  });

  describe('caching', () => {
    it('should cache documents', () => {
      const svg = `
        <svg width="100" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="10" y="10" width="80" height="80" fill="#fff"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'cache-test');
      const cached = service.getDocument(doc.id);

      expect(cached).toBe(doc);
    });

    it('should clear cache on dispose', () => {
      const svg = `
        <svg width="100" height="100" xmlns="http://www.w3.org/2000/svg">
          <rect x="10" y="10" width="80" height="80" fill="#fff"/>
        </svg>
      `;

      const doc = service.loadFromString(svg, 'dispose-test');
      service.dispose();

      expect(service.getDocument(doc.id)).toBeUndefined();
    });
  });
});
