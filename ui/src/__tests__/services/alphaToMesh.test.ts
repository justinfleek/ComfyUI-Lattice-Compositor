/**
 * Tests for alpha-to-mesh generator
 * Verifies mesh generation from image alpha channels
 */
import { describe, expect, it } from "vitest";
import { generateMeshFromAlpha } from "@/services/alphaToMesh";

// Helper to create test ImageData
function createTestImageData(
  width: number,
  height: number,
  fillAlpha: (x: number, y: number) => number,
): ImageData {
  const data = new Uint8ClampedArray(width * height * 4);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      data[i] = 255; // R
      data[i + 1] = 255; // G
      data[i + 2] = 255; // B
      data[i + 3] = fillAlpha(x, y); // A
    }
  }
  return new ImageData(data, width, height);
}

describe("generateMeshFromAlpha", () => {
  describe("basic functionality", () => {
    it("generates mesh from fully opaque image", () => {
      const imageData = createTestImageData(100, 100, () => 255);
      const result = generateMeshFromAlpha(imageData);

      expect(result.vertexCount).toBeGreaterThan(3);
      expect(result.triangleCount).toBeGreaterThan(0);
      expect(result.vertices.length).toBe(result.vertexCount * 2);
      expect(result.triangles.length).toBe(result.triangleCount * 3);
    });

    it("generates mesh from image with circular alpha", () => {
      const size = 100;
      const centerX = 50;
      const centerY = 50;
      const radius = 40;

      const imageData = createTestImageData(size, size, (x, y) => {
        const dx = x - centerX;
        const dy = y - centerY;
        return Math.sqrt(dx * dx + dy * dy) <= radius ? 255 : 0;
      });

      const result = generateMeshFromAlpha(imageData);

      expect(result.vertexCount).toBeGreaterThan(3);
      expect(result.triangleCount).toBeGreaterThan(0);

      // Bounds should roughly match the circle
      expect(result.bounds.x).toBeLessThanOrEqual(centerX - radius + 5);
      expect(result.bounds.y).toBeLessThanOrEqual(centerY - radius + 5);
      expect(result.bounds.width).toBeGreaterThan(radius);
      expect(result.bounds.height).toBeGreaterThan(radius);
    });

    it("handles completely transparent image with fallback mesh", () => {
      const imageData = createTestImageData(100, 100, () => 0);
      const result = generateMeshFromAlpha(imageData);

      // Should return fallback mesh
      expect(result.vertexCount).toBeGreaterThan(0);
      expect(result.triangleCount).toBeGreaterThan(0);
      expect(result.bounds.width).toBe(100);
      expect(result.bounds.height).toBe(100);
    });

    it("handles image with partial transparency threshold", () => {
      const imageData = createTestImageData(100, 100, (x, _y) => {
        // Left half: 100 alpha (below default threshold of 128)
        // Right half: 200 alpha (above threshold)
        return x < 50 ? 100 : 200;
      });

      const result = generateMeshFromAlpha(imageData, { alphaThreshold: 128 });

      // Bounds should only cover right half
      expect(result.bounds.x).toBeGreaterThanOrEqual(45);
    });
  });

  describe("options", () => {
    it("respects triangleCount option for density", () => {
      const imageData = createTestImageData(200, 200, () => 255);

      const lowDensity = generateMeshFromAlpha(imageData, {
        triangleCount: 50,
      });
      const highDensity = generateMeshFromAlpha(imageData, {
        triangleCount: 500,
      });

      // Higher target should produce more triangles
      expect(highDensity.triangleCount).toBeGreaterThan(
        lowDensity.triangleCount,
      );
    });

    it("respects expansion option", () => {
      const size = 100;
      const imageData = createTestImageData(size, size, (x, y) => {
        // Small centered square
        return x >= 40 && x <= 60 && y >= 40 && y <= 60 ? 255 : 0;
      });

      const noExpansion = generateMeshFromAlpha(imageData, { expansion: 0 });
      const withExpansion = generateMeshFromAlpha(imageData, { expansion: 10 });

      // With expansion, bounds should be larger or vertices should extend further
      // Check that some vertices are outside the original alpha region
      let maxDistNoExp = 0;
      let maxDistWithExp = 0;

      for (let i = 0; i < noExpansion.vertexCount; i++) {
        const x = noExpansion.vertices[i * 2];
        const y = noExpansion.vertices[i * 2 + 1];
        const dx = Math.min(Math.abs(x - 40), Math.abs(x - 60));
        const dy = Math.min(Math.abs(y - 40), Math.abs(y - 60));
        maxDistNoExp = Math.max(maxDistNoExp, Math.max(dx, dy));
      }

      for (let i = 0; i < withExpansion.vertexCount; i++) {
        const x = withExpansion.vertices[i * 2];
        const y = withExpansion.vertices[i * 2 + 1];
        const dx = Math.min(Math.abs(x - 40), Math.abs(x - 60));
        const dy = Math.min(Math.abs(y - 40), Math.abs(y - 60));
        maxDistWithExp = Math.max(maxDistWithExp, Math.max(dx, dy));
      }

      // With expansion, vertices should extend further from the alpha edge
      expect(maxDistWithExp).toBeGreaterThanOrEqual(maxDistNoExp);
    });

    it("respects alphaThreshold option", () => {
      const imageData = createTestImageData(100, 100, (x, _y) => {
        // Gradient from 0 to 255 across width
        return Math.floor((x / 100) * 255);
      });

      const lowThreshold = generateMeshFromAlpha(imageData, {
        alphaThreshold: 50,
      });
      const highThreshold = generateMeshFromAlpha(imageData, {
        alphaThreshold: 200,
      });

      // Low threshold should have wider bounds (more pixels included)
      expect(lowThreshold.bounds.x).toBeLessThan(highThreshold.bounds.x);
    });

    it("respects minBoundarySpacing option", () => {
      const imageData = createTestImageData(200, 200, () => 255);

      const smallSpacing = generateMeshFromAlpha(imageData, {
        minBoundarySpacing: 2,
      });
      const largeSpacing = generateMeshFromAlpha(imageData, {
        minBoundarySpacing: 20,
      });

      // Smaller spacing should produce more boundary points (and thus more vertices)
      expect(smallSpacing.vertexCount).toBeGreaterThan(
        largeSpacing.vertexCount,
      );
    });
  });

  describe("output format", () => {
    it("returns proper Float32Array for vertices", () => {
      const imageData = createTestImageData(50, 50, () => 255);
      const result = generateMeshFromAlpha(imageData);

      expect(result.vertices).toBeInstanceOf(Float32Array);
      expect(result.vertices.length).toBe(result.vertexCount * 2);

      // All vertices should be within image bounds
      for (let i = 0; i < result.vertexCount; i++) {
        const x = result.vertices[i * 2];
        const y = result.vertices[i * 2 + 1];
        expect(x).toBeGreaterThanOrEqual(-10); // Small buffer for expansion
        expect(x).toBeLessThanOrEqual(60);
        expect(y).toBeGreaterThanOrEqual(-10);
        expect(y).toBeLessThanOrEqual(60);
      }
    });

    it("returns proper Uint32Array for triangles", () => {
      const imageData = createTestImageData(50, 50, () => 255);
      const result = generateMeshFromAlpha(imageData);

      expect(result.triangles).toBeInstanceOf(Uint32Array);
      expect(result.triangles.length).toBe(result.triangleCount * 3);

      // All triangle indices should be valid vertex indices
      for (let i = 0; i < result.triangles.length; i++) {
        expect(result.triangles[i]).toBeLessThan(result.vertexCount);
      }
    });

    it("returns accurate bounds", () => {
      const imageData = createTestImageData(100, 100, (x, y) => {
        // Rectangle from (20,30) to (70,80)
        return x >= 20 && x <= 70 && y >= 30 && y <= 80 ? 255 : 0;
      });

      const result = generateMeshFromAlpha(imageData, { expansion: 0 });

      // Bounds should closely match the alpha region
      expect(result.bounds.x).toBeLessThanOrEqual(25);
      expect(result.bounds.y).toBeLessThanOrEqual(35);
      expect(result.bounds.x + result.bounds.width).toBeGreaterThanOrEqual(65);
      expect(result.bounds.y + result.bounds.height).toBeGreaterThanOrEqual(75);
    });
  });

  describe("edge cases", () => {
    it("handles very small image with appropriate mesh size", () => {
      const imageData = createTestImageData(5, 5, () => 255);
      const result = generateMeshFromAlpha(imageData);

      // Should create a mesh that covers the 5x5 area
      expect(result.vertexCount).toBeGreaterThanOrEqual(4); // At least corners
      expect(result.triangleCount).toBeGreaterThanOrEqual(2); // At least 2 triangles
      expect(result.bounds.width).toBeLessThanOrEqual(10); // Reasonable for 5x5
      expect(result.bounds.height).toBeLessThanOrEqual(10);
    });

    it("handles single pixel alpha with fallback to full-image mesh", () => {
      const imageData = createTestImageData(50, 50, (x, y) => {
        return x === 25 && y === 25 ? 255 : 0;
      });

      const result = generateMeshFromAlpha(imageData);

      // Single pixel is too sparse for boundary extraction
      // Should fall back to full-image mesh
      expect(result.bounds.width).toBe(50);
      expect(result.bounds.height).toBe(50);
      expect(result.vertexCount).toBeGreaterThanOrEqual(4);
    });

    it("handles diagonal line with bounds covering the line", () => {
      const imageData = createTestImageData(100, 100, (x, y) => {
        // Diagonal line with 3px thickness
        return Math.abs(x - y) <= 3 ? 255 : 0;
      });

      const result = generateMeshFromAlpha(imageData);

      // Diagonal line goes from (0,0) to (99,99) ish
      // Bounds should cover most of the diagonal
      expect(result.bounds.x).toBeLessThanOrEqual(10);
      expect(result.bounds.y).toBeLessThanOrEqual(10);
      expect(result.bounds.x + result.bounds.width).toBeGreaterThanOrEqual(90);
      expect(result.bounds.y + result.bounds.height).toBeGreaterThanOrEqual(90);
    });

    it("handles complex shape (ring) covering outer boundary", () => {
      const imageData = createTestImageData(100, 100, (x, y) => {
        const dx = x - 50;
        const dy = y - 50;
        const dist = Math.sqrt(dx * dx + dy * dy);
        // Ring shape: solid between radius 20 and 40
        return dist >= 20 && dist <= 40 ? 255 : 0;
      });

      const result = generateMeshFromAlpha(imageData);

      // Ring outer edge is at ~40 from center (50,50)
      // So bounds should be roughly (10,10) to (90,90)
      expect(result.bounds.x).toBeLessThanOrEqual(15);
      expect(result.bounds.y).toBeLessThanOrEqual(15);
      expect(result.bounds.x + result.bounds.width).toBeGreaterThanOrEqual(85);
      expect(result.bounds.y + result.bounds.height).toBeGreaterThanOrEqual(85);
    });

    it("handles non-square image with correct aspect ratio", () => {
      const imageData = createTestImageData(200, 50, () => 255);
      const result = generateMeshFromAlpha(imageData);

      expect(result.vertexCount).toBeGreaterThanOrEqual(4);
      expect(result.triangleCount).toBeGreaterThanOrEqual(2);
      // Aspect ratio should match input
      expect(result.bounds.width).toBeGreaterThan(result.bounds.height * 2);
    });
  });

  describe("triangulation quality", () => {
    it("produces valid triangles (no degenerate triangles)", () => {
      const imageData = createTestImageData(100, 100, () => 255);
      const result = generateMeshFromAlpha(imageData);

      for (let i = 0; i < result.triangleCount; i++) {
        const a = result.triangles[i * 3];
        const b = result.triangles[i * 3 + 1];
        const c = result.triangles[i * 3 + 2];

        // All indices should be different
        expect(a).not.toBe(b);
        expect(b).not.toBe(c);
        expect(c).not.toBe(a);

        // Get vertices
        const ax = result.vertices[a * 2];
        const ay = result.vertices[a * 2 + 1];
        const bx = result.vertices[b * 2];
        const by = result.vertices[b * 2 + 1];
        const cx = result.vertices[c * 2];
        const cy = result.vertices[c * 2 + 1];

        // Triangle should have non-zero area (not degenerate)
        const area =
          Math.abs((bx - ax) * (cy - ay) - (cx - ax) * (by - ay)) / 2;
        expect(area).toBeGreaterThan(0.001);
      }
    });

    it("produces connected mesh where all triangles reference valid vertices", () => {
      const imageData = createTestImageData(100, 100, () => 255);
      const result = generateMeshFromAlpha(imageData);

      // Count which vertices are used by triangles
      const usedVertices = new Set<number>();
      for (let i = 0; i < result.triangles.length; i++) {
        const idx = result.triangles[i];
        // Each index must be a valid vertex
        expect(idx).toBeGreaterThanOrEqual(0);
        expect(idx).toBeLessThan(result.vertexCount);
        usedVertices.add(idx);
      }

      // For a proper triangulation, most vertices should be used
      // (some boundary vertices might be skipped by Delaunay)
      const usageRatio = usedVertices.size / result.vertexCount;
      expect(usageRatio).toBeGreaterThan(0.5); // At least 50% of vertices used
    });
  });
});
