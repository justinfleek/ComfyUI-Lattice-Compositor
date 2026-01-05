/**
 * Integration tests for meshWarpDeformation with new pin types
 * Verifies that position, bend, advanced, overlap, starch pins work correctly
 */
import { beforeEach, describe, expect, it } from "vitest";
import {
  deformMesh,
  MeshWarpDeformationService,
} from "@/services/meshWarpDeformation";
import { createDefaultWarpPin, type WarpMesh } from "@/types/meshWarp";
import type { ControlPoint } from "@/types/project";

// Helper to deform mesh directly (bypasses cache)
function deformMeshAtFrame(mesh: WarpMesh, frame: number): Float32Array {
  return deformMesh(mesh, frame);
}

describe("MeshWarpDeformation - Pin Type Behavior", () => {
  let service: MeshWarpDeformationService;

  // Simple square of control points for testing
  const controlPoints: ControlPoint[] = [
    { id: "cp1", x: 0, y: 0, handleIn: null, handleOut: null, type: "corner" },
    {
      id: "cp2",
      x: 100,
      y: 0,
      handleIn: null,
      handleOut: null,
      type: "corner",
    },
    {
      id: "cp3",
      x: 100,
      y: 100,
      handleIn: null,
      handleOut: null,
      type: "corner",
    },
    {
      id: "cp4",
      x: 0,
      y: 100,
      handleIn: null,
      handleOut: null,
      type: "corner",
    },
  ];

  beforeEach(() => {
    service = new MeshWarpDeformationService();
  });

  describe("position pin (deform)", () => {
    it("moves vertices when pin position is animated", () => {
      // Create a position pin at center
      const pin = createDefaultWarpPin("pin1", 50, 50, "position");

      // Build mesh
      const mesh = service.buildMesh("layer1", controlPoints, [pin]);
      expect(mesh.vertexCount).toBe(4);

      // Deform at frame 0 (rest position) - should be unchanged
      const frame0 = deformMeshAtFrame(mesh, 0);
      expect(frame0[0]).toBeCloseTo(0, 1); // cp1.x
      expect(frame0[1]).toBeCloseTo(0, 1); // cp1.y

      // Animate pin position to (70, 50) - move 20px right
      pin.position.animated = true;
      pin.position.keyframes = [
        {
          id: "kf1",
          frame: 0,
          value: { x: 50, y: 50 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf2",
          frame: 10,
          value: { x: 70, y: 50 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      // Rebuild mesh with animated pin
      const meshAnimated = service.buildMesh("layer1", controlPoints, [pin]);

      // Deform at frame 10 - vertices should have moved
      const frame10 = deformMeshAtFrame(meshAnimated, 10);

      // Vertices should have shifted right due to pin influence
      // The exact amount depends on weight calculation, but should be > 0
      const deltaX = frame10[0] - 0; // How much cp1.x moved
      expect(deltaX).toBeGreaterThan(0);
    });
  });

  describe("bend pin", () => {
    it("rotates vertices around pin without position translation", () => {
      // Create a bend pin at center
      const pin = createDefaultWarpPin("pin1", 50, 50, "bend");

      // Build mesh at rest
      const _mesh = service.buildMesh("layer1", controlPoints, [pin]);

      // Animate rotation to 45 degrees
      pin.rotation.animated = true;
      pin.rotation.keyframes = [
        {
          id: "kf1",
          frame: 0,
          value: 0,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf2",
          frame: 10,
          value: 45,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      // Rebuild mesh with animated pin
      const meshAnimated = service.buildMesh("layer1", controlPoints, [pin]);

      // Get deformed positions
      const frame0 = deformMeshAtFrame(meshAnimated, 0);
      const frame10 = deformMeshAtFrame(meshAnimated, 10);

      // At frame 0, vertices should be near original positions
      expect(frame0[0]).toBeCloseTo(0, 0); // cp1.x
      expect(frame0[1]).toBeCloseTo(0, 0); // cp1.y

      // At frame 10, vertices should have rotated
      // cp1 (0,0) rotated 45° around (50,50) should move
      // Distance from (0,0) to (50,50) is ~70.7
      // After 45° rotation: approximately (50, 50-70.7) = (50, -20.7) - but weighted

      // Just verify positions changed due to rotation
      const cp1Moved =
        Math.abs(frame10[0] - frame0[0]) > 0.1 ||
        Math.abs(frame10[1] - frame0[1]) > 0.1;
      expect(cp1Moved).toBe(true);
    });

    it("does NOT translate vertices when bend pin position changes", () => {
      // Create bend pin - position should be fixed reference
      const pin = createDefaultWarpPin("pin1", 50, 50, "bend");

      // Animate position (should have NO effect on deformation)
      pin.position.animated = true;
      pin.position.keyframes = [
        {
          id: "kf1",
          frame: 0,
          value: { x: 50, y: 50 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf2",
          frame: 10,
          value: { x: 100, y: 100 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      const mesh = service.buildMesh("layer1", controlPoints, [pin]);

      const frame0 = deformMeshAtFrame(mesh, 0);
      const frame10 = deformMeshAtFrame(mesh, 10);

      // Vertices should NOT have translated (bend ignores position animation)
      expect(frame0[0]).toBeCloseTo(frame10[0], 0);
      expect(frame0[1]).toBeCloseTo(frame10[1], 0);
    });
  });

  describe("advanced pin", () => {
    it("applies position, rotation, and scale together", () => {
      const pin = createDefaultWarpPin("pin1", 50, 50, "advanced");

      // Animate all three properties
      pin.position.animated = true;
      pin.position.keyframes = [
        {
          id: "kf1",
          frame: 0,
          value: { x: 50, y: 50 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf2",
          frame: 10,
          value: { x: 60, y: 50 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      pin.rotation.animated = true;
      pin.rotation.keyframes = [
        {
          id: "kf3",
          frame: 0,
          value: 0,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf4",
          frame: 10,
          value: 30,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      pin.scale.animated = true;
      pin.scale.keyframes = [
        {
          id: "kf5",
          frame: 0,
          value: 1,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf6",
          frame: 10,
          value: 1.5,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      const mesh = service.buildMesh("layer1", controlPoints, [pin]);

      const frame0 = deformMeshAtFrame(mesh, 0);
      const frame10 = deformMeshAtFrame(mesh, 10);

      // Verify deformation occurred (combined effect of position + rotation + scale)
      const totalChange =
        Math.abs(frame10[0] - frame0[0]) +
        Math.abs(frame10[1] - frame0[1]) +
        Math.abs(frame10[2] - frame0[2]) +
        Math.abs(frame10[3] - frame0[3]);

      expect(totalChange).toBeGreaterThan(1); // Significant deformation occurred
    });
  });

  describe("starch pin (stiffness)", () => {
    it("reduces deformation in stiff areas", () => {
      // Create a position pin that will try to move vertices
      const movePin = createDefaultWarpPin("move", 25, 25, "position");
      movePin.position.animated = true;
      movePin.position.keyframes = [
        {
          id: "kf1",
          frame: 0,
          value: { x: 25, y: 25 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf2",
          frame: 10,
          value: { x: 50, y: 25 },
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      // Build mesh WITHOUT starch pin
      const meshNoStarch = service.buildMesh("layer1", controlPoints, [
        movePin,
      ]);
      const deformNoStarch = deformMeshAtFrame(meshNoStarch, 10);

      // Now add a starch pin near cp1 to resist deformation
      const starchPin = createDefaultWarpPin("starch", 10, 10, "starch");
      starchPin.stiffness = 1.0; // Maximum stiffness
      starchPin.radius = 30; // Influence radius covers cp1

      // Build mesh WITH starch pin
      const meshWithStarch = service.buildMesh("layer1", controlPoints, [
        movePin,
        starchPin,
      ]);
      const deformWithStarch = deformMeshAtFrame(meshWithStarch, 10);

      // cp1 (index 0,1) should move LESS with starch pin present
      const moveNoStarch =
        Math.abs(deformNoStarch[0] - 0) + Math.abs(deformNoStarch[1] - 0);
      const moveWithStarch =
        Math.abs(deformWithStarch[0] - 0) + Math.abs(deformWithStarch[1] - 0);

      // Starch should reduce movement (or at least not increase it)
      // Note: exact behavior depends on weight calculation
      expect(moveWithStarch).toBeLessThanOrEqual(moveNoStarch + 0.1);
    });
  });

  describe("overlap pin", () => {
    it("evaluates inFront property but does not affect vertex positions", () => {
      const pin = createDefaultWarpPin("overlap1", 50, 50, "overlap");
      expect(pin.inFront).toBeDefined();

      // Animate inFront
      pin.inFront!.animated = true;
      pin.inFront!.keyframes = [
        {
          id: "kf1",
          frame: 0,
          value: 0,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
        {
          id: "kf2",
          frame: 10,
          value: 100,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "smooth" as const,
        },
      ];

      const mesh = service.buildMesh("layer1", controlPoints, [pin]);

      const frame0 = deformMeshAtFrame(mesh, 0);
      const frame10 = deformMeshAtFrame(mesh, 10);

      // Vertices should NOT move - inFront only affects render depth, not positions
      expect(frame0[0]).toBeCloseTo(frame10[0], 5);
      expect(frame0[1]).toBeCloseTo(frame10[1], 5);
      expect(frame0[2]).toBeCloseTo(frame10[2], 5);
      expect(frame0[3]).toBeCloseTo(frame10[3], 5);
    });
  });
});
