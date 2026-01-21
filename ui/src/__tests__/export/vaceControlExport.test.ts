/**
 * VACE Control Export Tests
 * 
 * BUG HUNTING - focused on actual issues found:
 * 1. Duration=0 causes division by zero
 * 2. Path with < 2 control points
 */

import { describe, it, expect } from "vitest";
import {
  PathFollower,
  createPathFollower,
  createVACEExportConfig,
  calculateDurationForSpeed,
  calculateSpeed,
  splineLayerToPathFollower,
} from "@/services/export/vaceControlExport";

// Helper to create full SplineControlPoint objects
function makeControlPoint(x: number, y: number, opts?: {
  id?: string;
  handleIn?: { x: number; y: number } | null;
  handleOut?: { x: number; y: number } | null;
  type?: "corner" | "smooth" | "symmetric";
}) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
  const id = (opts !== null && opts !== undefined && typeof opts === "object" && "id" in opts && typeof opts.id === "string" && opts.id.length > 0) ? opts.id : `cp-${x}-${y}`;
  const handleIn = (opts !== null && opts !== undefined && typeof opts === "object" && "handleIn" in opts) ? opts.handleIn : null;
  const handleOut = (opts !== null && opts !== undefined && typeof opts === "object" && "handleOut" in opts) ? opts.handleOut : null;
  const type = (opts !== null && opts !== undefined && typeof opts === "object" && "type" in opts && typeof opts.type === "string" && (opts.type === "corner" || opts.type === "smooth" || opts.type === "symmetric")) ? opts.type as const : "corner" as const;
  return {
    id,
    x,
    y,
    handleIn,
    handleOut,
    type,
  };
}

describe("PathFollower", () => {
  describe("Duration of 0 (BUG FIXED)", () => {
    // BUG WAS: vaceControlExport.ts line 287
    // When duration=0, rawProgress = localFrame / 0 = NaN
    // FIX APPLIED: Added guard for duration <= 0 at line ~256

    it("should handle duration=0 without crashing", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 100),
      ], { duration: 0 });

      const follower = new PathFollower(config);

      // Should not throw after fix
      expect(() => follower.getStateAtFrame(0)).not.toThrow();
      expect(() => follower.getStateAtFrame(10)).not.toThrow();
    });

    it("should return invisible state when duration=0", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 100),
      ], { duration: 0 });

      const follower = new PathFollower(config);
      const state = follower.getStateAtFrame(0);

      // Should return default (invisible) state
      expect(state.visible).toBe(false);
    });
  });

  describe("Edge case: Less than 2 control points", () => {
    it("should handle empty control points", () => {
      const config = createPathFollower("test", [], { duration: 60 });
      const follower = new PathFollower(config);

      const state = follower.getStateAtFrame(30);
      expect(state.visible).toBe(false);
      expect(follower.getPathLength()).toBe(0);
    });

    it("should handle single control point", () => {
      const config = createPathFollower("test", [makeControlPoint(50, 50)], { duration: 60 });
      const follower = new PathFollower(config);

      const state = follower.getStateAtFrame(30);
      expect(state.visible).toBe(false);
    });
  });

  describe("Normal operation", () => {
    it("should calculate path length correctly", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 0), // Straight line
      ], { duration: 60 });

      const follower = new PathFollower(config);

      // Should be approximately 100 pixels (straight line)
      expect(follower.getPathLength()).toBeCloseTo(100, 0);
    });

    it("should calculate speed correctly", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 0),
      ], { duration: 50 });

      const follower = new PathFollower(config);

      // Speed = length / duration = 100 / 50 = 2 px/frame
      expect(follower.getSpeed()).toBeCloseTo(2, 0);
    });

    it("should return invisible before animation starts", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 100),
      ], { startFrame: 10, duration: 60 });

      const follower = new PathFollower(config);

      const state = follower.getStateAtFrame(5); // Before startFrame
      expect(state.visible).toBe(false);
    });

    it("should interpolate position along path", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 0),
      ], {
        startFrame: 0,
        duration: 100,
        easing: "linear",
      });

      const follower = new PathFollower(config);

      // At frame 50 (halfway), should be around x=50
      const state = follower.getStateAtFrame(50);
      expect(state.position.x).toBeCloseTo(50, 0);
    });
  });

  describe("Loop modes", () => {
    it("should restart loop correctly", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 0),
      ], {
        duration: 10,
        loop: true,
        loopMode: "restart",
        easing: "linear",
      });

      const follower = new PathFollower(config);

      // Frame 15 should be at same position as frame 5 (15 % 10 = 5)
      const state5 = follower.getStateAtFrame(5);
      const state15 = follower.getStateAtFrame(15);

      expect(state15.progress).toBeCloseTo(state5.progress, 2);
    });

    it("should pingpong loop correctly", () => {
      const config = createPathFollower("test", [
        makeControlPoint(0, 0),
        makeControlPoint(100, 0),
      ], {
        duration: 10,
        loop: true,
        loopMode: "pingpong",
        easing: "linear",
      });

      const follower = new PathFollower(config);

      // Frame 15 should be going backwards (10 - 5 = 5 in reverse)
      const state = follower.getStateAtFrame(15);
      expect(state.progress).toBeCloseTo(0.5, 1);
    });
  });
});

describe("Utility functions", () => {
  it("calculateDurationForSpeed returns correct duration", () => {
    // 100 pixel path at 5 px/frame = 20 frames
    expect(calculateDurationForSpeed(100, 5)).toBe(20);
  });

  it("calculateSpeed returns correct speed", () => {
    // 100 pixel path over 20 frames = 5 px/frame
    expect(calculateSpeed(100, 20)).toBe(5);
  });

  it("calculateSpeed handles division by zero", () => {
    const speed = calculateSpeed(100, 0);
    expect(speed).toBe(Infinity); // Expected behavior for division by zero
  });
});

describe("createVACEExportConfig", () => {
  it("creates config with defaults", () => {
    const config = createVACEExportConfig([]);
    
    expect(config.width).toBe(512);
    expect(config.height).toBe(512);
    expect(config.frameRate).toBe(16);
    expect(config.backgroundColor).toBe("#000000");
  });

  it("respects custom options", () => {
    const config = createVACEExportConfig([], {
      width: 1920,
      height: 1080,
      frameRate: 30,
    });
    
    expect(config.width).toBe(1920);
    expect(config.height).toBe(1080);
    expect(config.frameRate).toBe(30);
  });
});

describe("splineLayerToPathFollower", () => {
  it("converts spline control points to PathFollowerConfig", () => {
    const controlPoints = [
      { id: "cp-1", x: 0, y: 0, handleIn: { x: 0, y: 0 }, handleOut: { x: 10, y: 0 }, type: "corner" as const },
      { id: "cp-2", x: 100, y: 100, handleIn: { x: 90, y: 100 }, handleOut: { x: 110, y: 100 }, type: "corner" as const },
    ];
    
    const config = splineLayerToPathFollower("layer-1", controlPoints, false, 60);
    
    expect(config.id).toBe("layer-1");
    expect(config.duration).toBe(60);
    expect(config.closed).toBe(false);
    expect(config.controlPoints.length).toBe(2);
  });

  it("handles closed path", () => {
    const controlPoints = [
      { id: "cp-1", x: 0, y: 0, handleIn: { x: 0, y: 0 }, handleOut: { x: 10, y: 0 }, type: "corner" as const },
      { id: "cp-2", x: 100, y: 0, handleIn: { x: 90, y: 0 }, handleOut: { x: 110, y: 0 }, type: "corner" as const },
      { id: "cp-3", x: 50, y: 100, handleIn: { x: 40, y: 100 }, handleOut: { x: 60, y: 100 }, type: "corner" as const },
    ];
    
    const config = splineLayerToPathFollower("layer-2", controlPoints, true, 30);
    
    expect(config.closed).toBe(true);
  });

  it("passes custom options through", () => {
    const controlPoints = [
      { id: "cp-1", x: 0, y: 0, handleIn: null, handleOut: null, type: "corner" as const },
      { id: "cp-2", x: 100, y: 100, handleIn: null, handleOut: null, type: "corner" as const },
    ];

    const config = splineLayerToPathFollower("layer-3", controlPoints, false, 60, {
      easing: "ease-in-out",
      loopMode: "pingpong",
    });

    expect(config.easing).toBe("ease-in-out");
    expect(config.loopMode).toBe("pingpong");
  });

  it("handles empty control points", () => {
    const config = splineLayerToPathFollower("empty", [], false, 60);
    
    expect(config.controlPoints.length).toBe(0);
  });
});
