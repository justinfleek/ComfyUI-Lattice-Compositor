/**
 * Tests for motion recording service
 * Verifies smoothing, keyframe conversion, and simplification
 */
import { beforeEach, describe, expect, it, vi } from "vitest";
import {
  convertMotionToKeyframes,
  getMotionAverageSpeed,
  getMotionBounds,
  getMotionPathLength,
  MotionRecorder,
  type MotionSample,
  processRecordedMotion,
  type RecordedMotion,
  removeRedundantKeyframes,
  simplifyKeyframes,
  smoothMotion,
  smoothMotionMovingAverage,
} from "@/services/motionRecording";

// Helper to create test motion
function createTestMotion(
  pinId: string,
  samples: Array<{ time: number; x: number; y: number }>,
  speed: number = 1.0,
): RecordedMotion {
  return { pinId, samples, recordingSpeed: speed };
}

// Helper to create a line motion (constant velocity)
function createLinearMotion(
  pinId: string,
  start: { x: number; y: number },
  end: { x: number; y: number },
  durationMs: number,
  sampleCount: number,
): RecordedMotion {
  const samples: MotionSample[] = [];
  for (let i = 0; i < sampleCount; i++) {
    const t = i / (sampleCount - 1);
    samples.push({
      time: t * durationMs,
      x: start.x + (end.x - start.x) * t,
      y: start.y + (end.y - start.y) * t,
    });
  }
  return { pinId, samples, recordingSpeed: 1.0 };
}

// Helper to create circular motion
function createCircularMotion(
  pinId: string,
  center: { x: number; y: number },
  radius: number,
  durationMs: number,
  sampleCount: number,
): RecordedMotion {
  const samples: MotionSample[] = [];
  for (let i = 0; i < sampleCount; i++) {
    const t = i / (sampleCount - 1);
    const angle = t * 2 * Math.PI;
    samples.push({
      time: t * durationMs,
      x: center.x + Math.cos(angle) * radius,
      y: center.y + Math.sin(angle) * radius,
    });
  }
  return { pinId, samples, recordingSpeed: 1.0 };
}

// Helper to add noise to motion
function addNoise(motion: RecordedMotion, noiseLevel: number): RecordedMotion {
  return {
    ...motion,
    samples: motion.samples.map((s) => ({
      time: s.time,
      x: s.x + (Math.random() - 0.5) * noiseLevel * 2,
      y: s.y + (Math.random() - 0.5) * noiseLevel * 2,
    })),
  };
}

describe("smoothMotion", () => {
  it("returns unchanged motion for smoothing = 0", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      1000,
      10,
    );
    const smoothed = smoothMotion(motion, 0);

    expect(smoothed.samples.length).toBe(motion.samples.length);
    for (let i = 0; i < motion.samples.length; i++) {
      expect(smoothed.samples[i].x).toBe(motion.samples[i].x);
      expect(smoothed.samples[i].y).toBe(motion.samples[i].y);
    }
  });

  it("preserves sample count after smoothing", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      1000,
      20,
    );
    const smoothed = smoothMotion(motion, 50);

    expect(smoothed.samples.length).toBe(motion.samples.length);
  });

  it("preserves timestamps after smoothing", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      1000,
      10,
    );
    const smoothed = smoothMotion(motion, 50);

    for (let i = 0; i < motion.samples.length; i++) {
      expect(smoothed.samples[i].time).toBe(motion.samples[i].time);
    }
  });

  it("reduces noise in samples", () => {
    // Create a noisy line
    const cleanMotion = createLinearMotion(
      "pin1",
      { x: 0, y: 50 },
      { x: 100, y: 50 },
      1000,
      50,
    );
    const noisyMotion = addNoise(cleanMotion, 10); // +/- 10px noise

    const smoothed = smoothMotion(noisyMotion, 80);

    // Calculate average deviation from expected y=50 line
    let noisyDeviation = 0;
    let smoothedDeviation = 0;
    for (let i = 0; i < noisyMotion.samples.length; i++) {
      noisyDeviation += Math.abs(noisyMotion.samples[i].y - 50);
      smoothedDeviation += Math.abs(smoothed.samples[i].y - 50);
    }

    // Smoothed should have less deviation
    expect(smoothedDeviation).toBeLessThan(noisyDeviation);
  });

  it("handles short motion gracefully", () => {
    const motion = createTestMotion("pin1", [
      { time: 0, x: 10, y: 20 },
      { time: 100, x: 30, y: 40 },
    ]);

    const smoothed = smoothMotion(motion, 50);
    expect(smoothed.samples.length).toBe(2);
  });

  it("handles single sample gracefully", () => {
    const motion = createTestMotion("pin1", [{ time: 0, x: 10, y: 20 }]);
    const smoothed = smoothMotion(motion, 50);
    expect(smoothed.samples.length).toBe(1);
  });

  it("higher smoothing produces smoother result", () => {
    const noisyMotion = addNoise(
      createLinearMotion("pin1", { x: 0, y: 50 }, { x: 100, y: 50 }, 1000, 100),
      15,
    );

    const lowSmoothed = smoothMotion(noisyMotion, 20);
    const highSmoothed = smoothMotion(noisyMotion, 80);

    // Calculate variance of y positions
    const calcVariance = (motion: RecordedMotion) => {
      const mean =
        motion.samples.reduce((s, m) => s + m.y, 0) / motion.samples.length;
      return (
        motion.samples.reduce((s, m) => s + (m.y - mean) ** 2, 0) /
        motion.samples.length
      );
    };

    const lowVariance = calcVariance(lowSmoothed);
    const highVariance = calcVariance(highSmoothed);

    // Higher smoothing should have lower variance
    expect(highVariance).toBeLessThan(lowVariance);
  });
});

describe("smoothMotionMovingAverage", () => {
  it("applies moving average correctly", () => {
    const motion = createTestMotion("pin1", [
      { time: 0, x: 0, y: 0 },
      { time: 100, x: 10, y: 10 },
      { time: 200, x: 20, y: 20 },
      { time: 300, x: 30, y: 30 },
      { time: 400, x: 40, y: 40 },
    ]);

    const smoothed = smoothMotionMovingAverage(motion, 3);

    // Middle samples should be averaged with neighbors
    expect(smoothed.samples[2].x).toBeCloseTo(20, 1); // (10 + 20 + 30) / 3
    expect(smoothed.samples[2].y).toBeCloseTo(20, 1);
  });
});

describe("convertMotionToKeyframes", () => {
  it("converts motion to keyframes at correct frames", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      1000,
      10,
    );
    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    // 1000ms at 30fps = 30 frames + 1 (start)
    expect(keyframes.length).toBe(31);

    // First keyframe at frame 0
    expect(keyframes[0].frame).toBe(0);
    expect(keyframes[0].value.x).toBeCloseTo(0, 1);
    expect(keyframes[0].value.y).toBeCloseTo(0, 1);

    // Last keyframe at frame 30
    expect(keyframes[30].frame).toBe(30);
    expect(keyframes[30].value.x).toBeCloseTo(100, 1);
    expect(keyframes[30].value.y).toBeCloseTo(100, 1);
  });

  it("respects startFrame parameter", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      500,
      5,
    );
    const keyframes = convertMotionToKeyframes(motion, 30, 100);

    // Should start at frame 100
    expect(keyframes[0].frame).toBe(100);
    expect(keyframes[keyframes.length - 1].frame).toBeGreaterThan(100);
  });

  it("applies recording speed correctly - half speed", () => {
    const motion: RecordedMotion = {
      pinId: "pin1",
      samples: [
        { time: 0, x: 0, y: 0 },
        { time: 1000, x: 100, y: 100 },
      ],
      recordingSpeed: 0.5, // Half speed = 2x playback duration
    };

    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    // 1000ms recorded at 0.5 speed = 2000ms playback = 60 frames at 30fps
    expect(keyframes.length).toBe(61); // 60 + 1
    expect(keyframes[keyframes.length - 1].frame).toBe(60);
  });

  it("applies recording speed correctly - double speed", () => {
    const motion: RecordedMotion = {
      pinId: "pin1",
      samples: [
        { time: 0, x: 0, y: 0 },
        { time: 1000, x: 100, y: 100 },
      ],
      recordingSpeed: 2.0, // Double speed = 0.5x playback duration
    };

    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    // 1000ms recorded at 2.0 speed = 500ms playback = 15 frames at 30fps
    expect(keyframes.length).toBe(16); // 15 + 1
    expect(keyframes[keyframes.length - 1].frame).toBe(15);
  });

  it("creates valid keyframe structure", () => {
    const motion = createLinearMotion(
      "testPin",
      { x: 50, y: 50 },
      { x: 150, y: 150 },
      500,
      5,
    );
    const keyframes = convertMotionToKeyframes(motion, 24, 10);

    for (const kf of keyframes) {
      expect(kf.id).toBeDefined();
      expect(typeof kf.frame).toBe("number");
      expect(typeof kf.value.x).toBe("number");
      expect(typeof kf.value.y).toBe("number");
      expect(kf.interpolation).toBe("linear");
      expect(kf.inHandle).toBeDefined();
      expect(kf.outHandle).toBeDefined();
      expect(kf.controlMode).toBe("smooth");
    }
  });

  it("handles empty motion gracefully", () => {
    const motion = createTestMotion("pin1", []);
    const keyframes = convertMotionToKeyframes(motion, 30, 0);
    expect(keyframes.length).toBe(0);
  });

  it("handles single sample motion", () => {
    const motion = createTestMotion("pin1", [{ time: 0, x: 50, y: 50 }]);
    const keyframes = convertMotionToKeyframes(motion, 30, 0);
    expect(keyframes.length).toBe(1);
    expect(keyframes[0].value.x).toBe(50);
  });
});

describe("simplifyKeyframes (Douglas-Peucker)", () => {
  it("reduces keyframe count for near-linear motion", () => {
    // Due to interpolation at frame boundaries, keyframes may have tiny deviations
    // Even "linear" motion may not be perfectly colinear
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      1000,
      10,
    );
    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    // With tolerance=1, should significantly reduce linear motion
    const simplified = simplifyKeyframes(keyframes, 1);

    // Should have fewer keyframes than original
    expect(simplified.length).toBeLessThan(keyframes.length);

    // First and last should be preserved
    expect(simplified[0].frame).toBe(keyframes[0].frame);
    expect(simplified[simplified.length - 1].frame).toBe(
      keyframes[keyframes.length - 1].frame,
    );
  });

  it("simplifies linear motion to few keyframes with high tolerance", () => {
    // Create linear motion
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      1000,
      50,
    );
    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    // With high tolerance, should simplify to very few keyframes
    const simplified = simplifyKeyframes(keyframes, 10);

    // Should be significantly reduced (2-4 keyframes for near-linear motion)
    expect(simplified.length).toBeLessThanOrEqual(4);
    expect(simplified[0].frame).toBe(keyframes[0].frame);
    expect(simplified[simplified.length - 1].frame).toBe(
      keyframes[keyframes.length - 1].frame,
    );
  });

  it("preserves curve points in non-linear motion", () => {
    // Create motion with a sharp turn
    const motion = createTestMotion("pin1", [
      { time: 0, x: 0, y: 0 },
      { time: 500, x: 50, y: 0 }, // Moving right
      { time: 1000, x: 50, y: 50 }, // Sharp turn down
    ]);

    const keyframes = convertMotionToKeyframes(motion, 30, 0);
    const simplified = simplifyKeyframes(keyframes, 5);

    // Should preserve the turn point
    expect(simplified.length).toBeGreaterThan(2);

    // The turn around frame 15 (500ms at 30fps) should be preserved
    const turnFrames = simplified.filter(
      (kf) => kf.frame >= 10 && kf.frame <= 20,
    );
    expect(turnFrames.length).toBeGreaterThan(0);
  });

  it("handles circular motion preserving shape", () => {
    const motion = createCircularMotion("pin1", { x: 50, y: 50 }, 30, 1000, 50);
    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    const simplified = simplifyKeyframes(keyframes, 2);

    // Circular motion should keep multiple points (not just 2)
    expect(simplified.length).toBeGreaterThan(4);
    expect(simplified.length).toBeLessThan(keyframes.length);
  });

  it("handles two keyframes gracefully", () => {
    const motion = createTestMotion("pin1", [
      { time: 0, x: 0, y: 0 },
      { time: 100, x: 100, y: 100 },
    ]);
    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    // Should be ~4 keyframes for 100ms at 30fps
    const simplified = simplifyKeyframes(keyframes, 10);

    // Should have at least 2 (start and end)
    expect(simplified.length).toBeGreaterThanOrEqual(2);
  });
});

describe("removeRedundantKeyframes", () => {
  it("removes stationary keyframes", () => {
    const motion = createTestMotion("pin1", [
      { time: 0, x: 50, y: 50 },
      { time: 100, x: 50, y: 50 }, // Same position
      { time: 200, x: 50, y: 50 }, // Same position
      { time: 300, x: 100, y: 100 }, // Moved!
    ]);
    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    const simplified = removeRedundantKeyframes(keyframes, 5);

    // Should remove redundant stationary frames
    expect(simplified.length).toBeLessThan(keyframes.length);

    // First and last should be preserved
    expect(simplified[0].frame).toBe(keyframes[0].frame);
    expect(simplified[simplified.length - 1].frame).toBe(
      keyframes[keyframes.length - 1].frame,
    );
  });

  it("keeps frames with significant movement", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 100 },
      1000,
      10,
    );
    const keyframes = convertMotionToKeyframes(motion, 30, 0);

    const simplified = removeRedundantKeyframes(keyframes, 1);

    // With small tolerance and continuous motion, most should be kept
    expect(simplified.length).toBeGreaterThan(keyframes.length * 0.5);
  });
});

describe("MotionRecorder", () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });

  it("records samples during session", () => {
    const recorder = new MotionRecorder("pin1", { minSampleInterval: 0 });

    recorder.start(0, 0);
    expect(recorder.recording).toBe(true);

    vi.advanceTimersByTime(100);
    recorder.addSample(10, 10);

    vi.advanceTimersByTime(100);
    recorder.addSample(20, 20);

    const motion = recorder.stop();

    expect(motion.pinId).toBe("pin1");
    expect(motion.samples.length).toBe(3); // Initial + 2 added
    expect(motion.samples[0].x).toBe(0);
    expect(motion.samples[1].x).toBe(10);
    expect(motion.samples[2].x).toBe(20);
  });

  it("respects minSampleInterval", () => {
    const recorder = new MotionRecorder("pin1", { minSampleInterval: 50 });

    recorder.start(0, 0);

    // Add samples rapidly
    vi.advanceTimersByTime(10);
    recorder.addSample(1, 1);

    vi.advanceTimersByTime(10);
    recorder.addSample(2, 2); // Should be ignored (< 50ms since last)

    vi.advanceTimersByTime(10);
    recorder.addSample(3, 3); // Should be ignored

    vi.advanceTimersByTime(50);
    recorder.addSample(4, 4); // Should be recorded (> 50ms)

    const motion = recorder.stop();

    // Should have: initial (0) + one at ~80ms (4,4)
    expect(motion.samples.length).toBe(2);
    expect(motion.samples[1].x).toBe(4);
  });

  it("stores recording speed", () => {
    const recorder = new MotionRecorder("pin1", { speed: 0.5 });
    recorder.start(0, 0);
    const motion = recorder.stop();

    expect(motion.recordingSpeed).toBe(0.5);
  });

  it("tracks duration correctly", () => {
    const recorder = new MotionRecorder("pin1", { minSampleInterval: 0 });

    recorder.start(0, 0);
    vi.advanceTimersByTime(500);
    recorder.addSample(50, 50);
    vi.advanceTimersByTime(500);
    recorder.addSample(100, 100);

    expect(recorder.duration).toBeCloseTo(1000, -1);
  });

  it("ignores samples after stop", () => {
    const recorder = new MotionRecorder("pin1", { minSampleInterval: 0 });

    recorder.start(0, 0);
    recorder.addSample(10, 10);
    const motion = recorder.stop();

    recorder.addSample(999, 999); // Should be ignored

    expect(motion.samples.length).toBe(2);
    expect(motion.samples[1].x).toBe(10);
  });
});

describe("processRecordedMotion (full pipeline)", () => {
  it("produces simplified keyframes from noisy input", () => {
    // Create noisy circular motion
    const cleanMotion = createCircularMotion(
      "pin1",
      { x: 100, y: 100 },
      50,
      2000,
      100,
    );
    const noisyMotion = addNoise(cleanMotion, 5);

    const keyframes = processRecordedMotion(noisyMotion, 30, 0, 50, 3);

    // Should have keyframes
    expect(keyframes.length).toBeGreaterThan(0);

    // Should be fewer than raw conversion (due to simplification)
    const rawKeyframes = convertMotionToKeyframes(noisyMotion, 30, 0);
    expect(keyframes.length).toBeLessThan(rawKeyframes.length);
  });
});

describe("getMotionBounds", () => {
  it("calculates correct bounds", () => {
    const motion = createTestMotion("pin1", [
      { time: 0, x: 10, y: 20 },
      { time: 100, x: 50, y: 60 },
      { time: 200, x: 30, y: 40 },
    ]);

    const bounds = getMotionBounds(motion);

    expect(bounds.minX).toBe(10);
    expect(bounds.maxX).toBe(50);
    expect(bounds.minY).toBe(20);
    expect(bounds.maxY).toBe(60);
    expect(bounds.width).toBe(40);
    expect(bounds.height).toBe(40);
  });

  it("handles empty motion", () => {
    const motion = createTestMotion("pin1", []);
    const bounds = getMotionBounds(motion);

    expect(bounds.width).toBe(0);
    expect(bounds.height).toBe(0);
  });
});

describe("getMotionPathLength", () => {
  it("calculates correct path length for straight line", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 0 },
      1000,
      10,
    );
    const length = getMotionPathLength(motion);

    expect(length).toBeCloseTo(100, 0);
  });

  it("calculates correct path length for diagonal", () => {
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 30, y: 40 },
      1000,
      10,
    );
    const length = getMotionPathLength(motion);

    expect(length).toBeCloseTo(50, 0); // 3-4-5 triangle
  });
});

describe("getMotionAverageSpeed", () => {
  it("calculates correct average speed", () => {
    // 100 pixels over 1000ms = 100 pixels/second
    const motion = createLinearMotion(
      "pin1",
      { x: 0, y: 0 },
      { x: 100, y: 0 },
      1000,
      10,
    );
    const speed = getMotionAverageSpeed(motion);

    expect(speed).toBeCloseTo(100, 0);
  });

  it("handles empty motion", () => {
    const motion = createTestMotion("pin1", []);
    const speed = getMotionAverageSpeed(motion);
    expect(speed).toBe(0);
  });
});
