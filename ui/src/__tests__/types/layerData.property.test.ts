/**
 * Property tests for ui/src/types/layerData.ts
 * Tests: createDefaultPoseKeypoints
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import { createDefaultPoseKeypoints, type PoseKeypoint } from "@/types/layerData";

// OpenPose 18-keypoint format indices
const POSE_KEYPOINT_NAMES = [
  "nose",           // 0
  "neck",           // 1
  "right_shoulder", // 2
  "right_elbow",    // 3
  "right_wrist",    // 4
  "left_shoulder",  // 5
  "left_elbow",     // 6
  "left_wrist",     // 7
  "right_hip",      // 8
  "right_knee",     // 9
  "right_ankle",    // 10
  "left_hip",       // 11
  "left_knee",      // 12
  "left_ankle",     // 13
  "right_eye",      // 14
  "left_eye",       // 15
  "right_ear",      // 16
  "left_ear",       // 17
];

describe("PROPERTY: createDefaultPoseKeypoints", () => {
  it("returns an array", () => {
    const result = createDefaultPoseKeypoints();
    expect(Array.isArray(result)).toBe(true);
  });

  it("returns exactly 18 keypoints (OpenPose format)", () => {
    const result = createDefaultPoseKeypoints();
    expect(result).toHaveLength(18);
  });

  it("each keypoint has x, y, and confidence properties", () => {
    const result = createDefaultPoseKeypoints();
    for (const kp of result) {
      expect(kp).toHaveProperty("x");
      expect(kp).toHaveProperty("y");
      expect(kp).toHaveProperty("confidence");
    }
  });

  it("all x values are in range [0, 1]", () => {
    const result = createDefaultPoseKeypoints();
    for (const kp of result) {
      expect(kp.x).toBeGreaterThanOrEqual(0);
      expect(kp.x).toBeLessThanOrEqual(1);
    }
  });

  it("all y values are in range [0, 1]", () => {
    const result = createDefaultPoseKeypoints();
    for (const kp of result) {
      expect(kp.y).toBeGreaterThanOrEqual(0);
      expect(kp.y).toBeLessThanOrEqual(1);
    }
  });

  it("all confidence values are 1 (fully confident defaults)", () => {
    const result = createDefaultPoseKeypoints();
    for (const kp of result) {
      expect(kp.confidence).toBe(1);
    }
  });

  it("nose (index 0) is at top center", () => {
    const result = createDefaultPoseKeypoints();
    expect(result[0].x).toBe(0.5);
    expect(result[0].y).toBe(0.1);
  });

  it("neck (index 1) is below nose", () => {
    const result = createDefaultPoseKeypoints();
    expect(result[1].y).toBeGreaterThan(result[0].y);
  });

  it("eyes (14, 15) are above nose", () => {
    const result = createDefaultPoseKeypoints();
    expect(result[14].y).toBeLessThan(result[0].y); // right_eye above nose
    expect(result[15].y).toBeLessThan(result[0].y); // left_eye above nose
  });

  it("left side keypoints have higher x than right side", () => {
    const result = createDefaultPoseKeypoints();
    
    // Shoulders
    expect(result[5].x).toBeGreaterThan(result[2].x); // left_shoulder > right_shoulder
    
    // Hips
    expect(result[11].x).toBeGreaterThan(result[8].x); // left_hip > right_hip
    
    // Eyes
    expect(result[15].x).toBeGreaterThan(result[14].x); // left_eye > right_eye
  });

  it("keypoints form valid body structure (head above body)", () => {
    const result = createDefaultPoseKeypoints();
    
    // Head keypoints
    const headYs = [result[0].y, result[14].y, result[15].y, result[16].y, result[17].y];
    const maxHeadY = Math.max(...headYs);
    
    // Body keypoints
    const bodyYs = [result[8].y, result[11].y]; // hips
    const minBodyY = Math.min(...bodyYs);
    
    // Head should be above hips
    expect(maxHeadY).toBeLessThan(minBodyY);
  });

  it("feet (ankles) are at bottom of body", () => {
    const result = createDefaultPoseKeypoints();
    
    // Ankles should have highest y values
    const ankleY = Math.max(result[10].y, result[13].y);
    
    // All other keypoints should have lower y
    for (let i = 0; i < result.length; i++) {
      if (i !== 10 && i !== 13) {
        expect(result[i].y).toBeLessThanOrEqual(ankleY);
      }
    }
  });

  it("is deterministic (same output every call)", () => {
    const result1 = createDefaultPoseKeypoints();
    const result2 = createDefaultPoseKeypoints();
    expect(result1).toEqual(result2);
  });

  it("returns a new array each call (no mutation risk)", () => {
    const result1 = createDefaultPoseKeypoints();
    const result2 = createDefaultPoseKeypoints();
    expect(result1).not.toBe(result2);
  });

  it("returned keypoints can be modified without affecting next call", () => {
    const result1 = createDefaultPoseKeypoints();
    result1[0].x = 999;
    
    const result2 = createDefaultPoseKeypoints();
    expect(result2[0].x).toBe(0.5); // Original value
  });
});
