/**
 * Security Utilities Tests
 * Tests for NaN/Infinity rejection in project validation
 */

import { describe, expect, it } from "vitest";
import { ValidationError, validateProjectStructure } from "@/utils/security";

describe("validateProjectStructure", () => {
  // Valid project structure for baseline
  const createValidProject = () => ({
    version: "1.0.0",
    compositions: {
      main: {
        id: "main",
        name: "Main Comp",
        settings: {
          width: 1920,
          height: 1080,
          frameCount: 81,
          fps: 16,
        },
        layers: [],
      },
    },
  });

  describe("accepts valid projects", () => {
    it("should accept a valid project structure", () => {
      const project = createValidProject();
      expect(() => validateProjectStructure(project)).not.toThrow();
    });
  });

  describe("rejects NaN values", () => {
    it("should reject NaN width", () => {
      const project = createValidProject();
      project.compositions.main.settings.width = NaN;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
      expect(() => validateProjectStructure(project)).toThrow(
        /width.*positive finite/i,
      );
    });

    it("should reject NaN height", () => {
      const project = createValidProject();
      project.compositions.main.settings.height = NaN;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
    });

    it("should reject NaN frameCount", () => {
      const project = createValidProject();
      project.compositions.main.settings.frameCount = NaN;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
    });

    it("should reject NaN fps", () => {
      const project = createValidProject();
      project.compositions.main.settings.fps = NaN;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
    });
  });

  describe("rejects Infinity values", () => {
    it("should reject Infinity width", () => {
      const project = createValidProject();
      project.compositions.main.settings.width = Infinity;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
    });

    it("should reject -Infinity height", () => {
      const project = createValidProject();
      project.compositions.main.settings.height = -Infinity;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
    });
  });

  describe("rejects zero and negative values", () => {
    it("should reject zero width", () => {
      const project = createValidProject();
      project.compositions.main.settings.width = 0;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
    });

    it("should reject negative height", () => {
      const project = createValidProject();
      project.compositions.main.settings.height = -100;
      expect(() => validateProjectStructure(project)).toThrow(ValidationError);
    });
  });

  describe("handles missing fields gracefully", () => {
    it("should not throw if optional numeric field is undefined", () => {
      const project = createValidProject();
      delete (project.compositions.main.settings as any).fps;
      // fps is optional, should not throw
      expect(() => validateProjectStructure(project)).not.toThrow();
    });
  });
});
