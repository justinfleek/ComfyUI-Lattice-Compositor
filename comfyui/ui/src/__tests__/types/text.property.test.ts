/**
 * Property tests for ui/src/types/text.ts
 * Tests: createDefaultTextData
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import { createDefaultTextData } from "@/types/text";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// createDefaultTextData TESTS
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultTextData", () => {
  it("returns TextData with all required properties", () => {
    const textData = createDefaultTextData();
    
    // Core text properties
    expect(textData).toHaveProperty("text");
    expect(textData).toHaveProperty("fontFamily");
    expect(textData).toHaveProperty("fontSize");
    expect(textData).toHaveProperty("fontWeight");
    expect(textData).toHaveProperty("fontStyle");
    expect(textData).toHaveProperty("fill");
    expect(textData).toHaveProperty("stroke");
    expect(textData).toHaveProperty("strokeWidth");
    
    // Character properties
    expect(textData).toHaveProperty("tracking");
    expect(textData).toHaveProperty("lineSpacing");
    expect(textData).toHaveProperty("lineAnchor");
    expect(textData).toHaveProperty("characterOffset");
    expect(textData).toHaveProperty("characterValue");
    expect(textData).toHaveProperty("blur");
    
    // Paragraph properties
    expect(textData).toHaveProperty("letterSpacing");
    expect(textData).toHaveProperty("lineHeight");
    expect(textData).toHaveProperty("textAlign");
    
    // Path options
    expect(textData).toHaveProperty("pathLayerId");
    expect(textData).toHaveProperty("pathReversed");
    expect(textData).toHaveProperty("pathPerpendicularToPath");
    expect(textData).toHaveProperty("pathForceAlignment");
    expect(textData).toHaveProperty("pathFirstMargin");
    expect(textData).toHaveProperty("pathLastMargin");
    expect(textData).toHaveProperty("pathOffset");
    expect(textData).toHaveProperty("pathAlign");
    
    // More options
    expect(textData).toHaveProperty("anchorPointGrouping");
    expect(textData).toHaveProperty("groupingAlignment");
    expect(textData).toHaveProperty("fillAndStroke");
    expect(textData).toHaveProperty("interCharacterBlending");
    expect(textData).toHaveProperty("perCharacter3D");
  });

  it("text defaults to 'Text'", () => {
    const textData = createDefaultTextData();
    expect(textData.text).toBe("Text");
  });

  it("fontFamily defaults to 'Arial'", () => {
    const textData = createDefaultTextData();
    expect(textData.fontFamily).toBe("Arial");
  });

  it("fontSize defaults to 72", () => {
    const textData = createDefaultTextData();
    expect(textData.fontSize).toBe(72);
  });

  it("fontWeight defaults to 'normal'", () => {
    const textData = createDefaultTextData();
    expect(textData.fontWeight).toBe("normal");
  });

  it("fontStyle defaults to 'normal'", () => {
    const textData = createDefaultTextData();
    expect(textData.fontStyle).toBe("normal");
  });

  it("fill defaults to white (#ffffff)", () => {
    const textData = createDefaultTextData();
    expect(textData.fill).toBe("#ffffff");
  });

  it("stroke defaults to empty string", () => {
    const textData = createDefaultTextData();
    expect(textData.stroke).toBe("");
  });

  it("strokeWidth defaults to 0", () => {
    const textData = createDefaultTextData();
    expect(textData.strokeWidth).toBe(0);
  });

  it("tracking defaults to 0", () => {
    const textData = createDefaultTextData();
    expect(textData.tracking).toBe(0);
  });

  it("lineSpacing defaults to 1.2", () => {
    const textData = createDefaultTextData();
    expect(textData.lineSpacing).toBe(1.2);
  });

  it("lineAnchor defaults to 50", () => {
    const textData = createDefaultTextData();
    expect(textData.lineAnchor).toBe(50);
  });

  it("blur defaults to { x: 0, y: 0 }", () => {
    const textData = createDefaultTextData();
    expect(textData.blur).toEqual({ x: 0, y: 0 });
  });

  it("textAlign defaults to 'center'", () => {
    const textData = createDefaultTextData();
    expect(textData.textAlign).toBe("center");
  });

  it("pathLayerId defaults to empty string", () => {
    const textData = createDefaultTextData();
    expect(textData.pathLayerId).toBe("");
  });

  it("pathReversed defaults to false", () => {
    const textData = createDefaultTextData();
    expect(textData.pathReversed).toBe(false);
  });

  it("pathPerpendicularToPath defaults to true", () => {
    const textData = createDefaultTextData();
    expect(textData.pathPerpendicularToPath).toBe(true);
  });

  it("pathAlign defaults to 'center'", () => {
    const textData = createDefaultTextData();
    expect(textData.pathAlign).toBe("center");
  });

  it("anchorPointGrouping defaults to 'character'", () => {
    const textData = createDefaultTextData();
    expect(textData.anchorPointGrouping).toBe("character");
  });

  it("groupingAlignment defaults to { x: 50, y: 50 }", () => {
    const textData = createDefaultTextData();
    expect(textData.groupingAlignment).toEqual({ x: 50, y: 50 });
  });

  it("fillAndStroke defaults to 'fill-over-stroke'", () => {
    const textData = createDefaultTextData();
    expect(textData.fillAndStroke).toBe("fill-over-stroke");
  });

  it("interCharacterBlending defaults to 'normal'", () => {
    const textData = createDefaultTextData();
    expect(textData.interCharacterBlending).toBe("normal");
  });

  it("perCharacter3D defaults to false", () => {
    const textData = createDefaultTextData();
    expect(textData.perCharacter3D).toBe(false);
  });

  it("is deterministic (same values every call)", () => {
    const t1 = createDefaultTextData();
    const t2 = createDefaultTextData();
    
    expect(t1).toEqual(t2);
  });

  it("returns new object each call (no shared reference)", () => {
    const t1 = createDefaultTextData();
    const t2 = createDefaultTextData();
    
    expect(t1).not.toBe(t2);
    expect(t1.blur).not.toBe(t2.blur);
    expect(t1.groupingAlignment).not.toBe(t2.groupingAlignment);
  });
});
