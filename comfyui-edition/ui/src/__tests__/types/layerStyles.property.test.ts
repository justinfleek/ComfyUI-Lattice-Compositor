/**
 * Property tests for ui/src/types/layerStyles.ts
 * Tests: createStyleProperty, createRGBA, createDefaultLayerStyles,
 *        createDefaultDropShadow, createDefaultInnerShadow, createDefaultOuterGlow,
 *        createDefaultInnerGlow, createDefaultBevelEmboss, createDefaultSatin,
 *        createDefaultColorOverlay, createDefaultGradientOverlay, createDefaultStroke,
 *        createDefaultBlendingOptions, createDefaultGlobalLight
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createStyleProperty,
  createRGBA,
  createDefaultLayerStyles,
  createDefaultDropShadow,
  createDefaultInnerShadow,
  createDefaultOuterGlow,
  createDefaultInnerGlow,
  createDefaultBevelEmboss,
  createDefaultSatin,
  createDefaultColorOverlay,
  createDefaultGradientOverlay,
  createDefaultStroke,
  createDefaultBlendingOptions,
  createDefaultGlobalLight,
} from "@/types/layerStyles";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// createStyleProperty TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createStyleProperty", () => {
  it("returns AnimatableProperty with correct structure", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.double({ min: -1000, max: 1000, noNaN: true }),
        (name, value) => {
          const prop = createStyleProperty(name, value);
          
          expect(prop).toHaveProperty("id");
          expect(prop).toHaveProperty("name");
          expect(prop).toHaveProperty("type");
          expect(prop).toHaveProperty("value");
          expect(prop).toHaveProperty("animated");
          expect(prop).toHaveProperty("keyframes");
        }
      )
    );
  });

  it("name matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.double({ min: -1000, max: 1000, noNaN: true }),
        (name, value) => {
          const prop = createStyleProperty(name, value);
          expect(prop.name).toBe(name);
        }
      )
    );
  });

  it("value matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.double({ min: -1000, max: 1000, noNaN: true }),
        (name, value) => {
          const prop = createStyleProperty(name, value);
          expect(prop.value).toBe(value);
        }
      )
    );
  });

  it("defaults to not animated", () => {
    const prop = createStyleProperty("test", 100);
    expect(prop.animated).toBe(false);
    expect(prop.keyframes).toEqual([]);
  });

  it("respects type parameter", () => {
    const numProp = createStyleProperty("num", 100, "number");
    expect(numProp.type).toBe("number");
    
    const colorProp = createStyleProperty("color", { r: 255, g: 0, b: 0, a: 1 }, "color");
    expect(colorProp.type).toBe("color");
    
    const posProp = createStyleProperty("pos", { x: 0, y: 0 }, "position");
    expect(posProp.type).toBe("position");
  });

  it("id includes name for differentiation", () => {
    // Note: Date.now() may produce same timestamp in tight loops
    // But different names ensure uniqueness within a single style
    const prop1 = createStyleProperty("opacity", 100);
    const prop2 = createStyleProperty("color", { r: 0, g: 0, b: 0, a: 1 });
    
    expect(prop1.id).toContain("opacity");
    expect(prop2.id).toContain("color");
    expect(prop1.id).not.toBe(prop2.id);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createRGBA TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createRGBA", () => {
  it("returns RGBA with correct values", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 0, max: 255 }),
        fc.integer({ min: 0, max: 255 }),
        fc.integer({ min: 0, max: 255 }),
        fc.double({ min: 0, max: 1, noNaN: true }),
        (r, g, b, a) => {
          const rgba = createRGBA(r, g, b, a);
          expect(rgba.r).toBe(r);
          expect(rgba.g).toBe(g);
          expect(rgba.b).toBe(b);
          expect(rgba.a).toBe(a);
        }
      )
    );
  });

  it("alpha defaults to 1 when not provided", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 0, max: 255 }),
        fc.integer({ min: 0, max: 255 }),
        fc.integer({ min: 0, max: 255 }),
        (r, g, b) => {
          const rgba = createRGBA(r, g, b);
          expect(rgba.a).toBe(1);
        }
      )
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultLayerStyles TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultLayerStyles", () => {
  it("returns LayerStyles with enabled false", () => {
    const styles = createDefaultLayerStyles();
    expect(styles.enabled).toBe(false);
  });

  it("returns new object each call", () => {
    const s1 = createDefaultLayerStyles();
    const s2 = createDefaultLayerStyles();
    expect(s1).not.toBe(s2);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultDropShadow TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultDropShadow", () => {
  it("returns DropShadowStyle with all properties", () => {
    const shadow = createDefaultDropShadow();
    
    expect(shadow).toHaveProperty("enabled");
    expect(shadow).toHaveProperty("blendMode");
    expect(shadow).toHaveProperty("opacity");
    expect(shadow).toHaveProperty("color");
    expect(shadow).toHaveProperty("angle");
    expect(shadow).toHaveProperty("useGlobalLight");
    expect(shadow).toHaveProperty("distance");
    expect(shadow).toHaveProperty("spread");
    expect(shadow).toHaveProperty("size");
    expect(shadow).toHaveProperty("noise");
    expect(shadow).toHaveProperty("layerKnocksOut");
  });

  it("has correct default values", () => {
    const shadow = createDefaultDropShadow();
    
    expect(shadow.enabled).toBe(true);
    expect(shadow.blendMode).toBe("multiply");
    expect(shadow.opacity.value).toBe(75);
    expect(shadow.color.value).toEqual({ r: 0, g: 0, b: 0, a: 1 });
    expect(shadow.angle.value).toBe(120);
    expect(shadow.useGlobalLight).toBe(true);
    expect(shadow.distance.value).toBe(5);
    expect(shadow.spread.value).toBe(0);
    expect(shadow.size.value).toBe(5);
    expect(shadow.noise.value).toBe(0);
    expect(shadow.layerKnocksOut).toBe(true);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultInnerShadow TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultInnerShadow", () => {
  it("returns InnerShadowStyle with all properties", () => {
    const shadow = createDefaultInnerShadow();
    
    expect(shadow).toHaveProperty("enabled");
    expect(shadow).toHaveProperty("blendMode");
    expect(shadow).toHaveProperty("opacity");
    expect(shadow).toHaveProperty("color");
    expect(shadow).toHaveProperty("angle");
    expect(shadow).toHaveProperty("distance");
    expect(shadow).toHaveProperty("choke");
    expect(shadow).toHaveProperty("size");
    expect(shadow).toHaveProperty("noise");
  });

  it("has choke instead of spread (unlike drop shadow)", () => {
    const shadow = createDefaultInnerShadow();
    expect(shadow.choke).toBeDefined();
    expect(shadow.choke.value).toBe(0);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultOuterGlow TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultOuterGlow", () => {
  it("returns OuterGlowStyle with all properties", () => {
    const glow = createDefaultOuterGlow();
    
    expect(glow).toHaveProperty("enabled");
    expect(glow).toHaveProperty("blendMode");
    expect(glow).toHaveProperty("opacity");
    expect(glow).toHaveProperty("color");
    expect(glow).toHaveProperty("technique");
    expect(glow).toHaveProperty("spread");
    expect(glow).toHaveProperty("size");
    expect(glow).toHaveProperty("range");
    expect(glow).toHaveProperty("jitter");
    expect(glow).toHaveProperty("noise");
  });

  it("uses screen blend mode for glow effect", () => {
    const glow = createDefaultOuterGlow();
    expect(glow.blendMode).toBe("screen");
  });

  it("has warm yellow default color", () => {
    const glow = createDefaultOuterGlow();
    expect(glow.color.value).toEqual({ r: 255, g: 255, b: 190, a: 1 });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultInnerGlow TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultInnerGlow", () => {
  it("returns InnerGlowStyle with source property", () => {
    const glow = createDefaultInnerGlow();
    expect(glow.source).toBe("edge");
  });

  it("has choke property (unlike outer glow)", () => {
    const glow = createDefaultInnerGlow();
    expect(glow.choke).toBeDefined();
    expect(glow.choke.value).toBe(0);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultBevelEmboss TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultBevelEmboss", () => {
  it("returns BevelEmbossStyle with all properties", () => {
    const bevel = createDefaultBevelEmboss();
    
    expect(bevel).toHaveProperty("enabled");
    expect(bevel).toHaveProperty("style");
    expect(bevel).toHaveProperty("technique");
    expect(bevel).toHaveProperty("depth");
    expect(bevel).toHaveProperty("direction");
    expect(bevel).toHaveProperty("size");
    expect(bevel).toHaveProperty("soften");
    expect(bevel).toHaveProperty("angle");
    expect(bevel).toHaveProperty("altitude");
    expect(bevel).toHaveProperty("highlightMode");
    expect(bevel).toHaveProperty("highlightColor");
    expect(bevel).toHaveProperty("highlightOpacity");
    expect(bevel).toHaveProperty("shadowMode");
    expect(bevel).toHaveProperty("shadowColor");
    expect(bevel).toHaveProperty("shadowOpacity");
  });

  it("has correct default style", () => {
    const bevel = createDefaultBevelEmboss();
    expect(bevel.style).toBe("inner-bevel");
    expect(bevel.technique).toBe("smooth");
    expect(bevel.direction).toBe("up");
  });

  it("highlight uses screen mode, shadow uses multiply", () => {
    const bevel = createDefaultBevelEmboss();
    expect(bevel.highlightMode).toBe("screen");
    expect(bevel.shadowMode).toBe("multiply");
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultSatin TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultSatin", () => {
  it("returns SatinStyle with all properties", () => {
    const satin = createDefaultSatin();
    
    expect(satin).toHaveProperty("enabled");
    expect(satin).toHaveProperty("blendMode");
    expect(satin).toHaveProperty("opacity");
    expect(satin).toHaveProperty("color");
    expect(satin).toHaveProperty("angle");
    expect(satin).toHaveProperty("distance");
    expect(satin).toHaveProperty("size");
    expect(satin).toHaveProperty("invert");
  });

  it("has correct default values", () => {
    const satin = createDefaultSatin();
    expect(satin.opacity.value).toBe(50);
    expect(satin.angle.value).toBe(19);
    expect(satin.distance.value).toBe(11);
    expect(satin.size.value).toBe(14);
    expect(satin.invert).toBe(true);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultColorOverlay TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultColorOverlay", () => {
  it("returns ColorOverlayStyle with all properties", () => {
    const overlay = createDefaultColorOverlay();
    
    expect(overlay).toHaveProperty("enabled");
    expect(overlay).toHaveProperty("blendMode");
    expect(overlay).toHaveProperty("opacity");
    expect(overlay).toHaveProperty("color");
  });

  it("has red default color", () => {
    const overlay = createDefaultColorOverlay();
    expect(overlay.color.value).toEqual({ r: 255, g: 0, b: 0, a: 1 });
  });

  it("has normal blend mode at 100% opacity", () => {
    const overlay = createDefaultColorOverlay();
    expect(overlay.blendMode).toBe("normal");
    expect(overlay.opacity.value).toBe(100);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultGradientOverlay TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultGradientOverlay", () => {
  it("returns GradientOverlayStyle with all properties", () => {
    const overlay = createDefaultGradientOverlay();
    
    expect(overlay).toHaveProperty("enabled");
    expect(overlay).toHaveProperty("blendMode");
    expect(overlay).toHaveProperty("opacity");
    expect(overlay).toHaveProperty("gradient");
    expect(overlay).toHaveProperty("style");
    expect(overlay).toHaveProperty("angle");
    expect(overlay).toHaveProperty("scale");
    expect(overlay).toHaveProperty("alignWithLayer");
    expect(overlay).toHaveProperty("reverse");
    expect(overlay).toHaveProperty("offset");
  });

  it("has linear gradient from black to white", () => {
    const overlay = createDefaultGradientOverlay();
    const gradient = overlay.gradient.value;
    
    expect(gradient.type).toBe("linear");
    expect(gradient.stops.length).toBe(2);
    expect(gradient.stops[0].color).toEqual({ r: 0, g: 0, b: 0, a: 1 });
    expect(gradient.stops[1].color).toEqual({ r: 255, g: 255, b: 255, a: 1 });
  });

  it("has correct default angle and scale", () => {
    const overlay = createDefaultGradientOverlay();
    expect(overlay.angle.value).toBe(90);
    expect(overlay.scale.value).toBe(100);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultStroke TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultStroke", () => {
  it("returns StrokeStyle with all properties", () => {
    const stroke = createDefaultStroke();
    
    expect(stroke).toHaveProperty("enabled");
    expect(stroke).toHaveProperty("blendMode");
    expect(stroke).toHaveProperty("opacity");
    expect(stroke).toHaveProperty("color");
    expect(stroke).toHaveProperty("fillType");
    expect(stroke).toHaveProperty("size");
    expect(stroke).toHaveProperty("position");
  });

  it("has correct default values", () => {
    const stroke = createDefaultStroke();
    
    expect(stroke.enabled).toBe(true);
    expect(stroke.blendMode).toBe("normal");
    expect(stroke.fillType).toBe("color");
    expect(stroke.size.value).toBe(3);
    expect(stroke.position).toBe("outside");
  });

  it("has red default color", () => {
    const stroke = createDefaultStroke();
    expect(stroke.color.value).toEqual({ r: 255, g: 0, b: 0, a: 1 });
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultBlendingOptions TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultBlendingOptions", () => {
  it("returns StyleBlendingOptions with all properties", () => {
    const options = createDefaultBlendingOptions();
    
    expect(options).toHaveProperty("fillOpacity");
    expect(options).toHaveProperty("blendInteriorStylesAsGroup");
    expect(options).toHaveProperty("blendClippedLayersAsGroup");
    expect(options).toHaveProperty("transparencyShapesLayer");
    expect(options).toHaveProperty("layerMaskHidesEffects");
    expect(options).toHaveProperty("vectorMaskHidesEffects");
  });

  it("has correct default values", () => {
    const options = createDefaultBlendingOptions();
    
    expect(options.fillOpacity.value).toBe(100);
    expect(options.blendInteriorStylesAsGroup).toBe(false);
    expect(options.blendClippedLayersAsGroup).toBe(true);
    expect(options.transparencyShapesLayer).toBe(true);
    expect(options.layerMaskHidesEffects).toBe(false);
    expect(options.vectorMaskHidesEffects).toBe(false);
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createDefaultGlobalLight TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createDefaultGlobalLight", () => {
  it("returns GlobalLightSettings with angle and altitude", () => {
    const light = createDefaultGlobalLight();
    
    expect(light).toHaveProperty("angle");
    expect(light).toHaveProperty("altitude");
  });

  it("has correct default values (120°, 30°)", () => {
    const light = createDefaultGlobalLight();
    
    expect(light.angle.value).toBe(120);
    expect(light.altitude.value).toBe(30);
  });
});
