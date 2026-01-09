/**
 * Property tests for ui/src/types/templateBuilder.ts
 * Tests: createDefaultTemplateConfig, createExpressionControl,
 *        createExposedProperty, createPropertyGroup, createTemplateComment
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createDefaultTemplateConfig,
  createExpressionControl,
  createExposedProperty,
  createPropertyGroup,
  createTemplateComment,
  type ExpressionControlType,
  type ExposedPropertyType,
} from "@/types/templateBuilder";

// ============================================================
// ARBITRARIES
// ============================================================

const expressionControlTypeArb = fc.constantFrom(
  "slider", "checkbox", "dropdown", "color", "point", "angle"
) as fc.Arbitrary<ExpressionControlType>;

const exposedPropertyTypeArb = fc.constantFrom(
  "number", "position", "color", "boolean", "dropdown", "text"
) as fc.Arbitrary<ExposedPropertyType>;

// ============================================================
// createDefaultTemplateConfig TESTS
// ============================================================

describe("PROPERTY: createDefaultTemplateConfig", () => {
  it("returns TemplateConfig with all required properties", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 50 }),
        fc.string({ minLength: 1, maxLength: 50 }),
        (compId, compName) => {
          const config = createDefaultTemplateConfig(compId, compName);
          
          expect(config).toHaveProperty("name");
          expect(config).toHaveProperty("masterCompositionId");
          expect(config).toHaveProperty("exposedProperties");
          expect(config).toHaveProperty("groups");
          expect(config).toHaveProperty("comments");
          expect(config).toHaveProperty("posterFrame");
          expect(config).toHaveProperty("exportSettings");
          expect(config).toHaveProperty("created");
          expect(config).toHaveProperty("modified");
        }
      )
    );
  });

  it("name matches compositionName input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 50 }),
        fc.string({ minLength: 1, maxLength: 50 }),
        (compId, compName) => {
          const config = createDefaultTemplateConfig(compId, compName);
          expect(config.name).toBe(compName);
        }
      )
    );
  });

  it("masterCompositionId matches compositionId input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 50 }),
        fc.string({ minLength: 1, maxLength: 50 }),
        (compId, compName) => {
          const config = createDefaultTemplateConfig(compId, compName);
          expect(config.masterCompositionId).toBe(compId);
        }
      )
    );
  });

  it("starts with empty arrays", () => {
    const config = createDefaultTemplateConfig("comp1", "Test Comp");
    expect(config.exposedProperties).toEqual([]);
    expect(config.groups).toEqual([]);
    expect(config.comments).toEqual([]);
  });

  it("posterFrame defaults to 0", () => {
    const config = createDefaultTemplateConfig("comp1", "Test Comp");
    expect(config.posterFrame).toBe(0);
  });

  it("exportSettings has correct defaults", () => {
    const config = createDefaultTemplateConfig("comp1", "Test Comp");
    expect(config.exportSettings.includeFonts).toBe(true);
    expect(config.exportSettings.includeMedia).toBe(true);
    expect(config.exportSettings.allowDurationChange).toBe(false);
    expect(config.exportSettings.posterQuality).toBe("high");
  });

  it("created and modified are ISO date strings", () => {
    const config = createDefaultTemplateConfig("comp1", "Test Comp");
    expect(() => new Date(config.created)).not.toThrow();
    expect(() => new Date(config.modified)).not.toThrow();
  });
});

// ============================================================
// createExpressionControl TESTS
// ============================================================

describe("PROPERTY: createExpressionControl", () => {
  it("returns ExpressionControl with all required properties", () => {
    fc.assert(
      fc.property(
        expressionControlTypeArb,
        fc.string({ minLength: 1, maxLength: 30 }),
        (type, name) => {
          const control = createExpressionControl(type, name);
          
          expect(control).toHaveProperty("id");
          expect(control).toHaveProperty("name");
          expect(control).toHaveProperty("type");
          expect(control).toHaveProperty("value");
          expect(control).toHaveProperty("config");
          expect(control).toHaveProperty("expanded");
        }
      )
    );
  });

  it("type matches input", () => {
    fc.assert(
      fc.property(
        expressionControlTypeArb,
        fc.string({ minLength: 1, maxLength: 30 }),
        (type, name) => {
          const control = createExpressionControl(type, name);
          expect(control.type).toBe(type);
        }
      )
    );
  });

  it("name matches input", () => {
    fc.assert(
      fc.property(
        expressionControlTypeArb,
        fc.string({ minLength: 1, maxLength: 30 }),
        (type, name) => {
          const control = createExpressionControl(type, name);
          expect(control.name).toBe(name);
        }
      )
    );
  });

  it("expanded defaults to true", () => {
    fc.assert(
      fc.property(
        expressionControlTypeArb,
        fc.string({ minLength: 1, maxLength: 30 }),
        (type, name) => {
          const control = createExpressionControl(type, name);
          expect(control.expanded).toBe(true);
        }
      )
    );
  });

  it("slider type has correct default config", () => {
    const control = createExpressionControl("slider", "Test Slider");
    expect(control.value.value).toBe(0);
    expect(control.config.min).toBe(0);
    expect(control.config.max).toBe(100);
    expect(control.config.step).toBe(1);
  });

  it("checkbox type has boolean default", () => {
    const control = createExpressionControl("checkbox", "Test Checkbox");
    expect(control.value.value).toBe(false);
  });

  it("dropdown type has options array", () => {
    const control = createExpressionControl("dropdown", "Test Dropdown");
    expect(control.value.value).toBe(0);
    expect(control.config.options).toBeDefined();
    expect(Array.isArray(control.config.options)).toBe(true);
  });

  it("color type has RGBA default", () => {
    const control = createExpressionControl("color", "Test Color");
    expect(control.value.value).toEqual({ r: 1, g: 1, b: 1, a: 1 });
    expect(control.config.includeAlpha).toBe(true);
  });

  it("point type has x,y default", () => {
    const control = createExpressionControl("point", "Test Point");
    expect(control.value.value).toEqual({ x: 0, y: 0 });
    expect(control.config.is3D).toBe(false);
  });

  it("angle type has 0 default", () => {
    const control = createExpressionControl("angle", "Test Angle");
    expect(control.value.value).toBe(0);
    expect(control.config.displayUnit).toBe("degrees");
  });

  it("value type matches control type", () => {
    const slider = createExpressionControl("slider", "Slider");
    expect(slider.value.type).toBe("number");
    
    const color = createExpressionControl("color", "Color");
    expect(color.value.type).toBe("color");
    
    const point = createExpressionControl("point", "Point");
    expect(point.value.type).toBe("position");
  });
});

// ============================================================
// createExposedProperty TESTS
// ============================================================

describe("PROPERTY: createExposedProperty", () => {
  it("returns ExposedProperty with all required properties", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.string({ minLength: 1, maxLength: 50 }),
        fc.string({ minLength: 1, maxLength: 30 }),
        exposedPropertyTypeArb,
        fc.integer({ min: 0, max: 100 }),
        (layerId, propertyPath, name, type, order) => {
          const prop = createExposedProperty(layerId, propertyPath, name, type, order);
          
          expect(prop).toHaveProperty("id");
          expect(prop).toHaveProperty("name");
          expect(prop).toHaveProperty("type");
          expect(prop).toHaveProperty("sourceLayerId");
          expect(prop).toHaveProperty("sourcePropertyPath");
          expect(prop).toHaveProperty("order");
          expect(prop).toHaveProperty("config");
        }
      )
    );
  });

  it("sourceLayerId matches layerId input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.string({ minLength: 1, maxLength: 50 }),
        fc.string({ minLength: 1, maxLength: 30 }),
        exposedPropertyTypeArb,
        fc.integer({ min: 0, max: 100 }),
        (layerId, propertyPath, name, type, order) => {
          const prop = createExposedProperty(layerId, propertyPath, name, type, order);
          expect(prop.sourceLayerId).toBe(layerId);
        }
      )
    );
  });

  it("sourcePropertyPath matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.string({ minLength: 1, maxLength: 50 }),
        fc.string({ minLength: 1, maxLength: 30 }),
        exposedPropertyTypeArb,
        fc.integer({ min: 0, max: 100 }),
        (layerId, propertyPath, name, type, order) => {
          const prop = createExposedProperty(layerId, propertyPath, name, type, order);
          expect(prop.sourcePropertyPath).toBe(propertyPath);
        }
      )
    );
  });

  it("order matches input", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 0, max: 100 }),
        (order) => {
          const prop = createExposedProperty("layer1", "transform.position", "Position", "point", order);
          expect(prop.order).toBe(order);
        }
      )
    );
  });

  it("config is empty object by default", () => {
    const prop = createExposedProperty("layer1", "transform.position", "Position", "position", 0);
    expect(prop.config).toEqual({});
  });

  it("id starts with exp_ prefix", () => {
    const prop = createExposedProperty("layer1", "transform.position", "Position", "position", 0);
    expect(prop.id).toMatch(/^exp_/);
  });
});

// ============================================================
// createPropertyGroup TESTS
// ============================================================

describe("PROPERTY: createPropertyGroup", () => {
  it("returns PropertyGroup with all required properties", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.integer({ min: 0, max: 100 }),
        (name, order) => {
          const group = createPropertyGroup(name, order);
          
          expect(group).toHaveProperty("id");
          expect(group).toHaveProperty("name");
          expect(group).toHaveProperty("expanded");
          expect(group).toHaveProperty("order");
        }
      )
    );
  });

  it("name matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.integer({ min: 0, max: 100 }),
        (name, order) => {
          const group = createPropertyGroup(name, order);
          expect(group.name).toBe(name);
        }
      )
    );
  });

  it("order matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }),
        fc.integer({ min: 0, max: 100 }),
        (name, order) => {
          const group = createPropertyGroup(name, order);
          expect(group.order).toBe(order);
        }
      )
    );
  });

  it("expanded defaults to true", () => {
    const group = createPropertyGroup("Test Group", 0);
    expect(group.expanded).toBe(true);
  });

  it("id starts with grp_ prefix", () => {
    const group = createPropertyGroup("Test Group", 0);
    expect(group.id).toMatch(/^grp_/);
  });
});

// ============================================================
// createTemplateComment TESTS
// ============================================================

describe("PROPERTY: createTemplateComment", () => {
  it("returns TemplateComment with all required properties", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 200 }),
        fc.integer({ min: 0, max: 100 }),
        (text, order) => {
          const comment = createTemplateComment(text, order);
          
          expect(comment).toHaveProperty("id");
          expect(comment).toHaveProperty("text");
          expect(comment).toHaveProperty("order");
        }
      )
    );
  });

  it("text matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 200 }),
        fc.integer({ min: 0, max: 100 }),
        (text, order) => {
          const comment = createTemplateComment(text, order);
          expect(comment.text).toBe(text);
        }
      )
    );
  });

  it("order matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 200 }),
        fc.integer({ min: 0, max: 100 }),
        (text, order) => {
          const comment = createTemplateComment(text, order);
          expect(comment.order).toBe(order);
        }
      )
    );
  });

  it("id starts with cmt_ prefix", () => {
    const comment = createTemplateComment("Test comment", 0);
    expect(comment.id).toMatch(/^cmt_/);
  });
});
