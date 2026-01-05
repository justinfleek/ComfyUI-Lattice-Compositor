import { expect, type Page } from "@playwright/test";

export class CompositorHelper {
  constructor(private page: Page) {}

  // Project operations
  async newProject() {
    await this.page.keyboard.press("Control+Alt+n");
    await this.page.waitForSelector('[data-testid="project-panel"]');
  }

  async saveProject() {
    await this.page.keyboard.press("Control+s");
  }

  async importFile(_filePath: string) {
    await this.page.keyboard.press("Control+i");
    // Handle file dialog
  }

  // Composition operations
  async newComposition(
    name: string,
    width = 1920,
    height = 1080,
    fps = 16,
    duration = 5,
  ) {
    await this.page.keyboard.press("Control+n");
    await this.page.waitForSelector('[data-testid="comp-settings-dialog"]');
    await this.page.fill('[data-testid="comp-name"]', name);
    await this.page.fill('[data-testid="comp-width"]', String(width));
    await this.page.fill('[data-testid="comp-height"]', String(height));
    await this.page.fill('[data-testid="comp-fps"]', String(fps));
    await this.page.fill('[data-testid="comp-duration"]', String(duration));
    await this.page.click('[data-testid="comp-create-btn"]');
  }

  // Layer operations
  async newSolid(name?: string) {
    await this.page.keyboard.press("Control+y");
    if (name) {
      await this.page.fill('[data-testid="solid-name"]', name);
    }
    await this.page.click('[data-testid="solid-create-btn"]');
  }

  async newEffectLayer() {
    await this.page.keyboard.press("Control+Alt+y");
  }

  async newControlLayer() {
    await this.page.keyboard.press("Control+Alt+Shift+y");
  }

  async selectLayer(index: number) {
    await this.page.click(`[data-testid="layer-${index}"]`);
  }

  async duplicateLayer() {
    await this.page.keyboard.press("Control+d");
  }

  async deleteLayer() {
    await this.page.keyboard.press("Delete");
  }

  // Timeline navigation
  async goToStart() {
    await this.page.keyboard.press("Home");
  }

  async goToEnd() {
    await this.page.keyboard.press("End");
  }

  async goToFrame(frame: number) {
    await this.goToStart();
    for (let i = 0; i < frame; i++) {
      await this.page.keyboard.press("PageDown");
    }
  }

  async play() {
    await this.page.keyboard.press("Space");
  }

  async stop() {
    await this.page.keyboard.press("Space");
  }

  // Property shortcuts
  async isolatePosition() {
    await this.page.keyboard.press("p");
  }

  async isolateScale() {
    await this.page.keyboard.press("s");
  }

  async isolateRotation() {
    await this.page.keyboard.press("r");
  }

  async isolateOpacity() {
    await this.page.keyboard.press("t");
  }

  async revealAnimated() {
    await this.page.keyboard.press("u");
  }

  // Keyframes
  async toggleStopwatch(propertyName: string) {
    await this.page.click(`[data-testid="stopwatch-${propertyName}"]`);
  }

  async smoothEase() {
    await this.page.keyboard.press("F9");
  }

  // Undo/Redo
  async undo() {
    await this.page.keyboard.press("Control+z");
  }

  async redo() {
    await this.page.keyboard.press("Control+Shift+z");
  }

  // Assertions
  async expectLayerCount(count: number) {
    const layers = await this.page.locator('[data-testid^="layer-"]').count();
    expect(layers).toBe(count);
  }

  async expectPropertyValue(property: string, value: string | number) {
    const prop = this.page.locator(`[data-testid="property-${property}"]`);
    await expect(prop).toHaveValue(String(value));
  }

  // ============== CURVE EDITOR (Phase 10) ==============

  async toggleCurveEditor() {
    await this.page.click('[data-testid="curve-editor-toggle"]');
  }

  async setCurveEditorGraphType(type: "value" | "speed") {
    await this.page.click('[data-testid="graph-type-dropdown"]');
    await this.page.click(
      `text=${type === "value" ? "Value Graph" : "Speed Graph"}`,
    );
  }

  async separateDimensions(property: string) {
    await this.page.click(`[data-testid="property-${property}"]`, {
      button: "right",
    });
    await this.page.click("text=Separate Dimensions");
  }

  // ============== TEXT (Phase 12) ==============

  async newTextLayer(text: string) {
    await this.page.keyboard.press("t");
    await this.page.click('[data-testid="composition-panel"]');
    await this.page.keyboard.type(text);
    await this.page.keyboard.press("Escape");
  }

  async openCharacterPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click("text=Character");
  }

  async openParagraphPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click("text=Paragraph");
  }

  // ============== ALIGN (Phase 13) ==============

  async openAlignPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click("text=Align");
  }

  async alignHorizontalCenter() {
    await this.page.click('[data-testid="align-h-center"]');
  }

  async alignVerticalCenter() {
    await this.page.click('[data-testid="align-v-center"]');
  }

  async toggleGrid() {
    await this.page.keyboard.press("Control+'");
  }

  async toggleRulers() {
    await this.page.keyboard.press("Control+r");
  }

  async centerLayerInComp() {
    await this.page.keyboard.press("Control+Home");
  }

  // ============== EFFECTS (Phase 14) ==============

  async openEffectsPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click("text=Effects & Presets");
  }

  async searchEffects(query: string) {
    await this.page.fill('[data-testid="effects-search"]', query);
  }

  async applyEffect(effectName: string) {
    await this.page.dblclick(`[data-testid="effect-${effectName}"]`);
  }

  async toggleEffectEnabled(effectIndex: number) {
    await this.page.click(`[data-testid="effect-${effectIndex}-fx-toggle"]`);
  }

  // ============== PARENTING (Phase 15) ==============

  async setParent(childIndex: number, parentIndex: number | null) {
    await this.page.click(
      `[data-testid="layer-${childIndex}-parent-dropdown"]`,
    );
    if (parentIndex === null) {
      await this.page.click("text=None");
    } else {
      await this.page.click(`[data-testid="parent-option-${parentIndex}"]`);
    }
  }

  // ============== EXPRESSIONS (Phase 16) ==============

  async enableExpression(property: string) {
    await this.page.click(`[data-testid="stopwatch-${property}"]`, {
      modifiers: ["Alt"],
    });
  }

  async setExpression(property: string, expression: string) {
    const input = this.page.locator(`[data-testid="expression-${property}"]`);
    await input.fill(expression);
    await input.press("Enter");
  }

  // ============== NESTED COMPS (Phase 17) ==============

  async selectAllLayers() {
    await this.page.keyboard.press("Control+a");
  }

  async createNestedComp(name: string) {
    await this.page.keyboard.press("Control+Shift+c");
    await this.page.waitForSelector('[data-testid="nested-comp-dialog"]');
    await this.page.fill('[data-testid="nested-comp-name"]', name);
    await this.page.click('[data-testid="nested-comp-create-btn"]');
  }

  // ============== RENDER RANGE (Phase 18) ==============

  async setRenderRangeStart() {
    await this.page.keyboard.press("b");
  }

  async setRenderRangeEnd() {
    await this.page.keyboard.press("n");
  }

  // ============== EXPORT (Phase 19) ==============

  async addToRenderQueue() {
    await this.page.keyboard.press("Control+m");
  }

  // ============== PROPERTY VALUES ==============

  async setPropertyValue(property: string, value: string) {
    const input = this.page.locator(
      `[data-testid="property-${property}-value"]`,
    );
    await input.fill(value);
    await input.press("Enter");
  }

  async getPropertyValue(property: string): Promise<string> {
    return await this.page
      .locator(`[data-testid="property-${property}-value"]`)
      .inputValue();
  }

  // ============== DETERMINISM ==============

  async verifyDeterminism(properties: string[], targetFrame: number) {
    await this.goToFrame(targetFrame);
    const expected: Record<string, string> = {};
    for (const prop of properties) {
      expected[prop] = await this.getPropertyValue(prop);
    }

    await this.goToFrame(10);
    await this.goToFrame(60);
    await this.goToFrame(targetFrame);

    for (const prop of properties) {
      const actual = await this.getPropertyValue(prop);
      if (actual !== expected[prop]) {
        throw new Error(
          `Determinism failed for ${prop}: expected ${expected[prop]}, got ${actual}`,
        );
      }
    }
  }

  async revealAnimatedProperties() {
    await this.page.keyboard.press("u");
  }

  // ============== SHAPE LAYERS (Tutorial 02) ==============

  async newShapeLayer(name: string) {
    await this.page.click('[data-testid="layer-menu"]');
    await this.page.click("text=New");
    await this.page.click("text=Shape Layer");
    await this.selectLayer(0);
    await this.renameLayer(name);
  }

  async renameLayer(name: string) {
    await this.page.keyboard.press("Enter");
    await this.page.keyboard.type(name);
    await this.page.keyboard.press("Enter");
  }

  async expandShapeContents(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-expand"]`);
    await this.page.click(
      `[data-testid="layer-${layerIndex}-contents-expand"]`,
    );
  }

  async removeShapeFill(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-shape-fill"]`, {
      button: "right",
    });
    await this.page.click("text=Delete");
  }

  async setStrokeColor(layerIndex: number, color: string) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-stroke-color"]`,
      color,
    );
  }

  async setStrokeWidth(layerIndex: number, width: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-stroke-width"]`,
      String(width),
    );
  }

  async setStrokeLineCap(layerIndex: number, cap: "butt" | "round" | "square") {
    await this.page.click(`[data-testid="layer-${layerIndex}-stroke-linecap"]`);
    await this.page.click(`text=${cap}`);
  }

  async setStrokeLineJoin(
    layerIndex: number,
    join: "miter" | "round" | "bevel",
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-stroke-linejoin"]`,
    );
    await this.page.click(`text=${join}`);
  }

  // ============== TRIM PATHS (Tutorial 02) ==============

  async addTrimPaths(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-shape-add"]`);
    await this.page.click("text=Trim Paths");
  }

  async setTrimPathsStart(layerIndex: number, value: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-trimpath-start"]`,
      String(value),
    );
  }

  async setTrimPathsEnd(layerIndex: number, value: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-trimpath-end"]`,
      String(value),
    );
  }

  async setTrimPathsOffset(layerIndex: number, value: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-trimpath-offset"]`,
      String(value),
    );
  }

  async enableTrimPathsKeyframes(
    layerIndex: number,
    property: "start" | "end" | "offset",
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-trimpath-${property}-stopwatch"]`,
    );
  }

  // ============== EFFECTS - EXTENDED (Tutorial 02) ==============

  async addGradientRamp(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Gradient Ramp");
    await this.applyEffect("gradient-ramp");
  }

  async configureGradientRamp(options: {
    startX?: number;
    startY?: number;
    endX?: number;
    endY?: number;
    startColor?: string;
    endColor?: string;
    shape?: "linear" | "radial";
  }) {
    if (options.startX !== undefined) {
      await this.page.fill(
        '[data-testid="effect-gradient-ramp-start-x"]',
        String(options.startX),
      );
    }
    if (options.startY !== undefined) {
      await this.page.fill(
        '[data-testid="effect-gradient-ramp-start-y"]',
        String(options.startY),
      );
    }
    if (options.endX !== undefined) {
      await this.page.fill(
        '[data-testid="effect-gradient-ramp-end-x"]',
        String(options.endX),
      );
    }
    if (options.endY !== undefined) {
      await this.page.fill(
        '[data-testid="effect-gradient-ramp-end-y"]',
        String(options.endY),
      );
    }
    if (options.startColor) {
      await this.page.fill(
        '[data-testid="effect-gradient-ramp-start-color"]',
        options.startColor,
      );
    }
    if (options.endColor) {
      await this.page.fill(
        '[data-testid="effect-gradient-ramp-end-color"]',
        options.endColor,
      );
    }
    if (options.shape) {
      await this.page.click('[data-testid="effect-gradient-ramp-shape"]');
      await this.page.click(`text=${options.shape}`);
    }
  }

  async addFillEffect(layerIndex: number, color: string) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Fill");
    await this.applyEffect("fill");
    await this.page.fill('[data-testid="effect-fill-color"]', color);
  }

  async addTintEffect(
    layerIndex: number,
    mapBlack: string,
    mapWhite: string,
    amount: number,
  ) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Tint");
    await this.applyEffect("tint");
    await this.page.fill('[data-testid="effect-tint-map-black"]', mapBlack);
    await this.page.fill('[data-testid="effect-tint-map-white"]', mapWhite);
    await this.page.fill('[data-testid="effect-tint-amount"]', String(amount));
  }

  async configureGlow(
    effectIndex: number,
    options: {
      threshold?: number;
      radius?: number;
      intensity?: number;
      colorA?: string;
      colorB?: string;
    },
  ) {
    if (options.threshold !== undefined) {
      await this.page.fill(
        `[data-testid="effect-${effectIndex}-glow-threshold"]`,
        String(options.threshold),
      );
    }
    if (options.radius !== undefined) {
      await this.page.fill(
        `[data-testid="effect-${effectIndex}-glow-radius"]`,
        String(options.radius),
      );
    }
    if (options.intensity !== undefined) {
      await this.page.fill(
        `[data-testid="effect-${effectIndex}-glow-intensity"]`,
        String(options.intensity),
      );
    }
    if (options.colorA) {
      await this.page.fill(
        `[data-testid="effect-${effectIndex}-glow-color-a"]`,
        options.colorA,
      );
    }
    if (options.colorB) {
      await this.page.fill(
        `[data-testid="effect-${effectIndex}-glow-color-b"]`,
        options.colorB,
      );
    }
  }

  async addEchoEffect(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Echo");
    await this.applyEffect("echo");
  }

  async configureEcho(options: {
    echoTime?: number;
    numberOfEchoes?: number;
    startingIntensity?: number;
    decay?: number;
    operator?:
      | "add"
      | "maximum"
      | "screen"
      | "composite_back"
      | "composite_front";
  }) {
    if (options.echoTime !== undefined) {
      await this.page.fill(
        '[data-testid="effect-echo-time"]',
        String(options.echoTime),
      );
    }
    if (options.numberOfEchoes !== undefined) {
      await this.page.fill(
        '[data-testid="effect-echo-number"]',
        String(options.numberOfEchoes),
      );
    }
    if (options.startingIntensity !== undefined) {
      await this.page.fill(
        '[data-testid="effect-echo-intensity"]',
        String(options.startingIntensity),
      );
    }
    if (options.decay !== undefined) {
      await this.page.fill(
        '[data-testid="effect-echo-decay"]',
        String(options.decay),
      );
    }
    if (options.operator) {
      await this.page.click('[data-testid="effect-echo-operator"]');
      await this.page.click(`text=${options.operator}`);
    }
  }

  // ============== MOTION BLUR (Tutorial 02) ==============

  async enableLayerMotionBlur(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-motion-blur"]`);
  }

  async enableCompMotionBlur() {
    await this.page.click('[data-testid="comp-motion-blur-toggle"]');
  }

  async openCompositionSettings() {
    await this.page.keyboard.press("Control+k");
    await this.page.waitForSelector('[data-testid="comp-settings-dialog"]');
  }

  async configureMotionBlur(
    shutterAngle: number,
    shutterPhase: number,
    samples: number,
  ) {
    await this.openCompositionSettings();
    await this.page.fill(
      '[data-testid="comp-shutter-angle"]',
      String(shutterAngle),
    );
    await this.page.fill(
      '[data-testid="comp-shutter-phase"]',
      String(shutterPhase),
    );
    await this.page.fill(
      '[data-testid="comp-motion-blur-samples"]',
      String(samples),
    );
    await this.page.click('[data-testid="comp-settings-ok"]');
  }

  // ============== GRADIENT STROKE (Tutorial 02) ==============

  async addGradientStroke(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-shape-add"]`);
    await this.page.click("text=Gradient Stroke");
  }

  async configureGradientStroke(
    layerIndex: number,
    options: {
      type?: "linear" | "radial";
      startX?: number;
      startY?: number;
      endX?: number;
      endY?: number;
    },
  ) {
    if (options.type) {
      await this.page.click(
        `[data-testid="layer-${layerIndex}-gradient-stroke-type"]`,
      );
      await this.page.click(`text=${options.type}`);
    }
  }

  // ============== MASKS (Tutorial 02) ==============

  async addOvalMask(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.page.click('[data-testid="mask-tool-ellipse"]');
    await this.page.click('[data-testid="composition-panel"]');
  }

  async setMaskMode(
    layerIndex: number,
    maskIndex: number,
    mode: "add" | "subtract" | "intersect" | "difference",
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-mask-${maskIndex}-mode"]`,
    );
    await this.page.click(`text=${mode}`);
  }

  async setMaskFeather(layerIndex: number, maskIndex: number, feather: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-mask-${maskIndex}-feather"]`,
      String(feather),
    );
  }

  // ============== BLEND MODES (Tutorial 02) ==============

  async setBlendMode(layerIndex: number, mode: string) {
    await this.page.click(`[data-testid="layer-${layerIndex}-blend-mode"]`);
    await this.page.click(`text=${mode}`);
  }

  // ============== ADJUSTMENT LAYERS (Tutorial 02) ==============

  async newAdjustmentLayer(name: string) {
    await this.page.click('[data-testid="layer-menu"]');
    await this.page.click("text=New");
    await this.page.click("text=Adjustment Layer");
    await this.selectLayer(0);
    await this.renameLayer(name);
  }

  // ============== AUTO-ORIENT (Tutorial 02) ==============

  async enableAutoOrient(
    layerIndex: number,
    mode: "off" | "alongPath" | "towardsCamera",
  ) {
    await this.page.click(`[data-testid="layer-${layerIndex}"]`, {
      button: "right",
    });
    await this.page.click("text=Transform");
    await this.page.click("text=Auto-Orient");
    await this.page.click(`text=${mode}`);
  }

  // ============== COPY/PASTE (Tutorial 02) ==============

  async copy() {
    await this.page.keyboard.press("Control+c");
  }

  async paste() {
    await this.page.keyboard.press("Control+v");
  }

  async copyPathToPosition(sourceLayerIndex: number, targetLayerIndex: number) {
    await this.page.click(
      `[data-testid="layer-${sourceLayerIndex}-shape-path"]`,
    );
    await this.copy();
    await this.selectLayer(targetLayerIndex);
    await this.isolatePosition();
    await this.paste();
  }

  // ============== LAYER VISIBILITY/LOCK (Tutorial 02) ==============

  async toggleLayerVisibility(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-visibility"]`);
  }

  async toggleLayerLock() {
    await this.page.keyboard.press("Control+l");
  }

  // ============== MESH DEFORMATION (Tutorial 03) ==============

  async selectDeformPinTool() {
    await this.page.click('[data-testid="tool-deform-pin"]');
  }

  async selectStiffnessPinTool() {
    await this.page.click('[data-testid="tool-stiffness-pin"]');
  }

  async selectOverlapPinTool() {
    await this.page.click('[data-testid="tool-overlap-pin"]');
  }

  async selectBendPinTool() {
    await this.page.click('[data-testid="tool-bend-pin"]');
  }

  async selectAdvancedPinTool() {
    await this.page.click('[data-testid="tool-advanced-pin"]');
  }

  async placePinAtPosition(x: number, y: number) {
    const canvas = this.page.locator('[data-testid="composition-panel"]');
    await canvas.click({ position: { x, y } });
  }

  async renamePin(layerIndex: number, pinIndex: number, name: string) {
    await this.page.dblclick(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-name"]`,
    );
    await this.page.keyboard.type(name);
    await this.page.keyboard.press("Enter");
  }

  async getPinCount(layerIndex: number): Promise<number> {
    const pins = this.page.locator(`[data-testid^="layer-${layerIndex}-pin-"]`);
    return await pins.count();
  }

  async expectPinCount(layerIndex: number, count: number) {
    const actual = await this.getPinCount(layerIndex);
    expect(actual).toBe(count);
  }

  // ============== MESH CONFIGURATION (Tutorial 03) ==============

  async setMeshTriangleCount(layerIndex: number, count: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-mesh-triangles"]`,
      String(count),
    );
    await this.page.keyboard.press("Enter");
  }

  async setMeshExpansion(layerIndex: number, pixels: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-mesh-expansion"]`,
      String(pixels),
    );
    await this.page.keyboard.press("Enter");
  }

  async toggleMeshVisibility(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-mesh-show"]`);
  }

  async regenerateMesh(layerIndex: number) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-mesh-regenerate"]`,
    );
  }

  // ============== PIN PROPERTIES (Tutorial 03) ==============

  async selectPin(layerIndex: number, pinIndex: number) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}"]`,
    );
  }

  async movePinTo(layerIndex: number, pinIndex: number, x: number, y: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-x"]`,
      String(x),
    );
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-y"]`,
      String(y),
    );
  }

  async setStiffnessAmount(
    layerIndex: number,
    pinIndex: number,
    amount: number,
  ) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-stiffness-amount"]`,
      String(amount),
    );
  }

  async setStiffnessExtent(
    layerIndex: number,
    pinIndex: number,
    extent: number,
  ) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-stiffness-extent"]`,
      String(extent),
    );
  }

  async setOverlapInFront(layerIndex: number, pinIndex: number, value: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-overlap-infront"]`,
      String(value),
    );
  }

  async setOverlapExtent(layerIndex: number, pinIndex: number, extent: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-overlap-extent"]`,
      String(extent),
    );
  }

  async setBendRotation(layerIndex: number, pinIndex: number, degrees: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-bend-rotation"]`,
      String(degrees),
    );
  }

  async setBendScale(layerIndex: number, pinIndex: number, scale: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-bend-scale"]`,
      String(scale),
    );
  }

  async setAdvancedPinPosition(
    layerIndex: number,
    pinIndex: number,
    x: number,
    y: number,
  ) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-x"]`,
      String(x),
    );
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-y"]`,
      String(y),
    );
  }

  async setAdvancedPinRotation(
    layerIndex: number,
    pinIndex: number,
    degrees: number,
  ) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-rotation"]`,
      String(degrees),
    );
  }

  async setAdvancedPinScale(
    layerIndex: number,
    pinIndex: number,
    scale: number,
  ) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-scale"]`,
      String(scale),
    );
  }

  // ============== MOTION RECORDING (Tutorial 03) ==============

  async openRecordOptions() {
    await this.page.click('[data-testid="record-options-panel"]');
  }

  async setRecordSpeed(speed: number) {
    await this.page.fill('[data-testid="record-speed"]', String(speed));
  }

  async setRecordSmoothing(smoothing: number) {
    await this.page.fill('[data-testid="record-smoothing"]', String(smoothing));
  }

  async toggleDraftDeformation(enable: boolean) {
    const checkbox = this.page.locator(
      '[data-testid="record-draft-deformation"]',
    );
    const isChecked = await checkbox.isChecked();
    if (isChecked !== enable) {
      await checkbox.click();
    }
  }

  async startPinRecording(layerIndex: number, pinIndex: number) {
    await this.selectPin(layerIndex, pinIndex);
    await this.page.keyboard.down("Control");
  }

  async stopPinRecording() {
    await this.page.keyboard.up("Control");
  }

  async recordPinMotion(
    layerIndex: number,
    pinIndex: number,
    path: { x: number; y: number }[],
  ) {
    await this.startPinRecording(layerIndex, pinIndex);
    const canvas = this.page.locator('[data-testid="composition-panel"]');

    for (const point of path) {
      await canvas.hover({ position: { x: point.x, y: point.y } });
      await this.page.waitForTimeout(50);
    }

    await this.stopPinRecording();
  }

  async smoothKeyframes() {
    await this.page.click('[data-testid="keyframe-menu"]');
    await this.page.click("text=Smooth Keyframes");
  }

  // ============== LOOP EXPRESSIONS (Tutorial 03) ==============

  async addPinLoopExpression(
    layerIndex: number,
    pinIndex: number,
    loopType: "cycle" | "pingpong" | "offset" | "continue",
  ) {
    await this.selectPin(layerIndex, pinIndex);
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-expression-toggle"]`,
    );
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-expression"]`,
      `loopOut("${loopType}")`,
    );
    await this.page.keyboard.press("Enter");
  }

  // ============== MESH VERIFICATION (Tutorial 03) ==============

  async expectMeshDeformationEffect(layerIndex: number) {
    await expect(
      this.page.locator(
        `[data-testid="layer-${layerIndex}-effect-mesh-deformation"]`,
      ),
    ).toBeVisible();
  }

  async expectMeshGenerated(layerIndex: number) {
    await expect(
      this.page.locator(`[data-testid="layer-${layerIndex}-mesh-status-ok"]`),
    ).toBeVisible();
  }

  async expectMeshError(layerIndex: number) {
    await expect(
      this.page.locator(
        `[data-testid="layer-${layerIndex}-mesh-status-error"]`,
      ),
    ).toBeVisible();
  }

  // ============== TIME PROPERTIES (Tutorial 04) ==============

  /** Get layer timing info */
  async getLayerStartFrame(layerIndex: number): Promise<number> {
    const value = await this.page
      .locator(`[data-testid="layer-${layerIndex}-startframe"]`)
      .inputValue();
    return parseInt(value, 10);
  }

  async getLayerEndFrame(layerIndex: number): Promise<number> {
    const value = await this.page
      .locator(`[data-testid="layer-${layerIndex}-endframe"]`)
      .inputValue();
    return parseInt(value, 10);
  }

  /** Set layer timing */
  async setLayerStartFrame(layerIndex: number, frame: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-startframe"]`,
      String(frame),
    );
    await this.page.keyboard.press("Enter");
  }

  async setLayerEndFrame(layerIndex: number, frame: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-endframe"]`,
      String(frame),
    );
    await this.page.keyboard.press("Enter");
  }

  // ============== TIME STRETCH (Tutorial 04) ==============

  /** Get/Set time stretch */
  async getTimeStretch(layerIndex: number): Promise<number> {
    const value = await this.page
      .locator(`[data-testid="layer-${layerIndex}-timestretch"]`)
      .inputValue();
    return parseFloat(value);
  }

  async setTimeStretch(layerIndex: number, percentage: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-timestretch"]`,
      String(percentage),
    );
    await this.page.keyboard.press("Enter");
  }

  /** Set stretch anchor */
  async setStretchAnchor(
    layerIndex: number,
    anchor: "startFrame" | "endFrame" | "currentFrame",
  ) {
    await this.page.click(`[data-testid="layer-${layerIndex}-stretch-anchor"]`);
    await this.page.click(`text=${anchor}`);
  }

  /** Toggle time reverse */
  async setTimeReverse(layerIndex: number, reversed: boolean) {
    const checkbox = this.page.locator(
      `[data-testid="layer-${layerIndex}-time-reverse"]`,
    );
    const isChecked = await checkbox.isChecked();
    if (isChecked !== reversed) {
      await checkbox.click();
    }
  }

  // ============== SPEEDMAP / TIME REMAPPING (Tutorial 04) ==============

  /** Enable speedMap */
  async enableSpeedMap(layerIndex: number) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-speedmap-enable"]`,
    );
  }

  /** Check if speedMap enabled */
  async isSpeedMapEnabled(layerIndex: number): Promise<boolean> {
    return await this.page
      .locator(`[data-testid="layer-${layerIndex}-speedmap-enabled"]`)
      .isVisible();
  }

  /** Get speedMap value at current frame */
  async getSpeedMapValue(layerIndex: number): Promise<number> {
    const value = await this.page
      .locator(`[data-testid="layer-${layerIndex}-speedmap-value"]`)
      .inputValue();
    return parseFloat(value);
  }

  /** Set speedMap value (creates keyframe if stopwatch enabled) */
  async setSpeedMapValue(layerIndex: number, sourceFrame: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-speedmap-value"]`,
      String(sourceFrame),
    );
    await this.page.keyboard.press("Enter");
  }

  /** Add speedMap keyframe at current time */
  async addSpeedMapKeyframe(layerIndex: number, sourceFrame: number) {
    await this.setSpeedMapValue(layerIndex, sourceFrame);
  }

  /** Set keyframe interpolation to hold */
  async setKeyframeInterpolation(
    property: string,
    type: "linear" | "bezier" | "hold",
  ) {
    await this.page.click(`[data-testid="keyframe-${property}-selected"]`, {
      button: "right",
    });
    await this.page.click(`text=${type}`);
  }

  // ============== FRAME BLENDING (Tutorial 04) ==============

  /** Set frame blending mode */
  async setFrameBlending(layerIndex: number, mode: "none" | "mix" | "motion") {
    await this.page.click(`[data-testid="layer-${layerIndex}-frame-blending"]`);
    await this.page.click(`text=${mode}`);
  }

  /** Enable composition frame blending */
  async enableCompFrameBlending() {
    await this.page.click('[data-testid="comp-frame-blending-enable"]');
  }

  // ============== POSTERIZE TIME (Tutorial 04) ==============

  /** Add and configure PosterizeTime effect */
  async addPosterizeTimeEffect(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Posterize Time");
    await this.applyEffect("posterize-time");
  }

  async setPosterizeTimeFrameRate(effectIndex: number, frameRate: number) {
    await this.page.fill(
      `[data-testid="effect-${effectIndex}-posterize-framerate"]`,
      String(frameRate),
    );
    await this.page.keyboard.press("Enter");
  }

  // ============== FREEZE FRAME (Tutorial 04) ==============

  /** Add FreezeFrame effect */
  async addFreezeFrameEffect(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Freeze Frame");
    await this.applyEffect("freeze-frame");
  }

  async setFreezeAtFrame(effectIndex: number, frame: number) {
    await this.page.fill(
      `[data-testid="effect-${effectIndex}-freeze-at-frame"]`,
      String(frame),
    );
    await this.page.keyboard.press("Enter");
  }

  // ============== EXPRESSIONS (Tutorial 04) ==============

  /** Enable expression on property */
  async enablePropertyExpression(layerIndex: number, property: string) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-${property}-expression-enable"]`,
      { modifiers: ["Alt"] },
    );
  }

  /** Get expression text */
  async getExpressionText(
    layerIndex: number,
    property: string,
  ): Promise<string> {
    return await this.page
      .locator(`[data-testid="layer-${layerIndex}-${property}-expression"]`)
      .inputValue();
  }

  /** Set expression text */
  async setExpressionText(
    layerIndex: number,
    property: string,
    expression: string,
  ) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-${property}-expression"]`,
      expression,
    );
    await this.page.keyboard.press("Enter");
  }

  /** Check for expression error */
  async hasExpressionError(
    layerIndex: number,
    property: string,
  ): Promise<boolean> {
    return await this.page
      .locator(
        `[data-testid="layer-${layerIndex}-${property}-expression-error"]`,
      )
      .isVisible();
  }

  /** Get expression error message */
  async getExpressionError(
    layerIndex: number,
    property: string,
  ): Promise<string> {
    return (
      (await this.page
        .locator(
          `[data-testid="layer-${layerIndex}-${property}-expression-error"]`,
        )
        .textContent()) || ""
    );
  }

  /** Evaluate expression and get result */
  async getExpressionResult(
    layerIndex: number,
    property: string,
  ): Promise<string> {
    return await this.page
      .locator(`[data-testid="layer-${layerIndex}-${property}-value"]`)
      .inputValue();
  }

  // ============== EXPRESSION CONTROLS (Tutorial 04) ==============

  /** Add SliderControl effect */
  async addSliderControl(layerIndex: number, name: string = "Slider Control") {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Slider Control");
    await this.applyEffect("slider-control");
    if (name !== "Slider Control") {
      await this.page.dblclick('[data-testid="effect-0-name"]');
      await this.page.keyboard.type(name);
      await this.page.keyboard.press("Enter");
    }
  }

  async setSliderValue(effectIndex: number, value: number) {
    await this.page.fill(
      `[data-testid="effect-${effectIndex}-slider-value"]`,
      String(value),
    );
    await this.page.keyboard.press("Enter");
  }

  async getSliderValue(effectIndex: number): Promise<number> {
    const value = await this.page
      .locator(`[data-testid="effect-${effectIndex}-slider-value"]`)
      .inputValue();
    return parseFloat(value);
  }

  /** Add CheckboxControl effect */
  async addCheckboxControl(
    layerIndex: number,
    _name: string = "Checkbox Control",
  ) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Checkbox Control");
    await this.applyEffect("checkbox-control");
  }

  async setCheckboxValue(effectIndex: number, checked: boolean) {
    const checkbox = this.page.locator(
      `[data-testid="effect-${effectIndex}-checkbox-value"]`,
    );
    const isChecked = await checkbox.isChecked();
    if (isChecked !== checked) {
      await checkbox.click();
    }
  }

  /** Add ColorControl effect */
  async addColorControl(layerIndex: number, _name: string = "Color Control") {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Color Control");
    await this.applyEffect("color-control");
  }

  async setColorControlValue(effectIndex: number, color: string) {
    await this.page.fill(
      `[data-testid="effect-${effectIndex}-color-value"]`,
      color,
    );
  }

  /** Add PointControl effect */
  async addPointControl(layerIndex: number, _name: string = "Point Control") {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Point Control");
    await this.applyEffect("point-control");
  }

  async setPointControlValue(effectIndex: number, x: number, y: number) {
    await this.page.fill(
      `[data-testid="effect-${effectIndex}-point-x"]`,
      String(x),
    );
    await this.page.fill(
      `[data-testid="effect-${effectIndex}-point-y"]`,
      String(y),
    );
  }

  /** Add DropdownControl effect */
  async addDropdownControl(
    layerIndex: number,
    _name: string = "Dropdown Control",
  ) {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Dropdown Control");
    await this.applyEffect("dropdown-control");
  }

  async setDropdownValue(effectIndex: number, optionIndex: number) {
    await this.page.click(
      `[data-testid="effect-${effectIndex}-dropdown-value"]`,
    );
    await this.page.click(
      `[data-testid="effect-${effectIndex}-dropdown-option-${optionIndex}"]`,
    );
  }

  /** Add LayerControl effect */
  async addLayerControl(layerIndex: number, _name: string = "Layer Control") {
    await this.selectLayer(layerIndex);
    await this.searchEffects("Layer Control");
    await this.applyEffect("layer-control");
  }

  async setLayerControlTarget(effectIndex: number, targetLayerIndex: number) {
    await this.page.click(`[data-testid="effect-${effectIndex}-layer-value"]`);
    await this.page.click(
      `[data-testid="effect-${effectIndex}-layer-option-${targetLayerIndex}"]`,
    );
  }

  // ============== GRAPH EDITOR (Tutorial 04) ==============

  /** Open graph editor for property */
  async openGraphEditor(layerIndex: number, property: string) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-${property}-graph-editor"]`,
    );
  }

  /** Set graph type */
  async setGraphType(type: "value" | "speed") {
    await this.page.click('[data-testid="graph-type-selector"]');
    await this.page.click(
      `text=${type === "value" ? "Value Graph" : "Speed Graph"}`,
    );
  }

  // ============== DETERMINISM VERIFICATION (Tutorial 04) ==============

  /** Capture rendered frame for comparison */
  async captureFramePixels(): Promise<string> {
    const canvas = this.page.locator('[data-testid="composition-canvas"]');
    const screenshot = await canvas.screenshot();
    return screenshot.toString("base64");
  }

  /** Full determinism test */
  async verifyFrameDeterminism(targetFrame: number) {
    await this.goToFrame(targetFrame);
    const expected = await this.captureFramePixels();

    await this.goToFrame(0);
    await this.goToFrame(200);
    await this.goToFrame(50);

    await this.goToFrame(targetFrame);
    const actual = await this.captureFramePixels();

    expect(actual).toBe(expected);
  }

  /** Verify expression value determinism */
  async verifyExpressionDeterminism(
    layerIndex: number,
    property: string,
    targetFrame: number,
  ) {
    await this.goToFrame(targetFrame);
    const expected = await this.getExpressionResult(layerIndex, property);

    await this.goToFrame(0);
    await this.goToFrame(targetFrame * 2);
    await this.goToFrame(targetFrame);

    const actual = await this.getExpressionResult(layerIndex, property);
    expect(actual).toBe(expected);
  }

  /** Verify speedMap determinism */
  async verifySpeedMapDeterminism(layerIndex: number, targetFrame: number) {
    await this.goToFrame(targetFrame);
    const expected = await this.getSpeedMapValue(layerIndex);

    await this.goToFrame(0);
    await this.goToFrame(200);
    await this.goToFrame(50);
    await this.goToFrame(targetFrame);

    const actual = await this.getSpeedMapValue(layerIndex);
    expect(actual).toBe(expected);
  }

  // ============== ADDITIONAL HELPERS (Tutorial 04) ==============

  /** Reload the current project */
  async reloadProject() {
    await this.page.reload();
  }

  /** Enable pin keyframes */
  async enablePinKeyframes(
    layerIndex: number,
    pinIndex: number,
    property: string,
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-${property}-stopwatch"]`,
    );
  }

  /** Get keyframe count for a property */
  async expectKeyframeCount(
    layerIndex: number,
    pinIndex: number,
    property: string,
    count: number,
  ) {
    const keyframes = this.page.locator(
      `[data-testid^="layer-${layerIndex}-pin-${pinIndex}-${property}-keyframe-"]`,
    );
    const actual = await keyframes.count();
    expect(actual).toBe(count);
  }

  /** Select all keyframes for a property */
  async selectAllKeyframes(
    layerIndex: number,
    pinIndex: number,
    property: string,
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-${property}"]`,
    );
    await this.page.keyboard.press("Control+a");
  }

  /** Enable motion recording */
  async enableMotionRecording(layerIndex: number) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-motion-record-enable"]`,
    );
  }

  /** Start recording */
  async startRecording() {
    await this.page.click('[data-testid="record-start"]');
  }

  /** Stop recording */
  async stopRecording() {
    await this.page.click('[data-testid="record-stop"]');
  }

  /** Record pin movement */
  async recordPinMovement(
    layerIndex: number,
    pinIndex: number,
    frames: { frame: number; x: number; y: number }[],
  ) {
    for (const f of frames) {
      await this.goToFrame(f.frame);
      await this.movePinTo(layerIndex, pinIndex, f.x, f.y);
    }
  }

  /** Reset pin position */
  async resetPinPosition(layerIndex: number, pinIndex: number) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-reset"]`,
    );
  }

  /** Open pin expressions */
  async openPinExpressions(
    layerIndex: number,
    pinIndex: number,
    property: string,
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-${property}-expression-toggle"]`,
    );
  }

  /** Close expression editor */
  async closeExpressionEditor() {
    await this.page.keyboard.press("Escape");
  }

  /** Link pins together */
  async linkPins(
    layerIndex: number,
    childPinIndex: number,
    parentPinIndex: number,
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${childPinIndex}-parent"]`,
    );
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-parent-option-${parentPinIndex}"]`,
    );
  }

  /** Set bend angle */
  async setBendAngle(layerIndex: number, pinIndex: number, angle: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-bend-angle"]`,
      String(angle),
    );
    await this.page.keyboard.press("Enter");
  }

  /** Set bend length */
  async setBendLength(layerIndex: number, pinIndex: number, length: number) {
    await this.page.fill(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-bend-length"]`,
      String(length),
    );
    await this.page.keyboard.press("Enter");
  }

  /** Enable bend keyframes */
  async enableBendKeyframes(
    layerIndex: number,
    pinIndex: number,
    property: string,
  ) {
    await this.page.click(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-bend-${property}-stopwatch"]`,
    );
  }

  /** Set overlap in front (boolean version) */
  async setOverlapInFront(
    layerIndex: number,
    pinIndex: number,
    inFront: boolean,
  ) {
    const checkbox = this.page.locator(
      `[data-testid="layer-${layerIndex}-pin-${pinIndex}-overlap-infront"]`,
    );
    const isChecked = await checkbox.isChecked();
    if (isChecked !== inFront) {
      await checkbox.click();
    }
  }
}
