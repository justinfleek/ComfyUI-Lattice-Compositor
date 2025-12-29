import { Page, expect } from '@playwright/test';

export class CompositorHelper {
  constructor(private page: Page) {}

  // Project operations
  async newProject() {
    await this.page.keyboard.press('Control+Alt+n');
    await this.page.waitForSelector('[data-testid="project-panel"]');
  }

  async saveProject() {
    await this.page.keyboard.press('Control+s');
  }

  async importFile(filePath: string) {
    await this.page.keyboard.press('Control+i');
    // Handle file dialog
  }

  // Composition operations
  async newComposition(name: string, width = 1920, height = 1080, fps = 16, duration = 5) {
    await this.page.keyboard.press('Control+n');
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
    await this.page.keyboard.press('Control+y');
    if (name) {
      await this.page.fill('[data-testid="solid-name"]', name);
    }
    await this.page.click('[data-testid="solid-create-btn"]');
  }

  async newEffectLayer() {
    await this.page.keyboard.press('Control+Alt+y');
  }

  async newControlLayer() {
    await this.page.keyboard.press('Control+Alt+Shift+y');
  }

  async selectLayer(index: number) {
    await this.page.click(`[data-testid="layer-${index}"]`);
  }

  async duplicateLayer() {
    await this.page.keyboard.press('Control+d');
  }

  async deleteLayer() {
    await this.page.keyboard.press('Delete');
  }

  // Timeline navigation
  async goToStart() {
    await this.page.keyboard.press('Home');
  }

  async goToEnd() {
    await this.page.keyboard.press('End');
  }

  async goToFrame(frame: number) {
    await this.goToStart();
    for (let i = 0; i < frame; i++) {
      await this.page.keyboard.press('PageDown');
    }
  }

  async play() {
    await this.page.keyboard.press('Space');
  }

  async stop() {
    await this.page.keyboard.press('Space');
  }

  // Property shortcuts
  async isolatePosition() {
    await this.page.keyboard.press('p');
  }

  async isolateScale() {
    await this.page.keyboard.press('s');
  }

  async isolateRotation() {
    await this.page.keyboard.press('r');
  }

  async isolateOpacity() {
    await this.page.keyboard.press('t');
  }

  async revealAnimated() {
    await this.page.keyboard.press('u');
  }

  // Keyframes
  async toggleStopwatch(propertyName: string) {
    await this.page.click(`[data-testid="stopwatch-${propertyName}"]`);
  }

  async smoothEase() {
    await this.page.keyboard.press('F9');
  }

  // Undo/Redo
  async undo() {
    await this.page.keyboard.press('Control+z');
  }

  async redo() {
    await this.page.keyboard.press('Control+Shift+z');
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

  async setCurveEditorGraphType(type: 'value' | 'speed') {
    await this.page.click('[data-testid="graph-type-dropdown"]');
    await this.page.click(`text=${type === 'value' ? 'Value Graph' : 'Speed Graph'}`);
  }

  async separateDimensions(property: string) {
    await this.page.click(`[data-testid="property-${property}"]`, { button: 'right' });
    await this.page.click('text=Separate Dimensions');
  }

  // ============== TEXT (Phase 12) ==============

  async newTextLayer(text: string) {
    await this.page.keyboard.press('t');
    await this.page.click('[data-testid="composition-panel"]');
    await this.page.keyboard.type(text);
    await this.page.keyboard.press('Escape');
  }

  async openCharacterPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click('text=Character');
  }

  async openParagraphPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click('text=Paragraph');
  }

  // ============== ALIGN (Phase 13) ==============

  async openAlignPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click('text=Align');
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
    await this.page.keyboard.press('Control+r');
  }

  async centerLayerInComp() {
    await this.page.keyboard.press('Control+Home');
  }

  // ============== EFFECTS (Phase 14) ==============

  async openEffectsPanel() {
    await this.page.click('[data-testid="window-menu"]');
    await this.page.click('text=Effects & Presets');
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
    await this.page.click(`[data-testid="layer-${childIndex}-parent-dropdown"]`);
    if (parentIndex === null) {
      await this.page.click('text=None');
    } else {
      await this.page.click(`[data-testid="parent-option-${parentIndex}"]`);
    }
  }

  // ============== EXPRESSIONS (Phase 16) ==============

  async enableExpression(property: string) {
    await this.page.click(`[data-testid="stopwatch-${property}"]`, { modifiers: ['Alt'] });
  }

  async setExpression(property: string, expression: string) {
    const input = this.page.locator(`[data-testid="expression-${property}"]`);
    await input.fill(expression);
    await input.press('Enter');
  }

  // ============== NESTED COMPS (Phase 17) ==============

  async selectAllLayers() {
    await this.page.keyboard.press('Control+a');
  }

  async createNestedComp(name: string) {
    await this.page.keyboard.press('Control+Shift+c');
    await this.page.waitForSelector('[data-testid="nested-comp-dialog"]');
    await this.page.fill('[data-testid="nested-comp-name"]', name);
    await this.page.click('[data-testid="nested-comp-create-btn"]');
  }

  // ============== RENDER RANGE (Phase 18) ==============

  async setRenderRangeStart() {
    await this.page.keyboard.press('b');
  }

  async setRenderRangeEnd() {
    await this.page.keyboard.press('n');
  }

  // ============== EXPORT (Phase 19) ==============

  async addToRenderQueue() {
    await this.page.keyboard.press('Control+m');
  }

  // ============== PROPERTY VALUES ==============

  async setPropertyValue(property: string, value: string) {
    const input = this.page.locator(`[data-testid="property-${property}-value"]`);
    await input.fill(value);
    await input.press('Enter');
  }

  async getPropertyValue(property: string): Promise<string> {
    return await this.page.locator(`[data-testid="property-${property}-value"]`).inputValue();
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
        throw new Error(`Determinism failed for ${prop}: expected ${expected[prop]}, got ${actual}`);
      }
    }
  }

  async revealAnimatedProperties() {
    await this.page.keyboard.press('u');
  }

  // ============== SHAPE LAYERS (Tutorial 02) ==============

  async newShapeLayer(name: string) {
    await this.page.click('[data-testid="layer-menu"]');
    await this.page.click('text=New');
    await this.page.click('text=Shape Layer');
    await this.selectLayer(0);
    await this.renameLayer(name);
  }

  async renameLayer(name: string) {
    await this.page.keyboard.press('Enter');
    await this.page.keyboard.type(name);
    await this.page.keyboard.press('Enter');
  }

  async expandShapeContents(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-expand"]`);
    await this.page.click(`[data-testid="layer-${layerIndex}-contents-expand"]`);
  }

  async removeShapeFill(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-shape-fill"]`, { button: 'right' });
    await this.page.click('text=Delete');
  }

  async setStrokeColor(layerIndex: number, color: string) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-stroke-color"]`, color);
  }

  async setStrokeWidth(layerIndex: number, width: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-stroke-width"]`, String(width));
  }

  async setStrokeLineCap(layerIndex: number, cap: 'butt' | 'round' | 'square') {
    await this.page.click(`[data-testid="layer-${layerIndex}-stroke-linecap"]`);
    await this.page.click(`text=${cap}`);
  }

  async setStrokeLineJoin(layerIndex: number, join: 'miter' | 'round' | 'bevel') {
    await this.page.click(`[data-testid="layer-${layerIndex}-stroke-linejoin"]`);
    await this.page.click(`text=${join}`);
  }

  // ============== TRIM PATHS (Tutorial 02) ==============

  async addTrimPaths(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-shape-add"]`);
    await this.page.click('text=Trim Paths');
  }

  async setTrimPathsStart(layerIndex: number, value: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-trimpath-start"]`, String(value));
  }

  async setTrimPathsEnd(layerIndex: number, value: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-trimpath-end"]`, String(value));
  }

  async setTrimPathsOffset(layerIndex: number, value: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-trimpath-offset"]`, String(value));
  }

  async enableTrimPathsKeyframes(layerIndex: number, property: 'start' | 'end' | 'offset') {
    await this.page.click(`[data-testid="layer-${layerIndex}-trimpath-${property}-stopwatch"]`);
  }

  // ============== EFFECTS - EXTENDED (Tutorial 02) ==============

  async addGradientRamp(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.searchEffects('Gradient Ramp');
    await this.applyEffect('gradient-ramp');
  }

  async configureGradientRamp(options: {
    startX?: number;
    startY?: number;
    endX?: number;
    endY?: number;
    startColor?: string;
    endColor?: string;
    shape?: 'linear' | 'radial';
  }) {
    if (options.startX !== undefined) {
      await this.page.fill('[data-testid="effect-gradient-ramp-start-x"]', String(options.startX));
    }
    if (options.startY !== undefined) {
      await this.page.fill('[data-testid="effect-gradient-ramp-start-y"]', String(options.startY));
    }
    if (options.endX !== undefined) {
      await this.page.fill('[data-testid="effect-gradient-ramp-end-x"]', String(options.endX));
    }
    if (options.endY !== undefined) {
      await this.page.fill('[data-testid="effect-gradient-ramp-end-y"]', String(options.endY));
    }
    if (options.startColor) {
      await this.page.fill('[data-testid="effect-gradient-ramp-start-color"]', options.startColor);
    }
    if (options.endColor) {
      await this.page.fill('[data-testid="effect-gradient-ramp-end-color"]', options.endColor);
    }
    if (options.shape) {
      await this.page.click('[data-testid="effect-gradient-ramp-shape"]');
      await this.page.click(`text=${options.shape}`);
    }
  }

  async addFillEffect(layerIndex: number, color: string) {
    await this.selectLayer(layerIndex);
    await this.searchEffects('Fill');
    await this.applyEffect('fill');
    await this.page.fill('[data-testid="effect-fill-color"]', color);
  }

  async addTintEffect(layerIndex: number, mapBlack: string, mapWhite: string, amount: number) {
    await this.selectLayer(layerIndex);
    await this.searchEffects('Tint');
    await this.applyEffect('tint');
    await this.page.fill('[data-testid="effect-tint-map-black"]', mapBlack);
    await this.page.fill('[data-testid="effect-tint-map-white"]', mapWhite);
    await this.page.fill('[data-testid="effect-tint-amount"]', String(amount));
  }

  async configureGlow(effectIndex: number, options: {
    threshold?: number;
    radius?: number;
    intensity?: number;
    colorA?: string;
    colorB?: string;
  }) {
    if (options.threshold !== undefined) {
      await this.page.fill(`[data-testid="effect-${effectIndex}-glow-threshold"]`, String(options.threshold));
    }
    if (options.radius !== undefined) {
      await this.page.fill(`[data-testid="effect-${effectIndex}-glow-radius"]`, String(options.radius));
    }
    if (options.intensity !== undefined) {
      await this.page.fill(`[data-testid="effect-${effectIndex}-glow-intensity"]`, String(options.intensity));
    }
    if (options.colorA) {
      await this.page.fill(`[data-testid="effect-${effectIndex}-glow-color-a"]`, options.colorA);
    }
    if (options.colorB) {
      await this.page.fill(`[data-testid="effect-${effectIndex}-glow-color-b"]`, options.colorB);
    }
  }

  async addEchoEffect(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.searchEffects('Echo');
    await this.applyEffect('echo');
  }

  async configureEcho(options: {
    echoTime?: number;
    numberOfEchoes?: number;
    startingIntensity?: number;
    decay?: number;
    operator?: 'add' | 'maximum' | 'screen' | 'composite_back' | 'composite_front';
  }) {
    if (options.echoTime !== undefined) {
      await this.page.fill('[data-testid="effect-echo-time"]', String(options.echoTime));
    }
    if (options.numberOfEchoes !== undefined) {
      await this.page.fill('[data-testid="effect-echo-number"]', String(options.numberOfEchoes));
    }
    if (options.startingIntensity !== undefined) {
      await this.page.fill('[data-testid="effect-echo-intensity"]', String(options.startingIntensity));
    }
    if (options.decay !== undefined) {
      await this.page.fill('[data-testid="effect-echo-decay"]', String(options.decay));
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
    await this.page.keyboard.press('Control+k');
    await this.page.waitForSelector('[data-testid="comp-settings-dialog"]');
  }

  async configureMotionBlur(shutterAngle: number, shutterPhase: number, samples: number) {
    await this.openCompositionSettings();
    await this.page.fill('[data-testid="comp-shutter-angle"]', String(shutterAngle));
    await this.page.fill('[data-testid="comp-shutter-phase"]', String(shutterPhase));
    await this.page.fill('[data-testid="comp-motion-blur-samples"]', String(samples));
    await this.page.click('[data-testid="comp-settings-ok"]');
  }

  // ============== GRADIENT STROKE (Tutorial 02) ==============

  async addGradientStroke(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-shape-add"]`);
    await this.page.click('text=Gradient Stroke');
  }

  async configureGradientStroke(layerIndex: number, options: {
    type?: 'linear' | 'radial';
    startX?: number;
    startY?: number;
    endX?: number;
    endY?: number;
  }) {
    if (options.type) {
      await this.page.click(`[data-testid="layer-${layerIndex}-gradient-stroke-type"]`);
      await this.page.click(`text=${options.type}`);
    }
  }

  // ============== MASKS (Tutorial 02) ==============

  async addOvalMask(layerIndex: number) {
    await this.selectLayer(layerIndex);
    await this.page.click('[data-testid="mask-tool-ellipse"]');
    await this.page.click('[data-testid="composition-panel"]');
  }

  async setMaskMode(layerIndex: number, maskIndex: number, mode: 'add' | 'subtract' | 'intersect' | 'difference') {
    await this.page.click(`[data-testid="layer-${layerIndex}-mask-${maskIndex}-mode"]`);
    await this.page.click(`text=${mode}`);
  }

  async setMaskFeather(layerIndex: number, maskIndex: number, feather: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-mask-${maskIndex}-feather"]`, String(feather));
  }

  // ============== BLEND MODES (Tutorial 02) ==============

  async setBlendMode(layerIndex: number, mode: string) {
    await this.page.click(`[data-testid="layer-${layerIndex}-blend-mode"]`);
    await this.page.click(`text=${mode}`);
  }

  // ============== ADJUSTMENT LAYERS (Tutorial 02) ==============

  async newAdjustmentLayer(name: string) {
    await this.page.click('[data-testid="layer-menu"]');
    await this.page.click('text=New');
    await this.page.click('text=Adjustment Layer');
    await this.selectLayer(0);
    await this.renameLayer(name);
  }

  // ============== AUTO-ORIENT (Tutorial 02) ==============

  async enableAutoOrient(layerIndex: number, mode: 'off' | 'alongPath' | 'towardsCamera') {
    await this.page.click(`[data-testid="layer-${layerIndex}"]`, { button: 'right' });
    await this.page.click('text=Transform');
    await this.page.click('text=Auto-Orient');
    await this.page.click(`text=${mode}`);
  }

  // ============== COPY/PASTE (Tutorial 02) ==============

  async copy() {
    await this.page.keyboard.press('Control+c');
  }

  async paste() {
    await this.page.keyboard.press('Control+v');
  }

  async copyPathToPosition(sourceLayerIndex: number, targetLayerIndex: number) {
    await this.page.click(`[data-testid="layer-${sourceLayerIndex}-shape-path"]`);
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
    await this.page.keyboard.press('Control+l');
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
    await this.page.dblclick(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-name"]`);
    await this.page.keyboard.type(name);
    await this.page.keyboard.press('Enter');
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
    await this.page.fill(`[data-testid="layer-${layerIndex}-mesh-triangles"]`, String(count));
    await this.page.keyboard.press('Enter');
  }

  async setMeshExpansion(layerIndex: number, pixels: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-mesh-expansion"]`, String(pixels));
    await this.page.keyboard.press('Enter');
  }

  async toggleMeshVisibility(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-mesh-show"]`);
  }

  async regenerateMesh(layerIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-mesh-regenerate"]`);
  }

  // ============== PIN PROPERTIES (Tutorial 03) ==============

  async selectPin(layerIndex: number, pinIndex: number) {
    await this.page.click(`[data-testid="layer-${layerIndex}-pin-${pinIndex}"]`);
  }

  async movePinTo(layerIndex: number, pinIndex: number, x: number, y: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-x"]`, String(x));
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-y"]`, String(y));
  }

  async setStiffnessAmount(layerIndex: number, pinIndex: number, amount: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-stiffness-amount"]`, String(amount));
  }

  async setStiffnessExtent(layerIndex: number, pinIndex: number, extent: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-stiffness-extent"]`, String(extent));
  }

  async setOverlapInFront(layerIndex: number, pinIndex: number, value: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-overlap-infront"]`, String(value));
  }

  async setOverlapExtent(layerIndex: number, pinIndex: number, extent: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-overlap-extent"]`, String(extent));
  }

  async setBendRotation(layerIndex: number, pinIndex: number, degrees: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-bend-rotation"]`, String(degrees));
  }

  async setBendScale(layerIndex: number, pinIndex: number, scale: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-bend-scale"]`, String(scale));
  }

  async setAdvancedPinPosition(layerIndex: number, pinIndex: number, x: number, y: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-x"]`, String(x));
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-y"]`, String(y));
  }

  async setAdvancedPinRotation(layerIndex: number, pinIndex: number, degrees: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-rotation"]`, String(degrees));
  }

  async setAdvancedPinScale(layerIndex: number, pinIndex: number, scale: number) {
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-advanced-scale"]`, String(scale));
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
    const checkbox = this.page.locator('[data-testid="record-draft-deformation"]');
    const isChecked = await checkbox.isChecked();
    if (isChecked !== enable) {
      await checkbox.click();
    }
  }

  async startPinRecording(layerIndex: number, pinIndex: number) {
    await this.selectPin(layerIndex, pinIndex);
    await this.page.keyboard.down('Control');
  }

  async stopPinRecording() {
    await this.page.keyboard.up('Control');
  }

  async recordPinMotion(layerIndex: number, pinIndex: number, path: { x: number; y: number }[]) {
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
    await this.page.click('text=Smooth Keyframes');
  }

  // ============== LOOP EXPRESSIONS (Tutorial 03) ==============

  async addPinLoopExpression(layerIndex: number, pinIndex: number, loopType: 'cycle' | 'pingpong' | 'offset' | 'continue') {
    await this.selectPin(layerIndex, pinIndex);
    await this.page.click(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-expression-toggle"]`);
    await this.page.fill(`[data-testid="layer-${layerIndex}-pin-${pinIndex}-expression"]`, `loopOut("${loopType}")`);
    await this.page.keyboard.press('Enter');
  }

  // ============== MESH VERIFICATION (Tutorial 03) ==============

  async expectMeshDeformationEffect(layerIndex: number) {
    await expect(this.page.locator(`[data-testid="layer-${layerIndex}-effect-mesh-deformation"]`)).toBeVisible();
  }

  async expectMeshGenerated(layerIndex: number) {
    await expect(this.page.locator(`[data-testid="layer-${layerIndex}-mesh-status-ok"]`)).toBeVisible();
  }

  async expectMeshError(layerIndex: number) {
    await expect(this.page.locator(`[data-testid="layer-${layerIndex}-mesh-status-error"]`)).toBeVisible();
  }
}
