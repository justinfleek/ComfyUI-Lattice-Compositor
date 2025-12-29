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
}
