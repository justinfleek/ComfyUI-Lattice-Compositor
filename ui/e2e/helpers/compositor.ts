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
}
