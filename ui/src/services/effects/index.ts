/**
 * Effects Registry
 *
 * Centralizes registration of all effect renderers.
 * Import this module to initialize the effect system.
 */
import { registerBlurEffects } from './blurRenderer';

/**
 * Initialize all effect renderers
 * Call this once at application startup
 */
export function initializeEffects(): void {
  registerBlurEffects();
  // Future effects will be registered here:
  // registerColorEffects();
  // registerDistortEffects();
  // registerStylizeEffects();
}

// Re-export for convenience
export { gaussianBlurRenderer } from './blurRenderer';
