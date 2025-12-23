/**
 * Depthflow Actions
 *
 * Depthflow parallax layer creation and configuration.
 *
 * Extracted from compositorStore.ts for modularity.
 */

import type {
  Layer,
  DepthflowLayerData
} from '@/types/project';
import { createAnimatableProperty } from '@/types/project';

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface DepthflowStore {
  project: {
    meta: { modified: string };
  };

  // Methods the actions need to call
  getActiveCompLayers(): Layer[];
  createLayer(type: Layer['type'], name?: string): Layer;
}

// ============================================================================
// DEPTHFLOW LAYER CREATION
// ============================================================================

/**
 * Create a depthflow parallax layer
 */
export function createDepthflowLayer(
  store: DepthflowStore,
  sourceLayerId: string = '',
  depthLayerId: string = ''
): Layer {
  const layer = store.createLayer('depthflow', 'Depthflow');

  // Set up depthflow layer data
  const depthflowData: DepthflowLayerData = {
    sourceLayerId,
    depthLayerId,
    config: {
      preset: 'zoom_in',
      zoom: 1.0,
      offsetX: 0,
      offsetY: 0,
      rotation: 0,
      depthScale: 1.0,
      focusDepth: 0.5,
      dollyZoom: 0,
      orbitRadius: 0.1,
      orbitSpeed: 360,
      swingAmplitude: 0.1,
      swingFrequency: 1,
      edgeDilation: 5,
      inpaintEdges: true
    },
    animatedZoom: createAnimatableProperty('zoom', 1.0, 'number'),
    animatedOffsetX: createAnimatableProperty('offsetX', 0, 'number'),
    animatedOffsetY: createAnimatableProperty('offsetY', 0, 'number'),
    animatedRotation: createAnimatableProperty('rotation', 0, 'number'),
    animatedDepthScale: createAnimatableProperty('depthScale', 1.0, 'number')
  };

  layer.data = depthflowData;

  return layer;
}

// ============================================================================
// DEPTHFLOW CONFIG UPDATES
// ============================================================================

/**
 * Update depthflow config
 */
export function updateDepthflowConfig(
  store: DepthflowStore,
  layerId: string,
  updates: Partial<DepthflowLayerData['config']>
): void {
  const layer = store.getActiveCompLayers().find(l => l.id === layerId);
  if (!layer || layer.type !== 'depthflow') return;

  const data = layer.data as DepthflowLayerData;
  Object.assign(data.config, updates);
  store.project.meta.modified = new Date().toISOString();
}
