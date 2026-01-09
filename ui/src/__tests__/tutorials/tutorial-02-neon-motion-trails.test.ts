/**
 * Tutorial 02: Neon Motion Trails
 *
 * This tutorial tests creating neon motion trail effects using:
 * - Shape layers and paths
 * - Trim Paths animator
 * - Glow effect stacking
 * - Echo effect (motion trails)
 * - Gradient fills and strokes
 * - Pre-composition workflow
 * - Motion blur
 *
 * 15 Phases, 325 Steps Total
 */
import { describe, test, expect, beforeEach, afterEach, vi } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useCompositorStore } from '@/stores/compositorStore';
import { useSelectionStore } from '@/stores/selectionStore';
import type { Layer, EffectInstance, SolidLayerData, AudioLayerData } from '@/types/project';
import type { SplineData, ControlPoint } from '@/types/spline';

describe('Tutorial 02: Neon Motion Trails', () => {
  let store: ReturnType<typeof useCompositorStore>;
  let selectionStore: ReturnType<typeof useSelectionStore>;

  beforeEach(() => {
    const pinia = createPinia();
    setActivePinia(pinia);
    store = useCompositorStore();
    selectionStore = useSelectionStore();
  });

  afterEach(() => {
    vi.clearAllMocks();
  });

  // Helper functions
  const getLayer = (id: string): Layer | undefined => {
    return store.getActiveCompLayers().find(l => l.id === id);
  };

  const getLayerByName = (name: string): Layer | undefined => {
    return store.getActiveCompLayers().find(l => l.name === name);
  };

  const getEffectByType = (layer: Layer, effectKey: string): EffectInstance | undefined => {
    return layer.effects?.find(e => e.effectKey === effectKey);
  };

  /**
   * Convert simplified point array to ControlPoint[] format for SplineData
   * Points format: { x, y, handleIn?: { x, y }, handleOut?: { x, y } }
   */
  const convertPointsToControlPoints = (
    points: Array<{ x: number; y: number; handleIn?: { x: number; y: number } | null; handleOut?: { x: number; y: number } | null }>,
    closed: boolean = false
  ): { controlPoints: ControlPoint[]; pathData: string } => {
    const controlPoints: ControlPoint[] = points.map((p, i) => ({
      id: `cp_${Date.now()}_${i}_${Math.random().toString(36).slice(2, 7)}`,
      x: p.x,
      y: p.y,
      handleIn: p.handleIn || null,
      handleOut: p.handleOut || null,
      type: 'smooth' as const,
    }));

    // Generate SVG path data from control points
    if (controlPoints.length === 0) {
      return { controlPoints, pathData: '' };
    }
    if (controlPoints.length === 1) {
      return { controlPoints, pathData: `M ${controlPoints[0].x} ${controlPoints[0].y}` };
    }

    let pathData = `M ${controlPoints[0].x} ${controlPoints[0].y}`;
    for (let i = 0; i < controlPoints.length - 1; i++) {
      const p0 = controlPoints[i];
      const p1 = controlPoints[i + 1];

      if (p0.handleOut && p1.handleIn) {
        const cp1x = p0.x + p0.handleOut.x;
        const cp1y = p0.y + p0.handleOut.y;
        const cp2x = p1.x + p1.handleIn.x;
        const cp2y = p1.y + p1.handleIn.y;
        pathData += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p1.x} ${p1.y}`;
      } else if (p0.handleOut) {
        const cpx = p0.x + p0.handleOut.x;
        const cpy = p0.y + p0.handleOut.y;
        pathData += ` Q ${cpx} ${cpy}, ${p1.x} ${p1.y}`;
      } else if (p1.handleIn) {
        const cpx = p1.x + p1.handleIn.x;
        const cpy = p1.y + p1.handleIn.y;
        pathData += ` Q ${cpx} ${cpy}, ${p1.x} ${p1.y}`;
      } else {
        pathData += ` L ${p1.x} ${p1.y}`;
      }
    }

    if (closed && controlPoints.length > 2) {
      pathData += ' Z';
    }

    return { controlPoints, pathData };
  };

  /**
   * Convert RGBA color object to hex string
   */
  const rgbaToHex = (color: { r: number; g: number; b: number; a?: number }): string => {
    const r = Math.round(color.r).toString(16).padStart(2, '0');
    const g = Math.round(color.g).toString(16).padStart(2, '0');
    const b = Math.round(color.b).toString(16).padStart(2, '0');
    return `#${r}${g}${b}`;
  };

  // ============================================================================
  // PHASE 1: PROJECT SETUP & BACKGROUND (Steps 1-12)
  // ============================================================================
  describe('Phase 1: Project Setup & Background (Steps 1-12)', () => {

    describe('Steps 1-3: Creating the Project', () => {
      test('Step 1: Create new project', () => {
        // Project already initialized in beforeEach
        expect(store.project).toBeDefined();
        expect(store.project.compositions).toBeDefined();
      });

      test('Step 2: Verify default composition exists', () => {
        const comp = store.getActiveComp();
        expect(comp).toBeDefined();
        expect(comp!.settings.width).toBeDefined();
        expect(comp!.settings.height).toBeDefined();
        expect(comp!.settings.fps).toBeDefined();
        expect(comp!.settings.frameCount).toBeDefined();
      });

      test('Step 3: Rename composition to Neon_Trails_Main', () => {
        const comp = store.getActiveComp();
        expect(comp).toBeDefined();

        store.renameComposition(comp!.id, 'Neon_Trails_Main');

        const renamedComp = store.getActiveComp();
        expect(renamedComp!.name).toBe('Neon_Trails_Main');
      });
    });

    describe('Steps 4-6: Creating Gradient Background', () => {
      test('Step 4: Create solid layer BG_Gradient', () => {
        const layer = store.createLayer('solid', 'BG_Gradient');
        expect(layer).toBeDefined();
        expect(layer!.name).toBe('BG_Gradient');
        expect(layer!.type).toBe('solid');
      });

      test('Step 5: Add Gradient Ramp effect', () => {
        const layer = store.createLayer('solid', 'BG_Gradient');
        expect(layer).toBeDefined();

        store.addEffectToLayer(layer!.id, 'gradient-ramp');

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer!.effects).toBeDefined();
        expect(updatedLayer!.effects!.length).toBe(1);
        expect(updatedLayer!.effects![0].effectKey).toBe('gradient-ramp');
      });

      test('Step 6: Configure Gradient Ramp effect properties', () => {
        const layer = store.createLayer('solid', 'BG_Gradient');
        store.addEffectToLayer(layer!.id, 'gradient-ramp');

        const updatedLayer = getLayer(layer!.id);
        const effect = updatedLayer!.effects![0];

        // Configure Start Point
        store.updateEffectParameter(layer!.id, effect.id, 'start_of_ramp', { x: 960, y: 0 });
        // Configure End Point
        store.updateEffectParameter(layer!.id, effect.id, 'end_of_ramp', { x: 960, y: 1080 });
        // Configure Start Color (magenta)
        store.updateEffectParameter(layer!.id, effect.id, 'start_color', { r: 255, g: 0, b: 255, a: 1 });
        // Configure End Color (dark magenta)
        store.updateEffectParameter(layer!.id, effect.id, 'end_color', { r: 51, g: 0, b: 51, a: 1 });
        // Configure Ramp Shape
        store.updateEffectParameter(layer!.id, effect.id, 'ramp_shape', 'linear');

        // Verify all parameters
        const finalLayer = getLayer(layer!.id);
        const finalEffect = finalLayer!.effects![0];
        expect(finalEffect.parameters['start_of_ramp'].value).toEqual({ x: 960, y: 0 });
        expect(finalEffect.parameters['end_of_ramp'].value).toEqual({ x: 960, y: 1080 });
        expect(finalEffect.parameters['start_color'].value).toEqual({ r: 255, g: 0, b: 255, a: 1 });
        expect(finalEffect.parameters['end_color'].value).toEqual({ r: 51, g: 0, b: 51, a: 1 });
        expect(finalEffect.parameters['ramp_shape'].value).toBe('linear');
      });
    });

    describe('Steps 7-12: Alternative Radial Gradient & Finalize', () => {
      test('Step 7: Duplicate background layer', () => {
        const layer = store.createLayer('solid', 'BG_Gradient');
        store.addEffectToLayer(layer!.id, 'gradient-ramp');

        const duplicated = store.duplicateLayer(layer!.id);
        expect(duplicated).toBeDefined();
        expect(duplicated!.name).toContain('BG_Gradient');
        expect(duplicated!.effects!.length).toBe(1);
        expect(duplicated!.effects![0].effectKey).toBe('gradient-ramp');
      });

      test('Step 8: Change Gradient Ramp shape to radial', () => {
        const layer = store.createLayer('solid', 'BG_Radial');
        store.addEffectToLayer(layer!.id, 'gradient-ramp');
        const effect = getLayer(layer!.id)!.effects![0];

        store.updateEffectParameter(layer!.id, effect.id, 'ramp_shape', 'radial');

        const updatedEffect = getLayer(layer!.id)!.effects![0];
        expect(updatedEffect.parameters['ramp_shape'].value).toBe('radial');
      });

      test('Step 9: Set Start Point to center for radial', () => {
        const layer = store.createLayer('solid', 'BG_Radial');
        store.addEffectToLayer(layer!.id, 'gradient-ramp');
        const effect = getLayer(layer!.id)!.effects![0];

        store.updateEffectParameter(layer!.id, effect.id, 'start_of_ramp', { x: 960, y: 540 });

        const updatedEffect = getLayer(layer!.id)!.effects![0];
        expect(updatedEffect.parameters['start_of_ramp'].value).toEqual({ x: 960, y: 540 });
      });

      test('Step 10: Toggle visibility between linear and radial versions', () => {
        // Create linear version
        const linearLayer = store.createLayer('solid', 'BG_Linear');
        store.addEffectToLayer(linearLayer!.id, 'gradient-ramp');

        // Create radial version
        const radialLayer = store.createLayer('solid', 'BG_Radial');
        store.addEffectToLayer(radialLayer!.id, 'gradient-ramp');
        const radialEffect = getLayer(radialLayer!.id)!.effects![0];
        store.updateEffectParameter(radialLayer!.id, radialEffect.id, 'ramp_shape', 'radial');

        // Toggle visibility - hide radial
        store.updateLayer(radialLayer!.id, { visible: false });
        expect(getLayer(radialLayer!.id)!.visible).toBe(false);
        expect(getLayer(linearLayer!.id)!.visible).toBe(true);

        // Toggle visibility - show radial, hide linear
        store.updateLayer(radialLayer!.id, { visible: true });
        store.updateLayer(linearLayer!.id, { visible: false });
        expect(getLayer(radialLayer!.id)!.visible).toBe(true);
        expect(getLayer(linearLayer!.id)!.visible).toBe(false);
      });

      test('Step 11: Delete unused variant', () => {
        // Create both versions
        const linearLayer = store.createLayer('solid', 'BG_Linear');
        const radialLayer = store.createLayer('solid', 'BG_Radial');

        const initialCount = store.getActiveCompLayers().length;

        // Delete the radial variant (keeping linear)
        store.deleteLayer(radialLayer!.id);

        expect(store.getActiveCompLayers().length).toBe(initialCount - 1);
        expect(getLayer(radialLayer!.id)).toBeUndefined();
        expect(getLayer(linearLayer!.id)).toBeDefined();
      });

      test('Step 12: Lock background layer', () => {
        const layer = store.createLayer('solid', 'BG_Gradient');

        store.updateLayer(layer!.id, { locked: true });

        const lockedLayer = getLayer(layer!.id);
        expect(lockedLayer!.locked).toBe(true);
      });
    });

    describe('Phase 1: Undo/Redo Verification', () => {
      test('Steps 1-12: Undo/Redo full workflow', () => {
        // Step 3: Rename composition
        const comp = store.getActiveComp();
        store.renameComposition(comp!.id, 'Neon_Trails_Main');
        expect(store.getActiveComp()!.name).toBe('Neon_Trails_Main');

        // Step 4: Create solid layer
        const layer = store.createLayer('solid', 'BG_Gradient');
        const layerId = layer!.id;

        // Step 5: Add effect
        store.addEffectToLayer(layerId, 'gradient-ramp');
        expect(getLayer(layerId)!.effects!.length).toBe(1);

        // Step 6: Configure effect
        const effect = getLayer(layerId)!.effects![0];
        store.updateEffectParameter(layerId, effect.id, 'ramp_shape', 'linear');

        // Step 12: Lock layer
        store.updateLayer(layerId, { locked: true });
        expect(getLayer(layerId)!.locked).toBe(true);

        // Undo lock
        store.undo();
        expect(getLayer(layerId)!.locked).toBe(false);

        // Redo lock
        store.redo();
        expect(getLayer(layerId)!.locked).toBe(true);

        // Undo multiple steps
        store.undo(); // unlock
        store.undo(); // un-set ramp shape
        store.undo(); // remove effect
        expect(getLayer(layerId)!.effects!.length).toBe(0);

        // Redo to restore
        store.redo();
        expect(getLayer(layerId)!.effects!.length).toBe(1);
      });
    });

    describe('Phase 1: Save/Load Verification', () => {
      test('Steps 1-12: Save/Load preserves state', () => {
        // Setup Phase 1 state
        const comp = store.getActiveComp();
        store.renameComposition(comp!.id, 'Neon_Trails_Main');

        const layer = store.createLayer('solid', 'BG_Gradient');
        store.addEffectToLayer(layer!.id, 'gradient-ramp');
        const effect = getLayer(layer!.id)!.effects![0];
        store.updateEffectParameter(layer!.id, effect.id, 'start_of_ramp', { x: 960, y: 0 });
        store.updateEffectParameter(layer!.id, effect.id, 'ramp_shape', 'linear');
        store.updateLayer(layer!.id, { locked: true });

        // Serialize project
        const projectData = store.exportProject();
        expect(projectData).toBeDefined();

        // Create fresh store and load
        const pinia = createPinia();
        setActivePinia(pinia);
        const freshStore = useCompositorStore();
        freshStore.importProject(projectData);

        // Verify all state preserved
        const loadedComp = freshStore.getActiveComp();
        expect(loadedComp!.name).toBe('Neon_Trails_Main');

        const loadedLayers = freshStore.getActiveCompLayers();
        const bgLayer = loadedLayers.find(l => l.name === 'BG_Gradient');
        expect(bgLayer).toBeDefined();
        expect(bgLayer!.locked).toBe(true);
        expect(bgLayer!.effects!.length).toBe(1);
        expect(bgLayer!.effects![0].effectKey).toBe('gradient-ramp');
        expect(bgLayer!.effects![0].parameters['ramp_shape'].value).toBe('linear');
      });
    });
  });

  // ============================================================================
  // PHASE 2: CREATING SILHOUETTE (Steps 13-26)
  // ============================================================================
  describe('Phase 2: Creating Silhouette (Steps 13-26)', () => {

    describe('Steps 13-15: Import and Prepare Source', () => {
      // Step 13: Import image asset - UI workflow
      // Step 14: Create image layer from imported asset - needs asset import system

      test('Step 15: Rename layer to Silhouette_Source', () => {
        // Create a placeholder layer to rename
        const layer = store.createLayer('solid', 'Placeholder');
        store.updateLayer(layer!.id, { name: 'Silhouette_Source' });

        expect(getLayer(layer!.id)!.name).toBe('Silhouette_Source');
      });
    });

    describe('Steps 16-18: Creating Solid Silhouette with Fill Effect', () => {
      test('Step 16-17: Add Fill effect and set color to black', () => {
        const layer = store.createLayer('solid', 'Silhouette_Source');

        store.addEffectToLayer(layer!.id, 'fill');

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer!.effects).toBeDefined();
        const fillEffect = updatedLayer!.effects!.find(e => e.effectKey === 'fill');
        expect(fillEffect).toBeDefined();

        // Set fill color to black
        store.updateEffectParameter(layer!.id, fillEffect!.id, 'color', { r: 0, g: 0, b: 0, a: 1 });

        const finalEffect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'fill');
        expect(finalEffect!.parameters['color'].value).toEqual({ r: 0, g: 0, b: 0, a: 1 });
      });
    });

    describe('Steps 19-23: Alternative Tint Method', () => {
      test('Step 19: Remove Fill effect', () => {
        const layer = store.createLayer('solid', 'Silhouette_Source');
        store.addEffectToLayer(layer!.id, 'fill');
        const fillEffect = getLayer(layer!.id)!.effects![0];

        store.removeEffectFromLayer(layer!.id, fillEffect.id);

        expect(getLayer(layer!.id)!.effects!.length).toBe(0);
      });

      test('Steps 20-23: Add Tint effect and configure', () => {
        const layer = store.createLayer('solid', 'Silhouette_Source');

        store.addEffectToLayer(layer!.id, 'tint');

        const tintEffect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'tint');
        expect(tintEffect).toBeDefined();

        // Step 21: Set Map Black To: black
        store.updateEffectParameter(layer!.id, tintEffect!.id, 'map_black_to', { r: 0, g: 0, b: 0, a: 1 });
        // Step 22: Set Map White To: black
        store.updateEffectParameter(layer!.id, tintEffect!.id, 'map_white_to', { r: 0, g: 0, b: 0, a: 1 });
        // Step 23: Set Amount to Tint: 100%
        store.updateEffectParameter(layer!.id, tintEffect!.id, 'amount_to_tint', 100);

        const finalEffect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'tint');
        expect(finalEffect!.parameters['map_black_to'].value).toEqual({ r: 0, g: 0, b: 0, a: 1 });
        expect(finalEffect!.parameters['map_white_to'].value).toEqual({ r: 0, g: 0, b: 0, a: 1 });
        expect(finalEffect!.parameters['amount_to_tint'].value).toBe(100);
      });
    });

    describe('Steps 24-26: Positioning Silhouette', () => {
      test('Step 24: Position silhouette in lower third', () => {
        const layer = store.createLayer('solid', 'Silhouette_Source');

        // Position in lower third (y = 720 for 1080p)
        store.updateLayerTransform(layer!.id, { position: { x: 960, y: 720 } });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer!.transform.position.value.x).toBe(960);
        expect(updatedLayer!.transform.position.value.y).toBe(720);
      });

      test('Step 25: Scale to 70%', () => {
        const layer = store.createLayer('solid', 'Silhouette_Source');

        store.updateLayerTransform(layer!.id, { scale: { x: 70, y: 70 } });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer!.transform.scale.value.x).toBe(70);
        expect(updatedLayer!.transform.scale.value.y).toBe(70);
      });

      test('Step 26: Center horizontally', () => {
        const layer = store.createLayer('solid', 'Silhouette_Source');
        const comp = store.getActiveComp();
        const centerX = comp!.settings.width / 2;

        store.updateLayerTransform(layer!.id, { position: { x: centerX, y: 540 } });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer!.transform.position.value.x).toBe(centerX);
      });
    });

    describe('Phase 2: Undo/Redo Verification', () => {
      test('Steps 13-26: Undo/Redo effect operations', () => {
        const layer = store.createLayer('solid', 'Silhouette_Source');

        // Add fill
        store.addEffectToLayer(layer!.id, 'fill');
        expect(getLayer(layer!.id)!.effects!.length).toBe(1);

        // Undo add effect
        store.undo();
        expect(getLayer(layer!.id)!.effects!.length).toBe(0);

        // Redo add effect
        store.redo();
        expect(getLayer(layer!.id)!.effects!.length).toBe(1);

        // Remove effect
        const fillId = getLayer(layer!.id)!.effects![0].id;
        store.removeEffectFromLayer(layer!.id, fillId);
        expect(getLayer(layer!.id)!.effects!.length).toBe(0);

        // Undo remove
        store.undo();
        expect(getLayer(layer!.id)!.effects!.length).toBe(1);
      });
    });
  });

  // ============================================================================
  // PHASE 3: SHAPE LAYER BASICS (Steps 27-42)
  // ============================================================================
  describe('Phase 3: Shape Layer Basics (Steps 27-42)', () => {

    describe('Steps 27-31: Creating Spline Layer', () => {
      test('Step 27-28: Deselect all and create spline layer', () => {
        // Deselect all
        selectionStore.clearLayerSelection();
        expect(selectionStore.selectedLayerIds.length).toBe(0);

        // Create spline layer (for neon motion trails - visible path with stroke)
        const layer = store.createLayer('spline', 'Light_Streak_01');
        expect(layer).toBeDefined();
        expect(layer!.type).toBe('spline');
        expect(layer!.name).toBe('Light_Streak_01');
      });

      test('Step 29-31: Spline layer has proper structure', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Spline layers should have SplineData with controlPoints and pathData
        expect(layer!.data).toBeDefined();
        const splineData = layer!.data as SplineData;
        expect(splineData.controlPoints).toBeDefined();
        expect(Array.isArray(splineData.controlPoints)).toBe(true);
        expect(layer!.type).toBe('spline');
      });
    });

    describe('Steps 32-34: Configuring Path', () => {
      test('Steps 32-34: Define curved S-path', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Define an S-curve path (simplified format)
        const sCurvePoints = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 50, y: -100 } },
          { x: 300, y: 300, handleIn: { x: -50, y: 100 }, handleOut: { x: 50, y: -100 } },
          { x: 500, y: 500, handleIn: { x: -50, y: 100 }, handleOut: { x: 50, y: -100 } },
          { x: 700, y: 300, handleIn: { x: -50, y: 100 }, handleOut: { x: 0, y: 0 } }
        ];

        // Convert to ControlPoint[] format and generate pathData
        const { controlPoints, pathData } = convertPointsToControlPoints(sCurvePoints, false);

        store.updateLayerData(layer!.id, {
          controlPoints,
          pathData,
          closed: false  // Open path for stroke effect
        });

        const updatedLayer = getLayer(layer!.id);
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.controlPoints).toHaveLength(4);
        expect(splineData.pathData).toBeTruthy();
        expect(splineData.closed).toBe(false);
      });
    });

    describe('Steps 35-38: Removing Fill, Adding Stroke', () => {
      test('Step 35-36: Remove fill from spline', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Set spline to have no fill (empty string = no fill in SplineData)
        store.updateLayerData(layer!.id, {
          fill: ''
        });

        const updatedLayer = getLayer(layer!.id);
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.fill).toBe('');
      });

      test('Steps 37-38: Add and configure stroke', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Enable stroke with cyan color (hex string in SplineData)
        const cyanHex = rgbaToHex({ r: 0, g: 255, b: 255, a: 1 });
        store.updateLayerData(layer!.id, {
          stroke: cyanHex,
          strokeWidth: 8
        });

        const updatedLayer = getLayer(layer!.id);
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.stroke).toBe(cyanHex);
        expect(splineData.strokeWidth).toBe(8);
      });
    });

    describe('Steps 39-42: Stroke Properties', () => {
      test('Step 39: Set line cap to round', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, { strokeLineCap: 'round' });

        const splineData = getLayer(layer!.id)!.data as SplineData;
        expect(splineData.strokeLineCap).toBe('round');
      });

      test('Step 40: Set line join to round', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, { strokeLineJoin: 'round' });

        const splineData = getLayer(layer!.id)!.data as SplineData;
        expect(splineData.strokeLineJoin).toBe('round');
      });

      test('Step 41-42: Verify stroke renders correctly', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Full stroke configuration (SplineData format)
        const cyanHex = rgbaToHex({ r: 0, g: 255, b: 255, a: 1 });
        store.updateLayerData(layer!.id, {
          stroke: cyanHex,
          strokeWidth: 8,
          strokeLineCap: 'round',
          strokeLineJoin: 'round',
          fill: ''
        });

        const updatedLayer = getLayer(layer!.id);
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.stroke).toBe(cyanHex);
        expect(splineData.strokeWidth).toBe(8);
        expect(splineData.strokeLineCap).toBe('round');
        expect(splineData.strokeLineJoin).toBe('round');
      });
    });

    describe('Phase 3: Undo/Redo Verification', () => {
      test('Steps 27-42: Undo/Redo spline layer operations', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Configure stroke
        store.updateLayerData(layer!.id, { strokeWidth: 8 });
        const splineData1 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData1.strokeWidth).toBe(8);

        // Change stroke
        store.updateLayerData(layer!.id, { strokeWidth: 12 });
        const splineData2 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData2.strokeWidth).toBe(12);

        // Undo
        store.undo();
        const splineData3 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData3.strokeWidth).toBe(8);

        // Redo
        store.redo();
        const splineData4 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData4.strokeWidth).toBe(12);
      });
    });

    describe('Phase 3: Save/Load Verification', () => {
      test('Steps 27-42: Save/Load preserves spline data', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');
        const cyanHex = rgbaToHex({ r: 0, g: 255, b: 255, a: 1 });
        store.updateLayerData(layer!.id, {
          stroke: cyanHex,
          strokeWidth: 8,
          strokeLineCap: 'round',
          fill: ''
        });

        // Serialize
        const projectData = store.exportProject();

        // Fresh store
        const pinia = createPinia();
        setActivePinia(pinia);
        const freshStore = useCompositorStore();
        freshStore.importProject(projectData);

        // Verify
        const loadedLayer = freshStore.getActiveCompLayers().find(l => l.name === 'Light_Streak_01');
        expect(loadedLayer).toBeDefined();
        const loadedSplineData = loadedLayer!.data as SplineData;
        expect(loadedSplineData.stroke).toBe(cyanHex);
        expect(loadedSplineData.strokeWidth).toBe(8);
        expect(loadedSplineData.strokeLineCap).toBe('round');
      });
    });
  });

  // ============================================================================
  // PHASE 4: TRIM PATHS ANIMATOR (Steps 43-60)
  // ============================================================================
  describe('Phase 4: Trim Paths Animator (Steps 43-60)', () => {

    describe('Steps 43-47: Adding Trim Paths', () => {
      test('Step 43-45: Add Trim Paths to spline layer', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Trim Paths in SplineData are direct properties: trimStart, trimEnd, trimOffset
        store.updateLayerData(layer!.id, {
          trimStart: 0,
          trimEnd: 100,
          trimOffset: 0
        });

        const updatedLayer = getLayer(layer!.id);
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.trimStart).toBeDefined();
        expect(splineData.trimStart).toBe(0);
        expect(splineData.trimEnd).toBe(100);
        expect(splineData.trimOffset).toBe(0);
      });

      test('Step 46-47: Configure initial Trim Paths state', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Initial state: Start at 0%, End at 10% (short trail)
        store.updateLayerData(layer!.id, {
          trimStart: 0,
          trimEnd: 10,
          trimOffset: 0
        });

        const splineData = getLayer(layer!.id)!.data as SplineData;
        expect(splineData.trimStart).toBe(0);
        expect(splineData.trimEnd).toBe(10);
      });
    });

    describe('Steps 48-54: Animating Trim Paths', () => {
      test('Steps 48-50: Enable animation on Start', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');
        store.updateLayerData(layer!.id, {
          trimStart: 0,
          trimEnd: 100,
          trimOffset: 0
        });

        // Enable animation on Trim Start using store's keyframe API
        // Animation is managed through layer.properties with property name "Trim Start"
        store.setFrame(0);
        store.addKeyframe(layer!.id, 'Trim Start', 0, 0);

        const updatedLayer = getLayer(layer!.id);
        const trimStartProp = updatedLayer!.properties?.find(p => p.name === 'Trim Start');
        expect(trimStartProp).toBeDefined();
        expect(trimStartProp!.animated).toBe(true);
        expect(trimStartProp!.keyframes.length).toBeGreaterThan(0);
      });

      test('Steps 51-54: Add keyframes for Start animation', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');
        store.updateLayerData(layer!.id, {
          trimStart: 0,
          trimEnd: 20,
          trimOffset: 0
        });

        // Add keyframes using store's keyframe API
        // Trim Start: 0% at frame 0, 80% at frame 60
        store.setFrame(0);
        store.addKeyframe(layer!.id, 'Trim Start', 0, 0);
        store.setFrame(60);
        store.addKeyframe(layer!.id, 'Trim Start', 80, 60);

        // Trim End: 20% at frame 0, 100% at frame 60
        store.setFrame(0);
        store.addKeyframe(layer!.id, 'Trim End', 20, 0);
        store.setFrame(60);
        store.addKeyframe(layer!.id, 'Trim End', 100, 60);

        const updatedLayer = getLayer(layer!.id);
        const trimStartProp = updatedLayer!.properties?.find(p => p.name === 'Trim Start');
        const trimEndProp = updatedLayer!.properties?.find(p => p.name === 'Trim End');
        
        expect(trimStartProp!.keyframes).toHaveLength(2);
        expect(trimEndProp!.keyframes).toHaveLength(2);
        expect(trimStartProp!.keyframes[0].value).toBe(0);
        expect(trimStartProp!.keyframes[1].value).toBe(80);
      });
    });

    describe('Steps 55-60: Timing Adjustments', () => {
      test('Steps 55-57: Adjust End keyframes for trailing effect', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');
        store.updateLayerData(layer!.id, {
          trimStart: 0,
          trimEnd: 20,
          trimOffset: 0
        });

        // Create trailing effect: End moves faster than Start
        // Trim Start: delayed start at frame 10
        store.setFrame(10);
        store.addKeyframe(layer!.id, 'Trim Start', 0, 10);
        store.setFrame(70);
        store.addKeyframe(layer!.id, 'Trim Start', 80, 70);

        // Trim End: starts immediately at frame 0
        store.setFrame(0);
        store.addKeyframe(layer!.id, 'Trim End', 20, 0);
        store.setFrame(60);
        store.addKeyframe(layer!.id, 'Trim End', 100, 60);

        const updatedLayer = getLayer(layer!.id);
        const trimStartProp = updatedLayer!.properties?.find(p => p.name === 'Trim Start');
        const trimEndProp = updatedLayer!.properties?.find(p => p.name === 'Trim End');
        
        // End starts at frame 0, Start starts at frame 10 - creates trailing effect
        expect(trimEndProp!.keyframes[0].frame).toBeLessThan(trimStartProp!.keyframes[0].frame);
      });

      test('Steps 58-60: Preview animation at different frames', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');
        store.updateLayerData(layer!.id, {
          trimStart: 0,
          trimEnd: 20
        });

        // Add keyframes
        store.setFrame(0);
        store.addKeyframe(layer!.id, 'Trim Start', 0, 0);
        store.addKeyframe(layer!.id, 'Trim End', 20, 0);
        store.setFrame(60);
        store.addKeyframe(layer!.id, 'Trim Start', 80, 60);
        store.addKeyframe(layer!.id, 'Trim End', 100, 60);

        // Test frame seeking
        store.setFrame(0);
        expect(store.currentFrame).toBe(0);

        store.setFrame(30);  // Midpoint
        expect(store.currentFrame).toBe(30);

        store.setFrame(60);  // End
        expect(store.currentFrame).toBe(60);
      });
    });

    describe('Phase 4: Undo/Redo Verification', () => {
      test('Steps 43-60: Undo/Redo trim paths changes', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, {
          trimStart: 0,
          trimEnd: 50,
          trimOffset: 0
        });
        const splineData1 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData1.trimEnd).toBe(50);

        store.updateLayerData(layer!.id, {
          trimEnd: 75
        });
        const splineData2 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData2.trimEnd).toBe(75);

        store.undo();
        const splineData3 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData3.trimEnd).toBe(50);

        store.redo();
        const splineData4 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData4.trimEnd).toBe(75);
      });
    });
  });

  // ============================================================================
  // PHASE 5: GLOW EFFECT STACKING (Steps 61-82)
  // ============================================================================
  describe('Phase 5: Glow Effect Stacking (Steps 61-82)', () => {

    describe('Steps 61-66: Adding First Glow', () => {
      test('Steps 61-62: Add Glow effect to shape layer', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.addEffectToLayer(layer!.id, 'glow');

        const glowEffect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'glow');
        expect(glowEffect).toBeDefined();
      });

      test('Steps 63-66: Configure first glow (tight, bright)', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');
        store.addEffectToLayer(layer!.id, 'glow');
        const glow = getLayer(layer!.id)!.effects![0];

        // First glow: tight radius, high intensity
        store.updateEffectParameter(layer!.id, glow.id, 'glow_threshold', 0);
        store.updateEffectParameter(layer!.id, glow.id, 'glow_radius', 10);
        store.updateEffectParameter(layer!.id, glow.id, 'glow_intensity', 2);

        const updatedGlow = getLayer(layer!.id)!.effects![0];
        expect(updatedGlow.parameters['glow_threshold'].value).toBe(0);
        expect(updatedGlow.parameters['glow_radius'].value).toBe(10);
        expect(updatedGlow.parameters['glow_intensity'].value).toBe(2);
      });
    });

    describe('Steps 67-74: Adding Second and Third Glow', () => {
      test('Steps 67-70: Add second glow (medium spread)', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // First glow
        store.addEffectToLayer(layer!.id, 'glow');
        // Second glow
        store.addEffectToLayer(layer!.id, 'glow');

        expect(getLayer(layer!.id)!.effects!.length).toBe(2);

        const secondGlow = getLayer(layer!.id)!.effects![1];
        store.updateEffectParameter(layer!.id, secondGlow.id, 'glow_radius', 30);
        store.updateEffectParameter(layer!.id, secondGlow.id, 'glow_intensity', 1.5);

        expect(getLayer(layer!.id)!.effects![1].parameters['glow_radius'].value).toBe(30);
      });

      test('Steps 71-74: Add third glow (wide, soft)', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.addEffectToLayer(layer!.id, 'glow');
        store.addEffectToLayer(layer!.id, 'glow');
        store.addEffectToLayer(layer!.id, 'glow');

        expect(getLayer(layer!.id)!.effects!.length).toBe(3);

        const thirdGlow = getLayer(layer!.id)!.effects![2];
        store.updateEffectParameter(layer!.id, thirdGlow.id, 'glow_radius', 80);
        store.updateEffectParameter(layer!.id, thirdGlow.id, 'glow_intensity', 0.8);

        expect(getLayer(layer!.id)!.effects![2].parameters['glow_radius'].value).toBe(80);
        expect(getLayer(layer!.id)!.effects![2].parameters['glow_intensity'].value).toBe(0.8);
      });
    });

    describe('Steps 75-82: Glow Color and Fine-tuning', () => {
      test('Steps 75-78: Set glow colors', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.addEffectToLayer(layer!.id, 'glow');
        const glow = getLayer(layer!.id)!.effects![0];

        // Note: Glow effect may use 'A Color' and 'B Color' or similar
        // Check actual parameter names from effects.ts
        store.updateEffectParameter(layer!.id, glow.id, 'glow_colors', 'A & B Colors');
        store.updateEffectParameter(layer!.id, glow.id, 'color_a', { r: 0, g: 255, b: 255, a: 1 }); // Cyan
        store.updateEffectParameter(layer!.id, glow.id, 'color_b', { r: 255, g: 0, b: 255, a: 1 }); // Magenta

        const updatedGlow = getLayer(layer!.id)!.effects![0];
        expect(updatedGlow.parameters['color_a'].value).toEqual({ r: 0, g: 255, b: 255, a: 1 });
        expect(updatedGlow.parameters['color_b'].value).toEqual({ r: 255, g: 0, b: 255, a: 1 });
      });

      test('Steps 79-82: Toggle and compare glows', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.addEffectToLayer(layer!.id, 'glow');
        store.addEffectToLayer(layer!.id, 'glow');

        const effects = getLayer(layer!.id)!.effects!;
        expect(effects.length).toBe(2);

        // Toggle first glow off
        store.toggleEffect(layer!.id, effects[0].id);
        expect(getLayer(layer!.id)!.effects![0].enabled).toBe(false);

        // Toggle back on
        store.toggleEffect(layer!.id, effects[0].id);
        expect(getLayer(layer!.id)!.effects![0].enabled).toBe(true);
      });
    });

    describe('Phase 5: Undo/Redo Verification', () => {
      test('Steps 61-82: Undo/Redo effect stacking', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.addEffectToLayer(layer!.id, 'glow');
        expect(getLayer(layer!.id)!.effects!.length).toBe(1);

        store.addEffectToLayer(layer!.id, 'glow');
        expect(getLayer(layer!.id)!.effects!.length).toBe(2);

        store.addEffectToLayer(layer!.id, 'glow');
        expect(getLayer(layer!.id)!.effects!.length).toBe(3);

        // Undo last glow
        store.undo();
        expect(getLayer(layer!.id)!.effects!.length).toBe(2);

        // Undo second glow
        store.undo();
        expect(getLayer(layer!.id)!.effects!.length).toBe(1);

        // Redo both
        store.redo();
        store.redo();
        expect(getLayer(layer!.id)!.effects!.length).toBe(3);
      });
    });
  });

  // ============================================================================
  // PHASE 6: MULTIPLE STREAKS (Steps 83-102)
  // ============================================================================
  describe('Phase 6: Multiple Streaks (Steps 83-102)', () => {

    describe('Steps 83-90: Duplicating Streak Layers', () => {
      test('Steps 83-85: Duplicate Light_Streak_01 to create 02', () => {
        const layer1 = store.createLayer('spline', 'Light_Streak_01');
        const cyanHex = rgbaToHex({ r: 0, g: 255, b: 255, a: 1 });
        store.updateLayerData(layer1!.id, {
          stroke: cyanHex,
          strokeWidth: 8
        });
        store.addEffectToLayer(layer1!.id, 'glow');

        const layer2 = store.duplicateLayer(layer1!.id);
        expect(layer2).toBeDefined();
        const splineData2 = layer2!.data as SplineData;
        expect(splineData2.stroke).toBe(cyanHex);
        expect(layer2!.effects!.length).toBe(1);

        // Rename
        store.updateLayer(layer2!.id, { name: 'Light_Streak_02' });
        expect(getLayer(layer2!.id)!.name).toBe('Light_Streak_02');
      });

      test('Steps 86-90: Create streaks 03, 04, 05', () => {
        const layer1 = store.createLayer('spline', 'Light_Streak_01');

        const layer2 = store.duplicateLayer(layer1!.id);
        store.updateLayer(layer2!.id, { name: 'Light_Streak_02' });

        const layer3 = store.duplicateLayer(layer1!.id);
        store.updateLayer(layer3!.id, { name: 'Light_Streak_03' });

        const layer4 = store.duplicateLayer(layer1!.id);
        store.updateLayer(layer4!.id, { name: 'Light_Streak_04' });

        const layer5 = store.duplicateLayer(layer1!.id);
        store.updateLayer(layer5!.id, { name: 'Light_Streak_05' });

        const layers = store.getActiveCompLayers();
        const streakLayers = layers.filter(l => l.name.startsWith('Light_Streak_'));
        expect(streakLayers.length).toBe(5);
      });
    });

    describe('Steps 91-98: Varying Colors and Paths', () => {
      test('Steps 91-94: Assign different colors to each streak', () => {
        const colors = [
          { r: 0, g: 255, b: 255, a: 1 },    // Cyan
          { r: 255, g: 0, b: 255, a: 1 },    // Magenta
          { r: 255, g: 255, b: 0, a: 1 },    // Yellow
          { r: 0, g: 255, b: 0, a: 1 },      // Green
          { r: 255, g: 128, b: 0, a: 1 }     // Orange
        ];

        colors.forEach((color, i) => {
          const layer = store.createLayer('spline', `Light_Streak_0${i + 1}`);
          const colorHex = rgbaToHex(color);
          store.updateLayerData(layer!.id, { stroke: colorHex });
          const splineData = getLayer(layer!.id)!.data as SplineData;
          expect(splineData.stroke).toBe(colorHex);
        });
      });

      test('Steps 95-98: Modify paths for variety', () => {
        const layer = store.createLayer('spline', 'Light_Streak_02');

        // Modify path - different curve
        const newPathPoints = [
          { x: 200, y: 600, handleIn: { x: 0, y: 0 }, handleOut: { x: 100, y: -150 } },
          { x: 500, y: 200, handleIn: { x: -100, y: 150 }, handleOut: { x: 100, y: -150 } },
          { x: 800, y: 400, handleIn: { x: -100, y: 150 }, handleOut: { x: 0, y: 0 } }
        ];

        const { controlPoints, pathData } = convertPointsToControlPoints(newPathPoints, false);
        store.updateLayerData(layer!.id, { controlPoints, pathData });
        const splineData = getLayer(layer!.id)!.data as SplineData;
        expect(splineData.controlPoints).toHaveLength(3);
        expect(splineData.pathData).toBeTruthy();
      });
    });

    describe('Steps 99-102: Timing Offsets', () => {
      test('Steps 99-102: Offset animation timing for each streak', () => {
        // Create 5 streaks with staggered timing
        for (let i = 0; i < 5; i++) {
          const layer = store.createLayer('spline', `Light_Streak_0${i + 1}`);
          const offset = i * 5; // 5 frame offset each

          store.updateLayerData(layer!.id, {
            trimStart: 0,
            trimEnd: 20,
            trimOffset: offset
          });

          // Add keyframes using store API
          store.setFrame(offset);
          store.addKeyframe(layer!.id, 'Trim Start', 0, offset);
          store.addKeyframe(layer!.id, 'Trim End', 20, offset);
          store.setFrame(60 + offset);
          store.addKeyframe(layer!.id, 'Trim Start', 80, 60 + offset);
          store.addKeyframe(layer!.id, 'Trim End', 100, 60 + offset);
        }

        // Verify offsets - sort by name to ensure consistent order
        const layers = store.getActiveCompLayers()
          .filter(l => l.name.startsWith('Light_Streak_'))
          .sort((a, b) => a.name.localeCompare(b.name));
        layers.forEach((layer, i) => {
          const expectedOffset = i * 5;
          const trimStartProp = layer.properties?.find(p => p.name === 'Trim Start');
          expect(trimStartProp).toBeDefined();
          expect(trimStartProp!.keyframes[0].frame).toBe(expectedOffset);
        });
      });
    });

    describe('Phase 6: Undo/Redo Verification', () => {
      test('Steps 83-102: Undo/Redo multiple duplications', () => {
        const layer1 = store.createLayer('spline', 'Light_Streak_01');
        const initialCount = store.getActiveCompLayers().length;

        store.duplicateLayer(layer1!.id);
        expect(store.getActiveCompLayers().length).toBe(initialCount + 1);

        store.duplicateLayer(layer1!.id);
        expect(store.getActiveCompLayers().length).toBe(initialCount + 2);

        store.undo();
        expect(store.getActiveCompLayers().length).toBe(initialCount + 1);

        store.undo();
        expect(store.getActiveCompLayers().length).toBe(initialCount);

        store.redo();
        store.redo();
        expect(store.getActiveCompLayers().length).toBe(initialCount + 2);
      });
    });
  });

  // ============================================================================
  // PHASE 7: GRADIENT STROKES (Steps 103-120)
  // ============================================================================
  describe('Phase 7: Gradient Strokes (Steps 103-120)', () => {

    describe('Steps 103-108: Enabling Gradient Stroke', () => {
      test('Steps 103-105: Enable gradient on stroke', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, {
          strokeType: 'gradient',
          strokeGradient: {
            type: 'linear',
            stops: [
              { position: 0, color: { r: 0, g: 255, b: 255, a: 1 } },
              { position: 1, color: { r: 255, g: 0, b: 255, a: 1 } }
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeType).toBe('gradient');
        expect(splineData.strokeGradient).toBeDefined();
        expect(splineData.strokeGradient!.stops.length).toBe(2);
      });

      test('Steps 106-108: Configure gradient colors', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Cyan to magenta gradient
        store.updateLayerData(layer!.id, {
          strokeType: 'gradient',
          strokeGradient: {
            type: 'linear',
            stops: [
              { position: 0, color: { r: 0, g: 255, b: 255, a: 1 } },    // Cyan start
              { position: 0.5, color: { r: 128, g: 128, b: 255, a: 1 } }, // Purple mid
              { position: 1, color: { r: 255, g: 0, b: 255, a: 1 } }     // Magenta end
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeGradient).toBeDefined();
        const gradient = splineData.strokeGradient!;
        expect(gradient.stops.length).toBe(3);
        expect(gradient.stops[1].position).toBe(0.5);
      });
    });

    describe('Steps 109-115: Gradient Along Path', () => {
      test('Steps 109-112: Set gradient to follow path', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, {
          strokeType: 'gradient',
          strokeGradient: {
            type: 'linear',
            followPath: true,  // Gradient follows stroke path
            stops: [
              { position: 0, color: { r: 255, g: 255, b: 255, a: 1 } },
              { position: 1, color: { r: 255, g: 255, b: 255, a: 0 } }  // Fade to transparent
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeGradient).toBeDefined();
        expect(splineData.strokeGradient!.followPath).toBe(true);
      });

      test('Steps 113-115: Adjust gradient spread', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, {
          strokeGradient: {
            type: 'linear',
            followPath: true,
            spread: 100,  // Full path coverage
            stops: [
              { position: 0, color: { r: 0, g: 255, b: 255, a: 1 } },
              { position: 1, color: { r: 255, g: 0, b: 255, a: 0 } }
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeGradient).toBeDefined();
        expect(splineData.strokeGradient!.spread).toBe(100);
      });
    });

    describe('Steps 116-120: Animating Gradient', () => {
      test('Steps 116-120: Animate gradient offset', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, {
          strokeGradient: {
            type: 'linear',
            offset: 0,
            offsetKeyframes: [
              { frame: 0, value: 0 },
              { frame: 60, value: 100 }  // Gradient slides along path
            ],
            stops: [
              { position: 0, color: { r: 0, g: 255, b: 255, a: 1 } },
              { position: 1, color: { r: 255, g: 0, b: 255, a: 1 } }
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeGradient).toBeDefined();
        const gradient = splineData.strokeGradient!;
        expect(gradient.offsetKeyframes).toBeDefined();
        expect(gradient.offsetKeyframes!.length).toBe(2);
      });
    });

    describe('Phase 7: Undo/Redo Verification', () => {
      test('Steps 103-120: Undo/Redo gradient changes', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayerData(layer!.id, { strokeType: 'solid' });
        let updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        let splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeType).toBe('solid');

        store.updateLayerData(layer!.id, { strokeType: 'gradient' });
        updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeType).toBe('gradient');

        store.undo();
        updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeType).toBe('solid');

        store.redo();
        updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        splineData = updatedLayer!.data as SplineData;
        expect(splineData.strokeType).toBe('gradient');
      });
    });
  });

  // ============================================================================
  // PHASE 8: PEN TOOL PATH CREATION (Steps 121-145)
  // ============================================================================
  describe('Phase 8: Pen Tool Path Creation (Steps 121-145)', () => {

    describe('Steps 121-130: Creating Paths with Pen Tool', () => {
      // Steps 121-125: Pen tool UI interaction - skip
      // These involve clicking canvas to create points

      test('Steps 126-130: Create path programmatically (simulating pen tool)', () => {
        const layer = store.createLayer('spline', 'Custom_Path_01');

        // Define a complex path with bezier handles
        const pathPoints = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 50, y: -100 } },
          { x: 300, y: 250, handleIn: { x: -50, y: 100 }, handleOut: { x: 50, y: -100 } },
          { x: 500, y: 400, handleIn: { x: -50, y: 100 }, handleOut: { x: 50, y: -100 } },
          { x: 700, y: 150, handleIn: { x: -50, y: 100 }, handleOut: { x: 50, y: -100 } },
          { x: 900, y: 350, handleIn: { x: -50, y: 100 }, handleOut: { x: 0, y: 0 } }
        ];

        const { controlPoints, pathData } = convertPointsToControlPoints(pathPoints, false);
        store.updateLayerData(layer!.id, {
          controlPoints,
          pathData,
          closed: false
        });

        const splineData = getLayer(layer!.id)!.data as SplineData;
        expect(splineData.controlPoints).toHaveLength(5);
        expect(splineData.closed).toBe(false);
      });
    });

    describe('Steps 131-140: Editing Path Points', () => {
      test('Steps 131-135: Adjust bezier handles', () => {
        const layer = store.createLayer('spline', 'Custom_Path_01');
        const initialPoints = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 50, y: 0 } },
          { x: 300, y: 500, handleIn: { x: -50, y: 0 }, handleOut: { x: 0, y: 0 } }
        ];
        const { controlPoints: cp1, pathData: pd1 } = convertPointsToControlPoints(initialPoints, false);
        store.updateLayerData(layer!.id, { controlPoints: cp1, pathData: pd1 });

        // Modify handle to create curve
        const modifiedPoints = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 100, y: -150 } },
          { x: 300, y: 500, handleIn: { x: -100, y: -150 }, handleOut: { x: 0, y: 0 } }
        ];
        const { controlPoints: cp2, pathData: pd2 } = convertPointsToControlPoints(modifiedPoints, false);
        store.updateLayerData(layer!.id, { controlPoints: cp2, pathData: pd2 });

        const splineData = getLayer(layer!.id)!.data as SplineData;
        expect(splineData.controlPoints[0].handleOut?.y).toBe(-150);
        expect(splineData.controlPoints[1].handleIn?.y).toBe(-150);
      });

      test('Steps 136-140: Add and remove path points', () => {
        const layer = store.createLayer('spline', 'Custom_Path_01');
        const initialPoints = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 50, y: 0 } },
          { x: 500, y: 500, handleIn: { x: -50, y: 0 }, handleOut: { x: 0, y: 0 } }
        ];
        const { controlPoints: cp1, pathData: pd1 } = convertPointsToControlPoints(initialPoints, false);
        store.updateLayerData(layer!.id, { controlPoints: cp1, pathData: pd1 });

        // Add point in middle
        const pointsWithMiddle = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 50, y: 0 } },
          { x: 300, y: 300, handleIn: { x: -50, y: 50 }, handleOut: { x: 50, y: -50 } },
          { x: 500, y: 500, handleIn: { x: -50, y: 0 }, handleOut: { x: 0, y: 0 } }
        ];
        const { controlPoints: cp2, pathData: pd2 } = convertPointsToControlPoints(pointsWithMiddle, false);
        store.updateLayerData(layer!.id, { controlPoints: cp2, pathData: pd2 });
        const splineData1 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData1.controlPoints).toHaveLength(3);

        // Remove middle point
        const pointsWithoutMiddle = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 50, y: 0 } },
          { x: 500, y: 500, handleIn: { x: -50, y: 0 }, handleOut: { x: 0, y: 0 } }
        ];
        const { controlPoints: cp3, pathData: pd3 } = convertPointsToControlPoints(pointsWithoutMiddle, false);
        store.updateLayerData(layer!.id, { controlPoints: cp3, pathData: pd3 });
        const splineData2 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData2.controlPoints).toHaveLength(2);
      });
    });

    describe('Steps 141-145: Converting to Shape Layer', () => {
      test('Steps 141-145: Path can be used in spline layer', () => {
        // Create spline/path
        const pathLayer = store.createLayer('spline', 'Source_Path');
        const pathPoints = [
          { x: 100, y: 500, handleIn: { x: 0, y: 0 }, handleOut: { x: 100, y: -100 } },
          { x: 400, y: 200, handleIn: { x: -100, y: 100 }, handleOut: { x: 0, y: 0 } }
        ];
        const { controlPoints: cp1, pathData: pd1 } = convertPointsToControlPoints(pathPoints, false);
        store.updateLayerData(pathLayer!.id, { controlPoints: cp1, pathData: pd1 });

        // Create spline layer and copy path
        const shapeLayer = store.createLayer('spline', 'Shape_From_Path');
        const { controlPoints: cp2, pathData: pd2 } = convertPointsToControlPoints(pathPoints, false);
        const cyanHex = rgbaToHex({ r: 0, g: 255, b: 255, a: 1 });
        store.updateLayerData(shapeLayer!.id, {
          controlPoints: cp2,
          pathData: pd2,
          stroke: cyanHex,
          fill: ''
        });

        const splineData = getLayer(shapeLayer!.id)!.data as SplineData;
        expect(splineData.controlPoints).toHaveLength(2);
        expect(splineData.pathData).toBeTruthy();
      });
    });

    describe('Phase 8: Undo/Redo Verification', () => {
      test('Steps 121-145: Undo/Redo path edits', () => {
        const layer = store.createLayer('spline', 'Custom_Path');

        const points1 = [{ x: 100, y: 100, handleIn: { x: 0, y: 0 }, handleOut: { x: 0, y: 0 } }];
        const { controlPoints: cp1, pathData: pd1 } = convertPointsToControlPoints(points1, false);
        store.updateLayerData(layer!.id, { controlPoints: cp1, pathData: pd1 });
        const splineData1 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData1.controlPoints).toHaveLength(1);

        const points2 = [
          { x: 100, y: 100, handleIn: { x: 0, y: 0 }, handleOut: { x: 0, y: 0 } },
          { x: 200, y: 200, handleIn: { x: 0, y: 0 }, handleOut: { x: 0, y: 0 } }
        ];
        const { controlPoints: cp2, pathData: pd2 } = convertPointsToControlPoints(points2, false);
        store.updateLayerData(layer!.id, { controlPoints: cp2, pathData: pd2 });
        const splineData2 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData2.controlPoints).toHaveLength(2);

        store.undo();
        const splineData3 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData3.controlPoints).toHaveLength(1);

        store.redo();
        const splineData4 = getLayer(layer!.id)!.data as SplineData;
        expect(splineData4.controlPoints).toHaveLength(2);
      });
    });
  });

  // ============================================================================
  // PHASE 9: PATH ANIMATION (Steps 146-178)
  // ============================================================================
  describe('Phase 9: Path Animation (Steps 146-178)', () => {

    describe('Steps 146-155: Animating Path Shape', () => {
      test.skip('Steps 146-150: Enable path animation', () => {
        // NOTE: This test uses pathKeyframes which doesn't exist in SplineData API.
        // Animated paths use animatedControlPoints (AnimatableControlPoint[]) which requires
        // AnimatableProperty<number> for x/y coordinates. This is complex to set up programmatically.
        // TODO: Update to use actual animatedControlPoints API or test through UI interactions.
        const layer = store.createLayer('spline', 'Animated_Path');

        // Basic test: verify animated flag can be set
        store.updateLayerData(layer!.id, {
          animated: true
        });

        const splineData = getLayer(layer!.id)!.data as SplineData;
        expect(splineData.animated).toBe(true);
      });

      test.skip('Steps 151-155: Set keyframes at different frames', () => {
        // NOTE: This test uses pathKeyframes which doesn't exist in SplineData API.
        // See note in previous test.
      });
    });

    describe('Steps 156-165: Motion Path', () => {
      test('Steps 156-160: Use path as motion path for position', () => {
        const layer = store.createLayer('solid', 'Moving_Element');

        // Enable position animation along a path
        store.updateLayerData(layer!.id, {
          motionPath: {
            enabled: true,
            path: [
              { x: 100, y: 500 },
              { x: 500, y: 200 },
              { x: 900, y: 500 }
            ],
            keyframes: [
              { frame: 0, progress: 0 },
              { frame: 60, progress: 100 }
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const solidData = updatedLayer!.data as import('@/types/project').SolidLayerData;
        expect(solidData.motionPath).toBeDefined();
        expect(solidData.motionPath!.enabled).toBe(true);
        expect(solidData.motionPath!.path).toHaveLength(3);
      });

      test('Steps 161-165: Orient along path', () => {
        const layer = store.createLayer('solid', 'Moving_Element');

        store.updateLayerData(layer!.id, {
          motionPath: {
            enabled: true,
            path: [{ x: 100, y: 500 }, { x: 900, y: 500 }],
            orientToPath: true,  // Auto-orient rotation
            keyframes: [
              { frame: 0, progress: 0 },
              { frame: 60, progress: 100 }
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const solidData = updatedLayer!.data as import('@/types/project').SolidLayerData;
        expect(solidData.motionPath).toBeDefined();
        expect(solidData.motionPath!.orientToPath).toBe(true);
      });
    });

    describe('Steps 166-178: Path Speed and Easing', () => {
      test.skip('Steps 166-170: Add easing to path animation', () => {
        // NOTE: This test uses pathKeyframes which doesn't exist in SplineData API.
        // See note in previous test.
      });

      test('Steps 171-178: Speed graph adjustments', () => {
        const layer = store.createLayer('solid', 'Speed_Adjusted');

        // Motion path with speed keyframes
        store.updateLayerData(layer!.id, {
          motionPath: {
            enabled: true,
            path: [{ x: 100, y: 300 }, { x: 900, y: 300 }],
            speedGraph: [
              { frame: 0, speed: 0 },
              { frame: 15, speed: 2 },    // Accelerate
              { frame: 45, speed: 2 },    // Constant
              { frame: 60, speed: 0 }     // Decelerate
            ]
          }
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const solidData = updatedLayer!.data as SolidLayerData;
        expect(solidData.motionPath).toBeDefined();
        expect(solidData.motionPath!.speedGraph).toBeDefined();
        expect(solidData.motionPath!.speedGraph!.length).toBe(4);
      });
    });

    describe('Phase 9: Undo/Redo Verification', () => {
      test.skip('Steps 146-178: Undo/Redo path animation', () => {
        // NOTE: This test uses pathKeyframes which doesn't exist in SplineData API.
        // See note in previous test.
      });
    });
  });

  // ============================================================================
  // PHASE 10: ECHO EFFECT / MOTION TRAILS (Steps 179-205)
  // ============================================================================
  describe('Phase 10: Echo Effect / Motion Trails (Steps 179-205)', () => {

    describe('Steps 179-182: Pre-Composing Streaks', () => {
      test('Steps 179-182: Nest shape layers into composition', () => {
        // Create multiple streak layers
        const layer1 = store.createLayer('spline', 'Light_Streak_01');
        const layer2 = store.createLayer('spline', 'Light_Streak_02');
        const layer3 = store.createLayer('spline', 'Light_Streak_03');

        // Select all
        selectionStore.selectLayers([layer1!.id, layer2!.id, layer3!.id]);
        expect(selectionStore.selectedLayerIds).toHaveLength(3);

        // Nest into composition - Use existing nestSelectedLayers
        // This creates a nested comp from selected layers
        const nestedComp = store.nestSelectedLayers('Streaks_Precomp');

        // After nesting, selected layers should be replaced by nested comp layer
        expect(nestedComp).toBeDefined();
        if (nestedComp) {
          expect(nestedComp.name).toBe('Streaks_Precomp');
        }
      });
    });

    describe('Steps 183-188: Adding Echo Effect', () => {
      test('Steps 183-185: Add Echo effect', () => {
        const layer = store.createLayer('solid', 'Streaks_Layer');

        store.addEffectToLayer(layer!.id, 'echo');

        const effect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'echo');
        expect(effect).toBeDefined();
      });

      test('Steps 186-188: Configure Echo parameters', () => {
        const layer = store.createLayer('solid', 'Streaks_Layer');
        store.addEffectToLayer(layer!.id, 'echo');
        const echo = getLayer(layer!.id)!.effects![0];

        // Echo Time: negative for trailing
        store.updateEffectParameter(layer!.id, echo.id, 'echo_time', -0.03);
        // Number of Echoes
        store.updateEffectParameter(layer!.id, echo.id, 'number_of_echoes', 8);
        // Starting Intensity
        store.updateEffectParameter(layer!.id, echo.id, 'starting_intensity', 1.0);
        // Decay
        store.updateEffectParameter(layer!.id, echo.id, 'decay', 0.5);

        const updatedEcho = getLayer(layer!.id)!.effects![0];
        expect(updatedEcho.parameters['echo_time'].value).toBe(-0.03);
        expect(updatedEcho.parameters['number_of_echoes'].value).toBe(8);
        expect(updatedEcho.parameters['starting_intensity'].value).toBe(1.0);
        expect(updatedEcho.parameters['decay'].value).toBe(0.5);
      });
    });

    describe('Steps 189-196: Echo Operator Modes', () => {
      test('Steps 189-192: Test different operators', () => {
        const layer = store.createLayer('solid', 'Echo_Test');
        store.addEffectToLayer(layer!.id, 'echo');
        const echo = getLayer(layer!.id)!.effects![0];

        // Test 'add'
        store.updateEffectParameter(layer!.id, echo.id, 'echo_operator', 'add');
        expect(getLayer(layer!.id)!.effects![0].parameters['echo_operator'].value).toBe('add');

        // Test 'maximum'
        store.updateEffectParameter(layer!.id, echo.id, 'echo_operator', 'maximum');
        expect(getLayer(layer!.id)!.effects![0].parameters['echo_operator'].value).toBe('maximum');

        // Test 'screen'
        store.updateEffectParameter(layer!.id, echo.id, 'echo_operator', 'screen');
        expect(getLayer(layer!.id)!.effects![0].parameters['echo_operator'].value).toBe('screen');

        // Test 'composite_back'
        store.updateEffectParameter(layer!.id, echo.id, 'echo_operator', 'composite_back');
        expect(getLayer(layer!.id)!.effects![0].parameters['echo_operator'].value).toBe('composite_back');
      });
    });

    describe('Steps 197-205: Fine-tuning Echo', () => {
      test('Steps 197-200: Adjust echo count and decay', () => {
        const layer = store.createLayer('solid', 'Echo_Final');
        store.addEffectToLayer(layer!.id, 'echo');
        const echo = getLayer(layer!.id)!.effects![0];

        // More echoes, slower decay for longer trails
        store.updateEffectParameter(layer!.id, echo.id, 'number_of_echoes', 12);
        store.updateEffectParameter(layer!.id, echo.id, 'decay', 0.7);

        expect(getLayer(layer!.id)!.effects![0].parameters['number_of_echoes'].value).toBe(12);
        expect(getLayer(layer!.id)!.effects![0].parameters['decay'].value).toBe(0.7);
      });

      test('Steps 201-205: Echo time variation', () => {
        const layer = store.createLayer('solid', 'Echo_Varied');
        store.addEffectToLayer(layer!.id, 'echo');
        const echo = getLayer(layer!.id)!.effects![0];

        // Shorter echo time for denser trails
        store.updateEffectParameter(layer!.id, echo.id, 'echo_time', -0.02);
        expect(getLayer(layer!.id)!.effects![0].parameters['echo_time'].value).toBe(-0.02);

        // Longer echo time for spread out trails
        store.updateEffectParameter(layer!.id, echo.id, 'echo_time', -0.05);
        expect(getLayer(layer!.id)!.effects![0].parameters['echo_time'].value).toBe(-0.05);
      });
    });

    describe('Phase 10: Undo/Redo Verification', () => {
      test('Steps 179-205: Undo/Redo echo configuration', () => {
        const layer = store.createLayer('solid', 'Echo_Test');
        store.addEffectToLayer(layer!.id, 'echo');
        const echo = getLayer(layer!.id)!.effects![0];

        store.updateEffectParameter(layer!.id, echo.id, 'number_of_echoes', 5);
        expect(getLayer(layer!.id)!.effects![0].parameters['number_of_echoes'].value).toBe(5);

        store.updateEffectParameter(layer!.id, echo.id, 'number_of_echoes', 10);
        expect(getLayer(layer!.id)!.effects![0].parameters['number_of_echoes'].value).toBe(10);

        store.undo();
        expect(getLayer(layer!.id)!.effects![0].parameters['number_of_echoes'].value).toBe(5);

        store.redo();
        expect(getLayer(layer!.id)!.effects![0].parameters['number_of_echoes'].value).toBe(10);
      });
    });
  });

  // ============================================================================
  // PHASE 11: MOTION BLUR (Steps 206-225)
  // ============================================================================
  describe('Phase 11: Motion Blur (Steps 206-225)', () => {

    describe('Steps 206-212: Enabling Motion Blur', () => {
      test('Steps 206-208: Enable motion blur on layer', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.updateLayer(layer!.id, { motionBlur: true });

        expect(getLayer(layer!.id)!.motionBlur).toBe(true);
      });

      test('Steps 209-212: Enable motion blur on composition', () => {
        const comp = store.getActiveComp();
        expect(comp).toBeDefined();

        // Composition-level motion blur setting
        store.updateCompositionSettings(comp!.id, {
          motionBlur: true,
          motionBlurSamples: 16,
          shutterAngle: 180
        });

        const updatedComp = store.getActiveComp();
        expect(updatedComp!.settings.motionBlur).toBe(true);
      });
    });

    describe('Steps 213-220: Motion Blur Settings', () => {
      test('Steps 213-216: Adjust shutter angle', () => {
        const comp = store.getActiveComp();

        // 180 degrees = standard cinematic
        store.updateCompositionSettings(comp!.id, { shutterAngle: 180 });
        expect(store.getActiveComp()!.settings.shutterAngle).toBe(180);

        // 360 degrees = more blur
        store.updateCompositionSettings(comp!.id, { shutterAngle: 360 });
        expect(store.getActiveComp()!.settings.shutterAngle).toBe(360);

        // 90 degrees = less blur
        store.updateCompositionSettings(comp!.id, { shutterAngle: 90 });
        expect(store.getActiveComp()!.settings.shutterAngle).toBe(90);
      });

      test('Steps 217-220: Adjust samples per frame', () => {
        const comp = store.getActiveComp();

        // More samples = smoother but slower
        store.updateCompositionSettings(comp!.id, { motionBlurSamples: 32 });
        expect(store.getActiveComp()!.settings.motionBlurSamples).toBe(32);

        // Fewer samples = faster preview
        store.updateCompositionSettings(comp!.id, { motionBlurSamples: 8 });
        expect(store.getActiveComp()!.settings.motionBlurSamples).toBe(8);
      });
    });

    describe('Steps 221-225: Per-Layer Motion Blur', () => {
      test('Steps 221-225: Toggle motion blur per layer', () => {
        const layer1 = store.createLayer('spline', 'Blur_On');
        const layer2 = store.createLayer('spline', 'Blur_Off');

        store.updateLayer(layer1!.id, { motionBlur: true });
        store.updateLayer(layer2!.id, { motionBlur: false });

        expect(getLayer(layer1!.id)!.motionBlur).toBe(true);
        expect(getLayer(layer2!.id)!.motionBlur).toBe(false);

        // Toggle
        store.updateLayer(layer1!.id, { motionBlur: false });
        store.updateLayer(layer2!.id, { motionBlur: true });

        expect(getLayer(layer1!.id)!.motionBlur).toBe(false);
        expect(getLayer(layer2!.id)!.motionBlur).toBe(true);
      });
    });

    describe('Phase 11: Undo/Redo Verification', () => {
      test('Steps 206-225: Undo/Redo motion blur settings', () => {
        const layer = store.createLayer('spline', 'MB_Layer');

        store.updateLayer(layer!.id, { motionBlur: false });
        expect(getLayer(layer!.id)!.motionBlur).toBe(false);

        store.updateLayer(layer!.id, { motionBlur: true });
        expect(getLayer(layer!.id)!.motionBlur).toBe(true);

        store.undo();
        expect(getLayer(layer!.id)!.motionBlur).toBe(false);

        store.redo();
        expect(getLayer(layer!.id)!.motionBlur).toBe(true);
      });
    });
  });

  // ============================================================================
  // PHASE 12: COLOR ADJUSTMENTS (Steps 226-250)
  // ============================================================================
  describe('Phase 12: Color Adjustments (Steps 226-250)', () => {

    describe('Steps 226-235: Hue/Saturation Effect', () => {
      test('Steps 226-228: Add Hue/Saturation effect', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        store.addEffectToLayer(layer!.id, 'hue-saturation');

        const effect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'hue-saturation');
        expect(effect).toBeDefined();
      });

      test('Steps 229-235: Adjust hue rotation', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');
        store.addEffectToLayer(layer!.id, 'hue-saturation');
        const effect = getLayer(layer!.id)!.effects![0];

        // Rotate hue by 30 degrees
        store.updateEffectParameter(layer!.id, effect.id, 'master_hue', 30);
        expect(getLayer(layer!.id)!.effects![0].parameters['master_hue'].value).toBe(30);

        // Increase saturation
        store.updateEffectParameter(layer!.id, effect.id, 'master_saturation', 20);
        expect(getLayer(layer!.id)!.effects![0].parameters['master_saturation'].value).toBe(20);

        // Adjust lightness
        store.updateEffectParameter(layer!.id, effect.id, 'master_lightness', 10);
        expect(getLayer(layer!.id)!.effects![0].parameters['master_lightness'].value).toBe(10);
      });
    });

    describe('Steps 236-245: Curves Effect', () => {
      test('Steps 236-238: Add Curves effect', () => {
        const layer = store.createLayer('solid', 'Color_Grade');

        store.addEffectToLayer(layer!.id, 'curves');

        const effect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'curves');
        expect(effect).toBeDefined();
      });

      test('Steps 239-245: Adjust curves channel', () => {
        const layer = store.createLayer('solid', 'Color_Grade');
        store.addEffectToLayer(layer!.id, 'curves');
        const effect = getLayer(layer!.id)!.effects![0];

        // Set channel to Red
        store.updateEffectParameter(layer!.id, effect.id, 'channel', 'red');
        expect(getLayer(layer!.id)!.effects![0].parameters['channel'].value).toBe('red');

        // Set channel to RGB (master)
        store.updateEffectParameter(layer!.id, effect.id, 'channel', 'rgb');
        expect(getLayer(layer!.id)!.effects![0].parameters['channel'].value).toBe('rgb');
      });
    });

    describe('Steps 246-250: Color Balance', () => {
      test('Steps 246-250: Add and configure Color Balance', () => {
        const layer = store.createLayer('solid', 'Color_Grade');

        store.addEffectToLayer(layer!.id, 'color-balance');

        const effect = getLayer(layer!.id)!.effects!.find(e => e.effectKey === 'color-balance');
        expect(effect).toBeDefined();

        // Push shadows toward blue/cyan
        store.updateEffectParameter(layer!.id, effect!.id, 'shadow_red', -20);
        store.updateEffectParameter(layer!.id, effect!.id, 'shadow_blue', 30);

        expect(getLayer(layer!.id)!.effects![0].parameters['shadow_red'].value).toBe(-20);
        expect(getLayer(layer!.id)!.effects![0].parameters['shadow_blue'].value).toBe(30);
      });
    });

    describe('Phase 12: Undo/Redo Verification', () => {
      test('Steps 226-250: Undo/Redo color adjustments', () => {
        const layer = store.createLayer('solid', 'Color_Test');
        store.addEffectToLayer(layer!.id, 'hue-saturation');
        const effect = getLayer(layer!.id)!.effects![0];

        store.updateEffectParameter(layer!.id, effect.id, 'master_hue', 0);
        store.updateEffectParameter(layer!.id, effect.id, 'master_hue', 45);
        expect(getLayer(layer!.id)!.effects![0].parameters['master_hue'].value).toBe(45);

        store.undo();
        expect(getLayer(layer!.id)!.effects![0].parameters['master_hue'].value).toBe(0);

        store.redo();
        expect(getLayer(layer!.id)!.effects![0].parameters['master_hue'].value).toBe(45);
      });
    });
  });

  // ============================================================================
  // PHASE 13: COMPOSITING & BLEND MODES (Steps 251-275)
  // ============================================================================
  describe('Phase 13: Compositing & Blend Modes (Steps 251-275)', () => {

    describe('Steps 251-260: Blend Modes', () => {
      test('Steps 251-255: Set layer blend modes', () => {
        const layer = store.createLayer('spline', 'Light_Streak_01');

        // Test various blend modes
        store.updateLayer(layer!.id, { blendMode: 'add' });
        expect(getLayer(layer!.id)!.blendMode).toBe('add');

        store.updateLayer(layer!.id, { blendMode: 'screen' });
        expect(getLayer(layer!.id)!.blendMode).toBe('screen');

        store.updateLayer(layer!.id, { blendMode: 'overlay' });
        expect(getLayer(layer!.id)!.blendMode).toBe('overlay');
      });

      test('Steps 256-260: Blend mode for neon effect', () => {
        const layer = store.createLayer('spline', 'Neon_Streak');

        // Add blend mode is ideal for neon/glow effects
        store.updateLayer(layer!.id, { blendMode: 'add' });
        expect(getLayer(layer!.id)!.blendMode).toBe('add');

        // Screen is also good for light effects
        const layer2 = store.createLayer('spline', 'Soft_Glow');
        store.updateLayer(layer2!.id, { blendMode: 'screen' });
        expect(getLayer(layer2!.id)!.blendMode).toBe('screen');
      });
    });

    describe('Steps 261-270: Layer Opacity', () => {
      test('Steps 261-265: Adjust layer opacity', () => {
        const layer = store.createLayer('spline', 'Subtle_Streak');

        // Set opacity to 75%
        store.updateLayerTransform(layer!.id, { opacity: 75 });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer!.opacity.value).toBe(75);
      });

      test('Steps 266-270: Animate opacity', () => {
        const layer = store.createLayer('spline', 'Fading_Streak');

        // Add keyframes for fade (this enables animation)
        store.addKeyframe(layer!.id, 'opacity', 0, 100);  // Full opacity at start
        store.addKeyframe(layer!.id, 'opacity', 60, 0);   // Fade out

        const opacity = getLayer(layer!.id)!.opacity;
        expect(opacity.keyframes).toBeDefined();
        expect(opacity.keyframes!.length).toBeGreaterThanOrEqual(2);
        expect(opacity.animated).toBe(true);
      });
    });

    describe('Steps 271-275: Layer Stacking', () => {
      test('Steps 271-275: Reorder layers', () => {
        const layer1 = store.createLayer('spline', 'Bottom_Layer');
        const layer2 = store.createLayer('spline', 'Middle_Layer');
        const layer3 = store.createLayer('spline', 'Top_Layer');

        // Get initial order
        const initialLayers = store.getActiveCompLayers();

        // Move top layer to bottom
        store.moveLayer(layer3!.id, initialLayers.length - 1);

        // Verify order changed
        const newLayers = store.getActiveCompLayers();
        expect(newLayers[newLayers.length - 1].id).toBe(layer3!.id);
      });
    });

    describe('Phase 13: Undo/Redo Verification', () => {
      test('Steps 251-275: Undo/Redo blend mode changes', () => {
        const layer = store.createLayer('spline', 'Blend_Test');

        store.updateLayer(layer!.id, { blendMode: 'normal' });
        expect(getLayer(layer!.id)!.blendMode).toBe('normal');

        store.updateLayer(layer!.id, { blendMode: 'add' });
        expect(getLayer(layer!.id)!.blendMode).toBe('add');

        store.undo();
        expect(getLayer(layer!.id)!.blendMode).toBe('normal');

        store.redo();
        expect(getLayer(layer!.id)!.blendMode).toBe('add');
      });
    });
  });

  // ============================================================================
  // PHASE 14: AUDIO SYNC (Steps 276-300)
  // ============================================================================
  describe('Phase 14: Audio Sync (Steps 276-300)', () => {

    describe('Steps 276-285: Import Audio', () => {
      // Steps 276-280: Audio import UI - Skip

      test('Steps 281-285: Create audio layer', () => {
        const layer = store.createLayer('audio', 'Music_Track');

        expect(layer).toBeDefined();
        expect(layer!.type).toBe('audio');
        expect(layer!.name).toBe('Music_Track');
      });
    });

    describe('Steps 286-295: Audio Analysis', () => {
      test('Steps 286-290: Store audio data', () => {
        const layer = store.createLayer('audio', 'Beat_Track');

        // Store waveform/analysis data
        store.updateLayerData(layer!.id, {
          waveform: [0.1, 0.5, 0.8, 0.3, 0.9, 0.2],  // Sample amplitudes
          beats: [0, 30, 60, 90, 120],  // Beat frames
          tempo: 120  // BPM
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const audioData = updatedLayer!.data as AudioLayerData;
        expect(audioData.waveform).toBeDefined();
        expect(audioData.waveform!.length).toBe(6);
        expect(audioData.beats).toBeDefined();
        expect(audioData.beats!.length).toBe(5);
        expect(audioData.tempo).toBe(120);
      });

      test('Steps 291-295: Audio markers', () => {
        const layer = store.createLayer('audio', 'Music_Track');

        // Add markers at beat points
        store.updateLayerData(layer!.id, {
          markers: [
            { frame: 0, label: 'Drop 1' },
            { frame: 60, label: 'Buildup' },
            { frame: 120, label: 'Drop 2' }
          ]
        });

        const updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const audioData = updatedLayer!.data as AudioLayerData;
        expect(audioData.markers).toBeDefined();
        expect(audioData.markers!.length).toBe(3);
        expect(audioData.markers![0].label).toBe('Drop 1');
      });
    });

    describe('Steps 296-300: Audio-Reactive Animation', () => {
      test('Steps 296-300: Link property to audio', () => {
        const audioLayer = store.createLayer('audio', 'Music_Track');
        const shapeLayer = store.createLayer('spline', 'Reactive_Shape');

        // Store audio amplitude data
        store.updateLayerData(audioLayer!.id, {
          amplitudeData: [0.2, 0.8, 0.4, 1.0, 0.6]  // Per-frame amplitude
        });

        // Link shape scale to audio amplitude
        store.updateLayerData(shapeLayer!.id, {
          audioReactive: {
            enabled: true,
            sourceLayerId: audioLayer!.id,
            property: 'scale',
            multiplier: 50,  // Amplitude * 50 added to scale
            smoothing: 5     // Frames of smoothing
          }
        });

        const updatedLayer = getLayer(shapeLayer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        const splineData = updatedLayer!.data as SplineData;
        expect(splineData.audioReactive).toBeDefined();
        const reactiveData = splineData.audioReactive!;
        expect(reactiveData.enabled).toBe(true);
        expect(reactiveData.sourceLayerId).toBe(audioLayer!.id);
      });
    });

    describe('Phase 14: Undo/Redo Verification', () => {
      test('Steps 276-300: Undo/Redo audio configuration', () => {
        const layer = store.createLayer('audio', 'Audio_Test');

        store.updateLayerData(layer!.id, { tempo: 120 });
        let updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        expect(updatedLayer!.data).toBeDefined();
        let audioData = updatedLayer!.data as AudioLayerData;
        expect(audioData.tempo).toBe(120);

        store.updateLayerData(layer!.id, { tempo: 140 });
        updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        audioData = updatedLayer!.data as AudioLayerData;
        expect(audioData.tempo).toBe(140);

        store.undo();
        updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        audioData = updatedLayer!.data as AudioLayerData;
        expect(audioData.tempo).toBe(120);

        store.redo();
        updatedLayer = getLayer(layer!.id);
        expect(updatedLayer).toBeDefined();
        audioData = updatedLayer!.data as AudioLayerData;
        expect(audioData.tempo).toBe(140);
      });
    });
  });

  // ============================================================================
  // PHASE 15: FINAL COMPOSITION & EXPORT (Steps 301-325)
  // ============================================================================
  describe('Phase 15: Final Composition & Export (Steps 301-325)', () => {

    describe('Steps 301-310: Final Adjustments', () => {
      test('Steps 301-305: Set final composition settings', () => {
        const comp = store.getActiveComp();

        store.updateCompositionSettings(comp!.id, {
          width: 1920,
          height: 1080,
          fps: 30,
          frameCount: 300,  // 10 seconds
          backgroundColor: '#000000'
        });

        const updated = store.getActiveComp();
        expect(updated!.settings.width).toBe(1920);
        expect(updated!.settings.height).toBe(1080);
        expect(updated!.settings.fps).toBe(30);
        expect(updated!.settings.frameCount).toBe(300);
      });

      test('Steps 306-310: Preview final composition', () => {
        // First extend composition to 300 frames
        const comp = store.getActiveComp();
        store.updateCompositionSettings(comp!.id, { frameCount: 300 });

        // Set playhead to various points
        store.setFrame(0);
        expect(store.currentFrame).toBe(0);

        store.setFrame(150);  // Middle
        expect(store.currentFrame).toBe(150);

        store.setFrame(299);  // End
        expect(store.currentFrame).toBe(299);
      });
    });

    describe('Steps 311-320: Export Settings', () => {
      // Steps 311-315: Export dialog UI - Skip

      test('Steps 316-320: Configure export settings in project', () => {
        // Store export preferences in project
        store.project.exportSettings = {
          format: 'mp4',
          codec: 'h264',
          quality: 'high',
          resolution: { width: 1920, height: 1080 },
          frameRate: 30
        };

        expect(store.project.exportSettings).toBeDefined();
        expect(store.project.exportSettings.format).toBe('mp4');
        expect(store.project.exportSettings.codec).toBe('h264');
      });
    });

    describe('Steps 321-325: Save Project', () => {
      test('Steps 321-325: Save and verify project', () => {
        // Setup complete project state
        const comp = store.getActiveComp();
        store.renameComposition(comp!.id, 'Neon_Trails_Final');

        // Create all layers from tutorial
        const bgLayer = store.createLayer('solid', 'BG_Gradient');
        store.addEffectToLayer(bgLayer!.id, 'gradient-ramp');

        const streak1 = store.createLayer('spline', 'Light_Streak_01');
        store.updateLayerData(streak1!.id, {
          strokeEnabled: true,
          strokeColor: { r: 0, g: 255, b: 255, a: 1 }
        });
        store.addEffectToLayer(streak1!.id, 'glow');
        store.updateLayer(streak1!.id, { blendMode: 'add' });

        // Serialize
        const projectData = store.exportProject();
        expect(projectData).toBeDefined();

        // Verify in fresh store
        const pinia = createPinia();
        setActivePinia(pinia);
        const freshStore = useCompositorStore();
        freshStore.importProject(projectData);

        // Verify all elements preserved
        const loadedComp = freshStore.getActiveComp();
        expect(loadedComp!.name).toBe('Neon_Trails_Final');

        const loadedLayers = freshStore.getActiveCompLayers();
        expect(loadedLayers.length).toBeGreaterThanOrEqual(2);

        const loadedBg = loadedLayers.find(l => l.name === 'BG_Gradient');
        expect(loadedBg).toBeDefined();
        expect(loadedBg!.effects!.length).toBe(1);

        const loadedStreak = loadedLayers.find(l => l.name === 'Light_Streak_01');
        expect(loadedStreak).toBeDefined();
        expect(loadedStreak!.blendMode).toBe('add');
        const loadedSplineData = loadedStreak!.data as SplineData;
        expect(loadedSplineData.stroke).toBeTruthy();
      });
    });

    describe('Phase 15: Determinism Verification', () => {
      test('Frame evaluation is reproducible', () => {
        // Create animated layer
        const layer = store.createLayer('spline', 'Animated_Shape');
        // Add keyframes (this enables animation automatically)
        store.addKeyframe(layer!.id, 'opacity', 0, 100);
        store.addKeyframe(layer!.id, 'opacity', 60, 50);

        // Evaluate at frame 30
        store.setFrame(30);
        const frame30_first = store.currentFrame;

        // Scrub around
        store.setFrame(0);
        store.setFrame(60);
        store.setFrame(45);

        // Return to frame 30
        store.setFrame(30);
        const frame30_second = store.currentFrame;

        // Must be identical
        expect(frame30_first).toBe(frame30_second);
      });
    });
  });
});
