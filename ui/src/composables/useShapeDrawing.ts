/**
 * Shape Drawing Composable
 *
 * Handles creation of shape layers from drawn bounds on the canvas.
 * Supports rectangle, ellipse, polygon, and star shapes.
 */

import { ref, computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';

export interface ShapeDrawBounds {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
}

export interface ShapeDrawState {
  isDrawing: boolean;
  start: { x: number; y: number } | null;
  end: { x: number; y: number } | null;
  tool: 'rectangle' | 'ellipse' | 'polygon' | 'star' | null;
}

/**
 * Helper to create an animatable property
 */
function createAnimatableProp<T>(value: T): { value: T; animated: boolean; keyframes: any[] } {
  return {
    value,
    animated: false,
    keyframes: []
  };
}

/**
 * Create a default shape transform structure
 */
function createDefaultShapeTransform() {
  return {
    anchorPoint: createAnimatableProp({ x: 0, y: 0 }),
    position: createAnimatableProp({ x: 0, y: 0 }),
    scale: createAnimatableProp({ x: 100, y: 100 }),
    rotation: createAnimatableProp(0),
    skew: createAnimatableProp(0),
    skewAxis: createAnimatableProp(0),
    opacity: createAnimatableProp(100)
  };
}

export function useShapeDrawing() {
  const store = useCompositorStore();

  // State
  const isDrawingShape = ref(false);
  const shapeDrawStart = ref<{ x: number; y: number } | null>(null);
  const shapeDrawEnd = ref<{ x: number; y: number } | null>(null);
  const currentShapeTool = ref<'rectangle' | 'ellipse' | 'polygon' | 'star' | null>(null);

  // Check if current tool is a shape tool
  const isShapeTool = computed(() =>
    ['rectangle', 'ellipse', 'polygon', 'star'].includes(store.currentTool)
  );

  /**
   * Compute shape preview bounds with constrain/fromCenter options
   */
  const shapePreviewBounds = computed((): ShapeDrawBounds | null => {
    const start = shapeDrawStart.value;
    const end = shapeDrawEnd.value;
    if (!start || !end) return null;

    const options = store.shapeToolOptions;
    let x1 = start.x, y1 = start.y, x2 = end.x, y2 = end.y;

    // Handle constrain (shift) - make square/circle
    if (options.constrain) {
      const dx = x2 - x1;
      const dy = y2 - y1;
      const size = Math.max(Math.abs(dx), Math.abs(dy));
      x2 = x1 + size * Math.sign(dx || 1);
      y2 = y1 + size * Math.sign(dy || 1);
    }

    // Handle from center (alt) - draw from center outwards
    if (options.fromCenter) {
      const dx = x2 - x1;
      const dy = y2 - y1;
      x1 = start.x - dx;
      y1 = start.y - dy;
    }

    return { x1, y1, x2, y2 };
  });

  /**
   * Generate SVG path for shape preview
   */
  const shapePreviewPath = computed(() => {
    const bounds = shapePreviewBounds.value;
    if (!bounds) return '';

    const width = Math.abs(bounds.x2 - bounds.x1);
    const height = Math.abs(bounds.y2 - bounds.y1);
    if (width === 0 || height === 0) return '';

    const tool = currentShapeTool.value;
    const options = store.shapeToolOptions;

    switch (tool) {
      case 'rectangle':
        return `M 0 0 L ${width} 0 L ${width} ${height} L 0 ${height} Z`;

      case 'ellipse': {
        const rx = width / 2;
        const ry = height / 2;
        const cx = rx;
        const cy = ry;
        return `M ${cx} ${cy - ry} A ${rx} ${ry} 0 1 1 ${cx} ${cy + ry} A ${rx} ${ry} 0 1 1 ${cx} ${cy - ry} Z`;
      }

      case 'polygon': {
        const sides = options.polygonSides || 6;
        const cx = width / 2;
        const cy = height / 2;
        const r = Math.min(width, height) / 2;
        const points: string[] = [];
        for (let i = 0; i < sides; i++) {
          const angle = (i / sides) * Math.PI * 2 - Math.PI / 2;
          const px = cx + Math.cos(angle) * r;
          const py = cy + Math.sin(angle) * r;
          points.push(`${i === 0 ? 'M' : 'L'} ${px} ${py}`);
        }
        return points.join(' ') + ' Z';
      }

      case 'star': {
        const numPoints = options.starPoints || 5;
        const innerRatio = options.starInnerRadius || 0.5;
        const cx = width / 2;
        const cy = height / 2;
        const outerR = Math.min(width, height) / 2;
        const innerR = outerR * innerRatio;
        const points: string[] = [];
        for (let i = 0; i < numPoints * 2; i++) {
          const angle = (i / (numPoints * 2)) * Math.PI * 2 - Math.PI / 2;
          const r = i % 2 === 0 ? outerR : innerR;
          const px = cx + Math.cos(angle) * r;
          const py = cy + Math.sin(angle) * r;
          points.push(`${i === 0 ? 'M' : 'L'} ${px} ${py}`);
        }
        return points.join(' ') + ' Z';
      }

      default:
        return '';
    }
  });

  /**
   * Start shape drawing
   */
  function startDrawing(
    tool: 'rectangle' | 'ellipse' | 'polygon' | 'star',
    scenePos: { x: number; y: number }
  ) {
    currentShapeTool.value = tool;
    shapeDrawStart.value = { x: scenePos.x, y: scenePos.y };
    shapeDrawEnd.value = { x: scenePos.x, y: scenePos.y };
    isDrawingShape.value = true;
  }

  /**
   * Update shape drawing position
   */
  function updateDrawing(scenePos: { x: number; y: number }) {
    if (isDrawingShape.value && shapeDrawStart.value) {
      shapeDrawEnd.value = { x: scenePos.x, y: scenePos.y };
    }
  }

  /**
   * Cancel shape drawing
   */
  function cancelDrawing() {
    isDrawingShape.value = false;
    shapeDrawStart.value = null;
    shapeDrawEnd.value = null;
    currentShapeTool.value = null;
  }

  /**
   * Finish shape drawing and create the layer
   */
  function finishDrawing(): boolean {
    if (!isDrawingShape.value || !shapeDrawStart.value || !shapeDrawEnd.value) {
      cancelDrawing();
      return false;
    }

    const bounds = shapePreviewBounds.value;
    if (!bounds) {
      cancelDrawing();
      return false;
    }

    const width = Math.abs(bounds.x2 - bounds.x1);
    const height = Math.abs(bounds.y2 - bounds.y1);

    // Only create shape if it has meaningful size
    if (width > 5 || height > 5) {
      createShapeFromDraw(currentShapeTool.value!, bounds);
      cancelDrawing();
      return true;
    }

    cancelDrawing();
    return false;
  }

  /**
   * Create a shape layer from drawn bounds
   */
  function createShapeFromDraw(
    shapeType: 'rectangle' | 'ellipse' | 'polygon' | 'star',
    bounds: ShapeDrawBounds
  ) {
    const width = Math.abs(bounds.x2 - bounds.x1);
    const height = Math.abs(bounds.y2 - bounds.y1);
    const centerX = (bounds.x1 + bounds.x2) / 2;
    const centerY = (bounds.y1 + bounds.y2) / 2;

    // Create a new shape layer
    const newLayer = store.createLayer('shape');

    // Get current shape tool options
    const options = store.shapeToolOptions;

    // Create the appropriate shape generator based on type
    const shapeData = newLayer.data as any;
    if (!shapeData.contents || !Array.isArray(shapeData.contents)) {
      shapeData.contents = [];
    }

    // Find or create a default group
    let group = shapeData.contents.find((c: any) => c.type === 'group');
    if (!group) {
      group = {
        type: 'group',
        name: 'Group 1',
        contents: [],
        transform: createDefaultShapeTransform(),
        blendMode: 'normal'
      };
      shapeData.contents.push(group);
    }

    // Clear existing contents (remove default shapes)
    group.contents = [];

    // Create the shape generator
    let generator: any;
    switch (shapeType) {
      case 'rectangle':
        generator = {
          type: 'rectangle',
          name: 'Rectangle Path',
          size: createAnimatableProp({ x: width, y: height }),
          position: createAnimatableProp({ x: 0, y: 0 }),
          roundness: createAnimatableProp(0)
        };
        break;

      case 'ellipse':
        generator = {
          type: 'ellipse',
          name: 'Ellipse Path',
          size: createAnimatableProp({ x: width, y: height }),
          position: createAnimatableProp({ x: 0, y: 0 })
        };
        break;

      case 'polygon':
        generator = {
          type: 'polygon',
          name: 'Polygon Path',
          points: createAnimatableProp(options.polygonSides),
          position: createAnimatableProp({ x: 0, y: 0 }),
          outerRadius: createAnimatableProp(Math.min(width, height) / 2),
          outerRoundness: createAnimatableProp(0)
        };
        break;

      case 'star':
        generator = {
          type: 'star',
          name: 'Star Path',
          points: createAnimatableProp(options.starPoints),
          position: createAnimatableProp({ x: 0, y: 0 }),
          outerRadius: createAnimatableProp(Math.min(width, height) / 2),
          innerRadius: createAnimatableProp(Math.min(width, height) / 2 * options.starInnerRadius),
          outerRoundness: createAnimatableProp(0),
          innerRoundness: createAnimatableProp(0)
        };
        break;
    }

    // Add fill and stroke
    const fill = {
      type: 'fill',
      name: 'Fill',
      color: createAnimatableProp({ r: 0.4, g: 0.5, b: 1, a: 1 }),
      opacity: createAnimatableProp(100),
      blendMode: 'normal'
    };

    const stroke = {
      type: 'stroke',
      name: 'Stroke',
      color: createAnimatableProp({ r: 1, g: 1, b: 1, a: 1 }),
      opacity: createAnimatableProp(100),
      width: createAnimatableProp(2),
      lineCap: 'round',
      lineJoin: 'round',
      miterLimit: 4,
      blendMode: 'normal'
    };

    group.contents = [generator, fill, stroke];

    // Update the layer position to center of drawn shape
    store.updateLayer(newLayer.id, {
      transform: {
        ...newLayer.transform,
        position: {
          ...newLayer.transform!.position,
          value: { x: centerX, y: centerY, z: 0 }
        }
      },
      data: shapeData
    });

    // Select the new layer
    store.selectLayer(newLayer.id);

    // Switch back to select tool
    store.setTool('select');
  }

  return {
    // State
    isDrawingShape,
    shapeDrawStart,
    shapeDrawEnd,
    currentShapeTool,
    isShapeTool,

    // Computed
    shapePreviewBounds,
    shapePreviewPath,

    // Methods
    startDrawing,
    updateDrawing,
    cancelDrawing,
    finishDrawing,
    createShapeFromDraw
  };
}
