/**
 * Shape Drawing Composable
 *
 * Handles creation of shape layers from drawn bounds on the canvas.
 * Supports rectangle, ellipse, polygon, and star shapes.
 */

import { computed, ref } from "vue";
import { assertDefined } from "@/utils/typeGuards";
import { useLayerStore } from "@/stores/layerStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useUIStore } from "@/stores/uiStore";
import { createAnimatableProperty } from "@/types/animation";
import { createDefaultShapeTransform, createDefaultFill, createDefaultStroke } from "@/types/shapes";
import type { ShapeGenerator, ShapeGroup } from "@/types/shapes";

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
  tool: "rectangle" | "ellipse" | "polygon" | "star" | null;
}


export function useShapeDrawing() {
  const layerStore = useLayerStore();
  const selectionStore = useSelectionStore();
  const uiStore = useUIStore();

  // State
  const isDrawingShape = ref(false);
  const shapeDrawStart = ref<{ x: number; y: number } | null>(null);
  const shapeDrawEnd = ref<{ x: number; y: number } | null>(null);
  const currentShapeTool = ref<
    "rectangle" | "ellipse" | "polygon" | "star" | null
  >(null);

  // Check if current tool is a shape tool
  const isShapeTool = computed(() =>
    ["rectangle", "ellipse", "polygon", "star"].includes(selectionStore.currentTool),
  );

  /**
   * Compute shape preview bounds with constrain/fromCenter options
   * 
   * System F/Omega proof: Explicit validation of start and end points
   * Type proof: shapeDrawStart, shapeDrawEnd ∈ Point2D | null → ShapeDrawBounds (non-nullable)
   * Mathematical proof: Both start and end points must exist to calculate bounds
   * Pattern proof: Missing start or end point is an explicit failure condition, not a lazy null return
   */
  const shapePreviewBounds = computed((): ShapeDrawBounds => {
    const start = shapeDrawStart.value;
    const end = shapeDrawEnd.value;
    
    // System F/Omega proof: Explicit validation of start and end points
    // Type proof: start, end ∈ Point2D | null
    // Mathematical proof: Both points must exist to calculate bounds
    if (!start || !end) {
      throw new Error(
        `[useShapeDrawing] Cannot compute shape preview bounds: Start or end point missing. ` +
        `Start: ${start ? `(${start.x}, ${start.y})` : "null"}, end: ${end ? `(${end.x}, ${end.y})` : "null"}. ` +
        `Both start and end points must be set before calculating bounds. ` +
        `Wrap in try/catch if "not drawing" is an expected state.`
      );
    }

    const options = uiStore.shapeToolOptions;
    let x1 = start.x,
      y1 = start.y,
      x2 = end.x,
      y2 = end.y;

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
    // System F/Omega pattern: Wrap in try/catch for expected "not drawing" case
    let bounds: ShapeDrawBounds;
    try {
      bounds = shapePreviewBounds.value;
    } catch (error) {
      // Not drawing - return empty string (expected state)
      return "";
    }

    const width = Math.abs(bounds.x2 - bounds.x1);
    const height = Math.abs(bounds.y2 - bounds.y1);
    if (width === 0 || height === 0) return "";

    const tool = currentShapeTool.value;
    const options = uiStore.shapeToolOptions;

    switch (tool) {
      case "rectangle":
        return `M 0 0 L ${width} 0 L ${width} ${height} L 0 ${height} Z`;

      case "ellipse": {
        const rx = width / 2;
        const ry = height / 2;
        const cx = rx;
        const cy = ry;
        return `M ${cx} ${cy - ry} A ${rx} ${ry} 0 1 1 ${cx} ${cy + ry} A ${rx} ${ry} 0 1 1 ${cx} ${cy - ry} Z`;
      }

      case "polygon": {
        const sides = options.polygonSides || 6;
        const cx = width / 2;
        const cy = height / 2;
        const r = Math.min(width, height) / 2;
        const points: string[] = [];
        for (let i = 0; i < sides; i++) {
          const angle = (i / sides) * Math.PI * 2 - Math.PI / 2;
          const px = cx + Math.cos(angle) * r;
          const py = cy + Math.sin(angle) * r;
          points.push(`${i === 0 ? "M" : "L"} ${px} ${py}`);
        }
        return `${points.join(" ")} Z`;
      }

      case "star": {
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
          points.push(`${i === 0 ? "M" : "L"} ${px} ${py}`);
        }
        return `${points.join(" ")} Z`;
      }

      default:
        return "";
    }
  });

  /**
   * Start shape drawing
   */
  function startDrawing(
    tool: "rectangle" | "ellipse" | "polygon" | "star",
    scenePos: { x: number; y: number },
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

    // System F/Omega pattern: Wrap in try/catch for expected "not drawing" case
    let bounds: ShapeDrawBounds;
    try {
      bounds = shapePreviewBounds.value;
    } catch (error) {
      // Not drawing - cancel and return false (expected state)
      cancelDrawing();
      return false;
    }

    const width = Math.abs(bounds.x2 - bounds.x1);
    const height = Math.abs(bounds.y2 - bounds.y1);

    // Only create shape if it has meaningful size
    if (width > 5 || height > 5) {
      // Type proof: currentShapeTool is guaranteed non-null when isDrawingShape is true
      assertDefined(currentShapeTool.value, "currentShapeTool must exist when finishing shape drawing");
      createShapeFromDraw(currentShapeTool.value, bounds);
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
    shapeType: "rectangle" | "ellipse" | "polygon" | "star",
    bounds: ShapeDrawBounds,
  ) {
    const width = Math.abs(bounds.x2 - bounds.x1);
    const height = Math.abs(bounds.y2 - bounds.y1);
    const centerX = (bounds.x1 + bounds.x2) / 2;
    const centerY = (bounds.y1 + bounds.y2) / 2;

    // Create a new shape layer
    const newLayer = layerStore.createShapeLayer();

    // Get current shape tool options
    const options = uiStore.shapeToolOptions;

    // Create the appropriate shape generator based on type
    // Type-safe access - newLayer.data is ShapeLayerData for shape layers
    const shapeData = newLayer.data as import("@/types/shapes").ShapeLayerData;
    if (!shapeData.contents || !Array.isArray(shapeData.contents)) {
      shapeData.contents = [];
    }

    // Find or create a default group
    let group: ShapeGroup | undefined = shapeData.contents.find(
      (c): c is ShapeGroup => c.type === "group",
    );
    if (!group) {
      group = {
        type: "group",
        name: "Group 1",
        contents: [],
        transform: createDefaultShapeTransform(),
        blendMode: "normal",
      };
      shapeData.contents.push(group);
    }

    // Clear existing contents (remove default shapes)
    group.contents = [];

    // Create the shape generator
    let generator: ShapeGenerator;
    switch (shapeType) {
      case "rectangle":
        generator = {
          type: "rectangle",
          name: "Rectangle Path",
          size: createAnimatableProperty("Size", { x: width, y: height }, "position"),
          position: createAnimatableProperty("Position", { x: 0, y: 0 }, "position"),
          roundness: createAnimatableProperty("Roundness", 0, "number"),
          direction: 1,
        };
        break;

      case "ellipse":
        generator = {
          type: "ellipse",
          name: "Ellipse Path",
          size: createAnimatableProperty("Size", { x: width, y: height }, "position"),
          position: createAnimatableProperty("Position", { x: 0, y: 0 }, "position"),
          direction: 1,
        };
        break;

      case "polygon":
        generator = {
          type: "polygon",
          name: "Polygon Path",
          points: createAnimatableProperty("Points", options.polygonSides, "number"),
          position: createAnimatableProperty("Position", { x: 0, y: 0 }, "position"),
          outerRadius: createAnimatableProperty("Outer Radius", Math.min(width, height) / 2, "number"),
          outerRoundness: createAnimatableProperty("Outer Roundness", 0, "number"),
          rotation: createAnimatableProperty("Rotation", 0, "number"),
          direction: 1,
        };
        break;

      case "star":
        generator = {
          type: "star",
          name: "Star Path",
          points: createAnimatableProperty("Points", options.starPoints, "number"),
          position: createAnimatableProperty("Position", { x: 0, y: 0 }, "position"),
          outerRadius: createAnimatableProperty("Outer Radius", Math.min(width, height) / 2, "number"),
          innerRadius: createAnimatableProperty("Inner Radius", (Math.min(width, height) / 2) * options.starInnerRadius, "number"),
          outerRoundness: createAnimatableProperty("Outer Roundness", 0, "number"),
          innerRoundness: createAnimatableProperty("Inner Roundness", 0, "number"),
          rotation: createAnimatableProperty("Rotation", 0, "number"),
          direction: 1,
        };
        break;
    }

    // Add fill and stroke
    const fill = createDefaultFill();
    fill.color.value = { r: 0.4, g: 0.5, b: 1, a: 1 };

    const stroke = createDefaultStroke();
    stroke.color.value = { r: 1, g: 1, b: 1, a: 1 };
    stroke.width.value = 2;

    group.contents = [generator, fill, stroke];

    // Update the layer position to center of drawn shape
    layerStore.updateLayer(newLayer.id, {
      transform: {
        ...newLayer.transform,
        position: {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          id: newLayer.transform !== undefined && typeof newLayer.transform === "object" && "position" in newLayer.transform && typeof newLayer.transform.position === "object" && "id" in newLayer.transform.position && typeof newLayer.transform.position.id === "string"
            ? newLayer.transform.position.id
            : "",
          name: newLayer.transform !== undefined && typeof newLayer.transform === "object" && "position" in newLayer.transform && typeof newLayer.transform.position === "object" && "name" in newLayer.transform.position && typeof newLayer.transform.position.name === "string"
            ? newLayer.transform.position.name
            : "",
          type: newLayer.transform !== undefined && typeof newLayer.transform === "object" && "position" in newLayer.transform && typeof newLayer.transform.position === "object" && "type" in newLayer.transform.position
            ? newLayer.transform.position.type
            : "position",
          animated: newLayer.transform !== undefined && typeof newLayer.transform === "object" && "position" in newLayer.transform && typeof newLayer.transform.position === "object" && "animated" in newLayer.transform.position && typeof newLayer.transform.position.animated === "boolean"
            ? newLayer.transform.position.animated
            : false,
          keyframes: newLayer.transform !== undefined && typeof newLayer.transform === "object" && "position" in newLayer.transform && typeof newLayer.transform.position === "object" && "keyframes" in newLayer.transform.position && Array.isArray(newLayer.transform.position.keyframes)
            ? newLayer.transform.position.keyframes
            : [],
          value: { x: centerX, y: centerY, z: 0 },
        },
      },
      data: shapeData,
    });

    // Select the new layer
    selectionStore.selectLayer(newLayer.id);

    // Switch back to select tool
    selectionStore.setTool("select");
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
    createShapeFromDraw,
  };
}
