/**
 * Spline Interaction Composable
 *
 * Handles mouse events, dragging, and keyboard interactions for SplineEditor.
 * Extracted from SplineEditor.vue to reduce file size.
 */

import { type ComputedRef, computed, type Ref, ref } from "vue";
import type {
  ControlPoint,
  EvaluatedControlPoint,
  PathLayerData,
  SplineData,
} from "@/types/project";

export interface DragTarget {
  type:
    | "point"
    | "handleIn"
    | "handleOut"
    | "depth"
    | "newPoint"
    | "axisX"
    | "axisY";
  pointId: string;
  startX: number;
  startY: number;
  startDepth?: number;
  newPointX?: number;
  newPointY?: number;
  originalX?: number;
  originalY?: number;
  screenStartX?: number;
  screenStartY?: number;
}

export type PenSubMode = "add" | "insert" | "delete" | "convert";

export interface SplineInteractionOptions {
  layerId: Ref<string | null>;
  currentFrame: Ref<number>;
  canvasWidth: Ref<number>;
  canvasHeight: Ref<number>;
  containerWidth: Ref<number>;
  containerHeight: Ref<number>;
  zoom: Ref<number>;
  isPenMode: Ref<boolean>;
  visibleControlPoints: ComputedRef<(ControlPoint | EvaluatedControlPoint)[]>;
  isClosed: ComputedRef<boolean>;
  overlayStyle: ComputedRef<{
    width: string;
    height: string;
    left: string;
    top: string;
  }>;
  // Transform functions - passed in to use component's version with proper anchor point handling
  transformPoint: (p: { x: number; y: number }) => { x: number; y: number };
  inverseTransformPoint: (p: { x: number; y: number }) => {
    x: number;
    y: number;
  };
  // Store reference
  store: any;
  // Callbacks
  emit: {
    pointAdded: (point: ControlPoint) => void;
    pointMoved: (pointId: string, x: number, y: number) => void;
    handleMoved: (
      pointId: string,
      handleType: "in" | "out",
      x: number,
      y: number,
    ) => void;
    pointDeleted: (pointId: string) => void;
    pathUpdated: () => void;
    pathClosed: () => void;
    togglePenMode: () => void;
  };
}

// Helper: Check if layer is a spline or path type
function isSplineOrPathType(
  layerType: string | undefined,
): layerType is "spline" | "path" {
  return layerType === "spline" || layerType === "path";
}

const CLOSE_THRESHOLD = 15;

export function useSplineInteraction(options: SplineInteractionOptions) {
  const {
    layerId,
    canvasWidth,
    canvasHeight,
    zoom,
    isPenMode,
    visibleControlPoints,
    isClosed,
    overlayStyle,
    transformPoint,
    inverseTransformPoint,
    store,
    emit,
  } = options;

  // State
  const selectedPointId = ref<string | null>(null);
  const selectedPointIds = ref<string[]>([]);
  const hoveredPointId = ref<string | null>(null);
  const hoverFeedback = ref<string | null>(null);
  const hoverFeedbackPos = ref<{ x: number; y: number } | null>(null);
  const previewPoint = ref<{ x: number; y: number } | null>(null);
  const closePathPreview = ref(false);
  const previewCurve = ref<string | null>(null);
  const insertPreviewPoint = ref<{
    x: number;
    y: number;
    segmentIndex: number;
  } | null>(null);
  const penSubMode = ref<PenSubMode>("add");
  const dragTarget = ref<DragTarget | null>(null);

  // Computed: active tool tip text
  const activeToolTip = computed(() => {
    switch (penSubMode.value) {
      case "add":
        return "Click to add points. Drag after clicking to create curved handles. Right-click to finish drawing.";
      case "insert":
        return "Click on the path to insert a new point on that segment.";
      case "delete":
        return "Click on any point to delete it from the path.";
      case "convert":
        return "Click on a point to toggle between smooth (curved) and corner (sharp) type.";
      default:
        return "";
    }
  });

  // Computed: hover feedback style
  const hoverFeedbackStyle = computed(() => {
    if (!hoverFeedbackPos.value) return { display: "none" };
    const svgStyle = overlayStyle.value;
    const svgWidth = parseFloat(svgStyle.width);
    const svgHeight = parseFloat(svgStyle.height);
    const left =
      parseFloat(svgStyle.left) +
      (hoverFeedbackPos.value.x / canvasWidth.value) * svgWidth;
    const top =
      parseFloat(svgStyle.top) +
      (hoverFeedbackPos.value.y / canvasHeight.value) * svgHeight -
      25;
    return {
      position: "absolute" as const,
      left: `${left}px`,
      top: `${top}px`,
      transform: "translateX(-50%)",
    };
  });

  // Computed: selected point count
  const selectedPointCount = computed(() => selectedPointIds.value.length);

  // Convert screen coords to composition coords
  function screenToCanvas(
    screenX: number,
    screenY: number,
  ): { x: number; y: number } {
    const svgRect = overlayStyle.value;
    const svgWidth = parseFloat(svgRect.width);
    const svgHeight = parseFloat(svgRect.height);
    const x = (screenX / svgWidth) * canvasWidth.value;
    const y = (screenY / svgHeight) * canvasHeight.value;
    return { x, y };
  }

  // Get mouse position relative to SVG
  function getMousePos(event: MouseEvent): { x: number; y: number } {
    const svg = event.currentTarget as SVGSVGElement;
    const rect = svg.getBoundingClientRect();
    const screenX = event.clientX - rect.left;
    const screenY = event.clientY - rect.top;
    return screenToCanvas(screenX, screenY);
  }

  // Evaluate cubic bezier curve at parameter t
  function evaluateBezier(
    p0: { x: number; y: number },
    h0: { x: number; y: number } | null,
    h1: { x: number; y: number } | null,
    p1: { x: number; y: number },
    t: number,
  ): { x: number; y: number } {
    const cp0 = p0;
    const cp1 = h0 || p0;
    const cp2 = h1 || p1;
    const cp3 = p1;

    const mt = 1 - t;
    const mt2 = mt * mt;
    const mt3 = mt2 * mt;
    const t2 = t * t;
    const t3 = t2 * t;

    return {
      x: mt3 * cp0.x + 3 * mt2 * t * cp1.x + 3 * mt * t2 * cp2.x + t3 * cp3.x,
      y: mt3 * cp0.y + 3 * mt2 * t * cp1.y + 3 * mt * t2 * cp2.y + t3 * cp3.y,
    };
  }

  // Find closest point on path for insert mode
  function findClosestPointOnPath(pos: {
    x: number;
    y: number;
  }): { x: number; y: number; segmentIndex: number; t: number } | null {
    const points = visibleControlPoints.value;
    if (points.length < 2) return null;

    let closest: {
      x: number;
      y: number;
      segmentIndex: number;
      t: number;
      dist: number;
    } | null = null;

    const numSegments = isClosed.value ? points.length : points.length - 1;
    for (let i = 0; i < numSegments; i++) {
      const p0 = points[i];
      const p1 = points[(i + 1) % points.length];
      const h0 = p0.handleOut;
      const h1 = p1.handleIn;

      for (let t = 0; t <= 1; t += 0.02) {
        const pt = evaluateBezier(p0, h0, h1, p1, t);
        const dist = Math.sqrt((pos.x - pt.x) ** 2 + (pos.y - pt.y) ** 2);

        if (!closest || dist < closest.dist) {
          closest = { x: pt.x, y: pt.y, segmentIndex: i, t, dist };
        }
      }
    }

    if (closest && closest.dist < 20) {
      return {
        x: closest.x,
        y: closest.y,
        segmentIndex: closest.segmentIndex,
        t: closest.t,
      };
    }
    return null;
  }

  // Find point at position
  function findClickedPoint(pos: {
    x: number;
    y: number;
  }): (ControlPoint | EvaluatedControlPoint) | null {
    const threshold = 10;
    for (const point of visibleControlPoints.value) {
      const dist = Math.sqrt((pos.x - point.x) ** 2 + (pos.y - point.y) ** 2);
      if (dist < threshold) {
        return point;
      }
    }
    return null;
  }

  // Generate curve preview SVG path
  function generateCurvePreview(
    prevPoint: ControlPoint | EvaluatedControlPoint,
    newPoint: { x: number; y: number },
    dragPos: { x: number; y: number },
  ): string {
    const dx = dragPos.x - newPoint.x;
    const dy = dragPos.y - newPoint.y;

    let h1x: number, h1y: number;
    if (prevPoint.handleOut) {
      h1x = prevPoint.handleOut.x;
      h1y = prevPoint.handleOut.y;
    } else {
      const dirX = newPoint.x - prevPoint.x;
      const dirY = newPoint.y - prevPoint.y;
      h1x = prevPoint.x + dirX * 0.33;
      h1y = prevPoint.y + dirY * 0.33;
    }

    const h2x = newPoint.x - dx;
    const h2y = newPoint.y - dy;

    return `M ${prevPoint.x},${prevPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${newPoint.x},${newPoint.y}`;
  }

  // Set pen sub-mode
  function setPenSubMode(mode: PenSubMode) {
    penSubMode.value = mode;
  }

  // Handle mouse down
  function handleMouseDown(event: MouseEvent) {
    if (!isPenMode.value) return;

    const pos = getMousePos(event);
    const layerPos = inverseTransformPoint(pos);

    if (!layerId.value) return;
    const layer = store.layers.find((l: any) => l.id === layerId.value);
    if (!layer || !isSplineOrPathType(layer.type)) return;

    if (penSubMode.value === "add") {
      const newPoint: ControlPoint = {
        id: `cp_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        x: layerPos.x,
        y: layerPos.y,
        handleIn: null,
        handleOut: null,
        type: "corner",
      };

      store.addSplineControlPoint(layerId.value, newPoint);
      selectedPointId.value = newPoint.id;

      dragTarget.value = {
        type: "newPoint",
        pointId: newPoint.id,
        startX: pos.x,
        startY: pos.y,
        newPointX: pos.x,
        newPointY: pos.y,
      };

      emit.pointAdded(newPoint);
      emit.pathUpdated();
    } else if (penSubMode.value === "insert") {
      const closest = findClosestPointOnPath(pos);
      if (closest) {
        const closestLayerPos = inverseTransformPoint({
          x: closest.x,
          y: closest.y,
        });
        const newPoint: ControlPoint = {
          id: `cp_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
          x: closestLayerPos.x,
          y: closestLayerPos.y,
          handleIn: null,
          handleOut: null,
          type: "corner",
        };

        store.insertSplineControlPoint(
          layerId.value,
          newPoint,
          closest.segmentIndex + 1,
        );
        selectedPointId.value = newPoint.id;
        emit.pointAdded(newPoint);
        emit.pathUpdated();
      }
    } else if (penSubMode.value === "delete") {
      const clickedPoint = findClickedPoint(pos);
      if (clickedPoint) {
        store.deleteSplineControlPoint(layerId.value, clickedPoint.id);
        emit.pointDeleted(clickedPoint.id);
        emit.pathUpdated();
        selectedPointId.value = null;
      }
    } else if (penSubMode.value === "convert") {
      const clickedPoint = findClickedPoint(pos);
      if (clickedPoint) {
        const newType = clickedPoint.type === "smooth" ? "corner" : "smooth";
        if (newType === "corner") {
          store.updateSplineControlPoint(layerId.value, clickedPoint.id, {
            type: "corner",
            handleIn: null,
            handleOut: null,
          });
        } else {
          const handleOffset = 30;
          store.updateSplineControlPoint(layerId.value, clickedPoint.id, {
            type: "smooth",
            handleIn: { x: clickedPoint.x - handleOffset, y: clickedPoint.y },
            handleOut: { x: clickedPoint.x + handleOffset, y: clickedPoint.y },
          });
        }
        selectedPointId.value = clickedPoint.id;
        emit.pathUpdated();
      }
    }
  }

  // Handle mouse move
  function handleMouseMove(event: MouseEvent) {
    const pos = getMousePos(event);

    if (isPenMode.value) {
      previewPoint.value = pos;

      if (penSubMode.value === "insert") {
        const closest = findClosestPointOnPath(pos);
        insertPreviewPoint.value = closest;

        if (closest) {
          hoverFeedbackPos.value = { x: closest.x, y: closest.y };
          hoverFeedback.value = "Click to add point to spline";
        } else if (!hoveredPointId.value) {
          hoverFeedback.value = null;
        }
      } else {
        insertPreviewPoint.value = null;
        if (!hoveredPointId.value) {
          hoverFeedback.value = null;
        }
      }

      if (penSubMode.value === "add" && !dragTarget.value) {
        const points = visibleControlPoints.value;
        if (points.length > 0) {
          const lastPoint = points[points.length - 1];
          if (lastPoint.handleOut) {
            const h1x = lastPoint.handleOut.x;
            const h1y = lastPoint.handleOut.y;
            const dx = pos.x - lastPoint.x;
            const dy = pos.y - lastPoint.y;
            const h2x = pos.x - dx * 0.3;
            const h2y = pos.y - dy * 0.3;
            previewCurve.value = `M ${lastPoint.x},${lastPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${pos.x},${pos.y}`;
          } else {
            const dx = pos.x - lastPoint.x;
            const dy = pos.y - lastPoint.y;
            const h1x = lastPoint.x + dx * 0.3;
            const h1y = lastPoint.y + dy * 0.3;
            const h2x = pos.x - dx * 0.3;
            const h2y = pos.y - dy * 0.3;
            previewCurve.value = `M ${lastPoint.x},${lastPoint.y} C ${h1x},${h1y} ${h2x},${h2y} ${pos.x},${pos.y}`;
          }
        }
      }
    }

    // Generate curve preview when dragging new point
    if (dragTarget.value?.type === "newPoint") {
      const points = visibleControlPoints.value;
      if (points.length >= 1) {
        const newPoint = points.find((p) => p.id === dragTarget.value?.pointId);
        const newPointIndex = points.indexOf(newPoint!);
        const prevPointIndex = newPointIndex - 1;

        const layerPos = inverseTransformPoint(pos);
        const rawNewPointX = (newPoint as any)?.rawX ?? newPoint?.x ?? 0;
        const rawNewPointY = (newPoint as any)?.rawY ?? newPoint?.y ?? 0;

        if (newPoint && prevPointIndex >= 0) {
          const prevPoint = points[prevPointIndex];
          previewCurve.value = generateCurvePreview(prevPoint, newPoint, pos);

          if (layerId.value) {
            const dx = layerPos.x - rawNewPointX;
            const dy = layerPos.y - rawNewPointY;
            if (Math.sqrt(dx * dx + dy * dy) > 5) {
              store.updateSplineControlPoint(layerId.value, newPoint.id, {
                handleOut: { x: layerPos.x, y: layerPos.y },
                handleIn: { x: rawNewPointX - dx, y: rawNewPointY - dy },
                type: "smooth",
              });
            }
          }
        } else if (newPoint && prevPointIndex < 0) {
          if (layerId.value) {
            const dx = layerPos.x - rawNewPointX;
            const dy = layerPos.y - rawNewPointY;
            if (Math.sqrt(dx * dx + dy * dy) > 5) {
              store.updateSplineControlPoint(layerId.value, newPoint.id, {
                handleOut: { x: layerPos.x, y: layerPos.y },
                handleIn: { x: rawNewPointX - dx, y: rawNewPointY - dy },
                type: "smooth",
              });
            }
          }
        }
      }
    } else if (!isPenMode.value || penSubMode.value !== "add") {
      previewCurve.value = null;
    }

    // Check proximity to first point for close path preview
    if (visibleControlPoints.value.length > 2 && !isClosed.value) {
      const firstPoint = visibleControlPoints.value[0];
      const dx = pos.x - firstPoint.x;
      const dy = pos.y - firstPoint.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      closePathPreview.value = dist < CLOSE_THRESHOLD;
    } else {
      closePathPreview.value = false;
    }

    // Handle dragging
    if (dragTarget.value && layerId.value) {
      const layer = store.layers.find((l: any) => l.id === layerId.value);
      if (!layer || !isSplineOrPathType(layer.type)) return;

      const layerData = layer.data as SplineData | PathLayerData;
      const point = layerData.controlPoints?.find(
        (p) => p.id === dragTarget.value?.pointId,
      );
      if (!point) return;

      const layerPos = inverseTransformPoint(pos);

      if (dragTarget.value.type === "point") {
        const dx = layerPos.x - point.x;
        const dy = layerPos.y - point.y;

        const updates: any = { x: layerPos.x, y: layerPos.y };
        if (point.handleIn) {
          updates.handleIn = {
            x: point.handleIn.x + dx,
            y: point.handleIn.y + dy,
          };
        }
        if (point.handleOut) {
          updates.handleOut = {
            x: point.handleOut.x + dx,
            y: point.handleOut.y + dy,
          };
        }

        store.updateSplineControlPoint(layerId.value, point.id, updates);
        emit.pointMoved(point.id, layerPos.x, layerPos.y);
      } else if (dragTarget.value.type === "handleIn") {
        const updates: any = { handleIn: { x: layerPos.x, y: layerPos.y } };

        if (point.type === "smooth") {
          const dx = layerPos.x - point.x;
          const dy = layerPos.y - point.y;
          updates.handleOut = { x: point.x - dx, y: point.y - dy };
        }

        store.updateSplineControlPoint(layerId.value, point.id, updates);
        emit.handleMoved(point.id, "in", layerPos.x, layerPos.y);
      } else if (dragTarget.value.type === "handleOut") {
        const updates: any = { handleOut: { x: layerPos.x, y: layerPos.y } };

        if (point.type === "smooth") {
          const dx = layerPos.x - point.x;
          const dy = layerPos.y - point.y;
          updates.handleIn = { x: point.x - dx, y: point.y - dy };
        }

        store.updateSplineControlPoint(layerId.value, point.id, updates);
        emit.handleMoved(point.id, "out", layerPos.x, layerPos.y);
      } else if (dragTarget.value.type === "depth") {
        const screenDy =
          event.clientY - (dragTarget.value.screenStartY ?? event.clientY);
        const depthScale = 2;
        const newDepth = Math.max(
          0,
          (dragTarget.value.startDepth ?? 0) - screenDy * depthScale,
        );

        store.updateSplineControlPoint(layerId.value, point.id, {
          depth: newDepth,
        });
      } else if (dragTarget.value.type === "axisX") {
        const screenDx =
          event.clientX - (dragTarget.value.screenStartX ?? event.clientX);
        const dx = screenDx / (zoom.value || 1);
        const newX = (dragTarget.value.originalX ?? point.x) + dx;

        const handleDx = newX - point.x;
        const updates: any = { x: newX };
        if (point.handleIn) {
          updates.handleIn = {
            x: point.handleIn.x + handleDx,
            y: point.handleIn.y,
          };
        }
        if (point.handleOut) {
          updates.handleOut = {
            x: point.handleOut.x + handleDx,
            y: point.handleOut.y,
          };
        }

        store.updateSplineControlPoint(layerId.value, point.id, updates);
        emit.pointMoved(point.id, newX, point.y);
      } else if (dragTarget.value.type === "axisY") {
        const screenDy =
          event.clientY - (dragTarget.value.screenStartY ?? event.clientY);
        const dy = screenDy / (zoom.value || 1);
        const newY = (dragTarget.value.originalY ?? point.y) + dy;

        const handleDy = newY - point.y;
        const updates: any = { y: newY };
        if (point.handleIn) {
          updates.handleIn = {
            x: point.handleIn.x,
            y: point.handleIn.y + handleDy,
          };
        }
        if (point.handleOut) {
          updates.handleOut = {
            x: point.handleOut.x,
            y: point.handleOut.y + handleDy,
          };
        }

        store.updateSplineControlPoint(layerId.value, point.id, updates);
        emit.pointMoved(point.id, point.x, newY);
      }

      emit.pathUpdated();
    }
  }

  // Handle mouse up
  function handleMouseUp() {
    previewCurve.value = null;

    if (dragTarget.value && layerId.value) {
      if (dragTarget.value.type === "newPoint") {
        dragTarget.value = null;
        emit.pathUpdated();
        return;
      }

      const layer = store.layers.find((l: any) => l.id === layerId.value);
      if (layer && isSplineOrPathType(layer.type)) {
        const layerData = layer.data as SplineData | PathLayerData;
        const point = layerData.controlPoints?.find(
          (p) => p.id === dragTarget.value?.pointId,
        );
        if (point?.handleOut && dragTarget.value.type === "handleOut") {
          const dx = point.handleOut.x - point.x;
          const dy = point.handleOut.y - point.y;
          const dist = Math.sqrt(dx * dx + dy * dy);

          if (dist > 5) {
            store.updateSplineControlPoint(layerId.value, point.id, {
              type: "smooth",
              handleIn: { x: point.x - dx, y: point.y - dy },
            });
          } else {
            store.updateSplineControlPoint(layerId.value, point.id, {
              handleOut: null,
            });
          }
        }
      }

      dragTarget.value = null;
      emit.pathUpdated();
    }
  }

  // Handle right click
  function handleRightClick(event: MouseEvent) {
    event.preventDefault();
    event.stopPropagation();

    if (!layerId.value) return;

    if (isPenMode.value) {
      emit.togglePenMode();

      previewCurve.value = null;
      previewPoint.value = null;
      insertPreviewPoint.value = null;
      closePathPreview.value = false;
      hoverFeedback.value = null;
      hoveredPointId.value = null;
    }
  }

  // Handle click on control point
  function handlePointClick(pointId: string, event: MouseEvent) {
    const point = visibleControlPoints.value.find((p) => p.id === pointId);
    if (!point) return;

    if (isPenMode.value) {
      if (penSubMode.value === "delete") {
        if (layerId.value) {
          store.deleteSplineControlPoint(layerId.value, pointId);
          emit.pointDeleted(pointId);
          emit.pathUpdated();
          selectedPointId.value = null;
          hoveredPointId.value = null;
          hoverFeedback.value = null;
        }
        return;
      } else if (penSubMode.value === "convert") {
        if (layerId.value) {
          const newType = point.type === "smooth" ? "corner" : "smooth";
          if (newType === "corner") {
            store.updateSplineControlPoint(layerId.value, pointId, {
              type: "corner",
              handleIn: null,
              handleOut: null,
            });
          } else {
            const handleOffset = 30;
            store.updateSplineControlPoint(layerId.value, pointId, {
              type: "smooth",
              handleIn: { x: point.x - handleOffset, y: point.y },
              handleOut: { x: point.x + handleOffset, y: point.y },
            });
          }
          selectedPointId.value = pointId;
          emit.pathUpdated();
        }
        return;
      }
    }

    // Handle multi-select with Shift key
    if (event.shiftKey) {
      if (selectedPointIds.value.includes(pointId)) {
        selectedPointIds.value = selectedPointIds.value.filter(
          (id) => id !== pointId,
        );
      } else {
        selectedPointIds.value = [...selectedPointIds.value, pointId];
      }
      selectedPointId.value = pointId;
    } else {
      selectedPointId.value = pointId;
      selectedPointIds.value = [pointId];
    }

    if (!isPenMode.value) {
      const pos = getMousePos(event);
      dragTarget.value = {
        type: "point",
        pointId,
        startX: pos.x,
        startY: pos.y,
      };
    }
  }

  // Handle hover over control point
  function handlePointHover(pointId: string) {
    hoveredPointId.value = pointId;
    const point = visibleControlPoints.value.find((p) => p.id === pointId);

    if (isPenMode.value && point) {
      hoverFeedbackPos.value = { x: point.x, y: point.y };

      if (penSubMode.value === "delete") {
        hoverFeedback.value = "Click to delete point";
      } else if (penSubMode.value === "convert") {
        const currentType = point.type === "smooth" ? "smooth" : "corner";
        const newType = currentType === "smooth" ? "corner" : "smooth";
        hoverFeedback.value = `Click to convert to ${newType}`;
      } else {
        hoverFeedback.value = null;
      }
    } else {
      hoverFeedback.value = null;
    }
  }

  // Handle mouse leave from control point
  function handlePointLeave() {
    hoveredPointId.value = null;
    hoverFeedback.value = null;
    hoverFeedbackPos.value = null;
  }

  // Start dragging a point
  function startDragPoint(pointId: string, event: MouseEvent) {
    selectedPointId.value = pointId;

    if (!isPenMode.value) {
      const pos = getMousePos(event);
      dragTarget.value = {
        type: "point",
        pointId,
        startX: pos.x,
        startY: pos.y,
      };
    }
  }

  // Start dragging a handle
  function startDragHandle(
    pointId: string,
    handleType: "in" | "out",
    event: MouseEvent,
  ) {
    const pos = getMousePos(event);
    dragTarget.value = {
      type: handleType === "in" ? "handleIn" : "handleOut",
      pointId,
      startX: pos.x,
      startY: pos.y,
    };
  }

  // Start axis-constrained drag
  function startDragAxis(pointId: string, axis: "X" | "Y", event: MouseEvent) {
    const point = visibleControlPoints.value.find((p) => p.id === pointId);
    if (!point) return;

    const pos = getMousePos(event);

    selectedPointId.value = pointId;
    dragTarget.value = {
      type: axis === "X" ? "axisX" : "axisY",
      pointId,
      startX: pos.x,
      startY: pos.y,
      originalX: point.x,
      originalY: point.y,
      screenStartX: event.clientX,
      screenStartY: event.clientY,
    };
  }

  // Start dragging depth
  function startDragDepth(pointId: string, event: MouseEvent) {
    const point = visibleControlPoints.value.find((p) => p.id === pointId);
    if (!point) return;

    selectedPointId.value = pointId;
    dragTarget.value = {
      type: "depth",
      pointId,
      startX: event.clientX,
      startY: event.clientY,
      startDepth: (point as any).depth ?? 0,
      screenStartX: event.clientX,
      screenStartY: event.clientY,
    };
  }

  // Handle keyboard shortcuts
  function handleKeyDown(event: KeyboardEvent) {
    if (event.key === "Delete" || event.key === "Backspace") {
      if (selectedPointId.value && layerId.value) {
        const layer = store.layers.find((l: any) => l.id === layerId.value);
        if (layer && isSplineOrPathType(layer.type)) {
          const pointId = selectedPointId.value;
          store.deleteSplineControlPoint(layerId.value, pointId);
          emit.pointDeleted(pointId);
          emit.pathUpdated();
          selectedPointId.value = null;
          selectedPointIds.value = [];
        }
      }
    }

    if (event.key === "Escape") {
      selectedPointId.value = null;
      selectedPointIds.value = [];
      hoverFeedback.value = null;
      if (isPenMode.value) {
        emit.togglePenMode();
      }
    }
  }

  // Clear selection
  function clearSelection() {
    selectedPointId.value = null;
    selectedPointIds.value = [];
  }

  return {
    // State
    selectedPointId,
    selectedPointIds,
    hoveredPointId,
    hoverFeedback,
    hoverFeedbackPos,
    previewPoint,
    closePathPreview,
    previewCurve,
    insertPreviewPoint,
    penSubMode,
    dragTarget,
    // Computed
    activeToolTip,
    hoverFeedbackStyle,
    selectedPointCount,
    // Methods
    screenToCanvas,
    getMousePos,
    evaluateBezier,
    findClosestPointOnPath,
    findClickedPoint,
    generateCurvePreview,
    setPenSubMode,
    handleMouseDown,
    handleMouseMove,
    handleMouseUp,
    handleRightClick,
    handlePointClick,
    handlePointHover,
    handlePointLeave,
    startDragPoint,
    startDragHandle,
    startDragAxis,
    startDragDepth,
    handleKeyDown,
    clearSelection,
  };
}
