/**
 * Canvas Marquee Selection Composable
 *
 * Phase 8: Canvas Marquee Selection Implementation
 *
 * Features:
 * - Drag-to-select rectangle on canvas
 * - Shift+drag to add to selection
 * - Alt+drag to remove from selection
 * - Layer bounds hit testing
 */

import { ref, computed, type Ref, onMounted, onUnmounted } from 'vue';
import { createLogger } from '@/utils/logger';

const logger = createLogger('CanvasSelection');

// ============================================================================
// TYPES
// ============================================================================

export interface Rect {
  x: number;
  y: number;
  width: number;
  height: number;
}

export interface Point {
  x: number;
  y: number;
}

export interface SelectableItem {
  id: string;
  bounds: Rect;
}

export type SelectionMode = 'replace' | 'add' | 'subtract' | 'intersect';

export interface SelectionState {
  /** Is selection in progress */
  isSelecting: boolean;
  /** Selection rectangle in canvas coordinates */
  selectionRect: Rect | null;
  /** Start point of selection */
  startPoint: Point | null;
  /** Current point during selection */
  currentPoint: Point | null;
  /** Selection mode (based on modifier keys) */
  mode: SelectionMode;
}

export interface UseCanvasSelectionOptions {
  /** Canvas element ref */
  canvasRef: Ref<HTMLElement | null>;
  /** Get selectable items with their bounds */
  getSelectableItems: () => SelectableItem[];
  /** Callback when selection changes */
  onSelectionChange: (selectedIds: string[], mode: SelectionMode) => void;
  /** Current selected IDs */
  currentSelection?: Ref<string[]>;
  /** Minimum drag distance to start selection (pixels) */
  minDragDistance?: number;
  /** Enable selection */
  enabled?: Ref<boolean>;
}

// ============================================================================
// GEOMETRY HELPERS
// ============================================================================

/**
 * Check if two rectangles intersect
 */
export function rectsIntersect(a: Rect, b: Rect): boolean {
  return !(
    a.x + a.width < b.x ||
    b.x + b.width < a.x ||
    a.y + a.height < b.y ||
    b.y + b.height < a.y
  );
}

/**
 * Check if rect A completely contains rect B
 */
export function rectContains(container: Rect, item: Rect): boolean {
  return (
    container.x <= item.x &&
    container.y <= item.y &&
    container.x + container.width >= item.x + item.width &&
    container.y + container.height >= item.y + item.height
  );
}

/**
 * Create rect from two points
 */
export function rectFromPoints(p1: Point, p2: Point): Rect {
  return {
    x: Math.min(p1.x, p2.x),
    y: Math.min(p1.y, p2.y),
    width: Math.abs(p2.x - p1.x),
    height: Math.abs(p2.y - p1.y),
  };
}

/**
 * Get point from mouse event relative to element
 */
export function getRelativePoint(event: MouseEvent, element: HTMLElement): Point {
  const rect = element.getBoundingClientRect();
  return {
    x: event.clientX - rect.left,
    y: event.clientY - rect.top,
  };
}

/**
 * Calculate distance between two points
 */
export function pointDistance(p1: Point, p2: Point): number {
  const dx = p2.x - p1.x;
  const dy = p2.y - p1.y;
  return Math.sqrt(dx * dx + dy * dy);
}

// ============================================================================
// COMPOSABLE
// ============================================================================

export function useCanvasSelection(options: UseCanvasSelectionOptions) {
  const {
    canvasRef,
    getSelectableItems,
    onSelectionChange,
    currentSelection,
    minDragDistance = 5,
    enabled = ref(true),
  } = options;

  // State
  const state = ref<SelectionState>({
    isSelecting: false,
    selectionRect: null,
    startPoint: null,
    currentPoint: null,
    mode: 'replace',
  });

  // Track mouse state
  let isDragging = false;
  let hasDraggedPastThreshold = false;

  // ============================================================================
  // SELECTION MODE
  // ============================================================================

  /**
   * Determine selection mode from modifier keys
   */
  function getSelectionMode(event: MouseEvent | KeyboardEvent): SelectionMode {
    if (event.shiftKey && event.altKey) {
      return 'intersect';
    }
    if (event.shiftKey) {
      return 'add';
    }
    if (event.altKey) {
      return 'subtract';
    }
    return 'replace';
  }

  // ============================================================================
  // HIT TESTING
  // ============================================================================

  /**
   * Find items that intersect with selection rectangle
   */
  function findItemsInRect(rect: Rect): string[] {
    const items = getSelectableItems();
    return items
      .filter(item => rectsIntersect(rect, item.bounds))
      .map(item => item.id);
  }

  /**
   * Apply selection based on mode
   */
  function applySelection(selectedIds: string[], mode: SelectionMode): string[] {
    const current = currentSelection?.value || [];

    switch (mode) {
      case 'replace':
        return selectedIds;

      case 'add':
        return [...new Set([...current, ...selectedIds])];

      case 'subtract':
        return current.filter(id => !selectedIds.includes(id));

      case 'intersect':
        return current.filter(id => selectedIds.includes(id));

      default:
        return selectedIds;
    }
  }

  // ============================================================================
  // EVENT HANDLERS
  // ============================================================================

  function handleMouseDown(event: MouseEvent) {
    if (!enabled.value) return;
    if (!canvasRef.value) return;

    // Only start selection on left click
    if (event.button !== 0) return;

    // Don't start selection if clicking on a layer (let layer handle it)
    const target = event.target as HTMLElement;
    if (target.closest('[data-selectable]')) return;

    const point = getRelativePoint(event, canvasRef.value);

    state.value.startPoint = point;
    state.value.currentPoint = point;
    state.value.mode = getSelectionMode(event);
    isDragging = true;
    hasDraggedPastThreshold = false;

    // Prevent text selection
    event.preventDefault();
  }

  function handleMouseMove(event: MouseEvent) {
    if (!isDragging || !state.value.startPoint) return;
    if (!canvasRef.value) return;

    const point = getRelativePoint(event, canvasRef.value);
    state.value.currentPoint = point;

    // Check if we've dragged past threshold
    if (!hasDraggedPastThreshold) {
      const distance = pointDistance(state.value.startPoint, point);
      if (distance >= minDragDistance) {
        hasDraggedPastThreshold = true;
        state.value.isSelecting = true;
      }
    }

    if (hasDraggedPastThreshold) {
      // Update selection rectangle
      state.value.selectionRect = rectFromPoints(state.value.startPoint, point);

      // Update mode based on current modifier keys
      state.value.mode = getSelectionMode(event);
    }
  }

  function handleMouseUp(event: MouseEvent) {
    if (!isDragging) return;

    isDragging = false;

    if (hasDraggedPastThreshold && state.value.selectionRect) {
      // Find items in selection rect
      const selectedIds = findItemsInRect(state.value.selectionRect);

      // Apply selection mode
      const finalSelection = applySelection(selectedIds, state.value.mode);

      // Notify callback
      onSelectionChange(finalSelection, state.value.mode);

      logger.debug(`Selection completed: ${finalSelection.length} items (${state.value.mode})`);
    }

    // Reset state
    state.value.isSelecting = false;
    state.value.selectionRect = null;
    state.value.startPoint = null;
    state.value.currentPoint = null;
    hasDraggedPastThreshold = false;
  }

  function handleKeyDown(event: KeyboardEvent) {
    if (!state.value.isSelecting) return;

    // Update mode based on current modifier keys
    state.value.mode = getSelectionMode(event);
  }

  function handleKeyUp(event: KeyboardEvent) {
    if (!state.value.isSelecting) return;

    // Update mode based on current modifier keys
    state.value.mode = getSelectionMode(event);
  }

  // ============================================================================
  // LIFECYCLE
  // ============================================================================

  function setupListeners() {
    if (!canvasRef.value) return;

    canvasRef.value.addEventListener('mousedown', handleMouseDown);
    window.addEventListener('mousemove', handleMouseMove);
    window.addEventListener('mouseup', handleMouseUp);
    window.addEventListener('keydown', handleKeyDown);
    window.addEventListener('keyup', handleKeyUp);
  }

  function cleanupListeners() {
    if (canvasRef.value) {
      canvasRef.value.removeEventListener('mousedown', handleMouseDown);
    }
    window.removeEventListener('mousemove', handleMouseMove);
    window.removeEventListener('mouseup', handleMouseUp);
    window.removeEventListener('keydown', handleKeyDown);
    window.removeEventListener('keyup', handleKeyUp);
  }

  onMounted(() => {
    setupListeners();
  });

  onUnmounted(() => {
    cleanupListeners();
  });

  // ============================================================================
  // COMPUTED
  // ============================================================================

  const selectionRectStyle = computed(() => {
    if (!state.value.selectionRect) return null;

    const { x, y, width, height } = state.value.selectionRect;

    return {
      position: 'absolute' as const,
      left: `${x}px`,
      top: `${y}px`,
      width: `${width}px`,
      height: `${height}px`,
      border: '1px dashed var(--weyl-accent, #8B5CF6)',
      backgroundColor: 'rgba(139, 92, 246, 0.1)',
      pointerEvents: 'none' as const,
      zIndex: 9999,
    };
  });

  // ============================================================================
  // PUBLIC API
  // ============================================================================

  return {
    /** Current selection state */
    state: computed(() => state.value),

    /** Is currently selecting */
    isSelecting: computed(() => state.value.isSelecting),

    /** Selection rectangle */
    selectionRect: computed(() => state.value.selectionRect),

    /** Current selection mode */
    selectionMode: computed(() => state.value.mode),

    /** Style object for selection rectangle overlay */
    selectionRectStyle,

    /** Manually start selection at a point */
    startSelection(point: Point, mode: SelectionMode = 'replace') {
      state.value.startPoint = point;
      state.value.currentPoint = point;
      state.value.mode = mode;
      state.value.isSelecting = true;
      isDragging = true;
      hasDraggedPastThreshold = true;
    },

    /** Cancel current selection */
    cancelSelection() {
      state.value.isSelecting = false;
      state.value.selectionRect = null;
      state.value.startPoint = null;
      state.value.currentPoint = null;
      isDragging = false;
      hasDraggedPastThreshold = false;
    },

    /** Re-setup listeners (e.g., after canvas ref changes) */
    refresh() {
      cleanupListeners();
      setupListeners();
    },
  };
}

// ============================================================================
// EXPORTS
// ============================================================================

export default useCanvasSelection;
