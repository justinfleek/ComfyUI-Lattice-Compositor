// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // kanban
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Kanban board FFI for drag-and-drop functionality

/**
 * Initialize Kanban board drag and drop
 * @param {Element} container - Kanban board container
 * @param {Object} callbacks - Event callbacks
 * @param {Object} options - Configuration options
 * @returns {Object} Kanban controller
 */
export const initKanbanImpl = (container) => (callbacks) => (options) => () => {
  const { dragHandleClass, cardClass, columnClass } = options;

  let draggedElement = null;
  let draggedType = null; // 'card' or 'column'
  let sourceColumn = null;
  let sourceIndex = -1;
  let placeholder = null;

  /**
   * Get card ID from element
   */
  const getCardId = (element) => {
    const card = element.closest("[data-card-id]");
    return card ? card.getAttribute("data-card-id") : null;
  };

  /**
   * Get column ID from element
   */
  const getColumnId = (element) => {
    const column = element.closest("[data-column-id]");
    return column ? column.getAttribute("data-column-id") : null;
  };

  /**
   * Get swimlane ID from element
   */
  const getSwimlaneId = (element) => {
    const swimlane = element.closest("[data-swimlane]");
    return swimlane ? swimlane.getAttribute("data-swimlane") : null;
  };

  /**
   * Get index of card within column
   */
  const getCardIndex = (card) => {
    const column = card.closest(".kanban-column-content");
    if (!column) return -1;
    const cards = Array.from(column.querySelectorAll("[data-card-id]"));
    return cards.indexOf(card);
  };

  /**
   * Get index of column within board
   */
  const getColumnIndex = (column) => {
    const board = column.closest("[data-kanban-board]");
    if (!board) return -1;
    const columns = Array.from(board.querySelectorAll("[data-column-id]"));
    return columns.indexOf(column);
  };

  /**
   * Create placeholder element
   */
  const createPlaceholder = (type) => {
    const el = document.createElement("div");
    el.className =
      type === "card"
        ? "kanban-placeholder h-20 border-2 border-dashed border-primary/50 rounded-lg bg-primary/10 transition-all"
        : "kanban-placeholder w-72 h-full border-2 border-dashed border-primary/50 rounded-lg bg-primary/10";
    return el;
  };

  /**
   * Handle drag start
   */
  const handleDragStart = (e) => {
    const cardId = getCardId(e.target);
    const columnId = getColumnId(e.target);

    if (cardId) {
      draggedElement = e.target.closest("[data-card-id]");
      draggedType = "card";
      sourceColumn = getColumnId(draggedElement);
      sourceIndex = getCardIndex(draggedElement);

      // Set drag data
      e.dataTransfer.effectAllowed = "move";
      e.dataTransfer.setData("text/plain", cardId);
      e.dataTransfer.setData("application/x-kanban-card", cardId);

      // Add dragging style
      requestAnimationFrame(() => {
        draggedElement.classList.add("opacity-50", "rotate-2", "scale-105");
      });

      // Create placeholder
      placeholder = createPlaceholder("card");
    }
  };

  /**
   * Handle drag over
   */
  const handleDragOver = (e) => {
    e.preventDefault();
    e.dataTransfer.dropEffect = "move";

    if (!draggedElement || draggedType !== "card") return;

    // Find the column content area
    const columnContent = e.target.closest(".kanban-column-content");
    if (!columnContent) return;

    // Find the closest card
    const afterElement = getDragAfterElement(columnContent, e.clientY);

    // Insert placeholder
    if (placeholder && placeholder.parentNode !== columnContent) {
      // Remove from previous location
      if (placeholder.parentNode) {
        placeholder.parentNode.removeChild(placeholder);
      }
    }

    if (afterElement) {
      columnContent.insertBefore(placeholder, afterElement);
    } else {
      columnContent.appendChild(placeholder);
    }
  };

  /**
   * Get the element after which to insert
   */
  const getDragAfterElement = (columnContent, y) => {
    const cards = Array.from(
      columnContent.querySelectorAll("[data-card-id]:not(.opacity-50)")
    );

    return cards.reduce(
      (closest, card) => {
        const box = card.getBoundingClientRect();
        const offset = y - box.top - box.height / 2;

        if (offset < 0 && offset > closest.offset) {
          return { offset, element: card };
        }
        return closest;
      },
      { offset: Number.NEGATIVE_INFINITY, element: null }
    ).element;
  };

  /**
   * Handle drag leave
   */
  const handleDragLeave = (e) => {
    // Only handle if leaving the column content area
    const columnContent = e.target.closest(".kanban-column-content");
    const relatedTarget = e.relatedTarget?.closest(".kanban-column-content");

    if (columnContent && columnContent !== relatedTarget) {
      // Remove placeholder if leaving column
      if (placeholder && placeholder.parentNode === columnContent) {
        // Don't remove immediately - might be entering a card
      }
    }
  };

  /**
   * Handle drop
   */
  const handleDrop = (e) => {
    e.preventDefault();

    if (!draggedElement || draggedType !== "card") return;

    const columnContent = e.target.closest(".kanban-column-content");
    if (!columnContent) return;

    const toColumn = getColumnId(columnContent);
    const swimlaneId = getSwimlaneId(columnContent);

    // Calculate target index
    let toIndex = 0;
    if (placeholder && placeholder.parentNode === columnContent) {
      const cards = Array.from(columnContent.querySelectorAll("[data-card-id]"));
      toIndex = cards.indexOf(placeholder);
      if (toIndex === -1) toIndex = cards.length;
    }

    // Remove placeholder
    if (placeholder && placeholder.parentNode) {
      placeholder.parentNode.removeChild(placeholder);
    }

    // Reset dragged element styles
    draggedElement.classList.remove("opacity-50", "rotate-2", "scale-105");

    // Fire callback
    const cardId = draggedElement.getAttribute("data-card-id");
    if (cardId && toColumn) {
      callbacks.onCardMove({
        cardId,
        fromColumn: sourceColumn,
        toColumn,
        fromIndex: sourceIndex,
        toIndex,
        swimlaneId: swimlaneId || null,
      })();
    }

    // Cleanup
    draggedElement = null;
    draggedType = null;
    sourceColumn = null;
    sourceIndex = -1;
    placeholder = null;
  };

  /**
   * Handle drag end
   */
  const handleDragEnd = (e) => {
    // Cleanup any lingering state
    if (draggedElement) {
      draggedElement.classList.remove("opacity-50", "rotate-2", "scale-105");
    }

    if (placeholder && placeholder.parentNode) {
      placeholder.parentNode.removeChild(placeholder);
    }

    draggedElement = null;
    draggedType = null;
    sourceColumn = null;
    sourceIndex = -1;
    placeholder = null;

    // Remove any lingering placeholders
    container.querySelectorAll(".kanban-placeholder").forEach((el) => {
      el.parentNode?.removeChild(el);
    });
  };

  // Attach event listeners
  container.addEventListener("dragstart", handleDragStart);
  container.addEventListener("dragover", handleDragOver);
  container.addEventListener("dragleave", handleDragLeave);
  container.addEventListener("drop", handleDrop);
  container.addEventListener("dragend", handleDragEnd);

  return {
    container,
    destroy: () => {
      container.removeEventListener("dragstart", handleDragStart);
      container.removeEventListener("dragover", handleDragOver);
      container.removeEventListener("dragleave", handleDragLeave);
      container.removeEventListener("drop", handleDrop);
      container.removeEventListener("dragend", handleDragEnd);
    },
  };
};

/**
 * Destroy Kanban and cleanup
 * @param {Object} kanban - Kanban controller
 */
export const destroyKanbanImpl = (kanban) => () => {
  if (kanban && kanban.destroy) {
    kanban.destroy();
  }
};

/**
 * Unsafe placeholder for KanbanElement
 */
export const unsafeKanbanElement = {
  container: null,
  destroy: () => {},
};

/**
 * Take first n characters from a string
 * @param {number} n - Number of characters to take
 * @param {string} s - Source string
 * @returns {string} First n characters
 */
export const takeImpl = (n) => (s) => s.slice(0, n);
