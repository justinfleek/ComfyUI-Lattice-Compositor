// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // datagrid
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// JavaScript FFI for DataGrid interactive features:
// - Column resizing (drag handles)
// - Column reordering (drag & drop)
// - Virtual scrolling
// - Keyboard navigation
// - Export utilities

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // column resizing
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Initialize column resize functionality
 * @param {HTMLElement} gridEl - The grid container element
 * @param {function} onResize - Callback (columnKey, newWidth) => Effect Unit
 * @returns {function} Cleanup function
 */
export const initColumnResizeImpl = (gridEl) => (onResize) => () => {
  let isResizing = false;
  let currentColumn = null;
  let startX = 0;
  let startWidth = 0;

  const handleMouseDown = (e) => {
    const handle = e.target.closest('[data-resize-handle]');
    if (!handle) return;

    isResizing = true;
    currentColumn = handle.dataset.resizeHandle;
    const th = handle.closest('th');
    startX = e.pageX;
    startWidth = th.offsetWidth;

    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';

    e.preventDefault();
  };

  const handleMouseMove = (e) => {
    if (!isResizing || !currentColumn) return;

    const diff = e.pageX - startX;
    const newWidth = Math.max(50, startWidth + diff);
    
    // Update column width in DOM
    const th = gridEl.querySelector(`th[data-column-key="${currentColumn}"]`);
    if (th) {
      th.style.width = `${newWidth}px`;
      th.style.minWidth = `${newWidth}px`;
    }

    // Update all cells in this column
    const cells = gridEl.querySelectorAll(`td[data-column-key="${currentColumn}"]`);
    cells.forEach(cell => {
      cell.style.width = `${newWidth}px`;
      cell.style.minWidth = `${newWidth}px`;
    });
  };

  const handleMouseUp = () => {
    if (isResizing && currentColumn) {
      const th = gridEl.querySelector(`th[data-column-key="${currentColumn}"]`);
      if (th) {
        onResize({ columnKey: currentColumn, width: th.offsetWidth })();
      }
    }

    isResizing = false;
    currentColumn = null;
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
  };

  gridEl.addEventListener('mousedown', handleMouseDown);
  document.addEventListener('mousemove', handleMouseMove);
  document.addEventListener('mouseup', handleMouseUp);

  // Return cleanup function
  return () => {
    gridEl.removeEventListener('mousedown', handleMouseDown);
    document.removeEventListener('mousemove', handleMouseMove);
    document.removeEventListener('mouseup', handleMouseUp);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // column reordering
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Initialize column drag & drop reordering
 * @param {HTMLElement} gridEl - The grid container element
 * @param {function} onReorder - Callback (newColumnOrder: Array String) => Effect Unit
 * @returns {function} Cleanup function
 */
export const initColumnReorderImpl = (gridEl) => (onReorder) => () => {
  let draggedColumn = null;
  let dragOverColumn = null;

  const handleDragStart = (e) => {
    const th = e.target.closest('th[data-column-key]');
    if (!th) return;

    draggedColumn = th.dataset.columnKey;
    th.classList.add('opacity-50');
    e.dataTransfer.effectAllowed = 'move';
    e.dataTransfer.setData('text/plain', draggedColumn);
  };

  const handleDragOver = (e) => {
    e.preventDefault();
    const th = e.target.closest('th[data-column-key]');
    if (!th || th.dataset.columnKey === draggedColumn) return;

    dragOverColumn = th.dataset.columnKey;
    
    // Visual feedback
    const allTh = gridEl.querySelectorAll('th[data-column-key]');
    allTh.forEach(el => { el.classList.remove('border-l-2', 'border-primary'); });
    th.classList.add('border-l-2', 'border-primary');
  };

  const handleDragEnd = (e) => {
    const th = e.target.closest('th[data-column-key]');
    if (th) {
      th.classList.remove('opacity-50');
    }

    // Remove visual feedback
    const allTh = gridEl.querySelectorAll('th[data-column-key]');
    allTh.forEach(el => { el.classList.remove('border-l-2', 'border-primary'); });

    if (draggedColumn && dragOverColumn && draggedColumn !== dragOverColumn) {
      // Get current column order
      const columns = Array.from(gridEl.querySelectorAll('th[data-column-key]'))
        .map(el => el.dataset.columnKey);
      
      // Reorder
      const fromIndex = columns.indexOf(draggedColumn);
      const toIndex = columns.indexOf(dragOverColumn);
      
      if (fromIndex !== -1 && toIndex !== -1) {
        columns.splice(fromIndex, 1);
        columns.splice(toIndex, 0, draggedColumn);
        onReorder(columns)();
      }
    }

    draggedColumn = null;
    dragOverColumn = null;
  };

  // Make headers draggable
  const headers = gridEl.querySelectorAll('th[data-column-key]');
  headers.forEach(th => {
    th.setAttribute('draggable', 'true');
  });

  gridEl.addEventListener('dragstart', handleDragStart);
  gridEl.addEventListener('dragover', handleDragOver);
  gridEl.addEventListener('dragend', handleDragEnd);

  return () => {
    gridEl.removeEventListener('dragstart', handleDragStart);
    gridEl.removeEventListener('dragover', handleDragOver);
    gridEl.removeEventListener('dragend', handleDragEnd);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // virtual scrolling
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Virtual scrolling state
 */
class VirtualScroller {
  constructor(config, onVisibleRangeChange) {
    this.rowHeight = config.rowHeight || 40;
    this.overscan = config.overscan || 5;
    this.containerHeight = config.containerHeight || 400;
    this.totalRows = 0;
    this.onVisibleRangeChange = onVisibleRangeChange;
    this.scrollTop = 0;
  }

  setTotalRows(count) {
    this.totalRows = count;
  }

  handleScroll(scrollTop) {
    this.scrollTop = scrollTop;
    const range = this.getVisibleRange();
    this.onVisibleRangeChange(range)();
  }

  getVisibleRange() {
    const startIndex = Math.max(0, Math.floor(this.scrollTop / this.rowHeight) - this.overscan);
    const visibleCount = Math.ceil(this.containerHeight / this.rowHeight);
    const endIndex = Math.min(this.totalRows, startIndex + visibleCount + this.overscan * 2);
    
    return {
      startIndex,
      endIndex,
      offsetY: startIndex * this.rowHeight
    };
  }

  getTotalHeight() {
    return this.totalRows * this.rowHeight;
  }
}

/**
 * Initialize virtual scrolling
 * @param {HTMLElement} scrollContainer - The scrollable container
 * @param {Object} config - Virtual scroll configuration
 * @param {function} onRangeChange - Callback ({ startIndex, endIndex, offsetY }) => Effect Unit
 * @returns {Object} Scroller instance with methods
 */
export const initVirtualScrollImpl = (scrollContainer) => (config) => (onRangeChange) => () => {
  const scroller = new VirtualScroller(config, onRangeChange);

  const handleScroll = () => {
    scroller.handleScroll(scrollContainer.scrollTop);
  };

  scrollContainer.addEventListener('scroll', handleScroll, { passive: true });

  return {
    setTotalRows: (count) => () => scroller.setTotalRows(count),
    getVisibleRange: () => scroller.getVisibleRange(),
    getTotalHeight: () => scroller.getTotalHeight(),
    cleanup: () => {
      scrollContainer.removeEventListener('scroll', handleScroll);
    }
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // keyboard navigation
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Initialize keyboard navigation for grid
 * @param {HTMLElement} gridEl - The grid container element
 * @param {Object} handlers - Event handlers { onNavigate, onSelect, onEdit, onEscape }
 * @returns {function} Cleanup function
 */
export const initKeyboardNavImpl = (gridEl) => (handlers) => () => {
  let focusedRow = 0;
  let focusedCol = 0;
  let isEditing = false;

  const getRowCount = () => {
    return gridEl.querySelectorAll('tbody tr[data-row-key]').length;
  };

  const getColCount = () => {
    return gridEl.querySelectorAll('thead th[data-column-key]').length;
  };

  const focusCell = (row, col) => {
    const rowEl = gridEl.querySelectorAll('tbody tr[data-row-key]')[row];
    if (!rowEl) return;

    const cells = rowEl.querySelectorAll('td[data-column-key]');
    const cellEl = cells[col];
    if (!cellEl) return;

    // Remove previous focus
    gridEl.querySelectorAll('[data-focused="true"]').forEach(el => {
      el.removeAttribute('data-focused');
      el.classList.remove('ring-2', 'ring-ring', 'ring-offset-2');
    });

    // Add focus to new cell
    cellEl.setAttribute('data-focused', 'true');
    cellEl.classList.add('ring-2', 'ring-ring', 'ring-offset-2');
    cellEl.focus();

    focusedRow = row;
    focusedCol = col;

    if (handlers.onNavigate) {
      handlers.onNavigate({ rowIndex: row, colIndex: col })();
    }
  };

  const handleKeyDown = (e) => {
    // Skip if we're in an input/textarea
    if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') {
      if (e.key === 'Escape') {
        isEditing = false;
        if (handlers.onEscape) handlers.onEscape()();
        focusCell(focusedRow, focusedCol);
      }
      return;
    }

    const rowCount = getRowCount();
    const colCount = getColCount();

    switch (e.key) {
      case 'ArrowUp':
        e.preventDefault();
        if (focusedRow > 0) {
          focusCell(focusedRow - 1, focusedCol);
        }
        break;

      case 'ArrowDown':
        e.preventDefault();
        if (focusedRow < rowCount - 1) {
          focusCell(focusedRow + 1, focusedCol);
        }
        break;

      case 'ArrowLeft':
        e.preventDefault();
        if (focusedCol > 0) {
          focusCell(focusedRow, focusedCol - 1);
        }
        break;

      case 'ArrowRight':
        e.preventDefault();
        if (focusedCol < colCount - 1) {
          focusCell(focusedRow, focusedCol + 1);
        }
        break;

      case 'Enter':
        e.preventDefault();
        if (!isEditing) {
          isEditing = true;
          if (handlers.onEdit) {
            const row = gridEl.querySelectorAll('tbody tr[data-row-key]')[focusedRow];
            const columnKey = gridEl.querySelectorAll('thead th[data-column-key]')[focusedCol]?.dataset.columnKey;
            handlers.onEdit({ rowIndex: focusedRow, columnKey })();
          }
        }
        break;

      case ' ':
        e.preventDefault();
        if (handlers.onSelect) {
          const row = gridEl.querySelectorAll('tbody tr[data-row-key]')[focusedRow];
          const rowKey = row?.dataset.rowKey;
          if (rowKey) {
            handlers.onSelect(rowKey)();
          }
        }
        break;

      case 'Escape':
        e.preventDefault();
        isEditing = false;
        if (handlers.onEscape) handlers.onEscape()();
        break;

      case 'Home':
        e.preventDefault();
        if (e.ctrlKey) {
          focusCell(0, 0);
        } else {
          focusCell(focusedRow, 0);
        }
        break;

      case 'End':
        e.preventDefault();
        if (e.ctrlKey) {
          focusCell(rowCount - 1, colCount - 1);
        } else {
          focusCell(focusedRow, colCount - 1);
        }
        break;

      case 'PageUp':
        e.preventDefault();
        focusCell(Math.max(0, focusedRow - 10), focusedCol);
        break;

      case 'PageDown':
        e.preventDefault();
        focusCell(Math.min(rowCount - 1, focusedRow + 10), focusedCol);
        break;
    }
  };

  // Make grid focusable
  gridEl.setAttribute('tabindex', '0');
  gridEl.addEventListener('keydown', handleKeyDown);

  // Initial focus
  if (getRowCount() > 0 && getColCount() > 0) {
    focusCell(0, 0);
  }

  return () => {
    gridEl.removeEventListener('keydown', handleKeyDown);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // inline editing
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Start inline editing for a cell
 * @param {HTMLElement} cellEl - The cell element
 * @param {string} currentValue - Current cell value
 * @param {function} onSave - Callback (newValue) => Effect Unit
 * @param {function} onCancel - Callback () => Effect Unit
 */
export const startCellEditImpl = (cellEl) => (currentValue) => (onSave) => (onCancel) => () => {
  // Create input
  const input = document.createElement('input');
  input.type = 'text';
  input.value = currentValue;
  input.className = 'w-full h-full px-2 py-1 border-2 border-primary rounded text-sm bg-background focus:outline-none';
  
  // Store original content
  const originalContent = cellEl.innerHTML;
  
  // Replace content with input
  cellEl.innerHTML = '';
  cellEl.appendChild(input);
  input.focus();
  input.select();

  const handleKeyDown = (e) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      cleanup();
      onSave(input.value)();
    } else if (e.key === 'Escape') {
      e.preventDefault();
      cleanup();
      onCancel()();
    }
  };

  const handleBlur = () => {
    cleanup();
    onSave(input.value)();
  };

  const cleanup = () => {
    input.removeEventListener('keydown', handleKeyDown);
    input.removeEventListener('blur', handleBlur);
    cellEl.innerHTML = originalContent;
  };

  input.addEventListener('keydown', handleKeyDown);
  input.addEventListener('blur', handleBlur);
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // sorting
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Initialize sort click handlers
 * @param {HTMLElement} gridEl - The grid container
 * @param {function} onSort - Callback (Array SortConfig) => Effect Unit
 * @returns {function} Cleanup function
 */
export const initSortHandlersImpl = (gridEl) => (currentSorts) => (onSort) => () => {
  const handleHeaderClick = (e) => {
    const th = e.target.closest('th[data-column-key]');
    if (!th) return;

    const columnKey = th.dataset.columnKey;
    const ariaSort = th.getAttribute('aria-sort');
    
    // Check if column is sortable
    if (ariaSort === null) return;

    const shiftKey = e.shiftKey;
    let newSorts = [...currentSorts];

    const existingIndex = newSorts.findIndex(s => s.column === columnKey);

    if (existingIndex >= 0) {
      const existing = newSorts[existingIndex];
      if (existing.direction === 'ascending') {
        newSorts[existingIndex] = { column: columnKey, direction: 'descending' };
      } else {
        // Remove sort
        newSorts.splice(existingIndex, 1);
      }
    } else {
      const newSort = { column: columnKey, direction: 'ascending' };
      if (shiftKey) {
        newSorts.push(newSort);
      } else {
        newSorts = [newSort];
      }
    }

    onSort(newSorts)();
  };

  gridEl.addEventListener('click', handleHeaderClick);

  return () => {
    gridEl.removeEventListener('click', handleHeaderClick);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // export
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Export data as CSV and trigger download
 * @param {string} csvContent - CSV string content
 * @param {string} filename - Filename for download
 */
export const downloadCsvImpl = (csvContent) => (filename) => () => {
  const blob = new Blob([csvContent], { type: 'text/csv;charset=utf-8;' });
  const link = document.createElement('a');
  const url = URL.createObjectURL(blob);
  
  link.setAttribute('href', url);
  link.setAttribute('download', filename);
  link.style.visibility = 'hidden';
  
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
  
  URL.revokeObjectURL(url);
};

/**
 * Export data as JSON and trigger download
 * @param {string} jsonContent - JSON string content
 * @param {string} filename - Filename for download
 */
export const downloadJsonImpl = (jsonContent) => (filename) => () => {
  const blob = new Blob([jsonContent], { type: 'application/json;charset=utf-8;' });
  const link = document.createElement('a');
  const url = URL.createObjectURL(blob);
  
  link.setAttribute('href', url);
  link.setAttribute('download', filename);
  link.style.visibility = 'hidden';
  
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
  
  URL.revokeObjectURL(url);
};

/**
 * Copy data to clipboard
 * @param {string} content - Content to copy
 * @returns {Promise<void>}
 */
export const copyToClipboardImpl = (content) => (onSuccess) => (onError) => () => {
  navigator.clipboard.writeText(content)
    .then(() => onSuccess()())
    .catch(err => onError(err)());
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                         // responsive helpers
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Initialize responsive column hiding based on container width
 * @param {HTMLElement} gridEl - The grid container
 * @param {Array} columnPriorities - Array of { key, priority } where lower = more important
 * @param {function} onColumnsChange - Callback (visibleColumnKeys) => Effect Unit
 * @returns {function} Cleanup function
 */
export const initResponsiveColumnsImpl = (gridEl) => (columnPriorities) => (onColumnsChange) => () => {
  const sortedColumns = [...columnPriorities].sort((a, b) => a.priority - b.priority);
  let resizeObserver = null;

  const updateVisibleColumns = () => {
    const containerWidth = gridEl.clientWidth;
    const minColumnWidth = 100; // Minimum width per column
    
    const maxColumns = Math.floor(containerWidth / minColumnWidth);
    const visibleKeys = sortedColumns
      .slice(0, maxColumns)
      .map(col => col.key);
    
    onColumnsChange(visibleKeys)();
  };

  if (typeof ResizeObserver !== 'undefined') {
    resizeObserver = new ResizeObserver(updateVisibleColumns);
    resizeObserver.observe(gridEl);
  }

  // Initial update
  updateVisibleColumns();

  return () => {
    if (resizeObserver) {
      resizeObserver.disconnect();
    }
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // fixed column scroll
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Synchronize scroll shadows for fixed columns
 * @param {HTMLElement} scrollContainer - The scrollable container
 * @returns {function} Cleanup function
 */
export const initFixedColumnScrollImpl = (scrollContainer) => () => {
  const updateScrollShadows = () => {
    const { scrollLeft, scrollWidth, clientWidth } = scrollContainer;
    
    const hasLeftScroll = scrollLeft > 0;
    const hasRightScroll = scrollLeft < scrollWidth - clientWidth;

    scrollContainer.setAttribute('data-scroll-left', hasLeftScroll ? 'true' : 'false');
    scrollContainer.setAttribute('data-scroll-right', hasRightScroll ? 'true' : 'false');
  };

  scrollContainer.addEventListener('scroll', updateScrollShadows, { passive: true });
  updateScrollShadows();

  return () => {
    scrollContainer.removeEventListener('scroll', updateScrollShadows);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // row expansion
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Animate row expansion/collapse
 * @param {HTMLElement} rowEl - The expandable row element
 * @param {boolean} expand - Whether to expand or collapse
 * @param {function} onComplete - Callback when animation completes
 */
export const animateRowExpansionImpl = (rowEl) => (expand) => (onComplete) => () => {
  const content = rowEl.querySelector('[data-expandable-content]');
  if (!content) {
    onComplete()();
    return;
  }

  if (expand) {
    content.style.height = '0';
    content.style.overflow = 'hidden';
    content.style.display = 'block';
    
    const targetHeight = content.scrollHeight;
    content.style.transition = 'height 200ms ease-out';
    
    requestAnimationFrame(() => {
      content.style.height = `${targetHeight}px`;
    });

    content.addEventListener('transitionend', function handler() {
      content.removeEventListener('transitionend', handler);
      content.style.height = '';
      content.style.overflow = '';
      onComplete()();
    }, { once: true });
  } else {
    content.style.height = `${content.scrollHeight}px`;
    content.style.overflow = 'hidden';
    content.style.transition = 'height 200ms ease-out';
    
    requestAnimationFrame(() => {
      content.style.height = '0';
    });

    content.addEventListener('transitionend', function handler() {
      content.removeEventListener('transitionend', handler);
      content.style.display = 'none';
      content.style.height = '';
      content.style.overflow = '';
      onComplete()();
    }, { once: true });
  }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // filter popover
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Position a filter popover relative to its trigger
 * @param {HTMLElement} trigger - The trigger element (filter icon in header)
 * @param {HTMLElement} popover - The popover element
 */
export const positionFilterPopoverImpl = (trigger) => (popover) => () => {
  const triggerRect = trigger.getBoundingClientRect();
  const popoverRect = popover.getBoundingClientRect();
  
  let left = triggerRect.left;
  let top = triggerRect.bottom + 4;

  // Ensure popover stays within viewport
  if (left + popoverRect.width > window.innerWidth) {
    left = window.innerWidth - popoverRect.width - 8;
  }
  
  if (top + popoverRect.height > window.innerHeight) {
    top = triggerRect.top - popoverRect.height - 4;
  }

  popover.style.position = 'fixed';
  popover.style.left = `${left}px`;
  popover.style.top = `${top}px`;
};
