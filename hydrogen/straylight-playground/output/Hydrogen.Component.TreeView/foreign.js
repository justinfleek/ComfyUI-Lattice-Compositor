// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // hydrogen // treeview
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// TreeView FFI for drag-drop, keyboard navigation, and virtualization

/**
 * Initialize drag and drop functionality for tree nodes
 * @param {Element} container - Tree view container element
 * @param {Object} callbacks - Event callbacks
 * @param {Object} options - Configuration options
 * @returns {Object} TreeView controller
 */
export const initDragDropImpl = (container) => (callbacks) => (options) => () => {
  let draggedNodeId = null;
  let dropTargetId = null;
  let dropPosition = null;

  const getNodeId = (element) => {
    const node = element.closest("[data-node-id]");
    return node ? node.getAttribute("data-node-id") : null;
  };

  const handleDragStart = (e) => {
    const nodeId = getNodeId(e.target);
    if (!nodeId) return;

    draggedNodeId = nodeId;
    e.dataTransfer.effectAllowed = "move";
    e.dataTransfer.setData("text/plain", nodeId);

    // Add dragging class
    e.target.closest("[data-node-id]").classList.add("dragging");

    callbacks.onDragStart(nodeId)();
  };

  const handleDragOver = (e) => {
    e.preventDefault();
    const nodeId = getNodeId(e.target);
    if (!nodeId || nodeId === draggedNodeId) return;

    // Calculate drop position based on mouse position
    const rect = e.target.getBoundingClientRect();
    const y = e.clientY - rect.top;
    const height = rect.height;

    if (y < height * 0.25) {
      dropPosition = "before";
    } else if (y > height * 0.75) {
      dropPosition = "after";
    } else {
      dropPosition = "inside";
    }

    // Update drop indicator classes
    const node = e.target.closest("[data-node-id]");
    if (node) {
      node.classList.remove("drop-before", "drop-after", "drop-inside");
      node.classList.add(`drop-${dropPosition}`);
    }

    dropTargetId = nodeId;
    callbacks.onDragOver(nodeId)();
  };

  const handleDragLeave = (e) => {
    const node = e.target.closest("[data-node-id]");
    if (node) {
      node.classList.remove("drop-before", "drop-after", "drop-inside");
    }
  };

  const handleDrop = (e) => {
    e.preventDefault();
    const nodeId = getNodeId(e.target);

    // Remove all drag classes
    container.querySelectorAll("[data-node-id]").forEach((node) => {
      node.classList.remove(
        "dragging",
        "drop-before",
        "drop-after",
        "drop-inside"
      );
    });

    if (nodeId && draggedNodeId && nodeId !== draggedNodeId) {
      callbacks.onDrop(draggedNodeId)(nodeId)(dropPosition || "inside")();
    }

    draggedNodeId = null;
    dropTargetId = null;
    dropPosition = null;
  };

  const handleDragEnd = (e) => {
    container.querySelectorAll("[data-node-id]").forEach((node) => {
      node.classList.remove(
        "dragging",
        "drop-before",
        "drop-after",
        "drop-inside"
      );
    });

    draggedNodeId = null;
    dropTargetId = null;
    dropPosition = null;
  };

  // Attach event listeners
  container.addEventListener("dragstart", handleDragStart);
  container.addEventListener("dragover", handleDragOver);
  container.addEventListener("dragleave", handleDragLeave);
  container.addEventListener("drop", handleDrop);
  container.addEventListener("dragend", handleDragEnd);

  // Make nodes draggable
  container.querySelectorAll("[data-node-id]").forEach((node) => {
    node.setAttribute("draggable", "true");
  });

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
 * Destroy tree view and cleanup event listeners
 * @param {Object} treeView - TreeView controller
 */
export const destroyTreeViewImpl = (treeView) => () => {
  if (treeView && treeView.destroy) {
    treeView.destroy();
  }
};

/**
 * Initialize keyboard navigation
 * @param {Element} container - Tree view container
 * @param {Object} callbacks - Navigation callbacks
 * @returns {Object} Keyboard navigation controller
 */
export const initKeyboardNavImpl = (container) => (callbacks) => () => {
  let focusedNodeId = null;

  const getVisibleNodes = () => {
    return Array.from(container.querySelectorAll('[role="treeitem"]'));
  };

  const getFocusedIndex = (nodes) => {
    return nodes.findIndex(
      (node) =>
        node.closest("[data-node-id]")?.getAttribute("data-node-id") ===
        focusedNodeId
    );
  };

  const focusNode = (node) => {
    if (!node) return;
    const nodeId = node.closest("[data-node-id]")?.getAttribute("data-node-id");
    if (nodeId) {
      focusedNodeId = nodeId;
      node.focus();
      callbacks.onNavigate(nodeId)();
    }
  };

  const handleKeyDown = (e) => {
    const nodes = getVisibleNodes();
    const currentIndex = getFocusedIndex(nodes);

    switch (e.key) {
      case "ArrowDown":
        e.preventDefault();
        if (currentIndex < nodes.length - 1) {
          focusNode(nodes[currentIndex + 1]);
        }
        break;

      case "ArrowUp":
        e.preventDefault();
        if (currentIndex > 0) {
          focusNode(nodes[currentIndex - 1]);
        }
        break;

      case "ArrowRight":
        e.preventDefault();
        if (focusedNodeId) {
          callbacks.onToggle(focusedNodeId)();
        }
        break;

      case "ArrowLeft":
        e.preventDefault();
        if (focusedNodeId) {
          callbacks.onToggle(focusedNodeId)();
        }
        break;

      case "Enter":
      case " ":
        e.preventDefault();
        if (focusedNodeId) {
          callbacks.onSelect(focusedNodeId)();
        }
        break;

      case "Home":
        e.preventDefault();
        if (nodes.length > 0) {
          focusNode(nodes[0]);
        }
        break;

      case "End":
        e.preventDefault();
        if (nodes.length > 0) {
          focusNode(nodes[nodes.length - 1]);
        }
        break;
    }
  };

  container.addEventListener("keydown", handleKeyDown);

  // Focus first node initially
  const nodes = getVisibleNodes();
  if (nodes.length > 0) {
    const firstNodeId = nodes[0]
      .closest("[data-node-id]")
      ?.getAttribute("data-node-id");
    if (firstNodeId) {
      focusedNodeId = firstNodeId;
    }
  }

  return {
    container,
    destroy: () => {
      container.removeEventListener("keydown", handleKeyDown);
    },
  };
};

/**
 * Initialize virtual scrolling for large trees
 * @param {Element} container - Tree view container
 * @param {Object} callbacks - Render callbacks
 * @param {Object} options - Virtualization options
 * @returns {Object} Virtual scroll controller
 */
export const initVirtualScrollImpl =
  (container) => (callbacks) => (options) => () => {
    const { itemHeight, totalItems, renderRange } = callbacks;
    const { overscan = 5 } = options;

    let scrollTop = 0;
    let containerHeight = 0;

    const updateVisibleRange = () => {
      const startIndex = Math.max(
        0,
        Math.floor(scrollTop / itemHeight) - overscan
      );
      const endIndex = Math.min(
        totalItems - 1,
        Math.ceil((scrollTop + containerHeight) / itemHeight) + overscan
      );

      renderRange(startIndex)(endIndex)();
    };

    const handleScroll = (e) => {
      scrollTop = e.target.scrollTop;
      requestAnimationFrame(updateVisibleRange);
    };

    const handleResize = () => {
      containerHeight = container.clientHeight;
      updateVisibleRange();
    };

    // Set up container styles
    container.style.overflow = "auto";
    container.style.position = "relative";

    // Create spacer element
    const spacer = document.createElement("div");
    spacer.style.height = `${totalItems * itemHeight}px`;
    spacer.style.position = "absolute";
    spacer.style.top = "0";
    spacer.style.left = "0";
    spacer.style.right = "0";
    spacer.style.pointerEvents = "none";
    container.appendChild(spacer);

    // Attach listeners
    container.addEventListener("scroll", handleScroll);
    window.addEventListener("resize", handleResize);

    // Initial calculation
    containerHeight = container.clientHeight;
    updateVisibleRange();

    return {
      container,
      spacer,
      refresh: () => {
        spacer.style.height = `${totalItems * itemHeight}px`;
        updateVisibleRange();
      },
      destroy: () => {
        container.removeEventListener("scroll", handleScroll);
        window.removeEventListener("resize", handleResize);
        if (spacer.parentNode) {
          spacer.parentNode.removeChild(spacer);
        }
      },
    };
  };

/**
 * Unsafe placeholder for TreeViewElement
 * Used for initialization before FFI binding
 */
export const unsafeTreeViewElement = {
  destroy: () => {},
};
