// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                    // hydrogen // contextmenu
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // context menu manager
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Context menu state management
 */
const contextMenuState = new WeakMap();

/**
 * Initialize a context menu with event listeners
 * @param {Element} root - The context menu root element
 * @returns {Function} Cleanup function
 */
export const initContextMenuImpl = (root) => () => {
  const trigger = root.querySelector('[data-context-menu="trigger"]');
  const content = root.querySelector('[data-context-menu="content"]');

  if (!trigger || !content) return () => {};

  const state = {
    isOpen: false,
    position: { x: 0, y: 0 },
    focusedIndex: -1,
    cleanupFns: [],
  };

  contextMenuState.set(root, state);

  // Get all focusable menu items
  const getMenuItems = () => {
    return content.querySelectorAll(
      '[data-context-menu="item"]:not([data-disabled="true"])'
    );
  };

  // Open context menu at position
  const open = (x, y) => {
    state.isOpen = true;
    state.position = { x, y };
    state.focusedIndex = -1;

    root.dataset.state = "open";
    content.dataset.state = "open";
    content.classList.remove("hidden");

    // Position the menu
    content.style.left = `${x}px`;
    content.style.top = `${y}px`;

    // Adjust position if menu would overflow viewport
    requestAnimationFrame(() => {
      const rect = content.getBoundingClientRect();
      const viewportWidth = window.innerWidth;
      const viewportHeight = window.innerHeight;

      if (rect.right > viewportWidth) {
        content.style.left = `${x - rect.width}px`;
      }
      if (rect.bottom > viewportHeight) {
        content.style.top = `${y - rect.height}px`;
      }
    });
  };

  // Close context menu
  const close = () => {
    state.isOpen = false;
    root.dataset.state = "closed";
    content.dataset.state = "closed";
    content.classList.add("hidden");
    state.focusedIndex = -1;
  };

  // Focus menu item by index
  const focusItem = (index) => {
    const items = getMenuItems();
    if (items.length === 0) return;

    // Wrap around
    if (index < 0) index = items.length - 1;
    if (index >= items.length) index = 0;

    state.focusedIndex = index;
    items[index].focus();
  };

  // Handle right-click on trigger
  const handleContextMenu = (e) => {
    e.preventDefault();
    open(e.clientX, e.clientY);
  };

  trigger.addEventListener("contextmenu", handleContextMenu);
  state.cleanupFns.push(() =>
    trigger.removeEventListener("contextmenu", handleContextMenu)
  );

  // Close on click outside
  const handleClickOutside = (e) => {
    if (state.isOpen && !content.contains(e.target)) {
      close();
    }
  };

  document.addEventListener("click", handleClickOutside);
  state.cleanupFns.push(() =>
    document.removeEventListener("click", handleClickOutside)
  );

  // Close on escape and keyboard navigation
  const handleKeyDown = (e) => {
    if (!state.isOpen) return;

    switch (e.key) {
      case "Escape":
        e.preventDefault();
        close();
        break;

      case "ArrowDown":
        e.preventDefault();
        focusItem(state.focusedIndex + 1);
        break;

      case "ArrowUp":
        e.preventDefault();
        focusItem(state.focusedIndex - 1);
        break;

      case "Enter":
      case " ":
        if (state.focusedIndex >= 0) {
          e.preventDefault();
          const items = getMenuItems();
          items[state.focusedIndex].click();
          close();
        }
        break;

      case "ArrowRight": {
        // Open submenu if focused item has one
        const items = getMenuItems();
        if (state.focusedIndex >= 0) {
          const item = items[state.focusedIndex];
          const parent = item.closest('[data-context-menu="sub"]');
          if (parent) {
            const subContent = parent.querySelector(
              '[data-context-menu="sub-content"]'
            );
            if (subContent) {
              subContent.classList.remove("opacity-0", "invisible");
              subContent.classList.add("opacity-100", "visible");
              const subItems = subContent.querySelectorAll(
                '[data-context-menu="item"]'
              );
              if (subItems.length > 0) {
                subItems[0].focus();
              }
            }
          }
        }
        break;
      }

      case "ArrowLeft": {
        // Close submenu
        const activeElement = document.activeElement;
        const subContent = activeElement?.closest(
          '[data-context-menu="sub-content"]'
        );
        if (subContent) {
          subContent.classList.remove("opacity-100", "visible");
          subContent.classList.add("opacity-0", "invisible");
          const subTrigger = subContent
            .closest('[data-context-menu="sub"]')
            ?.querySelector('[data-context-menu="sub-trigger"]');
          if (subTrigger) {
            subTrigger.focus();
          }
        }
        break;
      }
    }
  };

  document.addEventListener("keydown", handleKeyDown);
  state.cleanupFns.push(() =>
    document.removeEventListener("keydown", handleKeyDown)
  );

  // Handle menu item clicks
  const handleItemClick = () => {
    close();
  };

  const items = content.querySelectorAll('[data-context-menu="item"]');
  for (const item of items) {
    item.addEventListener("click", handleItemClick);
    state.cleanupFns.push(() =>
      item.removeEventListener("click", handleItemClick)
    );
  }

  // Cleanup
  return () => {
    for (const fn of state.cleanupFns) {
      fn();
    }
    contextMenuState.delete(root);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // programmatic api
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Open context menu at specific position
 * @param {Element} root - The context menu root element
 * @param {number} x - X coordinate
 * @param {number} y - Y coordinate
 */
export const openContextMenuImpl = (root) => (x) => (y) => () => {
  const content = root.querySelector('[data-context-menu="content"]');
  if (content) {
    root.dataset.state = "open";
    content.dataset.state = "open";
    content.classList.remove("hidden");
    content.style.left = `${x}px`;
    content.style.top = `${y}px`;
  }
};

/**
 * Close context menu
 * @param {Element} root - The context menu root element
 */
export const closeContextMenuImpl = (root) => () => {
  const content = root.querySelector('[data-context-menu="content"]');
  if (content) {
    root.dataset.state = "closed";
    content.dataset.state = "closed";
    content.classList.add("hidden");
  }
};

/**
 * Get current position of context menu
 * @param {Element} root - The context menu root element
 * @returns {{ x: number, y: number }}
 */
export const getPositionImpl = (root) => () => {
  const state = contextMenuState.get(root);
  return state ? state.position : { x: 0, y: 0 };
};
