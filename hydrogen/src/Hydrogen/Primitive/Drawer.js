// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // drawer
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // drawer manager
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Drawer state management
 */
const drawerState = new WeakMap();

/**
 * Previously focused element (for focus restoration)
 */
let previouslyFocused = null;

/**
 * Initialize a drawer with event listeners and behaviors
 * @param {Element} root - The drawer root element
 * @returns {Function} Cleanup function
 */
export const initDrawerImpl = (root) => () => {
  const overlay = root.querySelector('[data-drawer="overlay"]');
  const content = root.querySelector('[data-drawer="content"]');
  const closeBtn = root.querySelector('[data-drawer="close"]');

  if (!content) return () => {};

  const state = {
    isOpen: root.dataset.state === "open",
    closeOnEscape: root.dataset.closeOnEscape === "true",
    trapFocus: root.dataset.trapFocus === "true",
    scrollLock: root.dataset.scrollLock === "true",
    cleanupFns: [],
  };

  drawerState.set(root, state);

  // Open function
  const open = () => {
    state.isOpen = true;
    previouslyFocused = document.activeElement;

    root.classList.remove("invisible");
    root.dataset.state = "open";
    content.dataset.state = "open";

    // Apply scroll lock
    if (state.scrollLock) {
      document.body.style.overflow = "hidden";
    }

    // Update animation classes based on side
    updateAnimationClasses(content, root.dataset.side, true);

    // Update overlay
    if (overlay) {
      overlay.classList.remove("opacity-0", "pointer-events-none");
      overlay.classList.add("opacity-100");
    }

    // Focus first focusable element
    if (state.trapFocus) {
      requestAnimationFrame(() => {
        const focusable = content.querySelectorAll(
          'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
        );
        if (focusable.length > 0) {
          focusable[0].focus();
        }
      });
    }
  };

  // Close function
  const close = () => {
    state.isOpen = false;
    root.dataset.state = "closed";
    content.dataset.state = "closed";

    // Update animation classes
    updateAnimationClasses(content, root.dataset.side, false);

    // Update overlay
    if (overlay) {
      overlay.classList.remove("opacity-100");
      overlay.classList.add("opacity-0", "pointer-events-none");
    }

    // Release scroll lock
    if (state.scrollLock) {
      document.body.style.overflow = "";
    }

    // Restore focus
    if (previouslyFocused && typeof previouslyFocused.focus === "function") {
      previouslyFocused.focus();
      previouslyFocused = null;
    }

    // Hide after animation
    setTimeout(() => {
      if (!state.isOpen) {
        root.classList.add("invisible");
      }
    }, 300);
  };

  // Close on escape
  if (state.closeOnEscape) {
    const handleEscape = (e) => {
      if (state.isOpen && e.key === "Escape") {
        close();
      }
    };
    document.addEventListener("keydown", handleEscape);
    state.cleanupFns.push(() =>
      document.removeEventListener("keydown", handleEscape)
    );
  }

  // Close button click
  if (closeBtn) {
    const handleClose = () => close();
    closeBtn.addEventListener("click", handleClose);
    state.cleanupFns.push(() =>
      closeBtn.removeEventListener("click", handleClose)
    );
  }

  // Overlay click (handled via HTML event handler, but we need close function)
  if (overlay) {
    const handleOverlayClick = () => close();
    overlay.addEventListener("click", handleOverlayClick);
    state.cleanupFns.push(() =>
      overlay.removeEventListener("click", handleOverlayClick)
    );
  }

  // Focus trap
  if (state.trapFocus) {
    const handleTab = (e) => {
      if (!state.isOpen || e.key !== "Tab") return;

      const focusable = content.querySelectorAll(
        'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
      );
      if (focusable.length === 0) return;

      const first = focusable[0];
      const last = focusable[focusable.length - 1];

      if (e.shiftKey && document.activeElement === first) {
        e.preventDefault();
        last.focus();
      } else if (!e.shiftKey && document.activeElement === last) {
        e.preventDefault();
        first.focus();
      }
    };

    content.addEventListener("keydown", handleTab);
    state.cleanupFns.push(() =>
      content.removeEventListener("keydown", handleTab)
    );
  }

  // Expose API on element
  root._drawerAPI = { open, close };

  // Cleanup
  return () => {
    for (const fn of state.cleanupFns) {
      fn();
    }
    if (state.scrollLock && state.isOpen) {
      document.body.style.overflow = "";
    }
    drawerState.delete(root);
  };
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                          // animation helpers
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Update animation classes based on drawer side and open state
 * @param {Element} content - Drawer content element
 * @param {string} side - Drawer side (left, right, top, bottom)
 * @param {boolean} isOpen - Whether drawer is open
 */
function updateAnimationClasses(content, side, isOpen) {
  const openClasses = {
    left: "translate-x-0",
    right: "translate-x-0",
    top: "translate-y-0",
    bottom: "translate-y-0",
  };

  const closedClasses = {
    left: "-translate-x-full",
    right: "translate-x-full",
    top: "-translate-y-full",
    bottom: "translate-y-full",
  };

  // Remove all transform classes
  content.classList.remove(
    "translate-x-0",
    "translate-y-0",
    "-translate-x-full",
    "translate-x-full",
    "-translate-y-full",
    "translate-y-full"
  );

  // Add appropriate class
  if (isOpen) {
    content.classList.add(openClasses[side] || "translate-x-0");
  } else {
    content.classList.add(closedClasses[side] || "translate-x-full");
  }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                            // programmatic api
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Open a drawer programmatically
 * @param {Element} root - The drawer root element
 */
export const openDrawerImpl = (root) => () => {
  if (root._drawerAPI) {
    root._drawerAPI.open();
  }
};

/**
 * Close a drawer programmatically
 * @param {Element} root - The drawer root element
 */
export const closeDrawerImpl = (root) => () => {
  if (root._drawerAPI) {
    root._drawerAPI.close();
  }
};

/**
 * Toggle drawer programmatically
 * @param {Element} root - The drawer root element
 */
export const toggleDrawerImpl = (root) => () => {
  const state = drawerState.get(root);
  if (state) {
    if (state.isOpen) {
      closeDrawerImpl(root)();
    } else {
      openDrawerImpl(root)();
    }
  }
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                               // scroll lock
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Lock body scroll
 */
export const lockScrollImpl = () => {
  document.body.style.overflow = "hidden";
};

/**
 * Unlock body scroll
 */
export const unlockScrollImpl = () => {
  document.body.style.overflow = "";
};

/**
 * Check if body scroll is locked
 */
export const isScrollLockedImpl = () => {
  return document.body.style.overflow === "hidden";
};
