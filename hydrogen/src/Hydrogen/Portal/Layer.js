// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                         // hydrogen // portal
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Portal root management

export const createRootImpl = () => {
  const root = document.createElement("div");
  root.id = "hydrogen-portal-root";
  root.setAttribute("data-hydrogen-portal", "true");
  root.style.cssText = "position: fixed; top: 0; left: 0; z-index: 1000; pointer-events: none;";
  document.body.appendChild(root);
  return root;
};

export const createRootInImpl = (parent) => () => {
  const root = document.createElement("div");
  root.setAttribute("data-hydrogen-portal", "true");
  root.style.cssText = "position: relative; z-index: 0;";
  parent.appendChild(root);
  return root;
};

export const destroyRootImpl = (element) => () => {
  if (element.parentNode) {
    element.parentNode.removeChild(element);
  }
};

export const traverseImpl = (f) => (arr) => () => {
  return arr.map((item) => f(item)());
};

// Layer management

export const createLayerImpl =
  (root) => (id) => (zIndex) => (className) => (ariaLabel) => (trapFocus) => () => {
    const layer = document.createElement("div");
    layer.id = id;
    layer.setAttribute("data-portal-layer", "true");
    layer.style.cssText = `position: fixed; top: 0; left: 0; right: 0; bottom: 0; z-index: ${zIndex}; pointer-events: none;`;

    if (className && className.value0) {
      layer.className = className.value0;
    }

    if (ariaLabel && ariaLabel.value0) {
      layer.setAttribute("aria-label", ariaLabel.value0);
    }

    if (trapFocus) {
      layer.setAttribute("data-trap-focus", "true");
    }

    root.appendChild(layer);
    return layer;
  };

export const destroyLayerImpl = (element) => () => {
  if (element.parentNode) {
    element.parentNode.removeChild(element);
  }
};

// Mounting

export const mountImpl = (layer) => (node) => () => {
  // Wrap in a container that enables pointer events
  const container = document.createElement("div");
  container.style.pointerEvents = "auto";
  container.appendChild(node);
  layer.appendChild(container);
};

export const unmountNodeImpl = (layer) => (node) => () => {
  // Find the wrapper container
  const parent = node.parentNode;
  if (parent && parent.parentNode === layer) {
    layer.removeChild(parent);
  } else if (node.parentNode === layer) {
    layer.removeChild(node);
  }
};

export const unmountAllImpl = (element) => () => {
  while (element.firstChild) {
    element.removeChild(element.firstChild);
  }
};

// Stacking context

export const sortByImpl = (f) => (arr) => {
  return [...arr].sort((a, b) => {
    const fa = f(a);
    const fb = f(b);
    if (fa < fb) return -1;
    if (fa > fb) return 1;
    return 0;
  });
};

export const lastImpl = (arr) => {
  if (arr.length === 0) return null; // Nothing
  return arr[arr.length - 1]; // Just value
};

export const bringToFrontImpl = (element) => () => {
  // Get all sibling layers and find max z-index
  const parent = element.parentNode;
  if (!parent) return;

  const siblings = parent.querySelectorAll("[data-portal-layer]");
  let maxZ = 0;
  siblings.forEach((el) => {
    const z = parseInt(el.style.zIndex || "0", 10);
    if (z > maxZ) maxZ = z;
  });

  element.style.zIndex = String(maxZ + 1);
};

export const sendToBackImpl = (element) => (originalZ) => () => {
  element.style.zIndex = String(originalZ);
};

export const getZIndexImpl = (element) => () => {
  return parseInt(element.style.zIndex || "0", 10);
};

// Focus management

let previouslyFocused = null;
let focusTrapCleanup = null;

export const trapFocusImpl = (element) => () => {
  // Save currently focused element
  previouslyFocused = document.activeElement;

  // Find all focusable elements
  const getFocusableElements = () => {
    return element.querySelectorAll(
      'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
    );
  };

  const handleKeyDown = (e) => {
    if (e.key !== "Tab") return;

    const focusable = getFocusableElements();
    if (focusable.length === 0) return;

    const first = focusable[0];
    const last = focusable[focusable.length - 1];

    if (e.shiftKey) {
      if (document.activeElement === first) {
        e.preventDefault();
        last.focus();
      }
    } else {
      if (document.activeElement === last) {
        e.preventDefault();
        first.focus();
      }
    }
  };

  element.addEventListener("keydown", handleKeyDown);

  // Focus first element
  const focusable = getFocusableElements();
  if (focusable.length > 0) {
    focusable[0].focus();
  }

  // Return cleanup function
  focusTrapCleanup = () => {
    element.removeEventListener("keydown", handleKeyDown);
  };

  return focusTrapCleanup;
};

export const releaseFocusImpl = (element) => () => {
  if (focusTrapCleanup) {
    focusTrapCleanup();
    focusTrapCleanup = null;
  }
};

export const restoreFocusImpl = () => {
  if (previouslyFocused && typeof previouslyFocused.focus === "function") {
    previouslyFocused.focus();
    previouslyFocused = null;
  }
};
