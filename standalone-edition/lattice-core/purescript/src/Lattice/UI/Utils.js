// Utils.js - Minimal FFI for DOM operations only
//
// This is the ONLY JavaScript in the UI layer.
// getElementById is necessary because the standard web-dom library
// returns Element, not HTMLElement, and we need HTMLElement for focus().

export const getElementByIdImpl = (id) => (doc) => () => doc.getElementById(id);
