// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                      // hydrogen // component // motion // property // angledial
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI for AngleDial.purs

// | Extract clientX from a mouse event
export const getClientX = function(event) {
  return event.clientX;
};

// | Extract clientY from a mouse event
export const getClientY = function(event) {
  return event.clientY;
};

// | Parse a string to a Number, returning Nothing on failure
// | Takes Just and Nothing constructors from PureScript
export const parseNumberImpl = function(just) {
  return function(nothing) {
    return function(str) {
      var result = parseFloat(str);
      if (isNaN(result) || !isFinite(result)) {
        return nothing;
      }
      return just(result);
    };
  };
};

// | Get element center X position from the event target
export const getElementCenterX = function(event) {
  var rect;
  if (event.currentTarget && event.currentTarget.getBoundingClientRect) {
    rect = event.currentTarget.getBoundingClientRect();
    return rect.left + rect.width / 2;
  }
  return event.clientX;
};

// | Get element center Y position from the event target
export const getElementCenterY = function(event) {
  var rect;
  if (event.currentTarget && event.currentTarget.getBoundingClientRect) {
    rect = event.currentTarget.getBoundingClientRect();
    return rect.top + rect.height / 2;
  }
  return event.clientY;
};
