// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                  // hydrogen // component // motion // property // scrubablenumber
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI for ScrubableNumber.purs

// | Extract clientX from a mouse event
export const getClientX = function(event) {
  return event.clientX;
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
