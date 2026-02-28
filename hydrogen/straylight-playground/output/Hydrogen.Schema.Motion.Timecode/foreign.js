// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                  // hydrogen // schema // motion // timecode
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI for Timecode.purs

export const unsafeParseInt = function(s) {
  return parseInt(s, 10);
};

export const isNaN_ = function(n) {
  return Number.isNaN(n);
};

// Traverse implementation for arrays with Maybe
export const traverseImpl = function(f) {
  return function(arr) {
    var result, i, maybeB;
    result = [];
    for (i = 0; i < arr.length; i++) {
      maybeB = f(arr[i]);
      if (maybeB.tag === "Nothing") {
        return { tag: "Nothing" };
      }
      result.push(maybeB.value0);
    }
    return { tag: "Just", value0: result };
  };
};
