// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                       // hydrogen // component // motion // curve // curvehandle
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// FFI for CurveHandle.purs

// | Extract clientX from a mouse event
export const getClientX = function(event) {
  return event.clientX;
};

// | Extract clientY from a mouse event
export const getClientY = function(event) {
  return event.clientY;
};
