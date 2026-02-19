/-
  Lattice.Composables.ViewportControls - Viewport zoom math and bounds

  Ported from: ui/src/composables/useViewportControls.ts
  Haskell: src/lattice/Composables/ViewportControls.hs

  Pure zoom/fit math only; no engine refs or DOM.
  Defs only; no NumericSafety import to avoid dependency on that lib's build.
-/

import Batteries.Lean.Float

namespace Lattice.Composables.ViewportControls

/-! ## Helpers (local, no Lattice.Utils dependency) -/

def isFinite (x : Float) : Bool :=
  !x.isNaN && !x.isInf

def clamp (value min max : Float) : Float :=
  if value < min then min
  else if value > max then max
  else value

/-! ## Zoom constants (match Haskell) -/

def minZoom : Float := 0.1
def maxZoom : Float := 10.0
def zoomStepIn : Float := 1.2
def zoomStepOut : Float := 0.8

/-! ## Zoom operations -/

/-- Clamp zoom to [minZoom, maxZoom] -/
def clampZoom (z : Float) : Float :=
  clamp z minZoom maxZoom

/-- Next zoom when zooming in (clamped) -/
def zoomInValue (z : Float) : Float :=
  min maxZoom (z * zoomStepIn)

/-- Next zoom when zooming out (clamped) -/
def zoomOutValue (z : Float) : Float :=
  max minZoom (z * zoomStepOut)

/-! ## Fit zoom -/

/-- Fit zoom with padding; returns 0 if any dimension ≤ 0 (invalid) -/
def fitZoomWithPadding (compW compH viewW viewH padding : Float) : Float :=
  if compW ≤ 0 || compH ≤ 0 || viewW ≤ 0 || viewH ≤ 0 then 0.0
  else
    let zw := (viewW * padding) / compW
    let zh := (viewH * padding) / compH
    if isFinite zw && isFinite zh then min zw zh else 0.0

/-! ## Screen-to-scene (viewport transform: scaleX, skewX, skewY, scaleY, panX, panY) -/

/-- Result of screen-to-scene conversion -/
structure ScreenToSceneResult where
  x : Float
  y : Float
  deriving Repr

/-- Convert screen (pixel) to scene using 6-element transform; returns none if invalid scale -/
def screenToScene (screenX screenY : Float) (vpt : List Float) : Option ScreenToSceneResult :=
  match vpt with
  | [scaleX, _, _, scaleY, panX, panY] =>
    if isFinite scaleX && scaleX != 0 && isFinite scaleY && scaleY != 0 then
      let px := if isFinite panX then panX else 0.0
      let py := if isFinite panY then panY else 0.0
      some ⟨(screenX - px) / scaleX, (screenY - py) / scaleY⟩
    else none
  | _ => none

end Lattice.Composables.ViewportControls
