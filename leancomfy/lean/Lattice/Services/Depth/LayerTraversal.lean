/-
  Lattice.Services.Depth.LayerTraversal - Layer Depth Extraction

  Pure functions for extracting depth information from layers:
  - Layer Z position extraction (static and animated)
  - Layer opacity extraction (static and animated)
  - Screen bounds calculation with transform
  - Layer sorting by depth

  Source: ui/src/services/export/depthRenderer.ts (lines 160-314)
-/

namespace Lattice.Services.Depth.LayerTraversal

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 3D position with x, y, z coordinates. -/
structure Position3D where
  x : Float
  y : Float
  z : Float
  deriving Repr

/-- 2D scale factors. -/
structure Scale2D where
  scaleX : Float
  scaleY : Float
  deriving Repr

/-- 2D anchor point (normalized 0-1 or pixel coordinates). -/
structure AnchorPoint where
  anchorX : Float
  anchorY : Float
  deriving Repr

/-- Layer transform data. -/
structure LayerTransform where
  position : Position3D
  scale : Scale2D
  anchor : AnchorPoint
  deriving Repr

/-- Screen bounds rectangle. -/
structure ScreenBounds where
  x : Float
  y : Float
  width : Float
  height : Float
  deriving Repr

/-- Keyframe for interpolation. -/
structure Keyframe where
  frame : Nat
  value : Float
  deriving Repr

/-- Multi-dimensional keyframe (for position, scale, etc.). -/
structure KeyframeMulti where
  frame : Nat
  values : Array Float
  deriving Repr

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default position at origin. -/
def defaultPosition : Position3D :=
  { x := 0.0, y := 0.0, z := 0.0 }

/-- Default scale (100%). -/
def defaultScale : Scale2D :=
  { scaleX := 1.0, scaleY := 1.0 }

/-- Default anchor at center (0.5, 0.5). -/
def defaultAnchor : AnchorPoint :=
  { anchorX := 0.5, anchorY := 0.5 }

/-- Default transform. -/
def defaultTransform : LayerTransform :=
  { position := defaultPosition
  , scale := defaultScale
  , anchor := defaultAnchor
  }

--------------------------------------------------------------------------------
-- Layer Depth Extraction
--------------------------------------------------------------------------------

/-- Extract Z value from static position. -/
def getStaticDepth (pos : Position3D) : Float :=
  pos.z

/-- Interpolate between two keyframe values.
    t should be in [0, 1] range. -/
def lerpValue (prev next t : Float) : Float :=
  prev + (next - prev) * t

/-- Find surrounding keyframes for a given frame.
    Returns (prevKeyframe, nextKeyframe, interpolationFactor). -/
def findSurroundingKeyframes (keyframes : Array KeyframeMulti) (frame : Nat)
    : Option (KeyframeMulti × KeyframeMulti × Float) :=
  if keyframes.size == 0 then none
  else
    let sorted := keyframes.qsort (fun a b => a.frame < b.frame)
    let first := sorted[0]!
    let last := sorted[sorted.size - 1]!

    -- Find prev and next
    let prev := sorted.foldl (fun acc kf =>
      if kf.frame <= frame then kf else acc) first
    let next := sorted.foldl (fun acc kf =>
      if kf.frame >= frame && acc.frame < frame then kf else acc) last

    if prev.frame == next.frame then
      some (prev, next, 0.0)
    else
      let t := (frame.toFloat - prev.frame.toFloat) /
               (next.frame.toFloat - prev.frame.toFloat)
      some (prev, next, t)

/-- Interpolate Z value from keyframes at given frame.
    Z is typically at index 2 in position keyframes. -/
def interpolateZFromKeyframes (keyframes : Array KeyframeMulti) (frame : Nat) : Float :=
  match findSurroundingKeyframes keyframes frame with
  | none => 0.0
  | some (prev, next, t) =>
    let prevZ := if prev.values.size > 2 then prev.values[2]! else 0.0
    let nextZ := if next.values.size > 2 then next.values[2]! else 0.0
    lerpValue prevZ nextZ t

/-- Get layer depth at frame.
    Checks for animated position first, falls back to static. -/
def getLayerDepth (transform : LayerTransform)
                  (positionKeyframes : Option (Array KeyframeMulti))
                  (frame : Nat) : Float :=
  match positionKeyframes with
  | some kfs =>
    if kfs.size > 0 then interpolateZFromKeyframes kfs frame
    else transform.position.z
  | none => transform.position.z

--------------------------------------------------------------------------------
-- Layer Opacity Extraction
--------------------------------------------------------------------------------

/-- Default opacity (100%). -/
def defaultOpacity : Float := 1.0

/-- Convert percentage opacity (0-100) to normalized (0-1). -/
def normalizeOpacity (percentOpacity : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 (percentOpacity / 100.0))

/-- Interpolate opacity from keyframes at given frame. -/
def interpolateOpacityFromKeyframes (keyframes : Array Keyframe) (frame : Nat) : Float :=
  if keyframes.size == 0 then defaultOpacity
  else
    let sorted := keyframes.qsort (fun a b => a.frame < b.frame)
    let first := sorted[0]!
    let last := sorted[sorted.size - 1]!

    let prev := sorted.foldl (fun acc kf =>
      if kf.frame <= frame then kf else acc) first
    let next := sorted.foldl (fun acc kf =>
      if kf.frame >= frame && acc.frame < frame then kf else acc) last

    if prev.frame == next.frame then
      normalizeOpacity prev.value
    else
      let t := (frame.toFloat - prev.frame.toFloat) /
               (next.frame.toFloat - prev.frame.toFloat)
      let interpolated := lerpValue prev.value next.value t
      normalizeOpacity interpolated

/-- Get layer opacity at frame.
    Returns value in [0, 1] range. -/
def getLayerOpacity (staticOpacity : Float)
                    (opacityKeyframes : Option (Array Keyframe))
                    (frame : Nat) : Float :=
  match opacityKeyframes with
  | some kfs =>
    if kfs.size > 0 then interpolateOpacityFromKeyframes kfs frame
    else normalizeOpacity staticOpacity
  | none => normalizeOpacity staticOpacity

--------------------------------------------------------------------------------
-- Screen Bounds Calculation
--------------------------------------------------------------------------------

/-- Calculate scaled dimensions. -/
def calculateScaledDimensions (layerWidth layerHeight : Float)
                               (scale : Scale2D) : Float × Float :=
  (layerWidth * scale.scaleX, layerHeight * scale.scaleY)

/-- Convert layer position to screen coordinates.
    Compositor origin is center of screen. -/
def toScreenCoordinates (position : Position3D)
                        (finalWidth finalHeight : Float)
                        (anchor : AnchorPoint)
                        (screenWidth screenHeight : Float) : Float × Float :=
  let screenX := position.x - finalWidth * anchor.anchorX + screenWidth / 2.0
  let screenY := position.y - finalHeight * anchor.anchorY + screenHeight / 2.0
  (screenX, screenY)

/-- Clip bounds to screen dimensions.
    Returns None if completely outside screen. -/
def clipBoundsToScreen (screenX screenY finalWidth finalHeight : Float)
                       (screenWidth screenHeight : Float) : Option ScreenBounds :=
  let clippedX := Float.max 0.0 (Float.min screenWidth screenX)
  let clippedY := Float.max 0.0 (Float.min screenHeight screenY)
  let clippedWidth := Float.max 0.0
    (Float.min (screenWidth - clippedX) (finalWidth - (clippedX - screenX)))
  let clippedHeight := Float.max 0.0
    (Float.min (screenHeight - clippedY) (finalHeight - (clippedY - screenY)))

  -- Geometric constraint: rectangle must have positive area
  if clippedWidth <= 0.0 || clippedHeight <= 0.0 then none
  else some { x := clippedX, y := clippedY, width := clippedWidth, height := clippedHeight }

/-- Calculate normalized anchor from pixel anchor point.
    Adds 0.5 to center the anchor. -/
def calculateNormalizedAnchor (pixelAnchor : AnchorPoint)
                               (layerWidth layerHeight : Float) : AnchorPoint :=
  { anchorX := pixelAnchor.anchorX / layerWidth + 0.5
  , anchorY := pixelAnchor.anchorY / layerHeight + 0.5
  }

/-- Get layer screen bounds.
    Calculates final position and size after transform. -/
def getLayerScreenBounds (transform : LayerTransform)
                         (layerWidth layerHeight : Float)
                         (screenWidth screenHeight : Float) : Option ScreenBounds :=
  let (finalWidth, finalHeight) := calculateScaledDimensions layerWidth layerHeight transform.scale
  let normalizedAnchor := calculateNormalizedAnchor transform.anchor layerWidth layerHeight
  let (screenX, screenY) := toScreenCoordinates transform.position
                                                 finalWidth finalHeight
                                                 normalizedAnchor
                                                 screenWidth screenHeight
  clipBoundsToScreen screenX screenY finalWidth finalHeight screenWidth screenHeight

--------------------------------------------------------------------------------
-- Layer Sorting
--------------------------------------------------------------------------------

/-- Layer with extracted depth for sorting. -/
structure LayerWithDepth (α : Type) where
  layer : α
  depth : Float
  deriving Repr

/-- Sort layers by depth (front to back from camera).
    Lower Z values are closer to camera. -/
def sortLayersByDepth {α : Type} (layers : Array (LayerWithDepth α))
    : Array (LayerWithDepth α) :=
  layers.qsort (fun a b => a.depth < b.depth)

/-- Filter out invisible layers (opacity below threshold). -/
def filterVisibleLayers {α : Type} (layers : Array (LayerWithDepth α × Float))
    (opacityThreshold : Float := 0.01) : Array (LayerWithDepth α) :=
  layers.filterMap fun (lwd, opacity) =>
    if opacity >= opacityThreshold then some lwd else none

end Lattice.Services.Depth.LayerTraversal
