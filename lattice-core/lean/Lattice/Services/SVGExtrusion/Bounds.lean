/-
  Lattice.Services.SVGExtrusion.Bounds - Bounding Box Mathematics

  Pure mathematical functions for bounding box calculations:
  - Min/Max from point sets
  - Center calculation
  - Width/Height computation
  - Bounds merging

  Source: ui/src/services/svgExtrusion.ts (lines 446-486)
-/

namespace Lattice.Services.SVGExtrusion.Bounds

--------------------------------------------------------------------------------
-- Bounding Box Type
--------------------------------------------------------------------------------

/-- 2D bounding box -/
structure BoundingBox2D where
  minX : Float
  minY : Float
  maxX : Float
  maxY : Float
deriving Repr, Inhabited

/-- Extended bounding box with derived properties -/
structure BoundsWithMetrics where
  minX : Float
  minY : Float
  maxX : Float
  maxY : Float
  width : Float
  height : Float
  centerX : Float
  centerY : Float
deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Empty bounds (for initial accumulator) -/
def emptyBounds : BoundingBox2D :=
  { minX := Float.ofScientific 10 false 38  -- Infinity approximation
  , minY := Float.ofScientific 10 false 38
  , maxX := Float.ofScientific (-10) false 38  -- -Infinity approximation
  , maxY := Float.ofScientific (-10) false 38 }

--------------------------------------------------------------------------------
-- Point Accumulation
--------------------------------------------------------------------------------

/-- Update bounds to include a point.

    @param bounds Current bounding box
    @param x Point X coordinate
    @param y Point Y coordinate
    @return Updated bounds -/
def includePoint (bounds : BoundingBox2D) (x y : Float) : BoundingBox2D :=
  { minX := Float.min bounds.minX x
  , minY := Float.min bounds.minY y
  , maxX := Float.max bounds.maxX x
  , maxY := Float.max bounds.maxY y }

/-- Calculate bounds from an array of (x, y) points.

    @param points Array of coordinate pairs
    @return Bounding box containing all points -/
def fromPoints (points : Array (Float × Float)) : BoundingBox2D :=
  points.foldl (fun acc (x, y) => includePoint acc x y) emptyBounds

--------------------------------------------------------------------------------
-- Bounds Metrics
--------------------------------------------------------------------------------

/-- Calculate width of bounding box.

    @param bounds The bounding box
    @return Width (maxX - minX) -/
def width (bounds : BoundingBox2D) : Float :=
  bounds.maxX - bounds.minX

/-- Calculate height of bounding box.

    @param bounds The bounding box
    @return Height (maxY - minY) -/
def height (bounds : BoundingBox2D) : Float :=
  bounds.maxY - bounds.minY

/-- Calculate center X coordinate.

    @param bounds The bounding box
    @return Center X (minX + width/2) -/
def centerX (bounds : BoundingBox2D) : Float :=
  bounds.minX + width bounds / 2.0

/-- Calculate center Y coordinate.

    @param bounds The bounding box
    @return Center Y (minY + height/2) -/
def centerY (bounds : BoundingBox2D) : Float :=
  bounds.minY + height bounds / 2.0

/-- Convert basic bounds to bounds with all metrics.

    @param bounds Basic bounding box
    @return Bounds with width, height, center computed -/
def withMetrics (bounds : BoundingBox2D) : BoundsWithMetrics :=
  let w := width bounds
  let h := height bounds
  { minX := bounds.minX
  , minY := bounds.minY
  , maxX := bounds.maxX
  , maxY := bounds.maxY
  , width := w
  , height := h
  , centerX := bounds.minX + w / 2.0
  , centerY := bounds.minY + h / 2.0 }

--------------------------------------------------------------------------------
-- Bounds Merging
--------------------------------------------------------------------------------

/-- Merge two bounding boxes.

    @param a First bounding box
    @param b Second bounding box
    @return Bounding box containing both -/
def merge (a b : BoundingBox2D) : BoundingBox2D :=
  { minX := Float.min a.minX b.minX
  , minY := Float.min a.minY b.minY
  , maxX := Float.max a.maxX b.maxX
  , maxY := Float.max a.maxY b.maxY }

/-- Merge an array of bounding boxes.

    @param bounds Array of bounding boxes
    @return Bounding box containing all -/
def mergeAll (bounds : Array BoundingBox2D) : BoundingBox2D :=
  bounds.foldl merge emptyBounds

--------------------------------------------------------------------------------
-- Bounds Queries
--------------------------------------------------------------------------------

/-- Check if a point is inside the bounding box.

    @param bounds The bounding box
    @param x Point X coordinate
    @param y Point Y coordinate
    @return True if point is inside (inclusive) -/
def containsPoint (bounds : BoundingBox2D) (x y : Float) : Bool :=
  x >= bounds.minX && x <= bounds.maxX &&
  y >= bounds.minY && y <= bounds.maxY

/-- Check if bounds is valid (non-empty).

    @param bounds The bounding box
    @return True if maxX >= minX and maxY >= minY -/
def isValid (bounds : BoundingBox2D) : Bool :=
  bounds.maxX >= bounds.minX && bounds.maxY >= bounds.minY

/-- Calculate area of bounding box.

    @param bounds The bounding box
    @return Area (width × height) -/
def area (bounds : BoundingBox2D) : Float :=
  width bounds * height bounds

/-- Calculate diagonal length of bounding box.

    @param bounds The bounding box
    @return Diagonal length -/
def diagonal (bounds : BoundingBox2D) : Float :=
  let w := width bounds
  let h := height bounds
  Float.sqrt (w * w + h * h)

--------------------------------------------------------------------------------
-- Bounds Transformation
--------------------------------------------------------------------------------

/-- Expand bounds by a margin.

    @param bounds The bounding box
    @param margin Amount to expand on all sides
    @return Expanded bounds -/
def expand (bounds : BoundingBox2D) (margin : Float) : BoundingBox2D :=
  { minX := bounds.minX - margin
  , minY := bounds.minY - margin
  , maxX := bounds.maxX + margin
  , maxY := bounds.maxY + margin }

/-- Scale bounds around its center.

    @param bounds The bounding box
    @param scale Scale factor
    @return Scaled bounds -/
def scale (bounds : BoundingBox2D) (scaleFactor : Float) : BoundingBox2D :=
  let cx := centerX bounds
  let cy := centerY bounds
  let hw := width bounds / 2.0 * scaleFactor
  let hh := height bounds / 2.0 * scaleFactor
  { minX := cx - hw
  , minY := cy - hh
  , maxX := cx + hw
  , maxY := cy + hh }

/-- Translate bounds by offset.

    @param bounds The bounding box
    @param dx X offset
    @param dy Y offset
    @return Translated bounds -/
def translate (bounds : BoundingBox2D) (dx dy : Float) : BoundingBox2D :=
  { minX := bounds.minX + dx
  , minY := bounds.minY + dy
  , maxX := bounds.maxX + dx
  , maxY := bounds.maxY + dy }

end Lattice.Services.SVGExtrusion.Bounds
