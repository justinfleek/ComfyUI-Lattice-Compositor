/-
  Lattice.Services.Mesh.Deformation - Mesh Warp Deformation

  Pure mathematical functions for mesh deformation using control pins.
  Uses inverse-distance weighting for smooth deformations.

  Features:
  - Inverse-distance weight calculation
  - Point rotation around origin
  - Point scaling around origin
  - Weighted vertex blending

  Source: ui/src/services/meshWarpDeformation.ts
-/

namespace Lattice.Services.Mesh.Deformation

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D point -/
structure Point2D where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

/-- Weight calculation options -/
structure WeightOptions where
  falloffPower : Float := 2.0     -- Power for inverse distance falloff
  minWeight : Float := 0.001     -- Minimum weight threshold
  normalize : Bool := true       -- Whether to normalize weights
  deriving Repr, Inhabited

/-- Default weight options -/
def defaultWeightOptions : WeightOptions := {}

/-- Pin state at a specific frame -/
structure PinState where
  position : Point2D
  rotation : Float  -- degrees
  scale : Float
  delta : Point2D   -- position - restPosition
  deriving Repr, Inhabited

/-- Pin rest state (initial pose) -/
structure PinRestState where
  position : Point2D
  rotation : Float
  scale : Float
  radius : Float := 100.0
  stiffness : Float := 0.0
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

/-- Distance between two points -/
def distance (a b : Point2D) : Float :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  Float.sqrt (dx * dx + dy * dy)

/-- Rotate a point around an origin -/
def rotatePoint (point origin : Point2D) (angleDegrees : Float) : Point2D :=
  let angleRadians := angleDegrees * Float.pi / 180.0
  let cos := Float.cos angleRadians
  let sin := Float.sin angleRadians
  let dx := point.x - origin.x
  let dy := point.y - origin.y
  ⟨origin.x + dx * cos - dy * sin,
   origin.y + dx * sin + dy * cos⟩

/-- Scale a point relative to an origin -/
def scalePoint (point origin : Point2D) (scale : Float) : Point2D :=
  ⟨origin.x + (point.x - origin.x) * scale,
   origin.y + (point.y - origin.y) * scale⟩

/-- Translate a point by a delta -/
def translatePoint (point delta : Point2D) : Point2D :=
  ⟨point.x + delta.x, point.y + delta.y⟩

--------------------------------------------------------------------------------
-- Weight Calculation
--------------------------------------------------------------------------------

/-- Calculate weight for a single vertex-pin pair.

    Uses inverse distance weighting with smooth falloff.

    Formula: weight = (1 / (1 + normalizedDist))^falloffPower
    where normalizedDist = distance / radius -/
def calculatePinWeight (vertex pinPos : Point2D) (radius : Float)
    (stiffness : Float) (options : WeightOptions) : Float :=
  let dist := distance vertex pinPos

  let weight :=
    if dist < 0.001 then 1000.0  -- Very close - high weight
    else if dist > radius * 3.0 then 0.0  -- Too far - no influence
    else
      let normalizedDist := dist / radius
      let baseWeight := (1.0 / (1.0 + normalizedDist)) ^ options.falloffPower

      -- Apply stiffness (starch pins reduce deformation)
      if stiffness > 0.0 then
        baseWeight * (1.0 - stiffness * 0.5)
      else
        baseWeight

  -- Apply minimum threshold
  if weight < options.minWeight then 0.0 else weight

/-- Calculate weights for all vertex-pin pairs.

    Returns flattened array: weights[v * pinCount + p] = weight of pin p on vertex v -/
def calculateWeights (vertices : Array Point2D) (pinRestStates : Array PinRestState)
    (options : WeightOptions := defaultWeightOptions) : Array Float :=
  let vertexCount := vertices.size
  let pinCount := pinRestStates.size

  if pinCount == 0 then #[]
  else
    let allWeights := Array.range vertexCount |>.foldl (fun acc v =>
      let vertex := vertices[v]!
      let vertexWeights := Array.range pinCount |>.map fun p =>
        let pin := pinRestStates[p]!
        calculatePinWeight vertex pin.position pin.radius pin.stiffness options

      -- Calculate total weight for normalization
      let totalWeight := vertexWeights.foldl (· + ·) 0.0

      -- Normalize if requested
      let normalizedWeights :=
        if options.normalize && totalWeight > 0.0 then
          vertexWeights.map (· / totalWeight)
        else
          vertexWeights

      acc ++ normalizedWeights
    ) #[]

    allWeights

--------------------------------------------------------------------------------
-- Deformation Application
--------------------------------------------------------------------------------

/-- Apply a single pin's transformation to a vertex.

    Handles translation, rotation, and scale based on pin delta. -/
def applyPinTransform (vertex : Point2D) (pinState : PinState)
    (restState : PinRestState) (applyTranslation : Bool)
    (applyRotation : Bool) (applyScale : Bool) : Point2D :=
  let result := vertex

  -- Apply translation
  let result := if applyTranslation then translatePoint result pinState.delta else result

  -- Apply rotation around pin position
  let result :=
    if applyRotation then
      let rotationDelta := pinState.rotation - restState.rotation
      if Float.abs rotationDelta > 0.001 then
        rotatePoint result pinState.position rotationDelta
      else result
    else result

  -- Apply scale around pin position
  let result :=
    if applyScale then
      if Float.abs (pinState.scale - restState.scale) > 0.001 then
        let scaleDelta := pinState.scale / restState.scale
        scalePoint result pinState.position scaleDelta
      else result
    else result

  result

/-- Deform a single vertex using weighted pin influences.

    Computes weighted average of per-pin deformed positions. -/
def deformVertex (vertex : Point2D) (vertexIndex : Nat)
    (pinStates : Array PinState) (pinRestStates : Array PinRestState)
    (weights : Array Float) : Point2D :=
  let pinCount := pinStates.size

  if pinCount == 0 then vertex
  else
    let (totalX, totalY, totalWeight) := Array.range pinCount |>.foldl
      (fun (accX, accY, accW) p =>
        let weight := weights[vertexIndex * pinCount + p]!
        if weight <= 0.0 then (accX, accY, accW)
        else
          let pinState := pinStates[p]!
          let restState := pinRestStates[p]!

          -- Apply transformations (all types for simplicity)
          let deformed := applyPinTransform vertex pinState restState
            true true true

          (accX + deformed.x * weight,
           accY + deformed.y * weight,
           accW + weight)
      ) (0.0, 0.0, 0.0)

    -- Return weighted average or original if no influence
    if totalWeight > 0.0 then
      ⟨totalX / totalWeight, totalY / totalWeight⟩
    else
      vertex

/-- Deform all vertices in a mesh.

    Returns array of deformed vertex positions. -/
def deformMesh (vertices : Array Point2D) (pinStates : Array PinState)
    (pinRestStates : Array PinRestState) (weights : Array Float) : Array Point2D :=
  vertices.mapIdx fun i vertex =>
    deformVertex vertex i.val pinStates pinRestStates weights

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

/-- Create pin state from current and rest positions -/
def createPinState (position : Point2D) (rotation scale : Float)
    (restPosition : Point2D) : PinState :=
  { position := position
  , rotation := rotation
  , scale := scale
  , delta := ⟨position.x - restPosition.x, position.y - restPosition.y⟩ }

/-- Linear interpolation between two points -/
def lerpPoint (a b : Point2D) (t : Float) : Point2D :=
  let tc := Float.max 0.0 (Float.min 1.0 t)
  ⟨a.x + (b.x - a.x) * tc, a.y + (b.y - a.y) * tc⟩

/-- Linear interpolation between two values -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * Float.max 0.0 (Float.min 1.0 t)

end Lattice.Services.Mesh.Deformation
