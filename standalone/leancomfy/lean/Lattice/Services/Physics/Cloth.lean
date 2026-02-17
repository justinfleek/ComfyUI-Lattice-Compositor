/-
  Lattice.Services.Physics.Cloth - Cloth Simulation Configuration

  Pure functions for cloth simulation:
  - Cloth grid configuration
  - Constraint generation (structural, shear, bend)
  - Tearing detection
  - State management

  All functions are total and deterministic.

  Source: ui/src/services/physics/PhysicsEngine.ts (ClothSimulator)
-/

namespace Lattice.Services.Physics.Cloth

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Constraint type enumeration -/
inductive ClothConstraintType
  | structural   -- Horizontal or vertical
  | shear        -- Diagonal
  | bend         -- Skip one particle
  deriving Repr, Inhabited, BEq

/-- Cloth configuration -/
structure ClothConfig where
  width : Nat                -- Grid width (particles)
  height : Nat               -- Grid height (particles)
  spacing : Float            -- Distance between adjacent particles
  originX : Float            -- Top-left X coordinate
  originY : Float            -- Top-left Y coordinate
  particleMass : Float       -- Mass per particle
  structuralStiffness : Float -- Stiffness for horizontal/vertical
  shearStiffness : Float     -- Stiffness for diagonal
  bendStiffness : Float      -- Stiffness for skip-one
  damping : Float            -- Velocity damping
  collisionRadius : Float    -- Particle collision radius
  iterations : Nat           -- Constraint solving iterations
  tearThreshold : Option Float -- Stretch ratio before tearing
  pinnedParticles : Array Nat -- Indices of pinned particles
  deriving Repr, Inhabited

/-- Cloth constraint definition -/
structure ClothConstraint where
  id : String
  indexA : Nat               -- Particle index A
  indexB : Nat               -- Particle index B
  constraintType : ClothConstraintType
  restLength : Float
  stiffness : Float
  tearThreshold : Option Float
  deriving Repr, Inhabited

/-- Information about a torn constraint -/
structure TornConstraint where
  row : Nat
  col : Nat
  constraintType : ClothConstraintType
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default cloth configuration -/
def defaultClothConfig : ClothConfig :=
  { width := 20
  , height := 20
  , spacing := 10.0
  , originX := 100.0
  , originY := 50.0
  , particleMass := 1.0
  , structuralStiffness := 0.9
  , shearStiffness := 0.5
  , bendStiffness := 0.3
  , damping := 0.98
  , collisionRadius := 2.0
  , iterations := 3
  , tearThreshold := none
  , pinnedParticles := #[] }

--------------------------------------------------------------------------------
-- Grid Operations
--------------------------------------------------------------------------------

/-- Convert (row, col) to particle index.

    @param row Row index (0-based)
    @param col Column index (0-based)
    @param width Grid width
    @return Linear particle index -/
def gridToIndex (row col width : Nat) : Nat :=
  row * width + col

/-- Convert particle index to (row, col).

    @param index Linear particle index
    @param width Grid width
    @return (row, col) tuple -/
def indexToGrid (index width : Nat) : Nat × Nat :=
  (index / width, index % width)

/-- Calculate initial particle position.

    @param config Cloth configuration
    @param row Particle row
    @param col Particle column
    @return (x, y) position -/
def particlePosition (config : ClothConfig) (row col : Nat) : Float × Float :=
  ( config.originX + row.toFloat * config.spacing
  , config.originY + col.toFloat * config.spacing )

--------------------------------------------------------------------------------
-- Constraint Generation
--------------------------------------------------------------------------------

/-- Generate structural constraints (horizontal and vertical).

    Creates constraints between horizontally and vertically adjacent particles.

    @param config Cloth configuration
    @param clothId Cloth identifier prefix
    @return Array of structural constraints -/
def generateStructuralConstraints (config : ClothConfig) (clothId : String) : Array ClothConstraint :=
  let w := config.width
  let h := config.height
  let spacing := config.spacing
  let stiffness := config.structuralStiffness
  let threshold := config.tearThreshold

  -- Horizontal constraints (within each row)
  let horizontal := Id.run do
    let mut result := #[]
    for r in [0:h] do
      for c in [0:w-1] do
        result := result.push {
          id := clothId ++ "_h_" ++ toString (gridToIndex r c w)
          indexA := gridToIndex r c w
          indexB := gridToIndex r (c + 1) w
          constraintType := ClothConstraintType.structural
          restLength := spacing
          stiffness := stiffness
          tearThreshold := threshold
        }
    result

  -- Vertical constraints (within each column)
  let vertical := Id.run do
    let mut result := #[]
    for r in [0:h-1] do
      for c in [0:w] do
        result := result.push {
          id := clothId ++ "_v_" ++ toString (gridToIndex r c w)
          indexA := gridToIndex r c w
          indexB := gridToIndex (r + 1) c w
          constraintType := ClothConstraintType.structural
          restLength := spacing
          stiffness := stiffness
          tearThreshold := threshold
        }
    result

  horizontal ++ vertical

/-- Generate shear constraints (diagonal).

    Creates constraints between diagonally adjacent particles.

    @param config Cloth configuration
    @param clothId Cloth identifier prefix
    @return Array of shear constraints -/
def generateShearConstraints (config : ClothConfig) (clothId : String) : Array ClothConstraint :=
  if config.shearStiffness <= 0.0 then
    #[]
  else
    let w := config.width
    let h := config.height
    let diagLength := config.spacing * Float.sqrt 2.0
    let stiffness := config.shearStiffness

    -- Diagonal 1 (top-left to bottom-right)
    let diagonal1 := Id.run do
      let mut result := #[]
      for r in [0:h-1] do
        for c in [0:w-1] do
          result := result.push {
            id := clothId ++ "_s1_" ++ toString (gridToIndex r c w)
            indexA := gridToIndex r c w
            indexB := gridToIndex (r + 1) (c + 1) w
            constraintType := ClothConstraintType.shear
            restLength := diagLength
            stiffness := stiffness
            tearThreshold := none
          }
      result

    -- Diagonal 2 (top-right to bottom-left)
    let diagonal2 := Id.run do
      let mut result := #[]
      for r in [0:h-1] do
        for c in [0:w-1] do
          result := result.push {
            id := clothId ++ "_s2_" ++ toString (gridToIndex r c w)
            indexA := gridToIndex r (c + 1) w
            indexB := gridToIndex (r + 1) c w
            constraintType := ClothConstraintType.shear
            restLength := diagLength
            stiffness := stiffness
            tearThreshold := none
          }
      result

    diagonal1 ++ diagonal2

/-- Generate bend constraints (skip one particle).

    Creates constraints between particles with one particle between them.
    This resists bending/folding of the cloth.

    @param config Cloth configuration
    @param clothId Cloth identifier prefix
    @return Array of bend constraints -/
def generateBendConstraints (config : ClothConfig) (clothId : String) : Array ClothConstraint :=
  if config.bendStiffness <= 0.0 then
    #[]
  else
    let w := config.width
    let h := config.height
    let skipLength := config.spacing * 2.0
    let stiffness := config.bendStiffness

    -- Horizontal bend (skip one column)
    let bendH := Id.run do
      let mut result := #[]
      for r in [0:h] do
        for c in [0:w-2] do
          result := result.push {
            id := clothId ++ "_bh_" ++ toString (gridToIndex r c w)
            indexA := gridToIndex r c w
            indexB := gridToIndex r (c + 2) w
            constraintType := ClothConstraintType.bend
            restLength := skipLength
            stiffness := stiffness
            tearThreshold := none
          }
      result

    -- Vertical bend (skip one row)
    let bendV := Id.run do
      let mut result := #[]
      for r in [0:h-2] do
        for c in [0:w] do
          result := result.push {
            id := clothId ++ "_bv_" ++ toString (gridToIndex r c w)
            indexA := gridToIndex r c w
            indexB := gridToIndex (r + 2) c w
            constraintType := ClothConstraintType.bend
            restLength := skipLength
            stiffness := stiffness
            tearThreshold := none
          }
      result

    bendH ++ bendV

/-- Generate all constraints for a cloth.

    @param config Cloth configuration
    @param clothId Cloth identifier prefix
    @return Array of all constraints -/
def generateAllConstraints (config : ClothConfig) (clothId : String) : Array ClothConstraint :=
  generateStructuralConstraints config clothId
  ++ generateShearConstraints config clothId
  ++ generateBendConstraints config clothId

--------------------------------------------------------------------------------
-- Tearing
--------------------------------------------------------------------------------

/-- Check if a constraint should tear based on current distance.

    @param constraint Constraint to check
    @param currentDist Current distance between particles
    @return True if constraint should tear -/
def checkTear (constraint : ClothConstraint) (currentDist : Float) : Bool :=
  match constraint.tearThreshold with
  | none => false
  | some threshold => currentDist > constraint.restLength * threshold

/-- Extract torn constraint info from constraint.

    @param constraint Constraint that tore
    @param width Grid width
    @return Torn constraint info -/
def tornConstraintInfo (constraint : ClothConstraint) (width : Nat) : TornConstraint :=
  let (row, col) := indexToGrid constraint.indexA width
  { row := row
  , col := col
  , constraintType := constraint.constraintType }

--------------------------------------------------------------------------------
-- Particle Count
--------------------------------------------------------------------------------

/-- Calculate total number of particles in cloth.

    @param config Cloth configuration
    @return Total particle count -/
def particleCount (config : ClothConfig) : Nat :=
  config.width * config.height

/-- Check if particle index is valid.

    @param config Cloth configuration
    @param index Particle index
    @return True if valid -/
def isValidIndex (config : ClothConfig) (index : Nat) : Bool :=
  index < particleCount config

/-- Check if particle is pinned.

    @param config Cloth configuration
    @param index Particle index
    @return True if pinned -/
def isPinned (config : ClothConfig) (index : Nat) : Bool :=
  config.pinnedParticles.contains index

end Lattice.Services.Physics.Cloth
