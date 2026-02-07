/-
  Lattice.Services.SVGExtrusion.CapProfile - Cap Profile Mathematics

  Pure mathematical functions for generating cap profile curves:
  - Fillet (quarter-circle) profile
  - Convex (outward bulging) profile
  - Concave (inward scooped) profile
  - Stepped (terraced) profile

  These profiles define the edge shape for 3D extrusion caps,
  similar to Cinema 4D/Blender fillet caps.

  Source: ui/src/services/svgExtrusion.ts (lines 166-251)
-/

namespace Lattice.Services.SVGExtrusion.CapProfile

--------------------------------------------------------------------------------
-- Point2D Type
--------------------------------------------------------------------------------

/-- 2D point for profile curves -/
structure Point2D where
  x : Float
  y : Float
deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Profile Types
--------------------------------------------------------------------------------

/-- Cap profile type -/
inductive CapProfileType
  | flat      -- Standard flat cap (no rounding)
  | fillet    -- Quarter-circle rounded edge
  | convex    -- Outward bulging profile
  | concave   -- Inward scooped profile
  | steps     -- Stepped/terraced profile
  | custom    -- Custom profile curve
deriving Repr, BEq

--------------------------------------------------------------------------------
-- Flat Profile
--------------------------------------------------------------------------------

/-- Generate flat cap profile (just start and end points).

    @param depth Cap depth
    @return Array of 2 points -/
def flatProfile (depth : Float) : Array Point2D :=
  #[Point2D.mk 0.0 0.0, Point2D.mk 0.0 depth]

--------------------------------------------------------------------------------
-- Fillet Profile
--------------------------------------------------------------------------------

/-- Generate quarter-circle fillet profile.

    Creates a smooth rounded edge transition.

    @param radius Fillet radius (horizontal extent)
    @param depth Cap depth (vertical extent)
    @param segments Number of curve segments
    @return Array of points along the fillet curve -/
def filletProfile (radius depth : Float) (segments : Nat) : Array Point2D :=
  Array.ofFn fun (i : Fin (segments + 1)) =>
    let t := Float.ofNat i.val / Float.ofNat segments
    let angle := (Float.pi / 2.0) * t
    let x := radius * (1.0 - Float.cos angle)
    let y := depth * Float.sin angle
    Point2D.mk x y

--------------------------------------------------------------------------------
-- Convex Profile
--------------------------------------------------------------------------------

/-- Generate convex (outward bulging) profile.

    Uses sine curve to create outward bulge.

    @param radius Bulge radius
    @param depth Cap depth
    @param segments Number of curve segments
    @return Array of points along the convex curve -/
def convexProfile (radius depth : Float) (segments : Nat) : Array Point2D :=
  Array.ofFn fun (i : Fin (segments + 1)) =>
    let t := Float.ofNat i.val / Float.ofNat segments
    -- Bulge outward using sine curve
    let bulge := Float.sin (Float.pi * t) * radius * 0.5
    let x := -bulge  -- Negative = outward
    let y := depth * t
    Point2D.mk x y

--------------------------------------------------------------------------------
-- Concave Profile
--------------------------------------------------------------------------------

/-- Generate concave (inward scooped) profile.

    Uses parabolic/sine curve to create inward scoop.

    @param radius Scoop radius
    @param depth Cap depth
    @param segments Number of curve segments
    @return Array of points along the concave curve -/
def concaveProfile (radius depth : Float) (segments : Nat) : Array Point2D :=
  Array.ofFn fun (i : Fin (segments + 1)) =>
    let t := Float.ofNat i.val / Float.ofNat segments
    -- Scoop inward using sine curve
    let scoop := Float.sin (Float.pi * t) * radius
    let x := scoop  -- Positive = inward
    let y := depth * t
    Point2D.mk x y

--------------------------------------------------------------------------------
-- Steps Profile
--------------------------------------------------------------------------------

/-- Generate stepped/terraced profile.

    Creates a staircase-like profile with flat steps and vertical risers.

    @param radius Total horizontal extent of steps
    @param depth Total vertical extent
    @param segments Total segments (step count = segments / 2)
    @return Array of points along the stepped profile -/
def stepsProfile (radius depth : Float) (segments : Nat) : Array Point2D :=
  let stepCount := Nat.max 2 (segments / 2)
  let stepHeight := depth / Float.ofNat stepCount
  let stepWidth := radius / Float.ofNat stepCount
  let result := Array.mkEmpty (stepCount * 2 + 1)
  -- Build steps with horizontal and vertical segments
  let rec buildSteps (i : Nat) (acc : Array Point2D) : Array Point2D :=
    if h : i > stepCount then acc
    else
      let iFloat := Float.ofNat i
      -- Horizontal step point
      let stepPt := Point2D.mk (iFloat * stepWidth) (iFloat * stepHeight)
      let acc' := acc.push stepPt
      -- Vertical riser point (except for last step)
      if i < stepCount then
        let riserPt := Point2D.mk (iFloat * stepWidth) ((iFloat + 1.0) * stepHeight)
        buildSteps (i + 1) (acc'.push riserPt)
      else
        acc'
  termination_by stepCount - i + 1
  buildSteps 0 result

--------------------------------------------------------------------------------
-- Custom Profile
--------------------------------------------------------------------------------

/-- Scale custom profile points to the desired radius and depth.

    @param customPoints Normalized custom profile (0-1 range)
    @param radius Horizontal scale factor
    @param depth Vertical scale factor
    @return Scaled profile points -/
def scaleCustomProfile (customPoints : Array Point2D) (radius depth : Float) : Array Point2D :=
  customPoints.map fun p => Point2D.mk (p.x * radius) (p.y * depth)

--------------------------------------------------------------------------------
-- Profile Generation
--------------------------------------------------------------------------------

/-- Generate cap profile curve based on type.

    @param profileType Type of cap profile
    @param radius Profile radius (horizontal extent)
    @param depth Profile depth (vertical extent)
    @param segments Number of segments for curved profiles
    @param customProfile Optional custom profile for 'custom' type
    @return Array of points defining the profile curve -/
def generateCapProfile
    (profileType : CapProfileType)
    (radius depth : Float)
    (segments : Nat)
    (customProfile : Option (Array Point2D) := none) : Array Point2D :=
  match profileType with
  | CapProfileType.flat => flatProfile depth
  | CapProfileType.fillet => filletProfile radius depth segments
  | CapProfileType.convex => convexProfile radius depth segments
  | CapProfileType.concave => concaveProfile radius depth segments
  | CapProfileType.steps => stepsProfile radius depth segments
  | CapProfileType.custom =>
    match customProfile with
    | some pts => if pts.size >= 2 then scaleCustomProfile pts radius depth
                  else filletProfile radius depth segments  -- Fallback
    | none => filletProfile radius depth segments  -- Fallback

--------------------------------------------------------------------------------
-- Profile Utilities
--------------------------------------------------------------------------------

/-- Check if profile type requires curve generation.

    @param profileType The profile type
    @return True if not flat -/
def requiresCurveGeneration (profileType : CapProfileType) : Bool :=
  profileType != CapProfileType.flat

/-- Get minimum segments for a profile type.

    @param profileType The profile type
    @return Minimum recommended segments -/
def minSegmentsFor (profileType : CapProfileType) : Nat :=
  match profileType with
  | CapProfileType.flat => 1
  | CapProfileType.fillet => 4
  | CapProfileType.convex => 4
  | CapProfileType.concave => 4
  | CapProfileType.steps => 4
  | CapProfileType.custom => 2

/-- Clamp segments to valid range.

    @param segments Requested segments
    @param profileType Profile type for minimum
    @return Clamped segment count (min to 32) -/
def clampSegments (segments : Nat) (profileType : CapProfileType) : Nat :=
  let minSeg := minSegmentsFor profileType
  Nat.max minSeg (Nat.min 32 segments)

end Lattice.Services.SVGExtrusion.CapProfile
