/-
  Lattice.Schemas.Exports.VACESchema

  VACE (Video Animation Control Engine) export format enums and types.

  Source: ui/src/schemas/exports/vace-schema.ts
-/

namespace Lattice.Schemas.Exports.VACESchema

--------------------------------------------------------------------------------
-- Path Follower Shape
--------------------------------------------------------------------------------

/-- Path follower shape options -/
inductive PathFollowerShape where
  | circle
  | square
  | triangle
  | diamond
  | arrow
  | custom
  deriving Repr, DecidableEq, Inhabited

def pathFollowerShapeFromString : String → Option PathFollowerShape
  | "circle" => some .circle
  | "square" => some .square
  | "triangle" => some .triangle
  | "diamond" => some .diamond
  | "arrow" => some .arrow
  | "custom" => some .custom
  | _ => Option.none

def pathFollowerShapeToString : PathFollowerShape → String
  | .circle => "circle"
  | .square => "square"
  | .triangle => "triangle"
  | .diamond => "diamond"
  | .arrow => "arrow"
  | .custom => "custom"

--------------------------------------------------------------------------------
-- Path Follower Easing
--------------------------------------------------------------------------------

/-- Path follower easing options -/
inductive PathFollowerEasing where
  | linear
  | ease_in
  | ease_out
  | ease_in_out
  | ease_in_cubic
  | ease_out_cubic
  deriving Repr, DecidableEq, Inhabited

def pathFollowerEasingFromString : String → Option PathFollowerEasing
  | "linear" => some .linear
  | "ease-in" => some .ease_in
  | "ease-out" => some .ease_out
  | "ease-in-out" => some .ease_in_out
  | "ease-in-cubic" => some .ease_in_cubic
  | "ease-out-cubic" => some .ease_out_cubic
  | _ => Option.none

def pathFollowerEasingToString : PathFollowerEasing → String
  | .linear => "linear"
  | .ease_in => "ease-in"
  | .ease_out => "ease-out"
  | .ease_in_out => "ease-in-out"
  | .ease_in_cubic => "ease-in-cubic"
  | .ease_out_cubic => "ease-out-cubic"

--------------------------------------------------------------------------------
-- Loop Mode
--------------------------------------------------------------------------------

/-- Loop mode options -/
inductive LoopMode where
  | restart
  | pingpong
  deriving Repr, DecidableEq, Inhabited

def loopModeFromString : String → Option LoopMode
  | "restart" => some .restart
  | "pingpong" => some .pingpong
  | _ => Option.none

def loopModeToString : LoopMode → String
  | .restart => "restart"
  | .pingpong => "pingpong"

--------------------------------------------------------------------------------
-- VACE Output Format
--------------------------------------------------------------------------------

/-- VACE output format options -/
inductive VACEOutputFormat where
  | canvas
  | webm
  | frames
  deriving Repr, DecidableEq, Inhabited

def vaceOutputFormatFromString : String → Option VACEOutputFormat
  | "canvas" => some .canvas
  | "webm" => some .webm
  | "frames" => some .frames
  | _ => Option.none

def vaceOutputFormatToString : VACEOutputFormat → String
  | .canvas => "canvas"
  | .webm => "webm"
  | .frames => "frames"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- 2D/3D control point for splines -/
structure SplineControlPoint where
  x : Float
  y : Float
  z : Option Float
  deriving Repr, Inhabited

/-- Path follower state at a frame -/
structure PathFollowerState where
  positionX : Float
  positionY : Float
  rotation : Float
  scale : Float
  opacity : Float
  progress : Float
  visible : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_CONTROL_POINTS : Nat := 100000
def MIN_CLOSED_PATH_POINTS : Nat := 3
def MAX_COORDINATE : Float := 16384.0
def MAX_SIZE : Float := 10000.0
def MAX_STROKE_WIDTH : Float := 1000.0
def MAX_ROTATION_OFFSET : Float := 360.0
def MAX_ROTATION_RADIANS : Float := 6.28318  -- 2π
def MAX_SCALE : Float := 100.0
def MAX_PATH_FOLLOWERS : Nat := 1000

end Lattice.Schemas.Exports.VACESchema
