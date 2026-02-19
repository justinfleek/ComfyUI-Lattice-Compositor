/-
  Basic types for interpolation
  Foundation for all interpolation proofs
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

namespace Interpolation.Basic

/-- Unit interval [0, 1] with proofs -/
structure UnitInterval where
  val : Float
  h_ge : 0 ≤ val
  h_le : val ≤ 1
deriving Repr, BEq

/-- Constructor with clamping -/
def mkUnitInterval (x : Float) : UnitInterval :=
  if h1 : 0 ≤ x then
    if h2 : x ≤ 1 then ⟨x, h1, h2⟩
    else ⟨1, by norm_num, le_refl 1⟩
  else ⟨0, le_refl 0, by norm_num⟩

/-- 2D Vector -/
structure Vec2 where
  x : Float
  y : Float
deriving Repr, BEq

/-- 3D Vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
deriving Repr, BEq

/-- 4D Vector (for RGBA colors) -/
structure Vec4 where
  x : Float
  y : Float
  z : Float
  w : Float
deriving Repr, BEq

end Interpolation.Basic
