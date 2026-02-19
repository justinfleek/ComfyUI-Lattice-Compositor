/-
  Lattice.Services.Blur.StackBlur - StackBlur Algorithm Mathematics

  Pure mathematical functions for StackBlur algorithm:
  - Multiplication lookup table (fast integer division)
  - Shift lookup table
  - Stack accumulator formulas

  StackBlur is O(n) per pixel regardless of radius, making it
  extremely fast for large blur radii.

  Based on: http://www.quasimondo.com/StackBlurForCanvas/StackBlurDemo.html
  Source: ui/src/services/effects/blurRenderer.ts (lines 427-463)
-/

namespace Lattice.Services.Blur.StackBlur

--------------------------------------------------------------------------------
-- Lookup Tables
--------------------------------------------------------------------------------

/-- Multiplication table for fast integer division approximation.

    StackBlur uses this to avoid expensive division operations.
    The value at index r gives the multiplier for radius r.

    Usage: result = (sum * mulTable[r]) >>> shgTable[r]

    @param radius Blur radius (0-255)
    @return Multiplier value -/
def mulTableValue (radius : Nat) : Nat :=
  -- Table values for radii 0-255
  let table : Array Nat := #[
    512, 512, 456, 512, 328, 456, 335, 512, 405, 328, 271, 456, 388, 335, 292,
    512, 454, 405, 364, 328, 298, 271, 496, 456, 420, 388, 360, 335, 312, 292,
    273, 512, 482, 454, 428, 405, 383, 364, 345, 328, 312, 298, 284, 271, 259,
    496, 475, 456, 437, 420, 404, 388, 374, 360, 347, 335, 323, 312, 302, 292,
    282, 273, 265, 512, 497, 482, 468, 454, 441, 428, 417, 405, 394, 383, 373,
    364, 354, 345, 337, 328, 320, 312, 305, 298, 291, 284, 278, 271, 265, 259,
    507, 496, 485, 475, 465, 456, 446, 437, 428, 420, 412, 404, 396, 388, 381,
    374, 367, 360, 354, 347, 341, 335, 329, 323, 318, 312, 307, 302, 297, 292,
    287, 282, 278, 273, 269, 265, 261, 512, 505, 497, 489, 482, 475, 468, 461,
    454, 447, 441, 435, 428, 422, 417, 411, 405, 399, 394, 389, 383, 378, 373,
    368, 364, 359, 354, 350, 345, 341, 337, 332, 328, 324, 320, 316, 312, 309,
    305, 301, 298, 294, 291, 287, 284, 281, 278, 274, 271, 268, 265, 262, 259,
    257, 507, 501, 496, 491, 485, 480, 475, 470, 465, 460, 456, 451, 446, 442,
    437, 433, 428, 424, 420, 416, 412, 408, 404, 400, 396, 392, 388, 385, 381,
    377, 374, 370, 367, 363, 360, 357, 354, 350, 347, 344, 341, 338, 335, 332,
    329, 326, 323, 320, 318, 315, 312, 310, 307, 304, 302, 299, 297, 294, 292,
    289, 287, 285, 282, 280, 278, 275, 273, 271, 269, 267, 265, 263, 261, 259
  ]
  if radius < table.size then table[radius]! else 512

/-- Shift table for fast integer division approximation.

    @param radius Blur radius (0-255)
    @return Shift amount -/
def shgTableValue (radius : Nat) : Nat :=
  let table : Array Nat := #[
    9, 11, 12, 13, 13, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 17, 17,
    17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19,
    19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
    20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
    21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22,
    22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22,
    22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23,
    23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23,
    23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23,
    23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    24, 24, 24, 24, 24, 24, 24
  ]
  if radius < table.size then table[radius]! else 24

--------------------------------------------------------------------------------
-- Stack Accumulator Formulas
--------------------------------------------------------------------------------

/-- Calculate the divisor for a given radius (stack size).

    For StackBlur, the effective divisor is (radius + 1)²
    but we use lookup tables for fast approximation.

    @param radius Blur radius
    @return Effective divisor -/
def stackDivisor (radius : Nat) : Nat :=
  let r1 := radius + 1
  r1 * r1

/-- Calculate weighted contribution of a pixel at distance from center.

    In StackBlur, pixels closer to center contribute more.
    Weight = radius + 1 - |distance|

    @param radius Blur radius
    @param distance Distance from center (-radius to +radius)
    @return Weight (positive) -/
def pixelWeight (radius : Nat) (distance : Int) : Nat :=
  let absDistance := Int.natAbs distance
  if absDistance > radius then 0
  else radius + 1 - absDistance

/-- Apply StackBlur division using lookup tables.

    Approximates: sum / divisor
    As: (sum * mulTable[radius]) >>> shgTable[radius]

    @param sum Accumulated weighted sum
    @param radius Blur radius (for table lookup)
    @return Divided result -/
def stackDivide (sum : Nat) (radius : Nat) : Nat :=
  let mul := mulTableValue radius
  let shg := shgTableValue radius
  (sum * mul) >>> shg

--------------------------------------------------------------------------------
-- Edge Handling
--------------------------------------------------------------------------------

/-- Clamp an index to valid range for edge pixel handling.

    @param index Requested index
    @param maxIndex Maximum valid index
    @return Clamped index -/
def clampIndex (index : Int) (maxIndex : Nat) : Nat :=
  if index < 0 then 0
  else if index > Int.ofNat maxIndex then maxIndex
  else Int.toNat index

--------------------------------------------------------------------------------
-- Stack Size Calculations
--------------------------------------------------------------------------------

/-- Calculate stack size for a given radius.

    Stack size = 2 * radius + 1

    @param radius Blur radius
    @return Number of stack nodes needed -/
def stackSize (radius : Nat) : Nat :=
  radius * 2 + 1

/-- Calculate the index offset for stack initialization.

    When processing pixel at position x:
    - Stack covers x - radius to x + radius
    - stackIn starts at beginning
    - stackOut starts at position (radius) in the circular list

    @param radius Blur radius
    @return Offset for stackOut pointer -/
def stackOutOffset (radius : Nat) : Nat := radius

end Lattice.Services.Blur.StackBlur
