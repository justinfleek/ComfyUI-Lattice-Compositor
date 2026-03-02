/-
  Lattice.Schemas.Exports.DepthSchema

  Depth export format enums and types.

  Source: ui/src/schemas/exports/depth-schema.ts
-/

namespace Lattice.Schemas.Exports.DepthSchema

--------------------------------------------------------------------------------
-- Depth Format
--------------------------------------------------------------------------------

/-- Depth output format options -/
inductive DepthFormat where
  | raw           -- Float32Array direct depth values
  | png           -- 8-bit grayscale PNG
  | png16         -- 16-bit grayscale PNG
  | exr           -- OpenEXR floating point
  | depth_anything  -- Depth-Anything model format
  | marigold      -- Marigold model format
  deriving Repr, DecidableEq, Inhabited

def depthFormatFromString : String → Option DepthFormat
  | "raw" => some .raw
  | "png" => some .png
  | "png16" => some .png16
  | "exr" => some .exr
  | "depth-anything" => some .depth_anything
  | "marigold" => some .marigold
  | _ => Option.none

def depthFormatToString : DepthFormat → String
  | .raw => "raw"
  | .png => "png"
  | .png16 => "png16"
  | .exr => "exr"
  | .depth_anything => "depth-anything"
  | .marigold => "marigold"

--------------------------------------------------------------------------------
-- Colormap
--------------------------------------------------------------------------------

/-- Colormap options for depth visualization -/
inductive Colormap where
  | grayscale
  | viridis
  | plasma
  | magma
  | inferno
  | turbo
  deriving Repr, DecidableEq, Inhabited

def colormapFromString : String → Option Colormap
  | "grayscale" => some .grayscale
  | "viridis" => some .viridis
  | "plasma" => some .plasma
  | "magma" => some .magma
  | "inferno" => some .inferno
  | "turbo" => some .turbo
  | _ => Option.none

def colormapToString : Colormap → String
  | .grayscale => "grayscale"
  | .viridis => "viridis"
  | .plasma => "plasma"
  | .magma => "magma"
  | .inferno => "inferno"
  | .turbo => "turbo"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Depth range specification -/
structure DepthRange where
  near : Float
  far : Float
  deriving Repr, Inhabited

/-- Depth statistics -/
structure DepthStats where
  min : Float
  max : Float
  mean : Option Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_DEPTH_RANGE : Float := 100000.0
def MAX_FRAMES : Nat := 100000
def MAX_DIMENSION : Nat := 16384

end Lattice.Schemas.Exports.DepthSchema
