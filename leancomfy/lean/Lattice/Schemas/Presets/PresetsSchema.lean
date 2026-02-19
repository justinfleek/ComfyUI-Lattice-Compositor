/-
  Lattice.Schemas.Presets.PresetsSchema

  Preset system enums for particles, effects, animations, etc.

  Source: ui/src/schemas/presets/presets-schema.ts
-/

namespace Lattice.Schemas.Presets.PresetsSchema

--------------------------------------------------------------------------------
-- Preset Category
--------------------------------------------------------------------------------

/-- Preset category options -/
inductive PresetCategory where
  | particle
  | effect
  | animation
  | camera_shake
  | camera_trajectory
  | path_effect
  | text_style
  | color_palette
  deriving Repr, DecidableEq, Inhabited

def presetCategoryFromString : String → Option PresetCategory
  | "particle" => some .particle
  | "effect" => some .effect
  | "animation" => some .animation
  | "camera-shake" => some .camera_shake
  | "camera-trajectory" => some .camera_trajectory
  | "path-effect" => some .path_effect
  | "text-style" => some .text_style
  | "color-palette" => some .color_palette
  | _ => none

def presetCategoryToString : PresetCategory → String
  | .particle => "particle"
  | .effect => "effect"
  | .animation => "animation"
  | .camera_shake => "camera-shake"
  | .camera_trajectory => "camera-trajectory"
  | .path_effect => "path-effect"
  | .text_style => "text-style"
  | .color_palette => "color-palette"

--------------------------------------------------------------------------------
-- Camera Shake Type
--------------------------------------------------------------------------------

/-- Camera shake type options -/
inductive CameraShakeType where
  | handheld
  | impact
  | earthquake
  | subtle
  | custom
  deriving Repr, DecidableEq, Inhabited

def cameraShakeTypeFromString : String → Option CameraShakeType
  | "handheld" => some .handheld
  | "impact" => some .impact
  | "earthquake" => some .earthquake
  | "subtle" => some .subtle
  | "custom" => some .custom
  | _ => none

def cameraShakeTypeToString : CameraShakeType → String
  | .handheld => "handheld"
  | .impact => "impact"
  | .earthquake => "earthquake"
  | .subtle => "subtle"
  | .custom => "custom"

--------------------------------------------------------------------------------
-- Text Align
--------------------------------------------------------------------------------

/-- Text alignment options -/
inductive TextAlign where
  | left
  | center
  | right
  | justify
  deriving Repr, DecidableEq, Inhabited

def textAlignFromString : String → Option TextAlign
  | "left" => some .left
  | "center" => some .center
  | "right" => some .right
  | "justify" => some .justify
  | _ => none

def textAlignToString : TextAlign → String
  | .left => "left"
  | .center => "center"
  | .right => "right"
  | .justify => "justify"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_PRESET_VERSION : Nat := 1000
def MAX_PRESETS_COUNT : Nat := 10000
def MAX_PARTICLES : Nat := 10000000
def MAX_GRAVITY : Float := 1000.0
def MAX_EMISSION_RATE : Nat := 100000
def MAX_LIFESPAN : Float := 3600.0  -- 1 hour
def MAX_SHAKE_FREQUENCY : Float := 100.0
def MAX_SHAKE_FRAMES : Nat := 100000
def MAX_FONT_SIZE : Float := 1000.0
def MAX_COLORS_COUNT : Nat := 1000
def MAX_KEYFRAMES : Nat := 100000

end Lattice.Schemas.Presets.PresetsSchema
