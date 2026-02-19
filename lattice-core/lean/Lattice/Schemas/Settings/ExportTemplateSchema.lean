/-
  Lattice.Schemas.Settings.ExportTemplateSchema

  Export template validation for localStorage settings.

  Source: ui/src/schemas/settings/export-template-schema.ts
-/

import Lattice.Schemas.SharedValidation
import Lattice.Schemas.ComfyUI.Targets

namespace Lattice.Schemas.Settings.ExportTemplateSchema

open SharedValidation
open ComfyUI.Targets

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_DIMENSION : Nat := 16384
def MAX_FRAMES : Nat := 100000
def MAX_FPS : Float := 120.0
def MAX_TIMESTAMP : Nat := 2147483647000
def MAX_TEMPLATES : Nat := 1000
def MAX_PATH_LENGTH : Nat := 500
def MAX_FILENAME_LENGTH : Nat := 255
def MAX_PROMPT_LENGTH : Nat := 10000
def MAX_SEED : Int := 2147483647
def MAX_STEPS : Nat := 1000
def MAX_CFG_SCALE : Float := 30.0
def MAX_URL_LENGTH : Nat := 2048

--------------------------------------------------------------------------------
-- Export Template Config
--------------------------------------------------------------------------------

/-- Partial export config for templates -/
structure ExportTemplateConfig where
  target : Option ExportTarget
  width : Option Nat
  height : Option Nat
  frameCount : Option Nat
  fps : Option Float
  startFrame : Option Nat
  endFrame : Option Nat
  outputDir : Option String
  filenamePrefix : Option String
  exportDepthMap : Option Bool
  exportControlImages : Option Bool
  exportCameraData : Option Bool
  exportReferenceFrame : Option Bool
  exportLastFrame : Option Bool
  depthFormat : Option DepthMapFormat
  controlType : Option ControlType
  prompt : Option String
  negativePrompt : Option String
  seed : Option Int
  steps : Option Nat
  cfgScale : Option Float
  comfyuiServer : Option String
  autoQueueWorkflow : Option Bool
  workflowTemplate : Option String
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Export Template
--------------------------------------------------------------------------------

/-- Export template structure -/
structure ExportTemplate where
  id : String
  name : String
  description : Option String
  createdAt : Nat
  modifiedAt : Nat
  config : ExportTemplateConfig
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Export Template Store
--------------------------------------------------------------------------------

/-- Export template store -/
structure ExportTemplateStore where
  templates : List ExportTemplate
  lastUsedTemplateId : Option String
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Validate ExportTemplateConfig -/
def validateExportTemplateConfig (config : ExportTemplateConfig) : Except ValidationError ExportTemplateConfig := do
  -- Validate width
  match config.width with
  | some w => if w > MAX_DIMENSION then
      throw (mkError "config.width" s!"must be at most {MAX_DIMENSION}")
    else pure ()
  | none => pure ()

  -- Validate height
  match config.height with
  | some h => if h > MAX_DIMENSION then
      throw (mkError "config.height" s!"must be at most {MAX_DIMENSION}")
    else pure ()
  | none => pure ()

  -- Validate frameCount
  match config.frameCount with
  | some fc => if fc > MAX_FRAMES then
      throw (mkError "config.frameCount" s!"must be at most {MAX_FRAMES}")
    else pure ()
  | none => pure ()

  -- Validate startFrame/endFrame relationship
  match config.startFrame, config.endFrame with
  | some sf, some ef => if ef < sf then
      throw (mkError "config.endFrame" "must be >= startFrame")
    else pure ()
  | _, _ => pure ()

  -- Validate outputDir
  match config.outputDir with
  | some od => if od.length > MAX_PATH_LENGTH then
      throw (mkError "config.outputDir" s!"must be at most {MAX_PATH_LENGTH} characters")
    else pure ()
  | none => pure ()

  -- Validate filenamePrefix
  match config.filenamePrefix with
  | some fp => if fp.length > MAX_FILENAME_LENGTH then
      throw (mkError "config.filenamePrefix" s!"must be at most {MAX_FILENAME_LENGTH} characters")
    else pure ()
  | none => pure ()

  -- Validate prompt
  match config.prompt with
  | some p => if p.length > MAX_PROMPT_LENGTH then
      throw (mkError "config.prompt" s!"must be at most {MAX_PROMPT_LENGTH} characters")
    else pure ()
  | none => pure ()

  -- Validate negativePrompt
  match config.negativePrompt with
  | some np => if np.length > MAX_PROMPT_LENGTH then
      throw (mkError "config.negativePrompt" s!"must be at most {MAX_PROMPT_LENGTH} characters")
    else pure ()
  | none => pure ()

  -- Validate seed
  match config.seed with
  | some s => if s > MAX_SEED then
      throw (mkError "config.seed" s!"must be at most {MAX_SEED}")
    else pure ()
  | none => pure ()

  -- Validate steps
  match config.steps with
  | some st => if st > MAX_STEPS then
      throw (mkError "config.steps" s!"must be at most {MAX_STEPS}")
    else pure ()
  | none => pure ()

  pure config

/-- Validate ExportTemplate -/
def validateExportTemplate (template : ExportTemplate) : Except ValidationError ExportTemplate := do
  _ ← validateEntityId "id" template.id
  _ ← validateNonEmptyString "name" MAX_NAME_LENGTH template.name

  -- Validate description
  match template.description with
  | some d => if d.length > MAX_DESCRIPTION_LENGTH then
      throw (mkError "description" s!"must be at most {MAX_DESCRIPTION_LENGTH} characters")
    else pure ()
  | none => pure ()

  -- Validate timestamps
  if template.createdAt > MAX_TIMESTAMP then
    throw (mkError "createdAt" s!"must be at most {MAX_TIMESTAMP}")
  if template.modifiedAt > MAX_TIMESTAMP then
    throw (mkError "modifiedAt" s!"must be at most {MAX_TIMESTAMP}")
  if template.modifiedAt < template.createdAt then
    throw (mkError "modifiedAt" "must be >= createdAt")

  _ ← validateExportTemplateConfig template.config
  pure template

/-- Safe validation -/
def safeValidateExportTemplate (template : ExportTemplate) : Option ExportTemplate :=
  match validateExportTemplate template with
  | .ok t => some t
  | .error _ => none

/-- Validate ExportTemplateStore -/
def validateExportTemplateStore (store : ExportTemplateStore) : Except ValidationError ExportTemplateStore := do
  if store.templates.length > MAX_TEMPLATES then
    throw (mkError "templates" s!"must have at most {MAX_TEMPLATES} templates")

  -- Validate all templates
  for t in store.templates do
    _ ← validateExportTemplate t

  -- Validate lastUsedTemplateId exists in templates
  match store.lastUsedTemplateId with
  | some lastId =>
    let exists := store.templates.any (fun t => t.id == lastId)
    if !exists then
      throw (mkError "lastUsedTemplateId" "must exist in templates array")
    else pure ()
  | none => pure ()

  pure store

/-- Safe validation -/
def safeValidateExportTemplateStore (store : ExportTemplateStore) : Option ExportTemplateStore :=
  match validateExportTemplateStore store with
  | .ok s => some s
  | .error _ => none

end Lattice.Schemas.Settings.ExportTemplateSchema
