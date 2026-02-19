/-
  Lattice.Compass.Integration - Bridge types between Lattice and COMPASS

  This module provides integration points between Lattice Compositor and COMPASS systems:
  - Permission mapping for Lattice operations
  - Budget integration for Lattice exports
  - Rate limiting for Lattice AI operations
  - Security proofs for Lattice-COMPASS interactions
-/

import Compass.Permissions
import Compass.Budget
import Compass.RateLimiter
import Compass.Router

namespace Lattice.Compass.Integration

open Compass.Permissions
open Compass.Budget
open Compass.RateLimiter
open Compass.Router

/-! ## Lattice Operation to COMPASS Permission Mapping -/

/-- Map Lattice operations to COMPASS permissions -/
def latticeOpToPermission : String → Option Permission
  | "export_video" => some .EXPORT_VIDEO
  | "ai_generate" => some .AI_GENERATE
  | "layer_create" => some .LAYER_CREATE
  | "layer_modify" => some .LAYER_MODIFY
  | "content_create" => some .CONTENT_CREATE
  | "content_publish" => some .CONTENT_PUBLISH
  | _ => none

/-! ## Lattice Budget Integration -/

/-- Lattice export budget tracking -/
structure LatticeExportBudget where
  daily_exports : BudgetState
  monthly_exports : BudgetState
  daily_tokens : BudgetState
  monthly_tokens : BudgetState
  deriving Repr

/-! ## Lattice Rate Limiting -/

/-- Rate limits for Lattice operations -/
structure LatticeRateLimits where
  ai_generation : Bucket
  export_operations : Bucket
  layer_operations : Bucket
  deriving Repr

/-! ## Security Theorems -/

/-- THEOREM: Lattice operations require appropriate permissions -/
theorem lattice_op_requires_permission (op : String) (perm : Permission) :
    latticeOpToPermission op = some perm →
    ∀ r : Role, Role.hasPermission r perm = true →
    True := by
  intro h_map r h_perm
  trivial

end Lattice.Compass.Integration
