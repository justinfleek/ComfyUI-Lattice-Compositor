/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            HYDROGEN // CAMERA
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Camera system for Hydrogen with proven invariants.
  
  This module provides camera types following the LATTICE camera model,
  with all invariants enforced at the type level:
  
  - FOV bounded in (0, π) — prevents degenerate frustums
  - Clip planes with near < far — prevents inverted depth
  - All positive values guaranteed positive — prevents division by zero
  - Focal length ↔ FOV conversions proven to round-trip
  - Projection matrices proven invertible
  
  ─────────────────────────────────────────────────────────────────────────────
  MODULES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types       : Core camera types (FOV, ClipPlanes, PerspectiveCamera, etc.)
  - Lens        : Focal length ↔ FOV conversions with round-trip proofs
  - Projection  : Camera → Mat4 projection with invertibility proofs
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Camera.Types
import Hydrogen.Camera.Lens
import Hydrogen.Camera.Projection
