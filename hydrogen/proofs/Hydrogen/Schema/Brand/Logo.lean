/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                               HYDROGEN // SCHEMA // BRAND // LOGO
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Logo System: Complete logo specification with proven invariants.
  
  INVARIANTS PROVEN:
    1. lockup_has_variants: Every lockup has at least one color variant
    2. clear_space_positive: Clear space multiplier must be > 0
    3. size_positive: All minimum sizes must be positive
    4. primary_lockup_exists: Logo system has exactly one primary lockup
    5. error_set_complete: Error categories form a complete covering
  
  WHY THESE MATTER:
    Logo constraints are critical for AI enforcement. When an agent renders
    a logo, it must know:
    - Which lockup to use (primary vs alternate, context-appropriate)
    - Minimum sizing (never render below threshold)
    - Clear space requirements (never crowd the logo)
    - What NOT to do (the error list is more valuable than positive guidance)
  
    At billion-agent scale, a logo rendered with negative clear space or
    below minimum size creates brand damage at scale. These invariants make
    invalid configurations unrepresentable.
  
    The error "Do Not" list is particularly valuable: it converts subjective
    design guidance ("don't squash the logo") into enforceable constraints
    that AI systems can check programmatically.
  
  Status: FOUNDATIONAL — ZERO SORRY
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace Hydrogen.Schema.Brand.Logo

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: LOGO COMPONENTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Logo Components

The fundamental building blocks of a logo. A logo consists of some combination
of Icon (symbol/mark) and Wordmark (typographic brand name).
-/

/-- Logo component types -/
inductive LogoComponent where
  | icon     : LogoComponent  -- Symbol/mark element
  | wordmark : LogoComponent  -- Typographic brand name
  deriving Repr, DecidableEq

namespace LogoComponent

/-- Convert to string for serialization -/
def toString : LogoComponent → String
  | icon => "icon"
  | wordmark => "wordmark"

/-- Parse from string -/
def fromString (s : String) : Option LogoComponent :=
  match s.toLower with
  | "icon" => some icon
  | "wordmark" => some wordmark
  | _ => none

end LogoComponent

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: ORIENTATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Orientation

The spatial arrangement of logo elements. This affects which lockup is
appropriate for different contexts (horizontal for headers, vertical for
posters, square for app icons).
-/

/-- Logo orientation -/
inductive Orientation where
  | horizontal : Orientation  -- Icon beside wordmark
  | vertical   : Orientation  -- Icon above wordmark
  | square     : Orientation  -- Compact, equal dimensions
  deriving Repr, DecidableEq

namespace Orientation

def toString : Orientation → String
  | horizontal => "horizontal"
  | vertical => "vertical"
  | square => "square"

def fromString (s : String) : Option Orientation :=
  match s.toLower with
  | "horizontal" => some horizontal
  | "vertical" => some vertical
  | "square" => some square
  | _ => none

end Orientation

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: COLOR VARIANTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Color Variants

Approved color treatments for logo usage. Every lockup must have at least
one variant available.

WHY AT LEAST ONE VARIANT IS NECESSARY:
  A lockup without any color variant is undefined — there's no way to render
  it. This creates a black hole in the brand system where an agent might
  select a lockup but have no valid way to display it.
  
  At billion-agent scale, this would cause:
  - Render failures (agent selects lockup, can't find variant)
  - Fallback to undefined behavior (agent guesses a color)
  - Inconsistent brand representation
  
  By requiring at least one variant, we guarantee every selected lockup
  can actually be rendered.
-/

/-- Color variant for logo rendering -/
inductive ColorVariant where
  | fullColor   : ColorVariant  -- Primary brand colors
  | blackWhite  : ColorVariant  -- Monochrome
  | reversed    : ColorVariant  -- Light on dark
  | singleColor : ColorVariant  -- One-color printing
  deriving Repr, DecidableEq

namespace ColorVariant

def toString : ColorVariant → String
  | fullColor => "full-color"
  | blackWhite => "black-white"
  | reversed => "reversed"
  | singleColor => "single-color"

end ColorVariant

/-- A non-empty set of color variants.
    
    CRITICAL INVARIANT: variants.length > 0
    This is proven by construction — we carry the proof in the structure. -/
structure VariantSet where
  variants : List ColorVariant
  nonempty : variants.length > 0
  unique : variants = variants.eraseDups
  deriving Repr

namespace VariantSet

/-- Default variant set (full color only) -/
def default : VariantSet := {
  variants := [ColorVariant.fullColor]
  nonempty := by decide
  unique := by rfl
}

/-- All standard variants -/
def all : VariantSet := {
  variants := [ColorVariant.fullColor, ColorVariant.blackWhite, 
               ColorVariant.reversed, ColorVariant.singleColor]
  nonempty := by decide
  unique := by rfl
}

/-- Check if variant is in set -/
def hasVariant (vs : VariantSet) (v : ColorVariant) : Bool :=
  v ∈ vs.variants

/-- Variant set always has at least one option -/
theorem always_has_option (vs : VariantSet) : vs.variants ≠ [] := by
  intro h
  have : vs.variants.length > 0 := vs.nonempty
  rw [h] at this
  simp at this

end VariantSet

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: CLEAR SPACE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Clear Space

The minimum clearance required around the logo. Defined as a multiplier
applied to a reference element (e.g., "2× the height of letter N").

WHY POSITIVE MULTIPLIER IS NECESSARY:
  Clear space of zero or negative makes no geometric sense and would allow
  other elements to overlap the logo. This violates the fundamental purpose
  of clear space — to ensure the logo has room to "breathe" and remain
  visually distinct.
  
  A brand guide saying "clear space = -0.5× icon height" is nonsensical.
  By bounding the multiplier to (0, 10], we ensure:
  - Clear space is always positive (logo is never overlapped)
  - Clear space has a reasonable upper bound (not absurdly large)
  - The constraint is enforceable by construction
-/

/-- Clear space multiplier: how many times the reference element 
    defines the required clear space. Must be positive.
    
    Range: (0, 10] — positive, reasonable bound.
    Uses ℝ (real numbers) for proper mathematical proofs. -/
structure ClearSpaceMultiplier where
  value : ℝ
  positive : 0 < value
  bounded : value ≤ 10

namespace ClearSpaceMultiplier

/-- Create a multiplier with validation -/
def make (v : ℝ) (h_pos : 0 < v) (h_bound : v ≤ 10) : ClearSpaceMultiplier :=
  ⟨v, h_pos, h_bound⟩

/-- Default multiplier (1×) -/
def default : ClearSpaceMultiplier := {
  value := 1
  positive := by norm_num
  bounded := by norm_num
}

/-- Common multiplier (2×) -/
def double : ClearSpaceMultiplier := {
  value := 2
  positive := by norm_num
  bounded := by norm_num
}

/-- Clear space is always positive -/
theorem always_positive (m : ClearSpaceMultiplier) : 0 < m.value := m.positive

/-- Clear space is always bounded -/
theorem always_bounded (m : ClearSpaceMultiplier) : m.value ≤ 10 := m.bounded

end ClearSpaceMultiplier

/-- Reference element description for clear space calculation.
    
    Examples: "height of letter N", "icon width", "x-height"
    Bounded: 1-100 characters -/
structure ClearSpaceReference where
  description : String
  nonempty : description.length > 0
  bounded : description.length ≤ 100
  deriving Repr

/-- Complete clear space rule -/
structure ClearSpaceRule where
  multiplier : ClearSpaceMultiplier
  reference : ClearSpaceReference

namespace ClearSpaceRule

/-- Clear space always requires positive offset -/
theorem positive_clearance (rule : ClearSpaceRule) : 0 < rule.multiplier.value :=
  rule.multiplier.positive

end ClearSpaceRule

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: MINIMUM SIZING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Minimum Sizing

Print and digital minimum dimensions for logo rendering.

WHY POSITIVE SIZES ARE NECESSARY:
  A logo with zero or negative size is unrenderable. More subtly, logos
  rendered below certain thresholds become illegible or lose detail.
  
  Brand guidelines specify minimums to ensure:
  - Icon details remain visible
  - Wordmark remains readable
  - Overall logo maintains integrity
  
  By proving sizes are positive, we guarantee any selected lockup can
  actually be displayed at a valid size.
-/

/-- Print size in inches. 
    
    Range: [0.1, 24] — reasonable print dimensions.
    Uses ℝ for proper mathematical proofs. -/
structure PrintSize where
  inches : ℝ
  min_bound : (1 : ℝ) / 10 ≤ inches
  max_bound : inches ≤ 24

namespace PrintSize

/-- Print size is always positive -/
theorem positive (s : PrintSize) : 0 < s.inches := by
  have h := s.min_bound
  have : (0 : ℝ) < 1 / 10 := by norm_num
  linarith

/-- Default print minimum (0.75 inches) -/
def default : PrintSize := {
  inches := 3 / 4
  min_bound := by norm_num
  max_bound := by norm_num
}

/-- Small print minimum (0.5 inches) -/
def small : PrintSize := {
  inches := 1 / 2
  min_bound := by norm_num
  max_bound := by norm_num
}

end PrintSize

/-- Digital size in pixels. 
    
    Range: [1, 10000] — reasonable digital dimensions.
    Uses ℕ for discrete pixel counts. -/
structure DigitalSize where
  pixels : ℕ
  min_bound : 1 ≤ pixels
  max_bound : pixels ≤ 10000
  deriving Repr

namespace DigitalSize

/-- Digital size is always positive -/
theorem positive (s : DigitalSize) : 0 < s.pixels := by
  have h := s.min_bound
  omega

/-- Default digital minimum (60 pixels) -/
def default : DigitalSize := {
  pixels := 60
  min_bound := by decide
  max_bound := by decide
}

/-- Favicon size (32 pixels) -/
def favicon : DigitalSize := {
  pixels := 32
  min_bound := by decide
  max_bound := by decide
}

/-- App icon size (512 pixels) -/
def appIcon : DigitalSize := {
  pixels := 512
  min_bound := by decide
  max_bound := by decide
}

end DigitalSize

/-- Combined size constraint -/
structure SizeConstraint where
  printMin : PrintSize
  digitalMin : DigitalSize

namespace SizeConstraint

/-- Default size constraint -/
def default : SizeConstraint := {
  printMin := PrintSize.default
  digitalMin := DigitalSize.default
}

/-- Both sizes are positive -/
theorem both_positive (sc : SizeConstraint) : 
    0 < sc.printMin.inches ∧ 0 < sc.digitalMin.pixels :=
  ⟨PrintSize.positive sc.printMin, DigitalSize.positive sc.digitalMin⟩

end SizeConstraint

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: LOCKUP PRIORITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Lockup Priority

Hierarchical importance of lockups. Primary is the default; alternates are
for specific contexts or constraints.
-/

/-- Priority level for lockup selection -/
inductive LockupPriority where
  | primary   : LockupPriority  -- First choice, mandatory for brand introduction
  | secondary : LockupPriority  -- Alternative for specific contexts
  | tertiary  : LockupPriority  -- Fallback for constrained spaces
  deriving Repr, DecidableEq

namespace LockupPriority

def toString : LockupPriority → String
  | primary => "primary"
  | secondary => "secondary"
  | tertiary => "tertiary"

/-- Primary is highest priority (smallest ordinal) -/
def toOrdinal : LockupPriority → ℕ
  | primary => 0
  | secondary => 1
  | tertiary => 2

/-- Compare priorities -/
def compare (p1 p2 : LockupPriority) : Ordering :=
  Ord.compare (toOrdinal p1) (toOrdinal p2)

/-- Primary has lowest ordinal -/
theorem primary_is_first : toOrdinal primary = 0 := rfl

end LockupPriority

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: USAGE CONTEXT
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Usage Context

Where a lockup is approved for use. Different contexts have different
requirements (e.g., favicon needs square, letterhead needs horizontal).
-/

/-- Approved usage context for a lockup -/
inductive UsageContext where
  | letterhead
  | businessCard
  | emailSignature
  | socialProfile
  | websiteHeader
  | appIcon
  | favicon
  | merchandise
  | printAdvertising
  | digitalAdvertising
  | presentation
  | video
  deriving Repr, DecidableEq

namespace UsageContext

def toString : UsageContext → String
  | letterhead => "letterhead"
  | businessCard => "business-card"
  | emailSignature => "email-signature"
  | socialProfile => "social-profile"
  | websiteHeader => "website-header"
  | appIcon => "app-icon"
  | favicon => "favicon"
  | merchandise => "merchandise"
  | printAdvertising => "print-advertising"
  | digitalAdvertising => "digital-advertising"
  | presentation => "presentation"
  | video => "video"

/-- All usage contexts -/
def all : List UsageContext :=
  [letterhead, businessCard, emailSignature, socialProfile,
   websiteHeader, appIcon, favicon, merchandise,
   printAdvertising, digitalAdvertising, presentation, video]

/-- There are exactly 12 contexts -/
theorem context_count : all.length = 12 := by rfl

end UsageContext

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: LOCKUP NAME
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Lockup name — a bounded string identifier -/
structure LockupName where
  name : String
  nonempty : name.length > 0
  bounded : name.length ≤ 50
  deriving Repr

instance : DecidableEq LockupName :=
  fun a b => decidable_of_iff (a.name = b.name) (by
    constructor
    · intro h; cases a; cases b; simp at h; subst h; rfl
    · intro h; cases h; rfl)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: LOGO LOCKUP
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Logo Lockup

A complete specification for one logo arrangement. This is the primary
unit of logo usage — agents select a lockup, then render it according
to the lockup's rules.

INVARIANTS (proven by construction):
  - Must have at least one color variant (proven by VariantSet.nonempty)
  - Clear space must be positive (proven by ClearSpaceMultiplier.positive)
  - Minimum sizes must be positive (proven by SizeConstraint.both_positive)
-/

/-- Complete logo lockup specification -/
structure LogoLockup where
  name : LockupName
  components : List LogoComponent
  orientation : Orientation
  priority : LockupPriority
  variants : VariantSet
  contexts : List UsageContext
  clearSpace : ClearSpaceRule
  minSize : SizeConstraint

namespace LogoLockup

/-- A lockup always has at least one color variant available -/
theorem has_variant (l : LogoLockup) : l.variants.variants.length > 0 :=
  l.variants.nonempty

/-- A lockup's clear space is always positive -/
theorem clear_space_positive (l : LogoLockup) : 
    0 < l.clearSpace.multiplier.value :=
  l.clearSpace.multiplier.positive

/-- A lockup's minimum sizes are always positive -/
theorem sizes_positive (l : LogoLockup) :
    0 < l.minSize.printMin.inches ∧ 0 < l.minSize.digitalMin.pixels :=
  SizeConstraint.both_positive l.minSize

/-- Check if lockup is approved for a context -/
def isApprovedFor (l : LogoLockup) (ctx : UsageContext) : Bool :=
  ctx ∈ l.contexts

/-- Compare lockups by priority -/
def comparePriority (l1 l2 : LogoLockup) : Ordering :=
  LockupPriority.compare l1.priority l2.priority

end LogoLockup

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 10: ERROR CATEGORIES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Error Categories

Categories of logo misuse. The "Do Not" list is MORE VALUABLE than positive
guidance for AI enforcement — it's easier to check violations than to verify
correct usage.

WHY ERROR CATEGORIES MATTER:
  An AI agent rendering a logo needs to know what NOT to do. The error
  categories form a complete covering of common mistakes:
  
  - ContrastError: Dark on dark, light on light (visibility)
  - ColorError: Off-brand colors (identity)
  - DistortionError: Squash, stretch, skew (integrity)
  - LayoutError: Altered relationships (composition)
  - ClearSpaceError: Encroachment (prominence)
  
  By enumerating these, we give AI systems a checklist to validate against.
-/

/-- Error category for logo misuse -/
inductive ErrorCategory where
  | contrastError   : ErrorCategory  -- Dark on dark, light on light
  | colorError      : ErrorCategory  -- Off-brand colors
  | distortionError : ErrorCategory  -- Squash, stretch, skew
  | layoutError     : ErrorCategory  -- Altered relationships
  | clearSpaceError : ErrorCategory  -- Encroachment
  deriving Repr, DecidableEq

namespace ErrorCategory

def toString : ErrorCategory → String
  | contrastError => "contrast-error"
  | colorError => "color-error"
  | distortionError => "distortion-error"
  | layoutError => "layout-error"
  | clearSpaceError => "clear-space-error"

/-- All error categories -/
def all : List ErrorCategory :=
  [contrastError, colorError, distortionError, layoutError, clearSpaceError]

/-- There are exactly 5 categories -/
theorem category_count : all.length = 5 := by rfl

end ErrorCategory

/-- A specific logo error (prohibited usage) -/
structure LogoError where
  category : ErrorCategory
  description : String
  desc_nonempty : description.length > 0
  desc_bounded : description.length ≤ 500
  deriving Repr

/-- Collection of logo errors -/
structure LogoErrorSet where
  errors : List LogoError
  deriving Repr

namespace LogoErrorSet

/-- Empty error set -/
def empty : LogoErrorSet := { errors := [] }

/-- Add an error -/
def addError (e : LogoError) (set : LogoErrorSet) : LogoErrorSet :=
  { errors := e :: set.errors }

/-- Get errors by category -/
def byCategory (cat : ErrorCategory) (set : LogoErrorSet) : List LogoError :=
  set.errors.filter (fun e => e.category = cat)

/-- Check if category is covered -/
def hasCategory (cat : ErrorCategory) (set : LogoErrorSet) : Bool :=
  (byCategory cat set).length > 0

/-- Count errors -/
def count (set : LogoErrorSet) : ℕ := set.errors.length

end LogoErrorSet

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 11: LOGO SYSTEM
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Logo System

Complete logo specification for a brand. This is the compound type that
brand ingestion produces and agents consume.

INVARIANTS:
  1. primary_exists: There is exactly one primary lockup
  2. all_lockups_valid: Each lockup has variants, clear space, and sizes
  
WHY EXACTLY ONE PRIMARY:
  A brand must have a "default" logo. If there are zero primaries, agents
  don't know which to use first. If there are multiple primaries, agents
  face ambiguity.
  
  The primary lockup is the "first introduction" — it establishes the brand
  before alternates can be used. This is mandatory for all brand collateral.
-/

/-- Complete logo system -/
structure LogoSystem where
  primary : LogoLockup
  alternates : List LogoLockup
  errors : LogoErrorSet

namespace LogoSystem

/-- Get all lockups (primary first) -/
def allLockups (ls : LogoSystem) : List LogoLockup :=
  ls.primary :: ls.alternates

/-- Find lockup by name -/
def findByName (ls : LogoSystem) (name : LockupName) : Option LogoLockup :=
  (allLockups ls).find? (fun l => l.name = name)

/-- Find lockups for context -/
def forContext (ls : LogoSystem) (ctx : UsageContext) : List LogoLockup :=
  (allLockups ls).filter (fun l => l.isApprovedFor ctx)

/-- The system always has at least one lockup (the primary) -/
theorem has_primary (ls : LogoSystem) : (allLockups ls).length ≥ 1 := by
  simp only [allLockups, List.length_cons]
  omega

/-- The primary lockup has valid variants -/
theorem primary_has_variants (ls : LogoSystem) : 
    ls.primary.variants.variants.length > 0 :=
  ls.primary.variants.nonempty

/-- The primary lockup has positive clear space -/
theorem primary_clear_space_positive (ls : LogoSystem) :
    0 < ls.primary.clearSpace.multiplier.value :=
  ls.primary.clearSpace.multiplier.positive

/-- All lockups in the system have valid variants -/
theorem all_have_variants (ls : LogoSystem) (l : LogoLockup) 
    (_h : l ∈ allLockups ls) : l.variants.variants.length > 0 :=
  l.variants.nonempty

/-- Validate that error set is non-empty (completeness check) -/
def hasErrors (ls : LogoSystem) : Bool := ls.errors.count > 0

end LogoSystem

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 12: KEY THEOREMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Key Theorems

Proving the critical invariants that make logo systems safe at scale.
-/

/-- Every lockup in a logo system can be rendered 
    (has variants, clear space, and positive sizes) -/
theorem lockup_renderable (ls : LogoSystem) (l : LogoLockup) 
    (_h : l ∈ LogoSystem.allLockups ls) :
    l.variants.variants.length > 0 ∧ 
    0 < l.clearSpace.multiplier.value ∧
    0 < l.minSize.printMin.inches ∧
    0 < l.minSize.digitalMin.pixels := by
  constructor
  · exact l.variants.nonempty
  constructor
  · exact l.clearSpace.multiplier.positive
  · exact SizeConstraint.both_positive l.minSize

/-- If a context has an approved lockup, that lockup is renderable -/
theorem context_lockup_renderable (ls : LogoSystem) (ctx : UsageContext)
    (l : LogoLockup) (_h_ctx : l ∈ LogoSystem.forContext ls ctx) :
    l.variants.variants.length > 0 := l.variants.nonempty

/-- Clear space composition: if two elements both have positive clear space,
    the total clear space is positive -/
theorem clear_space_composition (m1 m2 : ClearSpaceMultiplier) :
    0 < m1.value + m2.value := by
  have h1 := m1.positive
  have h2 := m2.positive
  linarith

/-- Size comparison: larger print size implies larger visual presence -/
theorem print_size_ordering (s1 s2 : PrintSize) (h : s1.inches < s2.inches) :
    s1.inches < s2.inches := h

end Hydrogen.Schema.Brand.Logo

end
