-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // lattice // ui // semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--    "At billion-agent scale, agents must reason about button PURPOSE:
--     'Find the play button' vs 'Find the submit button'
--     'All media controls should have consistent behavior'"
--
--                                                        — ButtonSemantics.purs
--
-- Semantic UI types that let agents UNDERSTAND what UI elements DO.
-- This is NOT visual styling - it's the semantic meaning that enables:
-- - Agent navigation: "Click the submit button"
-- - Accessibility: Proper ARIA roles and labels
-- - Coordination: Multiple agents understanding the same UI
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Mathlib.Data.Finset.Basic
import Mathlib.Data.String.Basic

namespace Lattice.UI

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // button purpose
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Semantic purpose of a button — WHAT it does, not HOW it looks.

This is orthogonal to visual styling (Primary/Secondary/etc).
A MediaControl can be styled as Primary or Ghost.
A FormSubmit can be styled as Destructive or Outline.

At billion-agent scale, this semantic tagging lets agents:
- Find buttons by purpose: "Click play" → find MediaControl with PlayAction
- Understand consequences: DangerAction requires confirmation
- Apply consistent patterns: All ToggleControls support aria-pressed -/
inductive ButtonPurpose where
  | ActionButton       -- General action trigger ("Save", "Continue", "Apply")
  | FormSubmit         -- Form submission (HTML submit semantics)
  | FormReset          -- Form reset (HTML reset semantics)
  | NavigationButton   -- Navigation trigger (link-like, changes route)
  | MediaControl       -- Media playback control (play/pause/stop/skip)
  | ToggleControl      -- Stateful toggle (on/off, pressed/unpressed)
  | MenuTrigger        -- Opens dropdown/menu (has popup indicator)
  | DialogTrigger      -- Opens modal/dialog
  | DisclosureTrigger  -- Expands/collapses content (accordion, details)
  | DangerAction       -- Destructive action requiring confirmation
  | IconAction         -- Icon-only action (edit, delete, copy, share)
  | FloatingAction     -- FAB - prominent floating action button
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // toggle state
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Toggle button state for aria-pressed attribute.

Used with ToggleControl buttons to indicate on/off state.
Maps directly to aria-pressed values: "true", "false", "mixed". -/
inductive ToggleState where
  | Pressed    -- Toggle is on (aria-pressed="true")
  | Unpressed  -- Toggle is off (aria-pressed="false")
  | Mixed      -- Indeterminate state (aria-pressed="mixed")
  deriving DecidableEq, Repr

/-- Is the toggle currently pressed/on? -/
def ToggleState.isPressed : ToggleState → Bool
  | .Pressed => true
  | _ => false

/-- Toggle state to ARIA string -/
def ToggleState.toAria : ToggleState → String
  | .Pressed => "true"
  | .Unpressed => "false"
  | .Mixed => "mixed"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // popup type
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Type of popup triggered by a button (aria-haspopup values).

Used with MenuTrigger and DialogTrigger buttons to indicate
what kind of popup will appear when activated. -/
inductive PopupType where
  | MenuPopup     -- Standard dropdown menu
  | ListboxPopup  -- Listbox/select dropdown
  | TreePopup     -- Tree widget popup
  | GridPopup     -- Grid widget popup
  | DialogPopup   -- Modal dialog
  deriving DecidableEq, Repr

/-- Popup type to ARIA string -/
def PopupType.toAria : PopupType → String
  | .MenuPopup => "menu"
  | .ListboxPopup => "listbox"
  | .TreePopup => "tree"
  | .GridPopup => "grid"
  | .DialogPopup => "dialog"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // media action
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Specific media control actions for MediaControl buttons.

A MediaControl button has a specific action it performs.
This determines the appropriate icon and aria-label.

At billion-agent scale, agents can:
- "Pause the video" → find MediaControl with PauseAction
- "Skip ahead" → find MediaControl with SkipForward
- Understand state transitions: Play ↔ Pause -/
inductive MediaAction where
  | PlayAction             -- Start/resume playback
  | PauseAction            -- Pause playback
  | StopAction             -- Stop and reset to beginning
  | SkipForwardAction      -- Skip forward (10s, 30s, etc.)
  | SkipBackwardAction     -- Skip backward (10s, 30s, etc.)
  | FastForwardAction      -- Fast forward (2x, 4x, etc.)
  | RewindAction           -- Rewind (2x, 4x, etc.)
  | NextTrackAction        -- Next track/chapter
  | PreviousTrackAction    -- Previous track/chapter
  | MuteAction             -- Mute audio
  | UnmuteAction           -- Unmute audio
  | VolumeUpAction         -- Increase volume
  | VolumeDownAction       -- Decrease volume
  | FullscreenAction       -- Enter fullscreen
  | ExitFullscreenAction   -- Exit fullscreen
  | PictureInPictureAction -- Toggle picture-in-picture
  | ClosedCaptionsAction   -- Toggle closed captions
  | SettingsAction         -- Open playback settings
  | RecordAction           -- Start recording
  | LiveAction             -- Jump to live (for live streams)
  deriving DecidableEq, Repr

/-- Get the standard aria-label for a media action. -/
def MediaAction.ariaLabel : MediaAction → String
  | .PlayAction => "Play"
  | .PauseAction => "Pause"
  | .StopAction => "Stop"
  | .SkipForwardAction => "Skip forward"
  | .SkipBackwardAction => "Skip backward"
  | .FastForwardAction => "Fast forward"
  | .RewindAction => "Rewind"
  | .NextTrackAction => "Next track"
  | .PreviousTrackAction => "Previous track"
  | .MuteAction => "Mute"
  | .UnmuteAction => "Unmute"
  | .VolumeUpAction => "Volume up"
  | .VolumeDownAction => "Volume down"
  | .FullscreenAction => "Enter fullscreen"
  | .ExitFullscreenAction => "Exit fullscreen"
  | .PictureInPictureAction => "Picture in picture"
  | .ClosedCaptionsAction => "Closed captions"
  | .SettingsAction => "Settings"
  | .RecordAction => "Record"
  | .LiveAction => "Go to live"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // aria mapping
-- ═══════════════════════════════════════════════════════════════════════════════

/-- ARIA role for a button purpose.

Returns none when the default button role is correct.
Returns some role when an explicit role override is needed. -/
def ButtonPurpose.ariaRole : ButtonPurpose → Option String
  | .ActionButton => none         -- default button role
  | .FormSubmit => none           -- default button role
  | .FormReset => none            -- default button role
  | .NavigationButton => some "link"  -- link semantics
  | .MediaControl => none         -- default button role
  | .ToggleControl => some "switch"   -- toggle semantics
  | .MenuTrigger => none          -- uses aria-haspopup instead
  | .DialogTrigger => none        -- uses aria-haspopup instead
  | .DisclosureTrigger => none    -- uses aria-expanded instead
  | .DangerAction => none         -- default button role
  | .IconAction => none           -- default button role
  | .FloatingAction => none       -- default button role

/-- HTML button type attribute value. -/
def ButtonPurpose.htmlType : ButtonPurpose → String
  | .FormSubmit => "submit"
  | .FormReset => "reset"
  | _ => "button"

/-- Does this button purpose require an aria-label?

Icon-only buttons MUST have aria-label for accessibility.
Media controls often need labels describing current action. -/
def ButtonPurpose.requiresAriaLabel : ButtonPurpose → Bool
  | .IconAction => true
  | .MediaControl => true     -- "Play", "Pause", "Stop", etc.
  | .FloatingAction => true   -- FABs are typically icon-only
  | _ => false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // element identity
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Unique element identifier (would be UUID5 in runtime).

At billion-agent scale, deterministic identity is critical:
- Same semantic configuration → same ID
- Two agents creating identical buttons get identical identifiers
- Enables deduplication, caching, and coordination -/
structure ElementId where
  value : Nat
  deriving DecidableEq, Repr

/-- UI element with semantic meaning.

This is the core type that bridges rendering to agent understanding.
An agent doesn't see "rectangle with text" - it sees "submit button for form X". -/
structure SemanticElement where
  id : ElementId
  purpose : ButtonPurpose
  label : String                    -- Text or aria-label
  toggleState : Option ToggleState  -- For ToggleControl
  popupType : Option PopupType      -- For Menu/Dialog triggers
  mediaAction : Option MediaAction  -- For MediaControl
  disabled : Bool                   -- Whether element is interactive
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // semantic properties
-- ═══════════════════════════════════════════════════════════════════════════════

/-- An element is accessible if it meets ARIA requirements. -/
def SemanticElement.isAccessible (elem : SemanticElement) : Bool :=
  -- If purpose requires aria-label, label must be non-empty
  if elem.purpose.requiresAriaLabel then
    elem.label.length > 0
  else
    true  -- Non-requiring purposes are accessible by default

/-- An element is operable by an agent if it's not disabled and accessible. -/
def SemanticElement.isOperable (elem : SemanticElement) : Bool :=
  !elem.disabled && elem.isAccessible

/-- MediaControl elements must have a mediaAction specified. -/
def SemanticElement.isValidMediaControl (elem : SemanticElement) : Bool :=
  match elem.purpose with
  | .MediaControl => elem.mediaAction.isSome
  | _ => true

/-- ToggleControl elements should have a toggleState specified. -/
def SemanticElement.isValidToggle (elem : SemanticElement) : Bool :=
  match elem.purpose with
  | .ToggleControl => elem.toggleState.isSome
  | _ => true

/-- MenuTrigger and DialogTrigger should specify popup type. -/
def SemanticElement.isValidTrigger (elem : SemanticElement) : Bool :=
  match elem.purpose with
  | .MenuTrigger | .DialogTrigger => elem.popupType.isSome
  | _ => true

/-- A fully valid semantic element meets all requirements. -/
def SemanticElement.isValid (elem : SemanticElement) : Bool :=
  elem.isAccessible &&
  elem.isValidMediaControl &&
  elem.isValidToggle &&
  elem.isValidTrigger

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // proofs
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Accessible elements with requiresAriaLabel have non-empty labels. -/
theorem accessible_requires_label
  (elem : SemanticElement)
  (h_accessible : elem.isAccessible = true)
  (h_requires : elem.purpose.requiresAriaLabel = true)
  : elem.label.length > 0 := by
  unfold SemanticElement.isAccessible at h_accessible
  simp [h_requires] at h_accessible
  exact h_accessible

/-- Operable elements are not disabled. -/
theorem operable_not_disabled
  (elem : SemanticElement)
  (h_operable : elem.isOperable = true)
  : elem.disabled = false := by
  unfold SemanticElement.isOperable at h_operable
  simp [Bool.and_eq_true] at h_operable
  exact Bool.not_eq_true'.mp h_operable.1

/-- Operable elements are accessible. -/
theorem operable_is_accessible
  (elem : SemanticElement)
  (h_operable : elem.isOperable = true)
  : elem.isAccessible = true := by
  unfold SemanticElement.isOperable at h_operable
  simp [Bool.and_eq_true] at h_operable
  exact h_operable.2

/-- Valid elements are accessible. -/
theorem valid_is_accessible
  (elem : SemanticElement)
  (h_valid : elem.isValid = true)
  : elem.isAccessible = true := by
  unfold SemanticElement.isValid at h_valid
  simp [Bool.and_eq_true] at h_valid
  exact h_valid.1

/-- All media actions have non-empty aria labels. -/
theorem media_action_has_label (action : MediaAction) : action.ariaLabel.length > 0 := by
  cases action <;> native_decide

/-- Toggle state aria representation is never empty. -/
theorem toggle_aria_nonempty (state : ToggleState) : state.toAria.length > 0 := by
  cases state <;> native_decide

/-- Popup type aria representation is never empty. -/
theorem popup_aria_nonempty (popup : PopupType) : popup.toAria.length > 0 := by
  cases popup <;> native_decide

end Lattice.UI
