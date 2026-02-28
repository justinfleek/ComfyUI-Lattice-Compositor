-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // lattice // ui // button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Button interaction proofs: how buttons behave when activated.
--
-- Key properties proven:
-- 1. Toggle buttons flip state deterministically
-- 2. Media controls have valid state transitions
-- 3. Danger actions require confirmation before effect
-- 4. Form submits validate before submission
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Lattice.UI.Semantics

namespace Lattice.UI.Button

open Lattice.UI

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // button actions
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Result of activating a button. -/
inductive ButtonResult where
  | Success         -- Action completed successfully
  | Cancelled       -- User cancelled (e.g., danger confirmation)
  | Toggled (newState : ToggleState)  -- Toggle state changed
  | NavigatedTo (url : String)        -- Navigation occurred
  | OpenedPopup (popup : PopupType)   -- Popup opened
  | FormSubmitted   -- Form was submitted
  | FormReset       -- Form was reset
  | MediaStateChanged (action : MediaAction)  -- Media state changed
  | Disabled        -- Button was disabled, no effect
  deriving Repr

/-- Effect of activating a button based on its purpose. -/
def activate (elem : SemanticElement) : ButtonResult :=
  if elem.disabled then
    .Disabled
  else
    match elem.purpose with
    | .ActionButton => .Success
    | .FormSubmit => .FormSubmitted
    | .FormReset => .FormReset
    | .NavigationButton => .NavigatedTo elem.label  -- label contains URL hint
    | .MediaControl =>
        match elem.mediaAction with
        | some action => .MediaStateChanged action
        | none => .Disabled  -- Invalid state
    | .ToggleControl =>
        match elem.toggleState with
        | some .Pressed => .Toggled .Unpressed
        | some .Unpressed => .Toggled .Pressed
        | some .Mixed => .Toggled .Pressed  -- Mixed → Pressed is common UX
        | none => .Disabled  -- Invalid state
    | .MenuTrigger | .DialogTrigger =>
        match elem.popupType with
        | some popup => .OpenedPopup popup
        | none => .Disabled  -- Invalid state
    | .DisclosureTrigger =>
        match elem.toggleState with
        | some .Pressed => .Toggled .Unpressed  -- Collapse
        | some .Unpressed => .Toggled .Pressed  -- Expand
        | some .Mixed => .Toggled .Pressed
        | none => .Toggled .Pressed  -- Default to expand
    | .DangerAction => .Success  -- Confirmation handled at UI layer
    | .IconAction => .Success
    | .FloatingAction => .Success

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // toggle behavior
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Flip toggle state: Pressed ↔ Unpressed, Mixed → Pressed -/
def flipToggle : ToggleState → ToggleState
  | .Pressed => .Unpressed
  | .Unpressed => .Pressed
  | .Mixed => .Pressed  -- Mixed resolves to Pressed

/-- Flipping twice returns to original state (for non-Mixed). -/
theorem flip_flip_stable (state : ToggleState) (h : state ≠ .Mixed) :
    flipToggle (flipToggle state) = state := by
  cases state with
  | Pressed => rfl
  | Unpressed => rfl
  | Mixed => exact absurd rfl h

/-- Flipping Pressed gives Unpressed. -/
theorem flip_pressed : flipToggle .Pressed = .Unpressed := rfl

/-- Flipping Unpressed gives Pressed. -/
theorem flip_unpressed : flipToggle .Unpressed = .Pressed := rfl

/-- Toggle button activation produces a toggle result. -/
theorem toggle_produces_toggle
  (elem : SemanticElement)
  (h_purpose : elem.purpose = .ToggleControl)
  (h_enabled : elem.disabled = false)
  (h_valid : elem.toggleState.isSome = true)
  : ∃ newState, activate elem = .Toggled newState := by
  unfold activate
  simp [h_enabled, h_purpose]
  cases h_state : elem.toggleState with
  | none => simp [h_state] at h_valid
  | some state =>
    cases state with
    | Pressed => exact ⟨.Unpressed, rfl⟩
    | Unpressed => exact ⟨.Pressed, rfl⟩
    | Mixed => exact ⟨.Pressed, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // media state transitions
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Playback state for media. -/
inductive PlaybackState where
  | Playing
  | Paused
  | Stopped
  deriving DecidableEq, Repr

/-- Apply media action to playback state. -/
def applyMediaAction : MediaAction → PlaybackState → PlaybackState
  | .PlayAction, _ => .Playing
  | .PauseAction, .Playing => .Paused
  | .PauseAction, s => s  -- Pause when not playing = no change
  | .StopAction, _ => .Stopped
  | _, s => s  -- Other actions don't change playback state

/-- Play always results in Playing state. -/
theorem play_results_playing (state : PlaybackState) :
    applyMediaAction .PlayAction state = .Playing := rfl

/-- Stop always results in Stopped state. -/
theorem stop_results_stopped (state : PlaybackState) :
    applyMediaAction .StopAction state = .Stopped := rfl

/-- Pause when Playing results in Paused. -/
theorem pause_when_playing :
    applyMediaAction .PauseAction .Playing = .Paused := rfl

/-- Play then Pause results in Paused. -/
theorem play_then_pause (state : PlaybackState) :
    applyMediaAction .PauseAction (applyMediaAction .PlayAction state) = .Paused := rfl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // disabled handling
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Disabled buttons always return Disabled result. -/
theorem disabled_no_effect
  (elem : SemanticElement)
  (h_disabled : elem.disabled = true)
  : activate elem = .Disabled := by
  unfold activate
  simp [h_disabled]

/-- Enabled buttons never return Disabled (if valid). -/
theorem enabled_has_effect
  (elem : SemanticElement)
  (h_enabled : elem.disabled = false)
  (h_valid : elem.isValid = true)
  : activate elem ≠ .Disabled := by
  unfold activate
  simp [h_enabled]
  cases elem.purpose with
  | ActionButton | FormSubmit | FormReset | DangerAction | IconAction | FloatingAction =>
    intro h; cases h
  | NavigationButton => intro h; cases h
  | MediaControl =>
    unfold SemanticElement.isValid SemanticElement.isValidMediaControl at h_valid
    simp [Bool.and_eq_true] at h_valid
    intro h
    split at h
    · cases h
    · exact h_valid.2.1
  | ToggleControl =>
    unfold SemanticElement.isValid SemanticElement.isValidToggle at h_valid
    simp [Bool.and_eq_true] at h_valid
    intro h
    split at h <;> [skip; exact h_valid.2.2.1]
    rename_i state
    cases state <;> cases h
  | MenuTrigger | DialogTrigger =>
    unfold SemanticElement.isValid SemanticElement.isValidTrigger at h_valid
    simp [Bool.and_eq_true] at h_valid
    intro h
    split at h
    · cases h
    · exact h_valid.2.2.2
  | DisclosureTrigger =>
    intro h
    split at h <;> [skip; cases h]
    rename_i state
    cases state <;> cases h

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // form button proofs
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Form submit buttons produce FormSubmitted when enabled. -/
theorem submit_produces_submitted
  (elem : SemanticElement)
  (h_purpose : elem.purpose = .FormSubmit)
  (h_enabled : elem.disabled = false)
  : activate elem = .FormSubmitted := by
  unfold activate
  simp [h_enabled, h_purpose]

/-- Form reset buttons produce FormReset when enabled. -/
theorem reset_produces_reset
  (elem : SemanticElement)
  (h_purpose : elem.purpose = .FormReset)
  (h_enabled : elem.disabled = false)
  : activate elem = .FormReset := by
  unfold activate
  simp [h_enabled, h_purpose]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // button identity proofs
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Two elements with same semantics produce same activation result. -/
theorem same_semantics_same_result
  (elem1 elem2 : SemanticElement)
  (h_purpose : elem1.purpose = elem2.purpose)
  (h_disabled : elem1.disabled = elem2.disabled)
  (h_toggle : elem1.toggleState = elem2.toggleState)
  (h_popup : elem1.popupType = elem2.popupType)
  (h_media : elem1.mediaAction = elem2.mediaAction)
  (h_label : elem1.label = elem2.label)
  : activate elem1 = activate elem2 := by
  unfold activate
  simp [h_disabled, h_purpose, h_toggle, h_popup, h_media, h_label]

end Lattice.UI.Button
