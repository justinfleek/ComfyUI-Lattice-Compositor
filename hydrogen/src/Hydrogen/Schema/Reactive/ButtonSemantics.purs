-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // reactive // button-semantics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonSemantics - semantic purpose taxonomy for button elements.
-- |
-- | Distinguishes WHAT a button DOES (purpose) from HOW it LOOKS (variant).
-- | A PlayButton and a CTAButton have different semantic roles, accessibility
-- | requirements, and interaction patterns — regardless of visual styling.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale, agents must reason about button PURPOSE:
-- | - "Find the play button" vs "Find the submit button"
-- | - "All media controls should have consistent behavior"
-- | - "Danger actions require confirmation patterns"
-- |
-- | Visual styling (Primary/Secondary/Ghost) is orthogonal to semantic purpose.

module Hydrogen.Schema.Reactive.ButtonSemantics
  ( -- * Button Purpose (What it does)
    ButtonPurpose
      ( ActionButton
      , FormSubmit
      , FormReset
      , NavigationButton
      , MediaControl
      , ToggleControl
      , MenuTrigger
      , DialogTrigger
      , DisclosureTrigger
      , DangerAction
      , IconAction
      , FloatingAction
      )
  -- * Constructor Helpers
  , actionButton
  , formSubmit
  , formReset
  , navigationButton
  , mediaControl
  , toggleControl
  , menuTrigger
  , dialogTrigger
  , disclosureTrigger
  , dangerAction
  , iconAction
  , floatingAction
  -- * ARIA Role Mapping
  , ariaRole
  , htmlType
  , requiresAriaLabel
  -- * Toggle State (for ToggleControl buttons)
  , ToggleState
      ( Pressed
      , Unpressed
      , Mixed
      )
  , pressed
  , unpressed
  , mixed
  , isPressed
  , toggleStateToAria
  -- * Popup Type (for MenuTrigger/DialogTrigger buttons)
  , PopupType
      ( MenuPopup
      , ListboxPopup
      , TreePopup
      , GridPopup
      , DialogPopup
      )
  , menuPopup
  , listboxPopup
  , treePopup
  , gridPopup
  , dialogPopup
  , popupTypeToAria
  -- * Button Identity (UUID5)
  , ButtonIdentity
  , buttonIdentity
  , buttonId
  , buttonIdString
  -- * Media Action (for MediaControl buttons)
  , MediaAction
      ( PlayAction
      , PauseAction
      , StopAction
      , SkipForwardAction
      , SkipBackwardAction
      , FastForwardAction
      , RewindAction
      , NextTrackAction
      , PreviousTrackAction
      , MuteAction
      , UnmuteAction
      , VolumeUpAction
      , VolumeDownAction
      , FullscreenAction
      , ExitFullscreenAction
      , PictureInPictureAction
      , ClosedCaptionsAction
      , SettingsAction
      , RecordAction
      , LiveAction
      )
  , playAction
  , pauseAction
  , stopAction
  , skipForwardAction
  , skipBackwardAction
  , fastForwardAction
  , rewindAction
  , nextTrackAction
  , previousTrackAction
  , muteAction
  , unmuteAction
  , volumeUpAction
  , volumeDownAction
  , fullscreenAction
  , exitFullscreenAction
  , pictureInPictureAction
  , closedCaptionsAction
  , settingsAction
  , recordAction
  , liveAction
  , mediaActionLabel
  ) where

import Data.Maybe (Maybe(Just, Nothing))

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // button purpose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic purpose of a button — WHAT it does, not HOW it looks.
-- |
-- | This is orthogonal to visual styling (Primary/Secondary/etc).
-- | A MediaControl can be styled as Primary or Ghost.
-- | A FormSubmit can be styled as Destructive or Outline.
data ButtonPurpose
  = ActionButton       -- ^ General action trigger ("Save", "Continue", "Apply")
  | FormSubmit         -- ^ Form submission (HTML submit semantics)
  | FormReset          -- ^ Form reset (HTML reset semantics)
  | NavigationButton   -- ^ Navigation trigger (link-like, changes route)
  | MediaControl       -- ^ Media playback control (play/pause/stop/skip)
  | ToggleControl      -- ^ Stateful toggle (on/off, pressed/unpressed)
  | MenuTrigger        -- ^ Opens dropdown/menu (has popup indicator)
  | DialogTrigger      -- ^ Opens modal/dialog
  | DisclosureTrigger  -- ^ Expands/collapses content (accordion, details)
  | DangerAction       -- ^ Destructive action requiring confirmation
  | IconAction         -- ^ Icon-only action (edit, delete, copy, share)
  | FloatingAction     -- ^ FAB - prominent floating action button

derive instance eqButtonPurpose :: Eq ButtonPurpose
derive instance ordButtonPurpose :: Ord ButtonPurpose

instance showButtonPurpose :: Show ButtonPurpose where
  show ActionButton = "action"
  show FormSubmit = "submit"
  show FormReset = "reset"
  show NavigationButton = "navigation"
  show MediaControl = "media"
  show ToggleControl = "toggle"
  show MenuTrigger = "menu"
  show DialogTrigger = "dialog"
  show DisclosureTrigger = "disclosure"
  show DangerAction = "danger"
  show IconAction = "icon"
  show FloatingAction = "fab"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // constructor helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | General action trigger ("Save", "Continue", "Apply")
actionButton :: ButtonPurpose
actionButton = ActionButton

-- | Form submission (HTML submit semantics)
formSubmit :: ButtonPurpose
formSubmit = FormSubmit

-- | Form reset (HTML reset semantics)
formReset :: ButtonPurpose
formReset = FormReset

-- | Navigation trigger (link-like, changes route)
navigationButton :: ButtonPurpose
navigationButton = NavigationButton

-- | Media playback control (play/pause/stop/skip)
mediaControl :: ButtonPurpose
mediaControl = MediaControl

-- | Stateful toggle (on/off, pressed/unpressed)
toggleControl :: ButtonPurpose
toggleControl = ToggleControl

-- | Opens dropdown/menu (has popup indicator)
menuTrigger :: ButtonPurpose
menuTrigger = MenuTrigger

-- | Opens modal/dialog
dialogTrigger :: ButtonPurpose
dialogTrigger = DialogTrigger

-- | Expands/collapses content (accordion, details)
disclosureTrigger :: ButtonPurpose
disclosureTrigger = DisclosureTrigger

-- | Destructive action requiring confirmation
dangerAction :: ButtonPurpose
dangerAction = DangerAction

-- | Icon-only action (edit, delete, copy, share)
iconAction :: ButtonPurpose
iconAction = IconAction

-- | FAB - prominent floating action button
floatingAction :: ButtonPurpose
floatingAction = FloatingAction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // aria role mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the appropriate ARIA role for a button purpose.
-- |
-- | Returns Nothing when the default button role is correct.
-- | Returns Just role when an explicit role override is needed.
ariaRole :: ButtonPurpose -> Maybe String
ariaRole ActionButton = Nothing           -- default button role
ariaRole FormSubmit = Nothing             -- default button role
ariaRole FormReset = Nothing              -- default button role
ariaRole NavigationButton = Just "link"   -- link semantics
ariaRole MediaControl = Nothing           -- default button role
ariaRole ToggleControl = Just "switch"    -- toggle semantics (or use aria-pressed)
ariaRole MenuTrigger = Nothing            -- uses aria-haspopup instead
ariaRole DialogTrigger = Nothing          -- uses aria-haspopup instead
ariaRole DisclosureTrigger = Nothing      -- uses aria-expanded instead
ariaRole DangerAction = Nothing           -- default button role
ariaRole IconAction = Nothing             -- default button role
ariaRole FloatingAction = Nothing         -- default button role

-- | Get the HTML button type attribute value.
-- |
-- | Returns the appropriate type for form semantics.
htmlType :: ButtonPurpose -> String
htmlType FormSubmit = "submit"
htmlType FormReset = "reset"
htmlType _ = "button"

-- | Does this button purpose require an aria-label?
-- |
-- | Icon-only buttons MUST have aria-label for accessibility.
-- | Media controls often need labels describing current action.
requiresAriaLabel :: ButtonPurpose -> Boolean
requiresAriaLabel IconAction = true
requiresAriaLabel MediaControl = true     -- "Play", "Pause", "Stop", etc.
requiresAriaLabel FloatingAction = true   -- FABs are typically icon-only
requiresAriaLabel _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // toggle state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toggle button state for aria-pressed attribute.
-- |
-- | Used with ToggleControl buttons to indicate on/off state.
-- | Maps directly to aria-pressed values: "true", "false", "mixed".
data ToggleState
  = Pressed    -- ^ Toggle is on (aria-pressed="true")
  | Unpressed  -- ^ Toggle is off (aria-pressed="false")
  | Mixed      -- ^ Indeterminate state (aria-pressed="mixed")

derive instance eqToggleState :: Eq ToggleState
derive instance ordToggleState :: Ord ToggleState

instance showToggleState :: Show ToggleState where
  show Pressed = "pressed"
  show Unpressed = "unpressed"
  show Mixed = "mixed"

-- | Toggle is on
pressed :: ToggleState
pressed = Pressed

-- | Toggle is off
unpressed :: ToggleState
unpressed = Unpressed

-- | Indeterminate state (e.g., "Select All" when some items selected)
mixed :: ToggleState
mixed = Mixed

-- | Is the toggle currently pressed/on?
isPressed :: ToggleState -> Boolean
isPressed Pressed = true
isPressed _ = false

-- | Convert toggle state to aria-pressed attribute value.
toggleStateToAria :: ToggleState -> String
toggleStateToAria Pressed = "true"
toggleStateToAria Unpressed = "false"
toggleStateToAria Mixed = "mixed"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // popup type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of popup triggered by a button (aria-haspopup values).
-- |
-- | Used with MenuTrigger and DialogTrigger buttons to indicate
-- | what kind of popup will appear when activated.
data PopupType
  = MenuPopup     -- ^ Standard dropdown menu (aria-haspopup="menu")
  | ListboxPopup  -- ^ Listbox/select dropdown (aria-haspopup="listbox")
  | TreePopup     -- ^ Tree widget popup (aria-haspopup="tree")
  | GridPopup     -- ^ Grid widget popup (aria-haspopup="grid")
  | DialogPopup   -- ^ Modal dialog (aria-haspopup="dialog")

derive instance eqPopupType :: Eq PopupType
derive instance ordPopupType :: Ord PopupType

instance showPopupType :: Show PopupType where
  show MenuPopup = "menu"
  show ListboxPopup = "listbox"
  show TreePopup = "tree"
  show GridPopup = "grid"
  show DialogPopup = "dialog"

-- | Standard dropdown menu
menuPopup :: PopupType
menuPopup = MenuPopup

-- | Listbox/select dropdown
listboxPopup :: PopupType
listboxPopup = ListboxPopup

-- | Tree widget popup
treePopup :: PopupType
treePopup = TreePopup

-- | Grid widget popup
gridPopup :: PopupType
gridPopup = GridPopup

-- | Modal dialog
dialogPopup :: PopupType
dialogPopup = DialogPopup

-- | Convert popup type to aria-haspopup attribute value.
popupTypeToAria :: PopupType -> String
popupTypeToAria MenuPopup = "menu"
popupTypeToAria ListboxPopup = "listbox"
popupTypeToAria TreePopup = "tree"
popupTypeToAria GridPopup = "grid"
popupTypeToAria DialogPopup = "dialog"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // button identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deterministic button identity for billion-agent scale.
-- |
-- | Same semantic configuration → same UUID5. Two agents creating
-- | identical buttons get identical identifiers.
-- |
-- | Identity is derived from:
-- | - Purpose (what the button does)
-- | - Label (text or aria-label)
-- | - Optional toggle state
-- | - Optional popup type
type ButtonIdentity =
  { purpose :: ButtonPurpose
  , label :: String
  , toggleState :: Maybe ToggleState
  , popupType :: Maybe PopupType
  }

-- | Create a button identity record.
buttonIdentity 
  :: ButtonPurpose 
  -> String 
  -> Maybe ToggleState 
  -> Maybe PopupType 
  -> ButtonIdentity
buttonIdentity purpose label toggleState popupType =
  { purpose
  , label
  , toggleState
  , popupType
  }

-- | Generate deterministic UUID5 from button identity.
-- |
-- | Same identity → same UUID5. Always. Everywhere.
-- | Enables deduplication, caching, and coordination at scale.
buttonId :: ButtonIdentity -> UUID5.UUID5
buttonId identity =
  let
    -- Serialize identity to canonical string
    canonical = serializeIdentity identity
  in
    UUID5.uuid5 UUID5.nsButton canonical

-- | Get button UUID5 as string (36 chars with dashes).
buttonIdString :: ButtonIdentity -> String
buttonIdString identity = UUID5.toString (buttonId identity)

-- | Serialize button identity to canonical string for hashing.
-- |
-- | Format: purpose|label|toggle|popup
-- | Deterministic serialization ensures identical inputs → identical UUIDs.
serializeIdentity :: ButtonIdentity -> String
serializeIdentity identity =
  show identity.purpose
    <> "|"
    <> identity.label
    <> "|"
    <> serializeToggle identity.toggleState
    <> "|"
    <> serializePopup identity.popupType

-- | Serialize optional toggle state.
serializeToggle :: Maybe ToggleState -> String
serializeToggle Nothing = "none"
serializeToggle (Just state) = show state

-- | Serialize optional popup type.
serializePopup :: Maybe PopupType -> String
serializePopup Nothing = "none"
serializePopup (Just popup) = show popup

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // media action
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specific media control actions for MediaControl buttons.
-- |
-- | A MediaControl button has a specific action it performs.
-- | This determines the appropriate icon and aria-label.
data MediaAction
  = PlayAction             -- ^ Start/resume playback
  | PauseAction            -- ^ Pause playback
  | StopAction             -- ^ Stop and reset to beginning
  | SkipForwardAction      -- ^ Skip forward (10s, 30s, etc.)
  | SkipBackwardAction     -- ^ Skip backward (10s, 30s, etc.)
  | FastForwardAction      -- ^ Fast forward (2x, 4x, etc.)
  | RewindAction           -- ^ Rewind (2x, 4x, etc.)
  | NextTrackAction        -- ^ Next track/chapter
  | PreviousTrackAction    -- ^ Previous track/chapter
  | MuteAction             -- ^ Mute audio
  | UnmuteAction           -- ^ Unmute audio
  | VolumeUpAction         -- ^ Increase volume
  | VolumeDownAction       -- ^ Decrease volume
  | FullscreenAction       -- ^ Enter fullscreen
  | ExitFullscreenAction   -- ^ Exit fullscreen
  | PictureInPictureAction -- ^ Toggle picture-in-picture
  | ClosedCaptionsAction   -- ^ Toggle closed captions
  | SettingsAction         -- ^ Open playback settings
  | RecordAction           -- ^ Start recording
  | LiveAction             -- ^ Jump to live (for live streams)

derive instance eqMediaAction :: Eq MediaAction
derive instance ordMediaAction :: Ord MediaAction

instance showMediaAction :: Show MediaAction where
  show PlayAction = "play"
  show PauseAction = "pause"
  show StopAction = "stop"
  show SkipForwardAction = "skip-forward"
  show SkipBackwardAction = "skip-backward"
  show FastForwardAction = "fast-forward"
  show RewindAction = "rewind"
  show NextTrackAction = "next-track"
  show PreviousTrackAction = "previous-track"
  show MuteAction = "mute"
  show UnmuteAction = "unmute"
  show VolumeUpAction = "volume-up"
  show VolumeDownAction = "volume-down"
  show FullscreenAction = "fullscreen"
  show ExitFullscreenAction = "exit-fullscreen"
  show PictureInPictureAction = "picture-in-picture"
  show ClosedCaptionsAction = "closed-captions"
  show SettingsAction = "settings"
  show RecordAction = "record"
  show LiveAction = "live"

-- | Start/resume playback
playAction :: MediaAction
playAction = PlayAction

-- | Pause playback
pauseAction :: MediaAction
pauseAction = PauseAction

-- | Stop and reset to beginning
stopAction :: MediaAction
stopAction = StopAction

-- | Skip forward (10s, 30s, etc.)
skipForwardAction :: MediaAction
skipForwardAction = SkipForwardAction

-- | Skip backward (10s, 30s, etc.)
skipBackwardAction :: MediaAction
skipBackwardAction = SkipBackwardAction

-- | Fast forward (2x, 4x, etc.)
fastForwardAction :: MediaAction
fastForwardAction = FastForwardAction

-- | Rewind (2x, 4x, etc.)
rewindAction :: MediaAction
rewindAction = RewindAction

-- | Next track/chapter
nextTrackAction :: MediaAction
nextTrackAction = NextTrackAction

-- | Previous track/chapter
previousTrackAction :: MediaAction
previousTrackAction = PreviousTrackAction

-- | Mute audio
muteAction :: MediaAction
muteAction = MuteAction

-- | Unmute audio
unmuteAction :: MediaAction
unmuteAction = UnmuteAction

-- | Increase volume
volumeUpAction :: MediaAction
volumeUpAction = VolumeUpAction

-- | Decrease volume
volumeDownAction :: MediaAction
volumeDownAction = VolumeDownAction

-- | Enter fullscreen
fullscreenAction :: MediaAction
fullscreenAction = FullscreenAction

-- | Exit fullscreen
exitFullscreenAction :: MediaAction
exitFullscreenAction = ExitFullscreenAction

-- | Toggle picture-in-picture
pictureInPictureAction :: MediaAction
pictureInPictureAction = PictureInPictureAction

-- | Toggle closed captions
closedCaptionsAction :: MediaAction
closedCaptionsAction = ClosedCaptionsAction

-- | Open playback settings
settingsAction :: MediaAction
settingsAction = SettingsAction

-- | Start recording
recordAction :: MediaAction
recordAction = RecordAction

-- | Jump to live (for live streams)
liveAction :: MediaAction
liveAction = LiveAction

-- | Get the standard aria-label for a media action.
-- |
-- | Provides accessible labels for screen readers.
mediaActionLabel :: MediaAction -> String
mediaActionLabel PlayAction = "Play"
mediaActionLabel PauseAction = "Pause"
mediaActionLabel StopAction = "Stop"
mediaActionLabel SkipForwardAction = "Skip forward"
mediaActionLabel SkipBackwardAction = "Skip backward"
mediaActionLabel FastForwardAction = "Fast forward"
mediaActionLabel RewindAction = "Rewind"
mediaActionLabel NextTrackAction = "Next track"
mediaActionLabel PreviousTrackAction = "Previous track"
mediaActionLabel MuteAction = "Mute"
mediaActionLabel UnmuteAction = "Unmute"
mediaActionLabel VolumeUpAction = "Volume up"
mediaActionLabel VolumeDownAction = "Volume down"
mediaActionLabel FullscreenAction = "Enter fullscreen"
mediaActionLabel ExitFullscreenAction = "Exit fullscreen"
mediaActionLabel PictureInPictureAction = "Picture in picture"
mediaActionLabel ClosedCaptionsAction = "Closed captions"
mediaActionLabel SettingsAction = "Settings"
mediaActionLabel RecordAction = "Record"
mediaActionLabel LiveAction = "Go to live"
