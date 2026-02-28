-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // audio // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio accessibility atoms for inclusive design.
-- |
-- | ## Design Philosophy
-- |
-- | Accessibility is not an afterthought — it's a first-class concern. These
-- | atoms enable agents to build interfaces that are usable by people with
-- | visual, auditory, and cognitive differences.
-- |
-- | ## Screen Reader Support
-- | Structured content for screen readers: announcements, regions, live updates.
-- |
-- | ## Audio Descriptions
-- | Descriptive audio for visual content: images, charts, motion graphics.
-- |
-- | ## Sonification
-- | Data-to-sound mapping for eyes-free interfaces: earcons, auditory icons,
-- | parameter mapping.
-- |
-- | ## Auditory UI
-- | Non-visual interface elements: audio menus, spatial audio navigation.
-- |
-- | ## Usage
-- | ```purescript
-- | import Hydrogen.Schema.Audio.Accessibility as A11y
-- |
-- | -- Create an announcement
-- | announcement = A11y.announcement
-- |   A11y.PriorityHigh
-- |   A11y.PolitenessAssertive
-- |   "File upload complete"
-- | ```

module Hydrogen.Schema.Audio.Accessibility
  ( -- * Announcement Atoms
    AnnouncementPriority(..)
  , Politeness(..)
  , priorityName
  , politenessName
  
  -- * Announcement Molecule
  , Announcement
  , announcement
  , announcementQuiet
  
  -- * Live Region
  , LiveRegion
  , liveRegion
  , liveRegionPolite
  , liveRegionAssertive
  
  -- * Audio Description
  , DescriptionLength(..)
  , DescriptionContext(..)
  , AudioDescription
  , audioDescription
  , descriptionBrief
  , descriptionExtended
  
  -- * Earcon Types
  , EarconCategory(..)
  , earconCategoryName
  
  -- * Earcon Molecule
  , Earcon
  , earcon
  , earconSuccess
  , earconError
  , earconWarning
  , earconNotification
  
  -- * Auditory Icon
  , AuditoryIcon
  , auditoryIcon
  
  -- * Sonification Mapping
  , SonificationDimension(..)
  , SonificationScale(..)
  , SonificationMapping
  , sonificationMapping
  
  -- * Audio Cue
  , AudioCue(..)
  , audioCueName
  
  -- * Navigation Sound
  , NavigationSound
  , navigationSound
  , navSoundFocus
  , navSoundSelect
  , navSoundBack
  
  -- * Reading Speed
  , ReadingSpeed(..)
  , readingSpeed
  , unwrapReadingSpeed
  , readingSpeedSlow
  , readingSpeedNormal
  , readingSpeedFast
  
  -- * Bounds
  , readingSpeedBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , (<)
  , (>)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // announcement
-- ═════════════════════════════════════════════════════════════════════════════

-- | AnnouncementPriority - urgency level for screen reader announcements.
data AnnouncementPriority
  = PriorityLow       -- ^ Background info, can be skipped
  | PriorityMedium    -- ^ Standard notification
  | PriorityHigh      -- ^ Important, should interrupt
  | PriorityCritical  -- ^ Urgent, must be heard immediately

derive instance eqAnnouncementPriority :: Eq AnnouncementPriority
derive instance ordAnnouncementPriority :: Ord AnnouncementPriority

instance showAnnouncementPriority :: Show AnnouncementPriority where
  show = priorityName

-- | Get display name for priority
priorityName :: AnnouncementPriority -> String
priorityName PriorityLow = "Low"
priorityName PriorityMedium = "Medium"
priorityName PriorityHigh = "High"
priorityName PriorityCritical = "Critical"

-- | Politeness - ARIA live region politeness setting.
data Politeness
  = PolitenessOff        -- ^ No live updates
  | PolitenessPolite     -- ^ Announce when convenient
  | PolitenessAssertive  -- ^ Announce immediately

derive instance eqPoliteness :: Eq Politeness
derive instance ordPoliteness :: Ord Politeness

instance showPoliteness :: Show Politeness where
  show = politenessName

-- | Get display name for politeness
politenessName :: Politeness -> String
politenessName PolitenessOff = "off"
politenessName PolitenessPolite = "polite"
politenessName PolitenessAssertive = "assertive"

-- | Announcement - content for screen reader announcement.
type Announcement =
  { priority :: AnnouncementPriority
  , politeness :: Politeness
  , text :: String
  , clearPrevious :: Boolean   -- ^ Clear pending announcements
  }

-- | Create an announcement.
announcement :: AnnouncementPriority -> Politeness -> String -> Announcement
announcement p pol txt =
  { priority: p
  , politeness: pol
  , text: txt
  , clearPrevious: false
  }

-- | Create a quiet (polite, low priority) announcement.
announcementQuiet :: String -> Announcement
announcementQuiet txt =
  { priority: PriorityLow
  , politeness: PolitenessPolite
  , text: txt
  , clearPrevious: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // live region
-- ═════════════════════════════════════════════════════════════════════════════

-- | LiveRegion - ARIA live region configuration.
type LiveRegion =
  { id :: String
  , politeness :: Politeness
  , atomic :: Boolean         -- ^ Announce entire region vs. changes
  , relevant :: String        -- ^ "additions", "removals", "text", "all"
  }

-- | Create a live region.
liveRegion :: String -> Politeness -> LiveRegion
liveRegion regionId pol =
  { id: regionId
  , politeness: pol
  , atomic: false
  , relevant: "additions text"
  }

-- | Polite live region preset.
liveRegionPolite :: String -> LiveRegion
liveRegionPolite regionId =
  { id: regionId
  , politeness: PolitenessPolite
  , atomic: false
  , relevant: "additions text"
  }

-- | Assertive live region preset.
liveRegionAssertive :: String -> LiveRegion
liveRegionAssertive regionId =
  { id: regionId
  , politeness: PolitenessAssertive
  , atomic: true
  , relevant: "all"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // audio description
-- ═════════════════════════════════════════════════════════════════════════════

-- | DescriptionLength - verbosity of audio description.
data DescriptionLength
  = LengthBrief       -- ^ One sentence summary
  | LengthStandard    -- ^ Moderate detail
  | LengthExtended    -- ^ Full detail for complex content

derive instance eqDescriptionLength :: Eq DescriptionLength
derive instance ordDescriptionLength :: Ord DescriptionLength

instance showDescriptionLength :: Show DescriptionLength where
  show LengthBrief = "Brief"
  show LengthStandard = "Standard"
  show LengthExtended = "Extended"

-- | DescriptionContext - what type of content is being described.
data DescriptionContext
  = ContextImage      -- ^ Static image
  | ContextChart      -- ^ Data visualization
  | ContextVideo      -- ^ Video content
  | ContextAnimation  -- ^ Motion graphic
  | ContextIcon       -- ^ UI icon
  | ContextLayout     -- ^ Page/screen layout

derive instance eqDescriptionContext :: Eq DescriptionContext
derive instance ordDescriptionContext :: Ord DescriptionContext

instance showDescriptionContext :: Show DescriptionContext where
  show ContextImage = "Image"
  show ContextChart = "Chart"
  show ContextVideo = "Video"
  show ContextAnimation = "Animation"
  show ContextIcon = "Icon"
  show ContextLayout = "Layout"

-- | AudioDescription - descriptive audio for visual content.
type AudioDescription =
  { context :: DescriptionContext
  , length :: DescriptionLength
  , text :: String
  , alternativeText :: Maybe String  -- ^ Shorter alternative
  }

-- | Create an audio description.
audioDescription :: DescriptionContext -> DescriptionLength -> String -> AudioDescription
audioDescription ctx len txt =
  { context: ctx
  , length: len
  , text: txt
  , alternativeText: Nothing
  }

-- | Create a brief description.
descriptionBrief :: DescriptionContext -> String -> AudioDescription
descriptionBrief ctx txt =
  { context: ctx
  , length: LengthBrief
  , text: txt
  , alternativeText: Nothing
  }

-- | Create an extended description with alternative.
descriptionExtended :: DescriptionContext -> String -> String -> AudioDescription
descriptionExtended ctx full brief =
  { context: ctx
  , length: LengthExtended
  , text: full
  , alternativeText: Just brief
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // earcons
-- ═════════════════════════════════════════════════════════════════════════════

-- | EarconCategory - semantic category for non-verbal audio cues.
data EarconCategory
  = EarconSuccess     -- ^ Positive completion
  | EarconError       -- ^ Error/failure
  | EarconWarning     -- ^ Caution needed
  | EarconInfo        -- ^ Informational
  | EarconProgress    -- ^ Ongoing process
  | EarconComplete    -- ^ Process finished
  | EarconNotify      -- ^ Attention needed
  | EarconNavigate    -- ^ Navigation event

derive instance eqEarconCategory :: Eq EarconCategory
derive instance ordEarconCategory :: Ord EarconCategory

instance showEarconCategory :: Show EarconCategory where
  show = earconCategoryName

-- | Get display name for earcon category
earconCategoryName :: EarconCategory -> String
earconCategoryName EarconSuccess = "Success"
earconCategoryName EarconError = "Error"
earconCategoryName EarconWarning = "Warning"
earconCategoryName EarconInfo = "Info"
earconCategoryName EarconProgress = "Progress"
earconCategoryName EarconComplete = "Complete"
earconCategoryName EarconNotify = "Notify"
earconCategoryName EarconNavigate = "Navigate"

-- | Earcon - abstract auditory signal molecule.
type Earcon =
  { category :: EarconCategory
  , durationMs :: Number
  , volume :: Number           -- ^ 0.0 to 1.0
  , priority :: AnnouncementPriority
  }

-- | Create an earcon.
earcon :: EarconCategory -> Number -> Number -> Earcon
earcon cat dur vol =
  { category: cat
  , durationMs: clampDuration dur
  , volume: clampVolume vol
  , priority: PriorityMedium
  }
  where
    clampDuration d
      | d < 50.0 = 50.0
      | d > 2000.0 = 2000.0
      | otherwise = d
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Success earcon preset
earconSuccess :: Earcon
earconSuccess =
  { category: EarconSuccess
  , durationMs: 300.0
  , volume: 0.7
  , priority: PriorityMedium
  }

-- | Error earcon preset
earconError :: Earcon
earconError =
  { category: EarconError
  , durationMs: 500.0
  , volume: 0.8
  , priority: PriorityHigh
  }

-- | Warning earcon preset
earconWarning :: Earcon
earconWarning =
  { category: EarconWarning
  , durationMs: 400.0
  , volume: 0.75
  , priority: PriorityHigh
  }

-- | Notification earcon preset
earconNotification :: Earcon
earconNotification =
  { category: EarconNotify
  , durationMs: 250.0
  , volume: 0.6
  , priority: PriorityMedium
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // auditory icon
-- ═════════════════════════════════════════════════════════════════════════════

-- | AuditoryIcon - real-world sound representing an action.
-- | Unlike earcons (abstract), auditory icons are representational.
type AuditoryIcon =
  { soundDescription :: String   -- ^ What the sound represents (e.g., "paper crumple")
  , action :: String             -- ^ What action it indicates (e.g., "delete")
  , volume :: Number
  , durationMs :: Number
  }

-- | Create an auditory icon.
auditoryIcon :: String -> String -> Number -> Number -> AuditoryIcon
auditoryIcon soundDesc action' vol dur =
  { soundDescription: soundDesc
  , action: action'
  , volume: clampVolume vol
  , durationMs: clampDuration dur
  }
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v
    clampDuration d
      | d < 50.0 = 50.0
      | d > 3000.0 = 3000.0
      | otherwise = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sonification
-- ═════════════════════════════════════════════════════════════════════════════

-- | SonificationDimension - what audio parameter to map data to.
data SonificationDimension
  = DimPitch        -- ^ Higher value = higher pitch
  | DimVolume       -- ^ Higher value = louder
  | DimPan          -- ^ Value position in stereo field
  | DimTempo        -- ^ Higher value = faster rhythm
  | DimTimbre       -- ^ Value changes sound quality
  | DimDuration     -- ^ Value affects note length

derive instance eqSonificationDimension :: Eq SonificationDimension
derive instance ordSonificationDimension :: Ord SonificationDimension

instance showSonificationDimension :: Show SonificationDimension where
  show DimPitch = "Pitch"
  show DimVolume = "Volume"
  show DimPan = "Pan"
  show DimTempo = "Tempo"
  show DimTimbre = "Timbre"
  show DimDuration = "Duration"

-- | SonificationScale - how to scale data values to audio.
data SonificationScale
  = ScaleLinear     -- ^ Linear mapping
  | ScaleLogarithmic -- ^ Log scale (for wide ranges)
  | ScaleExponential -- ^ Exponential (emphasize high values)
  | ScaleDiscrete   -- ^ Step-based mapping

derive instance eqSonificationScale :: Eq SonificationScale
derive instance ordSonificationScale :: Ord SonificationScale

instance showSonificationScale :: Show SonificationScale where
  show ScaleLinear = "Linear"
  show ScaleLogarithmic = "Logarithmic"
  show ScaleExponential = "Exponential"
  show ScaleDiscrete = "Discrete"

-- | SonificationMapping - how to map a data dimension to sound.
type SonificationMapping =
  { dataMin :: Number
  , dataMax :: Number
  , audioDimension :: SonificationDimension
  , audioMin :: Number
  , audioMax :: Number
  , scale :: SonificationScale
  }

-- | Create a sonification mapping.
sonificationMapping 
  :: Number 
  -> Number 
  -> SonificationDimension 
  -> Number 
  -> Number 
  -> SonificationScale 
  -> SonificationMapping
sonificationMapping dMin dMax dim aMin aMax scl =
  { dataMin: dMin
  , dataMax: dMax
  , audioDimension: dim
  , audioMin: aMin
  , audioMax: aMax
  , scale: scl
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // audio cue
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioCue - contextual audio feedback types.
data AudioCue
  = CueFocusEnter      -- ^ Element receives focus
  | CueFocusLeave      -- ^ Element loses focus
  | CueSelect          -- ^ Item selected
  | CueDeselect        -- ^ Item deselected
  | CueExpand          -- ^ Container expanded
  | CueCollapse        -- ^ Container collapsed
  | CueScrollStart     -- ^ Scrolling began
  | CueScrollEnd       -- ^ Scrolling ended
  | CueBoundary        -- ^ Reached edge/limit
  | CueLoading         -- ^ Loading in progress
  | CueReady           -- ^ Content ready

derive instance eqAudioCue :: Eq AudioCue
derive instance ordAudioCue :: Ord AudioCue

instance showAudioCue :: Show AudioCue where
  show = audioCueName

-- | Get display name for audio cue
audioCueName :: AudioCue -> String
audioCueName CueFocusEnter = "Focus Enter"
audioCueName CueFocusLeave = "Focus Leave"
audioCueName CueSelect = "Select"
audioCueName CueDeselect = "Deselect"
audioCueName CueExpand = "Expand"
audioCueName CueCollapse = "Collapse"
audioCueName CueScrollStart = "Scroll Start"
audioCueName CueScrollEnd = "Scroll End"
audioCueName CueBoundary = "Boundary"
audioCueName CueLoading = "Loading"
audioCueName CueReady = "Ready"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // navigation sound
-- ═════════════════════════════════════════════════════════════════════════════

-- | NavigationSound - audio feedback for spatial navigation.
type NavigationSound =
  { cue :: AudioCue
  , pan :: Number          -- ^ -1.0 (left) to 1.0 (right)
  , elevation :: Number    -- ^ Perceived height (-1 to 1)
  , distance :: Number     -- ^ Perceived distance (0 = close, 1 = far)
  , volume :: Number
  }

-- | Create a navigation sound.
navigationSound :: AudioCue -> Number -> Number -> NavigationSound
navigationSound c p vol =
  { cue: c
  , pan: clampPan p
  , elevation: 0.0
  , distance: 0.0
  , volume: clampVolume vol
  }
  where
    clampPan x
      | x < (-1.0) = (-1.0)
      | x > 1.0 = 1.0
      | otherwise = x
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Focus navigation sound preset
navSoundFocus :: NavigationSound
navSoundFocus =
  { cue: CueFocusEnter
  , pan: 0.0
  , elevation: 0.0
  , distance: 0.0
  , volume: 0.5
  }

-- | Select navigation sound preset
navSoundSelect :: NavigationSound
navSoundSelect =
  { cue: CueSelect
  , pan: 0.0
  , elevation: 0.0
  , distance: 0.0
  , volume: 0.6
  }

-- | Back/exit navigation sound preset
navSoundBack :: NavigationSound
navSoundBack =
  { cue: CueFocusLeave
  , pan: 0.0
  , elevation: 0.0
  , distance: 0.2
  , volume: 0.4
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // reading speed
-- ═════════════════════════════════════════════════════════════════════════════

-- | ReadingSpeed - TTS/screen reader speech rate multiplier.
-- | 1.0 = normal, 0.5 = half speed, 2.0 = double speed.
newtype ReadingSpeed = ReadingSpeed Number

derive instance eqReadingSpeed :: Eq ReadingSpeed
derive instance ordReadingSpeed :: Ord ReadingSpeed

instance showReadingSpeed :: Show ReadingSpeed where
  show (ReadingSpeed n) = show n <> "x reading speed"

-- | Create a ReadingSpeed value (clamped to 0.25-4.0)
readingSpeed :: Number -> ReadingSpeed
readingSpeed n
  | n < 0.25 = ReadingSpeed 0.25
  | n > 4.0 = ReadingSpeed 4.0
  | otherwise = ReadingSpeed n

unwrapReadingSpeed :: ReadingSpeed -> Number
unwrapReadingSpeed (ReadingSpeed n) = n

-- | Slow reading speed (0.75x)
readingSpeedSlow :: ReadingSpeed
readingSpeedSlow = ReadingSpeed 0.75

-- | Normal reading speed (1.0x)
readingSpeedNormal :: ReadingSpeed
readingSpeedNormal = ReadingSpeed 1.0

-- | Fast reading speed (1.5x)
readingSpeedFast :: ReadingSpeed
readingSpeedFast = ReadingSpeed 1.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for ReadingSpeed
-- |
-- | Min: 0.25 (quarter speed)
-- | Max: 4.0 (quadruple speed)
readingSpeedBounds :: Bounded.NumberBounds
readingSpeedBounds = Bounded.numberBounds 0.25 4.0 "readingSpeed" "TTS/screen reader rate multiplier (0.25-4.0)"
