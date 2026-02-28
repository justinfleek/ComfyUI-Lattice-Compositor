-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // scheduling // event
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Event — Calendar event core types and accessors.
-- |
-- | Represents a scheduled event with Google Meet/Zoom level granularity:
-- | - Title, description, location
-- | - Start/end datetime with timezone
-- | - All-day events
-- | - Attendees with RSVP tracking
-- | - Recurrence rules
-- | - Reminders
-- | - Video conferencing links
-- |
-- | Follows RFC 5545 (iCalendar) semantics for interoperability.
-- |
-- | ## Related Modules
-- |
-- | - EventQuery: Boolean predicates and computed properties
-- | - EventMod: Modifier functions and display/export

module Hydrogen.Schema.Scheduling.Event
  ( -- * Types
    Event(Event)
  , EventId
  , DateTime
  , Location(Physical, Virtual, Hybrid)
  , EventStatus(Confirmed, Tentative, Cancelled)
  , Visibility(Public, Private, Confidential)
  , Reminder
  , ReminderMethod(Email, Popup, SMS)
  
  -- * Constructors
  , event
  , eventAllDay
  , eventSimple
  , reminder
  , makeDateTime
  , getDatePart
  
  -- * Accessors
  , getId
  , getTitle
  , getDescription
  , getLocation
  , getStartDateTime
  , getEndDateTime
  , getTimezone
  , isAllDay
  , getOrganizerId
  , getAttendeeIds
  , getRecurrence
  , getReminders
  , getStatus
  , getVisibility
  , getConferenceLink
  , getCreatedAt
  , getUpdatedAt
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Scheduling.Contact (ContactId)
import Hydrogen.Schema.Scheduling.Recurrence (Recurrence)
import Hydrogen.Schema.Temporal.Timezone (TimezoneId)
import Hydrogen.Schema.Temporal.TimeOfDay (TimeOfDay)
import Hydrogen.Schema.Temporal.TimeOfDay as TimeOfDay

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // event id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for an event
-- |
-- | Should be UUID5 for deterministic generation.
newtype EventId = EventId String

derive instance eqEventId :: Eq EventId
derive instance ordEventId :: Ord EventId

instance showEventId :: Show EventId where
  show (EventId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // date-time
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete datetime with date and time components
-- |
-- | Represents a specific moment with year, month, day, and time-of-day.
-- | Timezone is stored separately at the event level.
type DateTime =
  { year :: Int
  , month :: Int  -- 1-12
  , day :: Int    -- 1-31
  , time :: TimeOfDay
  }

-- | Create a DateTime
makeDateTime :: Int -> Int -> Int -> TimeOfDay -> DateTime
makeDateTime y m d t = { year: y, month: m, day: d, time: t }

-- | Get date portion as record
getDatePart :: DateTime -> { year :: Int, month :: Int, day :: Int }
getDatePart dt = { year: dt.year, month: dt.month, day: dt.day }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // location
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event location type
data Location
  = Physical 
      { address :: String
      , room :: Maybe String
      , instructions :: Maybe String
      }
  | Virtual
      { url :: String
      , provider :: Maybe String  -- "Google Meet", "Zoom", etc.
      , meetingId :: Maybe String
      , passcode :: Maybe String
      }
  | Hybrid
      { physical :: { address :: String, room :: Maybe String }
      , virtual :: { url :: String, provider :: Maybe String }
      }

derive instance eqLocation :: Eq Location

instance showLocation :: Show Location where
  show (Physical p) = p.address
  show (Virtual v) = v.url
  show (Hybrid h) = h.physical.address <> " + " <> h.virtual.url

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // event status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event confirmation status
data EventStatus
  = Confirmed   -- Event is confirmed
  | Tentative   -- Event is tentative
  | Cancelled   -- Event has been cancelled

derive instance eqEventStatus :: Eq EventStatus
derive instance ordEventStatus :: Ord EventStatus

instance showEventStatus :: Show EventStatus where
  show Confirmed = "Confirmed"
  show Tentative = "Tentative"
  show Cancelled = "Cancelled"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event visibility/privacy level
data Visibility
  = Public       -- Visible to everyone
  | Private      -- Only visible to attendees
  | Confidential -- Time shown as busy, details hidden

derive instance eqVisibility :: Eq Visibility
derive instance ordVisibility :: Ord Visibility

instance showVisibility :: Show Visibility where
  show Public = "Public"
  show Private = "Private"
  show Confidential = "Confidential"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // reminder
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to deliver the reminder
data ReminderMethod
  = Email
  | Popup
  | SMS

derive instance eqReminderMethod :: Eq ReminderMethod
derive instance ordReminderMethod :: Ord ReminderMethod

instance showReminderMethod :: Show ReminderMethod where
  show Email = "Email"
  show Popup = "Popup"
  show SMS = "SMS"

-- | Event reminder configuration
-- |
-- | Specifies when and how to remind attendees.
type Reminder =
  { minutesBefore :: Int  -- Minutes before event start
  , method :: ReminderMethod
  }

-- | Create a reminder
reminder :: Int -> ReminderMethod -> Reminder
reminder mins method = { minutesBefore: mins, method: method }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // event
-- ═════════════════════════════════════════════════════════════════════════════

-- | A calendar event
-- |
-- | Full-featured scheduling entity with:
-- | - Identity (id, title, description)
-- | - Timing (start, end, timezone, all-day)
-- | - Location (physical, virtual, or hybrid)
-- | - Participants (organizer, attendees by ID)
-- | - Recurrence rules
-- | - Reminders
-- | - Metadata (status, visibility, timestamps)
newtype Event = Event
  { id :: EventId
  , title :: String
  , description :: Maybe String
  , location :: Maybe Location
  , startDateTime :: DateTime
  , endDateTime :: DateTime
  , timezone :: TimezoneId
  , allDay :: Boolean
  , organizerId :: ContactId
  , attendeeIds :: Array ContactId
  , recurrence :: Maybe Recurrence
  , reminders :: Array Reminder
  , status :: EventStatus
  , visibility :: Visibility
  , conferenceLink :: Maybe String
  , createdAt :: DateTime
  , updatedAt :: DateTime
  }

derive instance eqEvent :: Eq Event

instance showEvent :: Show Event where
  show e = getTitle e

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an event with all fields
event
  :: String        -- Event ID
  -> String        -- Title
  -> Maybe String  -- Description
  -> DateTime      -- Start
  -> DateTime      -- End
  -> TimezoneId    -- Timezone
  -> ContactId     -- Organizer
  -> DateTime      -- Created at
  -> Event
event id title desc start end tz organizer createdAt = Event
  { id: EventId id
  , title: title
  , description: desc
  , location: Nothing
  , startDateTime: start
  , endDateTime: end
  , timezone: tz
  , allDay: false
  , organizerId: organizer
  , attendeeIds: []
  , recurrence: Nothing
  , reminders: []
  , status: Confirmed
  , visibility: Public
  , conferenceLink: Nothing
  , createdAt: createdAt
  , updatedAt: createdAt
  }

-- | Create an all-day event
eventAllDay
  :: String        -- Event ID
  -> String        -- Title
  -> Int           -- Start year
  -> Int           -- Start month
  -> Int           -- Start day
  -> Int           -- End year
  -> Int           -- End month
  -> Int           -- End day
  -> TimezoneId    -- Timezone
  -> ContactId     -- Organizer
  -> DateTime      -- Created at
  -> Event
eventAllDay id title sy sm sd ey em ed tz organizer createdAt = Event
  { id: EventId id
  , title: title
  , description: Nothing
  , location: Nothing
  , startDateTime: makeDateTime sy sm sd TimeOfDay.midnight
  , endDateTime: makeDateTime ey em ed TimeOfDay.midnight
  , timezone: tz
  , allDay: true
  , organizerId: organizer
  , attendeeIds: []
  , recurrence: Nothing
  , reminders: []
  , status: Confirmed
  , visibility: Public
  , conferenceLink: Nothing
  , createdAt: createdAt
  , updatedAt: createdAt
  }

-- | Create a simple event (most common use case)
eventSimple
  :: String      -- Event ID
  -> String      -- Title
  -> Int -> Int -> Int -> Int -> Int  -- Start: year, month, day, hour, minute
  -> Int -> Int -> Int -> Int -> Int  -- End: year, month, day, hour, minute
  -> TimezoneId  -- Timezone
  -> ContactId   -- Organizer
  -> Event
eventSimple id title sy sm sd sh smin ey em ed eh emin tz organizer =
  let
    now = makeDateTime sy sm sd (TimeOfDay.timeHM sh smin)
  in
    event id title Nothing
      (makeDateTime sy sm sd (TimeOfDay.timeHM sh smin))
      (makeDateTime ey em ed (TimeOfDay.timeHM eh emin))
      tz organizer now

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the event ID
getId :: Event -> EventId
getId (Event e) = e.id

-- | Get the event title
getTitle :: Event -> String
getTitle (Event e) = e.title

-- | Get the event description
getDescription :: Event -> Maybe String
getDescription (Event e) = e.description

-- | Get the event location
getLocation :: Event -> Maybe Location
getLocation (Event e) = e.location

-- | Get the start datetime
getStartDateTime :: Event -> DateTime
getStartDateTime (Event e) = e.startDateTime

-- | Get the end datetime
getEndDateTime :: Event -> DateTime
getEndDateTime (Event e) = e.endDateTime

-- | Get the event timezone
getTimezone :: Event -> TimezoneId
getTimezone (Event e) = e.timezone

-- | Check if this is an all-day event
isAllDay :: Event -> Boolean
isAllDay (Event e) = e.allDay

-- | Get the organizer's contact ID
getOrganizerId :: Event -> ContactId
getOrganizerId (Event e) = e.organizerId

-- | Get all attendee contact IDs
getAttendeeIds :: Event -> Array ContactId
getAttendeeIds (Event e) = e.attendeeIds

-- | Get the recurrence rule
getRecurrence :: Event -> Maybe Recurrence
getRecurrence (Event e) = e.recurrence

-- | Get all reminders
getReminders :: Event -> Array Reminder
getReminders (Event e) = e.reminders

-- | Get the event status
getStatus :: Event -> EventStatus
getStatus (Event e) = e.status

-- | Get the event visibility
getVisibility :: Event -> Visibility
getVisibility (Event e) = e.visibility

-- | Get the video conference link
getConferenceLink :: Event -> Maybe String
getConferenceLink (Event e) = e.conferenceLink

-- | Get when the event was created
getCreatedAt :: Event -> DateTime
getCreatedAt (Event e) = e.createdAt

-- | Get when the event was last updated
getUpdatedAt :: Event -> DateTime
getUpdatedAt (Event e) = e.updatedAt
