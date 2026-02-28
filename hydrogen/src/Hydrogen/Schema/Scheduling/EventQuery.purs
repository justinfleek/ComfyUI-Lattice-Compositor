-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // scheduling // event-query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | EventQuery — Query functions for calendar events.
-- |
-- | Boolean predicates and computed properties for Event introspection.
-- | Separates read-only queries from mutations (EventMod).

module Hydrogen.Schema.Scheduling.EventQuery
  ( -- * Boolean Queries
    hasRecurrence
  , hasConference
  , hasAttendees
  , isMultiDay
  , isCancelled
  , isPrivate
  , isSameDay
  , needsLocation
  
  -- * Computed Properties
  , getDurationMinutes
  , getAttendeeCount
  , getReminderMinutes
  
  -- * Internal Helpers
  , dateTimeToMinutes
  ) where

import Prelude
  ( map
  , not
  , (-)
  , (+)
  , (*)
  , (/)
  , (==)
  , (/=)
  , (&&)
  , (||)
  )

import Data.Array (length, null)
import Data.Maybe (isJust, isNothing)
import Hydrogen.Schema.Scheduling.Event
  ( Event
  , DateTime
  , EventStatus(Cancelled)
  , Visibility(Private, Confidential)
  , getStartDateTime
  , getEndDateTime
  , getAttendeeIds
  , getRecurrence
  , getReminders
  , getStatus
  , getVisibility
  , getConferenceLink
  , getLocation
  )
import Hydrogen.Schema.Temporal.TimeOfDay as TimeOfDay

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // boolean queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if event has recurrence
hasRecurrence :: Event -> Boolean
hasRecurrence e = isJust (getRecurrence e)

-- | Check if event has video conference
hasConference :: Event -> Boolean
hasConference e = isJust (getConferenceLink e)

-- | Check if event has attendees (besides organizer)
hasAttendees :: Event -> Boolean
hasAttendees e = not (null (getAttendeeIds e))

-- | Check if event spans multiple days
isMultiDay :: Event -> Boolean
isMultiDay e =
  let
    start = getStartDateTime e
    end = getEndDateTime e
  in
    start.year /= end.year ||
    start.month /= end.month ||
    start.day /= end.day

-- | Check if event is cancelled
isCancelled :: Event -> Boolean
isCancelled e = getStatus e == Cancelled

-- | Check if event is private
isPrivate :: Event -> Boolean
isPrivate e =
  let vis = getVisibility e
  in vis == Private || vis == Confidential

-- | Check if start and end are on the same calendar day
isSameDay :: Event -> Boolean
isSameDay e =
  let
    start = getStartDateTime e
    end = getEndDateTime e
  in
    start.year == end.year &&
    start.month == end.month &&
    start.day == end.day

-- | Check if event needs a location (no location and not virtual)
needsLocation :: Event -> Boolean
needsLocation e = isNothing (getLocation e) && isNothing (getConferenceLink e)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get event duration in minutes
getDurationMinutes :: Event -> Int
getDurationMinutes e =
  let
    startMins = dateTimeToMinutes (getStartDateTime e)
    endMins = dateTimeToMinutes (getEndDateTime e)
  in
    endMins - startMins

-- | Get the number of attendees
getAttendeeCount :: Event -> Int
getAttendeeCount e = length (getAttendeeIds e)

-- | Get all reminder times as minutes before event
getReminderMinutes :: Event -> Array Int
getReminderMinutes e = map (\r -> r.minutesBefore) (getReminders e)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert datetime to minutes since epoch (simplified)
-- |
-- | Used for duration calculations. Not astronomically accurate.
dateTimeToMinutes :: DateTime -> Int
dateTimeToMinutes dt =
  let
    yearMins = dt.year * 525600
    monthMins = dt.month * 43200
    dayMins = dt.day * 1440
    timeMins = TimeOfDay.toMillisOfDay dt.time / 60000
  in
    yearMins + monthMins + dayMins + timeMins
