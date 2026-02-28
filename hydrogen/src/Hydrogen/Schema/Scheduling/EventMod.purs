-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // scheduling // event-mod
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | EventMod — Modifier and display functions for calendar events.
-- |
-- | Functions that transform events (setters, updaters) and format them
-- | for display or export (iCalendar).

module Hydrogen.Schema.Scheduling.EventMod
  ( -- * Modifiers
    setLocation
  , setDescription
  , setConferenceLink
  , addAttendee
  , addReminder
  , setRecurrence
  , cancel
  
  -- * Offset Operations
  , getStartOffsetMinutes
  , getEndOffsetMinutes
  , getTimezoneOffset
  
  -- * Display
  , toDisplayString
  , toICalString
  
  -- * Formatting Helpers
  , formatDateTimeShort
  , formatDateTimeICal
  , statusToICalString
  , visibilityToICalString
  ) where

import Prelude
  ( show
  , otherwise
  , (<>)
  , (<)
  , (+)
  , (*)
  )

import Data.Maybe (Maybe(Just))
import Hydrogen.Schema.Scheduling.Contact (ContactId)
import Hydrogen.Schema.Scheduling.Event
  ( Event(Event)
  , DateTime
  , Location
  , Reminder
  , EventStatus(Confirmed, Tentative, Cancelled)
  , Visibility(Public, Private, Confidential)
  , getTitle
  , getStartDateTime
  , getEndDateTime
  , getTimezone
  , getStatus
  , getVisibility
  , getId
  )
import Hydrogen.Schema.Scheduling.Recurrence (Recurrence)
import Hydrogen.Schema.Temporal.Timezone (UtcOffset)
import Hydrogen.Schema.Temporal.Timezone as Timezone
import Hydrogen.Schema.Temporal.TimeOfDay (TimeOfDay)
import Hydrogen.Schema.Temporal.TimeOfDay as TimeOfDay

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the event location
setLocation :: Event -> Location -> Event
setLocation (Event e) loc = Event (e { location = Just loc })

-- | Set the event description
setDescription :: Event -> String -> Event
setDescription (Event e) desc = Event (e { description = Just desc })

-- | Set a video conference link
setConferenceLink :: Event -> String -> Event
setConferenceLink (Event e) link = Event (e { conferenceLink = Just link })

-- | Add an attendee to the event
addAttendee :: Event -> ContactId -> Event
addAttendee (Event e) attendeeId = Event (e { attendeeIds = e.attendeeIds <> [attendeeId] })

-- | Add a reminder to the event
addReminder :: Event -> Reminder -> Event
addReminder (Event e) rem = Event (e { reminders = e.reminders <> [rem] })

-- | Set recurrence rule
setRecurrence :: Event -> Recurrence -> Event
setRecurrence (Event e) rec = Event (e { recurrence = Just rec })

-- | Cancel the event
cancel :: Event -> Event
cancel (Event e) = Event (e { status = Cancelled })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // offset operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get start time as UTC offset in minutes from midnight
getStartOffsetMinutes :: Event -> Int
getStartOffsetMinutes e =
  let
    start = getStartDateTime e
    rec = TimeOfDay.toRecord start.time
    tzOffset = Timezone.totalOffsetMinutes (Timezone.getStandardOffset (getTimezone e))
  in
    rec.hour * 60 + rec.minute + tzOffset

-- | Get end time as UTC offset in minutes from midnight
getEndOffsetMinutes :: Event -> Int
getEndOffsetMinutes e =
  let
    end = getEndDateTime e
    rec = TimeOfDay.toRecord end.time
    tzOffset = Timezone.totalOffsetMinutes (Timezone.getStandardOffset (getTimezone e))
  in
    rec.hour * 60 + rec.minute + tzOffset

-- | Get the event's timezone UTC offset
getTimezoneOffset :: Event -> UtcOffset
getTimezoneOffset e = Timezone.getStandardOffset (getTimezone e)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable display string
toDisplayString :: Event -> String
toDisplayString e =
  getTitle e <> " (" <> formatDateTimeShort (getStartDateTime e) <> ")"

-- | Convert to iCalendar VEVENT string
-- |
-- | Basic iCalendar format for interoperability.
toICalString :: Event -> String
toICalString e =
  "BEGIN:VEVENT\r\n" <>
  "UID:" <> show (getId e) <> "\r\n" <>
  "SUMMARY:" <> getTitle e <> "\r\n" <>
  "DTSTART:" <> formatDateTimeICal (getStartDateTime e) <> "\r\n" <>
  "DTEND:" <> formatDateTimeICal (getEndDateTime e) <> "\r\n" <>
  "STATUS:" <> statusToICalString (getStatus e) <> "\r\n" <>
  "CLASS:" <> visibilityToICalString (getVisibility e) <> "\r\n" <>
  "END:VEVENT\r\n"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // formatting helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format datetime for display
formatDateTimeShort :: DateTime -> String
formatDateTimeShort dt =
  show dt.month <> "/" <> show dt.day <> "/" <> show dt.year <>
  " " <> TimeOfDay.format12H dt.time

-- | Format datetime for iCalendar
formatDateTimeICal :: DateTime -> String
formatDateTimeICal dt =
  padZero4 dt.year <> padZero dt.month <> padZero dt.day <>
  "T" <> formatTimeICal dt.time

-- | Format time for iCalendar (HHMMSS)
formatTimeICal :: TimeOfDay -> String
formatTimeICal t =
  let
    rec = TimeOfDay.toRecord t
  in
    padZero rec.hour <> padZero rec.minute <> padZero rec.second

-- | Convert EventStatus to iCalendar STATUS value
statusToICalString :: EventStatus -> String
statusToICalString Confirmed = "CONFIRMED"
statusToICalString Tentative = "TENTATIVE"
statusToICalString Cancelled = "CANCELLED"

-- | Convert Visibility to iCalendar CLASS value
visibilityToICalString :: Visibility -> String
visibilityToICalString Public = "PUBLIC"
visibilityToICalString Private = "PRIVATE"
visibilityToICalString Confidential = "CONFIDENTIAL"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pad to 2 digits
padZero :: Int -> String
padZero n
  | n < 10 = "0" <> show n
  | otherwise = show n

-- | Pad to 4 digits
padZero4 :: Int -> String
padZero4 n
  | n < 10 = "000" <> show n
  | n < 100 = "00" <> show n
  | n < 1000 = "0" <> show n
  | otherwise = show n
