-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // qrcode // content // calendar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar Content — QR encoding for calendar events.
-- |
-- | ## Encoding Format
-- |
-- | vCalendar/iCalendar format:
-- | ```
-- | BEGIN:VCALENDAR
-- | VERSION:2.0
-- | BEGIN:VEVENT
-- | SUMMARY:Event Title
-- | DTSTART:20260224T150000Z
-- | DTEND:20260224T160000Z
-- | DESCRIPTION:Event description
-- | LOCATION:Event location
-- | END:VEVENT
-- | END:VCALENDAR
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)
-- | - Data.String (joining lines)

module Hydrogen.Element.Compound.QRCode.Content.Types.Calendar
  ( -- * Calendar Content
    CalendarContent
  , calendarContent
  
  -- * Encoding
  , encodeCalendar
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.String (joinWith)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // calendar content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calendar event content configuration.
-- |
-- | For full calendar integration, use Schema.Scheduling.Event
-- | This is a simplified version for QR encoding.
type CalendarContent =
  { title :: String
  , description :: Maybe String
  , location :: Maybe String
  , startDate :: String         -- ^ ISO 8601 format: 20260224T150000Z
  , endDate :: String           -- ^ ISO 8601 format
  , allDay :: Boolean
  }

-- | Create calendar event content
calendarContent :: String -> String -> String -> CalendarContent
calendarContent title startDate endDate =
  { title
  , description: Nothing
  , location: Nothing
  , startDate
  , endDate
  , allDay: false
  }

-- | Encode calendar to vEvent format
encodeCalendar :: CalendarContent -> String
encodeCalendar c =
  let
    lines =
      [ "BEGIN:VCALENDAR"
      , "VERSION:2.0"
      , "BEGIN:VEVENT"
      , "SUMMARY:" <> c.title
      , "DTSTART:" <> c.startDate
      , "DTEND:" <> c.endDate
      ] <>
      maybe [] (\d -> ["DESCRIPTION:" <> d]) c.description <>
      maybe [] (\l -> ["LOCATION:" <> l]) c.location <>
      [ "END:VEVENT"
      , "END:VCALENDAR"
      ]
  in
    joinWith "\n" lines
