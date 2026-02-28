-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // scheduling // rsvp
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | RSVP — Attendee response status for calendar events.
-- |
-- | Represents the response state of an event invitation.
-- | Follows Google Calendar / iCalendar / RFC 5545 semantics.

module Hydrogen.Schema.Scheduling.RSVP
  ( -- * Type
    RSVP(Pending, Accepted, Declined, Tentative, Delegated)
  
  -- * Queries
  , isConfirmed
  , isDeclined
  , isPending
  , needsResponse
  
  -- * Display
  , toDisplayString
  , toICalString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // rsvp
-- ═════════════════════════════════════════════════════════════════════════════

-- | RSVP response status
-- |
-- | ## Values
-- |
-- | - Pending: No response yet (default state)
-- | - Accepted: Attendee confirmed attendance
-- | - Declined: Attendee declined the invitation
-- | - Tentative: Attendee might attend (provisional yes)
-- | - Delegated: Attendee delegated to someone else
data RSVP
  = Pending
  | Accepted
  | Declined
  | Tentative
  | Delegated

derive instance eqRSVP :: Eq RSVP
derive instance ordRSVP :: Ord RSVP

instance showRSVP :: Show RSVP where
  show = toDisplayString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if attendee has confirmed (Accepted or Tentative)
isConfirmed :: RSVP -> Boolean
isConfirmed Accepted = true
isConfirmed Tentative = true
isConfirmed _ = false

-- | Check if attendee has declined
isDeclined :: RSVP -> Boolean
isDeclined Declined = true
isDeclined _ = false

-- | Check if awaiting response
isPending :: RSVP -> Boolean
isPending Pending = true
isPending _ = false

-- | Check if a response is still needed (Pending)
needsResponse :: RSVP -> Boolean
needsResponse = isPending

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable display string
toDisplayString :: RSVP -> String
toDisplayString Pending = "Pending"
toDisplayString Accepted = "Accepted"
toDisplayString Declined = "Declined"
toDisplayString Tentative = "Tentative"
toDisplayString Delegated = "Delegated"

-- | iCalendar PARTSTAT value (RFC 5545)
-- |
-- | Used for interoperability with calendar systems.
toICalString :: RSVP -> String
toICalString Pending = "NEEDS-ACTION"
toICalString Accepted = "ACCEPTED"
toICalString Declined = "DECLINED"
toICalString Tentative = "TENTATIVE"
toICalString Delegated = "DELEGATED"
