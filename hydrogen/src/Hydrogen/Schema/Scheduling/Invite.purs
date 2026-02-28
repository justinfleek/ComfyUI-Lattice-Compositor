-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // scheduling // invite
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Invite — Event invitation linking an attendee to an event.
-- |
-- | Represents the relationship between a Contact and an Event, including
-- | RSVP status, role, and notification preferences.

module Hydrogen.Schema.Scheduling.Invite
  ( -- * Types
    Invite
  , InviteId
  , AttendeeRole(Organizer, Required, Optional, Chair, NonParticipant)
  
  -- * Constructors
  , invite
  , inviteRequired
  , inviteOptional
  , inviteOrganizer
  
  -- * Accessors
  , getId
  , getEventId
  , getContactId
  , getContact
  , getRole
  , getRsvp
  , getSentAt
  , getRespondedAt
  , getComment
  
  -- * Modifiers
  , respond
  , respondWithComment
  , updateRole
  
  -- * Queries
  , isOrganizer
  , isRequired
  , isOptional
  , hasResponded
  , isAttending
  
  -- * Display
  , toDisplayString
  , roleToICalString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , (||)
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)
import Hydrogen.Schema.Scheduling.Contact (Contact, ContactId)
import Hydrogen.Schema.Scheduling.Contact as Contact
import Hydrogen.Schema.Scheduling.RSVP (RSVP)
import Hydrogen.Schema.Scheduling.RSVP as RSVP

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // invite id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for an invite
newtype InviteId = InviteId String

derive instance eqInviteId :: Eq InviteId
derive instance ordInviteId :: Ord InviteId

instance showInviteId :: Show InviteId where
  show (InviteId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // attendee role
-- ═════════════════════════════════════════════════════════════════════════════

-- | Role of attendee in the event
-- |
-- | Follows iCalendar ROLE parameter (RFC 5545)
data AttendeeRole
  = Organizer      -- Event creator/owner
  | Required       -- Must attend (REQ-PARTICIPANT)
  | Optional       -- May attend (OPT-PARTICIPANT)
  | Chair          -- Presides over event (CHAIR)
  | NonParticipant -- For information only (NON-PARTICIPANT)

derive instance eqAttendeeRole :: Eq AttendeeRole
derive instance ordAttendeeRole :: Ord AttendeeRole

instance showAttendeeRole :: Show AttendeeRole where
  show Organizer = "Organizer"
  show Required = "Required"
  show Optional = "Optional"
  show Chair = "Chair"
  show NonParticipant = "Non-Participant"

-- | Convert to iCalendar ROLE value
roleToICalString :: AttendeeRole -> String
roleToICalString Organizer = "ORGANIZER"
roleToICalString Required = "REQ-PARTICIPANT"
roleToICalString Optional = "OPT-PARTICIPANT"
roleToICalString Chair = "CHAIR"
roleToICalString NonParticipant = "NON-PARTICIPANT"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // invite
-- ═════════════════════════════════════════════════════════════════════════════

-- | An invitation to an event
-- |
-- | Links a Contact to an Event with role and RSVP state.
-- | Tracks when the invite was sent and when the attendee responded.
-- |
-- | Contains both contactId (for relational reference) and contact (for
-- | denormalized access). The contactId is the source of truth; the embedded
-- | contact is a snapshot at invite creation time.
newtype Invite = Invite
  { id :: InviteId
  , eventId :: String  -- Reference to Event.EventId
  , contactId :: ContactId  -- Relational reference
  , contact :: Contact  -- Denormalized snapshot
  , role :: AttendeeRole
  , rsvp :: RSVP
  , sentAt :: Maybe DateTime  -- When invite was sent
  , respondedAt :: Maybe DateTime  -- When response was received
  , comment :: Maybe String  -- Attendee's response message
  }

derive instance eqInvite :: Eq Invite
derive instance ordInvite :: Ord Invite

instance showInvite :: Show Invite where
  show i = toDisplayString i

-- | Simple datetime for invite tracking
-- | (Full DateTime type would be in a separate module)
type DateTime =
  { year :: Int
  , month :: Int
  , day :: Int
  , hour :: Int
  , minute :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an invite with all fields
invite
  :: String  -- Invite ID
  -> String  -- Event ID
  -> Contact
  -> AttendeeRole
  -> RSVP
  -> Maybe DateTime
  -> Invite
invite id eventId contact role rsvp sentAt = Invite
  { id: InviteId id
  , eventId: eventId
  , contactId: Contact.getId contact
  , contact: contact
  , role: role
  , rsvp: rsvp
  , sentAt: sentAt
  , respondedAt: Nothing
  , comment: Nothing
  }

-- | Create a required attendee invite (most common)
inviteRequired :: String -> String -> Contact -> Invite
inviteRequired id eventId contact = Invite
  { id: InviteId id
  , eventId: eventId
  , contactId: Contact.getId contact
  , contact: contact
  , role: Required
  , rsvp: RSVP.Pending
  , sentAt: Nothing
  , respondedAt: Nothing
  , comment: Nothing
  }

-- | Create an optional attendee invite
inviteOptional :: String -> String -> Contact -> Invite
inviteOptional id eventId contact = Invite
  { id: InviteId id
  , eventId: eventId
  , contactId: Contact.getId contact
  , contact: contact
  , role: Optional
  , rsvp: RSVP.Pending
  , sentAt: Nothing
  , respondedAt: Nothing
  , comment: Nothing
  }

-- | Create an organizer invite (auto-accepted)
inviteOrganizer :: String -> String -> Contact -> Invite
inviteOrganizer id eventId contact = Invite
  { id: InviteId id
  , eventId: eventId
  , contactId: Contact.getId contact
  , contact: contact
  , role: Organizer
  , rsvp: RSVP.Accepted
  , sentAt: Nothing
  , respondedAt: Nothing
  , comment: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the invite ID
getId :: Invite -> InviteId
getId (Invite i) = i.id

-- | Get the event ID
getEventId :: Invite -> String
getEventId (Invite i) = i.eventId

-- | Get the contact ID (relational reference)
getContactId :: Invite -> ContactId
getContactId (Invite i) = i.contactId

-- | Get the invited contact (denormalized snapshot)
getContact :: Invite -> Contact
getContact (Invite i) = i.contact

-- | Get the attendee role
getRole :: Invite -> AttendeeRole
getRole (Invite i) = i.role

-- | Get the RSVP status
getRsvp :: Invite -> RSVP
getRsvp (Invite i) = i.rsvp

-- | Get when the invite was sent
getSentAt :: Invite -> Maybe DateTime
getSentAt (Invite i) = i.sentAt

-- | Get when the attendee responded
getRespondedAt :: Invite -> Maybe DateTime
getRespondedAt (Invite i) = i.respondedAt

-- | Get the attendee's response comment
getComment :: Invite -> Maybe String
getComment (Invite i) = i.comment

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Record an RSVP response
respond :: Invite -> RSVP -> DateTime -> Invite
respond (Invite i) rsvp respondedAt = Invite
  (i { rsvp = rsvp, respondedAt = Just respondedAt })

-- | Record an RSVP response with a comment
respondWithComment :: Invite -> RSVP -> DateTime -> String -> Invite
respondWithComment (Invite i) rsvp respondedAt comment = Invite
  (i { rsvp = rsvp, respondedAt = Just respondedAt, comment = Just comment })

-- | Update the attendee role
updateRole :: Invite -> AttendeeRole -> Invite
updateRole (Invite i) role = Invite (i { role = role })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if attendee is the organizer
isOrganizer :: Invite -> Boolean
isOrganizer (Invite i) = i.role == Organizer

-- | Check if attendee is required
isRequired :: Invite -> Boolean
isRequired (Invite i) = i.role == Required || i.role == Chair

-- | Check if attendee is optional
isOptional :: Invite -> Boolean
isOptional (Invite i) = i.role == Optional || i.role == NonParticipant

-- | Check if attendee has responded
hasResponded :: Invite -> Boolean
hasResponded (Invite i) = isJust i.respondedAt

-- | Check if attendee is attending (Accepted or Tentative)
isAttending :: Invite -> Boolean
isAttending (Invite i) = RSVP.isConfirmed i.rsvp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable display string
toDisplayString :: Invite -> String
toDisplayString (Invite i) =
  Contact.getName i.contact <> " (" <> show i.role <> ") - " <> show i.rsvp
