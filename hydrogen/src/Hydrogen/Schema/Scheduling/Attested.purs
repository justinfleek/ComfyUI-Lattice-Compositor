-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // scheduling // attested
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Attested Scheduling — Cryptographically verified scheduling primitives.
-- |
-- | This module composes the Attestation pillar with the Scheduling schema
-- | to provide verifiable, tamper-evident scheduling actions:
-- |
-- | - **AttestedEvent**: An event with cryptographic proof of creation time
-- | - **AttestedInvite**: An invitation with verifiable sender identity
-- | - **AttestedRSVP**: A response with proof of responder and timestamp
-- |
-- | ## Why Attested Scheduling?
-- |
-- | At billion-agent scale, scheduling requires:
-- | 1. **Non-repudiation**: Proof that an action occurred
-- | 2. **Tamper detection**: Verify content hasn't been modified
-- | 3. **Deterministic identity**: Same content = same hash
-- | 4. **x402 compatibility**: Foundation for on-chain verification
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Create an attested event
-- | attestedEvent <- attestEvent myEvent currentTimestamp
-- |
-- | -- Verify the event hasn't been tampered with
-- | isValid = verifyEvent attestedEvent
-- |
-- | -- Get the attestation proof
-- | proof = getEventAttestation attestedEvent
-- | ```

module Hydrogen.Schema.Scheduling.Attested
  ( -- * Attested Types
    AttestedEvent
  , AttestedInvite
  , AttestedRSVP
  , RSVPResponse
  
  -- * Event Attestation
  , attestEvent
  , attestEventFromBytes
  , verifyEvent
  , verifyEventBytes
  , getEventAttestation
  , getEventContent
  , getEventId
  , getEventContentHash
  , getEventTimestamp
  
  -- * Invite Attestation
  , attestInvite
  , attestInviteFromBytes
  , verifyInvite
  , verifyInviteBytes
  , getInviteAttestation
  , getInviteContent
  , getInviteId
  , getInviteContentHash
  , getInviteTimestamp
  
  -- * RSVP Attestation
  , attestRSVP
  , attestRSVPFromBytes
  , verifyRSVP
  , verifyRSVPBytes
  , getRSVPAttestation
  , getRSVPContent
  , getRSVPId
  , getRSVPContentHash
  , getRSVPTimestamp
  
  -- * Serialization
  , serializeEvent
  , serializeInvite
  , serializeRSVPResponse
  
  -- * Display
  , getEventContentHashHex
  , getInviteContentHashHex
  , getRSVPContentHashHex
  ) where

import Prelude
  ( show
  , ($)
  , (<>)
  , (<)
  )

import Data.Array (foldl, snoc) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

import Hydrogen.Schema.Attestation.Timestamp (Timestamp)
import Hydrogen.Schema.Attestation.Attestation 
  ( Attestation
  , ContentHash
  , attestationFromBytes
  , verifyBytes
  , getId
  , getTimestamp
  , getContentHash
  , getContentHashHex
  )
import Hydrogen.Schema.Attestation.Attested as Attested
import Hydrogen.Schema.Attestation.UUID5 (UUID5)

import Hydrogen.Schema.Scheduling.Event (Event)
import Hydrogen.Schema.Scheduling.Event as Event
import Hydrogen.Schema.Scheduling.Invite (Invite)
import Hydrogen.Schema.Scheduling.Invite as Invite
import Hydrogen.Schema.Scheduling.RSVP (RSVP)
import Hydrogen.Schema.Scheduling.RSVP as RSVP
import Hydrogen.Schema.Scheduling.Contact as Contact


-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // attested types
-- ═════════════════════════════════════════════════════════════════════════════

-- | An event with cryptographic attestation.
-- |
-- | The attestation proves:
-- | - When the event was created/attested
-- | - The exact content of the event at that time
-- | - A deterministic ID derived from content
type AttestedEvent = Attested.Attested Event

-- | An invitation with cryptographic attestation.
-- |
-- | The attestation proves:
-- | - When the invite was sent
-- | - Who sent the invite (via content hash)
-- | - The exact invitation details
type AttestedInvite = Attested.Attested Invite

-- | An RSVP response with cryptographic attestation.
-- |
-- | The attestation proves:
-- | - When the response was made
-- | - Who responded (via contact info in content)
-- | - The exact response (Accepted, Declined, etc.)
type AttestedRSVP = Attested.Attested RSVPResponse

-- | RSVP response with context (who responded to what)
type RSVPResponse =
  { inviteId :: String
  , contactId :: String
  , response :: RSVP
  , comment :: Maybe String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // event attestation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an attested event.
-- |
-- | The event is serialized to bytes and hashed to create the attestation.
-- | The timestamp records when the attestation was created.
attestEvent :: Event -> Timestamp -> AttestedEvent
attestEvent event ts =
  Attested.attestWithSerializer event ts serializeEvent

-- | Verify that an attested event hasn't been tampered with.
-- |
-- | Re-serializes the event and checks that the hash matches.
verifyEvent :: AttestedEvent -> Boolean
verifyEvent attested = Attested.verifyAttested attested serializeEvent

-- | Get the attestation proof from an attested event.
getEventAttestation :: AttestedEvent -> Attestation
getEventAttestation = Attested.getAttestation

-- | Get the event content from an attested event.
getEventContent :: AttestedEvent -> Event
getEventContent = Attested.getContent

-- | Create an attested event from raw bytes.
-- |
-- | Use when you have pre-serialized content and need direct control.
attestEventFromBytes :: Event -> Array Int -> Timestamp -> AttestedEvent
attestEventFromBytes event bytes ts =
  let
    att = attestationFromBytes bytes ts
  in
    { content: event, attestation: att }

-- | Verify an attested event using raw bytes.
-- |
-- | Use when verifying against externally-serialized content.
verifyEventBytes :: AttestedEvent -> Array Int -> Boolean
verifyEventBytes attested bytes = verifyBytes attested.attestation bytes

-- | Get the deterministic UUID from an attested event.
getEventId :: AttestedEvent -> UUID5
getEventId attested = getId attested.attestation

-- | Get the content hash from an attested event.
getEventContentHash :: AttestedEvent -> ContentHash
getEventContentHash attested = getContentHash attested.attestation

-- | Get the attestation timestamp from an attested event.
getEventTimestamp :: AttestedEvent -> Timestamp
getEventTimestamp attested = getTimestamp attested.attestation

-- | Get the content hash as hex string (for display/logging).
getEventContentHashHex :: AttestedEvent -> String
getEventContentHashHex attested = getContentHashHex attested.attestation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // invite attestation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an attested invite.
-- |
-- | Records when the invite was sent with cryptographic proof.
attestInvite :: Invite -> Timestamp -> AttestedInvite
attestInvite invite ts =
  Attested.attestWithSerializer invite ts serializeInvite

-- | Verify that an attested invite hasn't been tampered with.
verifyInvite :: AttestedInvite -> Boolean
verifyInvite attested = Attested.verifyAttested attested serializeInvite

-- | Get the attestation proof from an attested invite.
getInviteAttestation :: AttestedInvite -> Attestation
getInviteAttestation = Attested.getAttestation

-- | Get the invite content from an attested invite.
getInviteContent :: AttestedInvite -> Invite
getInviteContent = Attested.getContent

-- | Create an attested invite from raw bytes.
-- |
-- | Use when you have pre-serialized content and need direct control.
attestInviteFromBytes :: Invite -> Array Int -> Timestamp -> AttestedInvite
attestInviteFromBytes invite bytes ts =
  let
    att = attestationFromBytes bytes ts
  in
    { content: invite, attestation: att }

-- | Verify an attested invite using raw bytes.
-- |
-- | Use when verifying against externally-serialized content.
verifyInviteBytes :: AttestedInvite -> Array Int -> Boolean
verifyInviteBytes attested bytes = verifyBytes attested.attestation bytes

-- | Get the deterministic UUID from an attested invite.
getInviteId :: AttestedInvite -> UUID5
getInviteId attested = getId attested.attestation

-- | Get the content hash from an attested invite.
getInviteContentHash :: AttestedInvite -> ContentHash
getInviteContentHash attested = getContentHash attested.attestation

-- | Get the attestation timestamp from an attested invite.
getInviteTimestamp :: AttestedInvite -> Timestamp
getInviteTimestamp attested = getTimestamp attested.attestation

-- | Get the content hash as hex string (for display/logging).
getInviteContentHashHex :: AttestedInvite -> String
getInviteContentHashHex attested = getContentHashHex attested.attestation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // rsvp attestation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an attested RSVP response.
-- |
-- | Records who responded, to what, with what answer, and when.
attestRSVP 
  :: String       -- Invite ID being responded to
  -> String       -- Contact ID of responder
  -> RSVP         -- The response
  -> Maybe String -- Optional comment
  -> Timestamp    -- When the response was made
  -> AttestedRSVP
attestRSVP inviteId contactId response comment ts =
  let
    rsvpResponse =
      { inviteId: inviteId
      , contactId: contactId
      , response: response
      , comment: comment
      }
  in
    Attested.attestWithSerializer rsvpResponse ts serializeRSVPResponse

-- | Verify that an attested RSVP hasn't been tampered with.
verifyRSVP :: AttestedRSVP -> Boolean
verifyRSVP attested = Attested.verifyAttested attested serializeRSVPResponse

-- | Get the attestation proof from an attested RSVP.
getRSVPAttestation :: AttestedRSVP -> Attestation
getRSVPAttestation = Attested.getAttestation

-- | Get the RSVP content from an attested RSVP.
getRSVPContent :: AttestedRSVP -> RSVPResponse
getRSVPContent = Attested.getContent

-- | Create an attested RSVP from raw bytes.
-- |
-- | Use when you have pre-serialized content and need direct control.
attestRSVPFromBytes :: RSVPResponse -> Array Int -> Timestamp -> AttestedRSVP
attestRSVPFromBytes rsvpResponse bytes ts =
  let
    att = attestationFromBytes bytes ts
  in
    { content: rsvpResponse, attestation: att }

-- | Verify an attested RSVP using raw bytes.
-- |
-- | Use when verifying against externally-serialized content.
verifyRSVPBytes :: AttestedRSVP -> Array Int -> Boolean
verifyRSVPBytes attested bytes = verifyBytes attested.attestation bytes

-- | Get the deterministic UUID from an attested RSVP.
getRSVPId :: AttestedRSVP -> UUID5
getRSVPId attested = getId attested.attestation

-- | Get the content hash from an attested RSVP.
getRSVPContentHash :: AttestedRSVP -> ContentHash
getRSVPContentHash attested = getContentHash attested.attestation

-- | Get the attestation timestamp from an attested RSVP.
getRSVPTimestamp :: AttestedRSVP -> Timestamp
getRSVPTimestamp attested = getTimestamp attested.attestation

-- | Get the content hash as hex string (for display/logging).
getRSVPContentHashHex :: AttestedRSVP -> String
getRSVPContentHashHex attested = getContentHashHex attested.attestation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize an Event to bytes for hashing.
-- |
-- | Uses a deterministic format that includes all identity-relevant fields.
-- | The format is: id|title|start|end|organizer
serializeEvent :: Event -> Array Int
serializeEvent event =
  let
    idStr = show $ Event.getId event
    title = Event.getTitle event
    start = serializeDateTime $ Event.getStartDateTime event
    end = serializeDateTime $ Event.getEndDateTime event
    organizer = show $ Event.getOrganizerId event
    
    str = idStr <> "|" <> title <> "|" <> start <> "|" <> end <> "|" <> organizer
  in
    stringToBytes str

-- | Serialize an Invite to bytes for hashing.
-- |
-- | Format: id|eventId|contactId|contactEmail|contactName|role
-- | Includes contact details for complete audit trail.
serializeInvite :: Invite -> Array Int
serializeInvite invite =
  let
    idStr = show $ Invite.getId invite
    eventId = Invite.getEventId invite
    contact = Invite.getContact invite
    contactId = show $ Invite.getContactId invite
    contactEmail = maybeToString $ Contact.getEmail contact
    contactName = Contact.getName contact
    role = show $ Invite.getRole invite
    
    str = idStr <> "|" <> eventId <> "|" <> contactId <> "|" <> 
          contactEmail <> "|" <> contactName <> "|" <> role
  in
    stringToBytes str

-- | Serialize an RSVP response to bytes for hashing.
-- |
-- | Format: inviteId|contactId|response|comment
serializeRSVPResponse :: RSVPResponse -> Array Int
serializeRSVPResponse r =
  let
    commentStr = case r.comment of
      Nothing -> ""
      Just c -> c
    
    str = r.inviteId <> "|" <> r.contactId <> "|" <> 
          RSVP.toICalString r.response <> "|" <> commentStr
  in
    stringToBytes str

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a string to bytes (ASCII)
stringToBytes :: String -> Array Int
stringToBytes str =
  let
    chars = String.toCharArray str
  in
    Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars

-- | Serialize a DateTime to string
serializeDateTime :: Event.DateTime -> String
serializeDateTime dt =
  show dt.year <> "-" <> 
  padZero2 dt.month <> "-" <> 
  padZero2 dt.day <> "T" <>
  show dt.time

-- | Pad number to 2 digits
padZero2 :: Int -> String
padZero2 n = if n < 10 then "0" <> show n else show n

-- | Convert Maybe String to String (empty if Nothing)
maybeToString :: Maybe String -> String
maybeToString (Just s) = s
maybeToString Nothing = ""
