-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // scheduling // contact
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Contact — Person or resource that can attend calendar events.
-- |
-- | Represents an individual or shared resource (room, equipment) that
-- | can be invited to events. Follows vCard/iCalendar ATTENDEE semantics.

module Hydrogen.Schema.Scheduling.Contact
  ( -- * Types
    Contact
  , ContactId
  , ContactType(Person, Room, Resource, Group)
  
  -- * Constructors
  , contact
  , contactWithId
  , person
  , room
  , resource
  , group
  
  -- * Accessors
  , getId
  , getName
  , getEmail
  , getAvatarUrl
  , getContactType
  , getTimezone
  
  -- * Queries
  , isPerson
  , isResource
  , hasEmail
  , hasAvatar
  
  -- * Display
  , toDisplayName
  , toEmailString
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
import Hydrogen.Schema.Temporal.Timezone (TimezoneId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // contact id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a contact
-- |
-- | Should be UUID5 for deterministic generation, or external system ID.
newtype ContactId = ContactId String

derive instance eqContactId :: Eq ContactId
derive instance ordContactId :: Ord ContactId

instance showContactId :: Show ContactId where
  show (ContactId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // contact type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of contact
-- |
-- | - Person: Individual human attendee
-- | - Room: Physical meeting room
-- | - Resource: Equipment or shared resource (projector, car, etc.)
-- | - Group: Distribution list or team
data ContactType
  = Person
  | Room
  | Resource
  | Group

derive instance eqContactType :: Eq ContactType
derive instance ordContactType :: Ord ContactType

instance showContactType :: Show ContactType where
  show Person = "Person"
  show Room = "Room"
  show Resource = "Resource"
  show Group = "Group"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // contact
-- ═════════════════════════════════════════════════════════════════════════════

-- | A contact that can attend events
-- |
-- | Contains identity, contact info, and optional timezone preference.
newtype Contact = Contact
  { id :: ContactId
  , name :: String
  , email :: Maybe String
  , avatarUrl :: Maybe String
  , contactType :: ContactType
  , timezone :: Maybe TimezoneId
  }

derive instance eqContact :: Eq Contact
derive instance ordContact :: Ord Contact

instance showContact :: Show Contact where
  show c = toDisplayName c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a contact with all fields
contact 
  :: ContactId 
  -> String 
  -> Maybe String 
  -> Maybe String 
  -> ContactType 
  -> Maybe TimezoneId 
  -> Contact
contact id name email avatar ctype tz = Contact
  { id: id
  , name: name
  , email: email
  , avatarUrl: avatar
  , contactType: ctype
  , timezone: tz
  }

-- | Create a contact with ID string
contactWithId 
  :: String 
  -> String 
  -> Maybe String 
  -> Maybe String 
  -> ContactType 
  -> Maybe TimezoneId 
  -> Contact
contactWithId id = contact (ContactId id)

-- | Create a person contact (most common case)
person :: String -> String -> String -> Contact
person id name email = Contact
  { id: ContactId id
  , name: name
  , email: Just email
  , avatarUrl: Nothing
  , contactType: Person
  , timezone: Nothing
  }

-- | Create a room contact
room :: String -> String -> Contact
room id name = Contact
  { id: ContactId id
  , name: name
  , email: Nothing
  , avatarUrl: Nothing
  , contactType: Room
  , timezone: Nothing
  }

-- | Create a resource contact
resource :: String -> String -> Contact
resource id name = Contact
  { id: ContactId id
  , name: name
  , email: Nothing
  , avatarUrl: Nothing
  , contactType: Resource
  , timezone: Nothing
  }

-- | Create a group contact
group :: String -> String -> String -> Contact
group id name email = Contact
  { id: ContactId id
  , name: name
  , email: Just email
  , avatarUrl: Nothing
  , contactType: Group
  , timezone: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the contact ID
getId :: Contact -> ContactId
getId (Contact c) = c.id

-- | Get the contact name
getName :: Contact -> String
getName (Contact c) = c.name

-- | Get the contact email
getEmail :: Contact -> Maybe String
getEmail (Contact c) = c.email

-- | Get the avatar URL
getAvatarUrl :: Contact -> Maybe String
getAvatarUrl (Contact c) = c.avatarUrl

-- | Get the contact type
getContactType :: Contact -> ContactType
getContactType (Contact c) = c.contactType

-- | Get the contact's preferred timezone
getTimezone :: Contact -> Maybe TimezoneId
getTimezone (Contact c) = c.timezone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if contact is a person
isPerson :: Contact -> Boolean
isPerson (Contact c) = c.contactType == Person

-- | Check if contact is a resource (Room, Resource, or Group)
isResource :: Contact -> Boolean
isResource (Contact c) = c.contactType == Room 
  || c.contactType == Resource 
  || c.contactType == Group

-- | Check if contact has an email address
hasEmail :: Contact -> Boolean
hasEmail (Contact c) = isJust c.email

-- | Check if contact has an avatar
hasAvatar :: Contact -> Boolean
hasAvatar (Contact c) = isJust c.avatarUrl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get display name for the contact
toDisplayName :: Contact -> String
toDisplayName (Contact c) = c.name

-- | Format email for display or mailto link
toEmailString :: Contact -> String
toEmailString (Contact c) = case c.email of
  Nothing -> ""
  Just email -> c.name <> " <" <> email <> ">"
