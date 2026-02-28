-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // qrcode // content // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Content Types — Structured data that QR codes can encode.
-- |
-- | ## Design Philosophy
-- |
-- | QR codes aren't just "strings encoded as squares." They encode **actions**:
-- | - Opening a URL
-- | - Sending an email
-- | - Connecting to WiFi
-- | - Adding a contact
-- | - Triggering a webhook
-- | - Starting a Slack conversation
-- |
-- | This module defines the ADT for all supported content types, each with
-- | its own structured configuration and encoding format.
-- |
-- | ## Module Structure
-- |
-- | This is the orchestrator module that re-exports all content types:
-- | - Types.Helpers: URI encoding utilities
-- | - Types.WiFi: WiFi network configuration
-- | - Types.VCard: Contact cards
-- | - Types.Calendar: Calendar events
-- | - Types.Geo: Geographic locations
-- | - Types.Bitcoin: Cryptocurrency payments
-- | - Types.Slack: Slack deep links
-- | - Types.Webhook: Webhook triggers
-- | - Types.DeepLink: App deep links
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)

module Hydrogen.Element.Compound.QRCode.Content.Types
  ( -- * Main Content ADT
    QRContent(..)
  , contentToString
  
  -- * URL Content
  , URLContent
  , urlContent
  , urlWithLabel
  
  -- * Email Content
  , EmailContent
  , emailContent
  , emailWithSubject
  , emailWithBody
  , emailFull
  
  -- * Phone Content
  , PhoneContent
  , phoneContent
  
  -- * SMS Content
  , SMSContent
  , smsContent
  , smsWithBody
  
  -- * WiFi Content (re-exported)
  , module WiFi
  
  -- * vCard Contact (re-exported)
  , module VCard
  
  -- * Calendar Event (re-exported)
  , module Calendar
  
  -- * Geo Location (re-exported)
  , module Geo
  
  -- * Bitcoin/Crypto (re-exported)
  , module Bitcoin
  
  -- * Slack (re-exported)
  , module Slack
  
  -- * Webhook (re-exported)
  , module Webhook
  
  -- * Deep Link (re-exported)
  , module DeepLink
  
  -- * Plain Text
  , textContent
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (/=)
  , (==)
  , map
  )

import Data.Array (filter, length)
import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.String (joinWith)
import Data.Tuple (Tuple(Tuple))

-- Re-exported modules
import Hydrogen.Element.Compound.QRCode.Content.Types.WiFi
  ( WiFiSecurity(WEP, WPA, WPA2, WPA3, NoPassword)
  , WiFiContent
  , wifiContent
  , wifiHidden
  , encodeWiFi
  ) as WiFi

import Hydrogen.Element.Compound.QRCode.Content.Types.VCard
  ( VCardContent
  , vCardContent
  , vCardFull
  , encodeVCard
  ) as VCard

import Hydrogen.Element.Compound.QRCode.Content.Types.Calendar
  ( CalendarContent
  , calendarContent
  , encodeCalendar
  ) as Calendar

import Hydrogen.Element.Compound.QRCode.Content.Types.Geo
  ( GeoContent
  , geoContent
  , geoWithAltitude
  , geoWithQuery
  , encodeGeo
  ) as Geo

import Hydrogen.Element.Compound.QRCode.Content.Types.Bitcoin
  ( BitcoinContent
  , bitcoinContent
  , bitcoinWithAmount
  , bitcoinFull
  , encodeBitcoin
  ) as Bitcoin

import Hydrogen.Element.Compound.QRCode.Content.Types.Slack
  ( SlackAction(SlackOpenChannel, SlackComposeMessage, SlackTriggerWorkflow)
  , SlackContent
  , slackChannel
  , slackUser
  , slackCompose
  , encodeSlack
  ) as Slack

import Hydrogen.Element.Compound.QRCode.Content.Types.Webhook
  ( HTTPMethod(GET, POST, PUT, DELETE, PATCH)
  , WebhookContent
  , webhookGet
  , webhookPost
  , encodeWebhook
  ) as Webhook

import Hydrogen.Element.Compound.QRCode.Content.Types.DeepLink
  ( DeepLinkContent
  , deepLink
  , deepLinkWithFallback
  , encodeDeepLink
  ) as DeepLink

import Hydrogen.Element.Compound.QRCode.Content.Types.Helpers (encodeURIComponent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // main content
-- ═════════════════════════════════════════════════════════════════════════════

-- | All supported QR code content types.
-- |
-- | Each variant encodes to a specific URI scheme or data format.
data QRContent
  = ContentURL URLContent              -- ^ Web URL (https://, http://)
  | ContentEmail EmailContent          -- ^ Email (mailto:)
  | ContentPhone PhoneContent          -- ^ Phone call (tel:)
  | ContentSMS SMSContent              -- ^ SMS message (sms:)
  | ContentWiFi WiFi.WiFiContent       -- ^ WiFi network config
  | ContentVCard VCard.VCardContent    -- ^ Contact card (vCard)
  | ContentCalendar Calendar.CalendarContent  -- ^ Calendar event (vEvent)
  | ContentGeo Geo.GeoContent          -- ^ Geographic location (geo:)
  | ContentBitcoin Bitcoin.BitcoinContent     -- ^ Bitcoin payment (bitcoin:)
  | ContentSlack Slack.SlackContent    -- ^ Slack deep link
  | ContentWebhook Webhook.WebhookContent     -- ^ Webhook trigger URL
  | ContentDeepLink DeepLink.DeepLinkContent  -- ^ App deep link
  | ContentText String                 -- ^ Plain text

derive instance eqQRContent :: Eq QRContent

instance showQRContent :: Show QRContent where
  show (ContentURL _) = "URL"
  show (ContentEmail _) = "Email"
  show (ContentPhone _) = "Phone"
  show (ContentSMS _) = "SMS"
  show (ContentWiFi _) = "WiFi"
  show (ContentVCard _) = "vCard"
  show (ContentCalendar _) = "Calendar"
  show (ContentGeo _) = "Geo"
  show (ContentBitcoin _) = "Bitcoin"
  show (ContentSlack _) = "Slack"
  show (ContentWebhook _) = "Webhook"
  show (ContentDeepLink _) = "DeepLink"
  show (ContentText _) = "Text"

-- | Convert content to encoded string for QR generation.
-- |
-- | This is the string that gets encoded into the QR matrix.
contentToString :: QRContent -> String
contentToString = case _ of
  ContentURL c -> encodeURL c
  ContentEmail c -> encodeEmail c
  ContentPhone c -> encodePhone c
  ContentSMS c -> encodeSMS c
  ContentWiFi c -> WiFi.encodeWiFi c
  ContentVCard c -> VCard.encodeVCard c
  ContentCalendar c -> Calendar.encodeCalendar c
  ContentGeo c -> Geo.encodeGeo c
  ContentBitcoin c -> Bitcoin.encodeBitcoin c
  ContentSlack c -> Slack.encodeSlack c
  ContentWebhook c -> Webhook.encodeWebhook c
  ContentDeepLink c -> DeepLink.encodeDeepLink c
  ContentText t -> t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // url content
-- ═════════════════════════════════════════════════════════════════════════════

-- | URL content configuration.
type URLContent =
  { url :: String
  , label :: Maybe String  -- ^ Optional human-readable label
  }

-- | Create URL content
urlContent :: String -> QRContent
urlContent url = ContentURL { url, label: Nothing }

-- | Create URL content with label
urlWithLabel :: String -> String -> QRContent
urlWithLabel url label = ContentURL { url, label: Just label }

-- | Encode URL to string
encodeURL :: URLContent -> String
encodeURL c = c.url

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // email content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Email content configuration.
type EmailContent =
  { to :: Array String      -- ^ Primary recipients
  , cc :: Array String      -- ^ CC recipients
  , bcc :: Array String     -- ^ BCC recipients
  , subject :: Maybe String -- ^ Email subject
  , body :: Maybe String    -- ^ Email body
  }

-- | Create simple email content
emailContent :: String -> QRContent
emailContent to = ContentEmail
  { to: [to]
  , cc: []
  , bcc: []
  , subject: Nothing
  , body: Nothing
  }

-- | Create email with subject
emailWithSubject :: String -> String -> QRContent
emailWithSubject to subject = ContentEmail
  { to: [to]
  , cc: []
  , bcc: []
  , subject: Just subject
  , body: Nothing
  }

-- | Create email with body
emailWithBody :: String -> String -> String -> QRContent
emailWithBody to subject body = ContentEmail
  { to: [to]
  , cc: []
  , bcc: []
  , subject: Just subject
  , body: Just body
  }

-- | Create full email configuration
emailFull :: Array String -> Array String -> Array String -> Maybe String -> Maybe String -> QRContent
emailFull to cc bcc subject body = ContentEmail { to, cc, bcc, subject, body }

-- | Encode email to mailto: URI
encodeEmail :: EmailContent -> String
encodeEmail c =
  let
    recipients = joinWith "," c.to
    params = filter (\(Tuple _ v) -> v /= "")
      [ Tuple "cc" (joinWith "," c.cc)
      , Tuple "bcc" (joinWith "," c.bcc)
      , Tuple "subject" (maybe "" encodeURIComponent c.subject)
      , Tuple "body" (maybe "" encodeURIComponent c.body)
      ]
    paramStr = if length params == 0
      then ""
      else "?" <> joinWith "&" (map (\(Tuple k v) -> k <> "=" <> v) params)
  in
    "mailto:" <> recipients <> paramStr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // phone content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phone content configuration.
type PhoneContent =
  { number :: String  -- ^ Phone number (with country code)
  }

-- | Create phone content
phoneContent :: String -> QRContent
phoneContent number = ContentPhone { number }

-- | Encode phone to tel: URI
encodePhone :: PhoneContent -> String
encodePhone c = "tel:" <> c.number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sms content
-- ═════════════════════════════════════════════════════════════════════════════

-- | SMS content configuration.
type SMSContent =
  { number :: String       -- ^ Phone number
  , body :: Maybe String   -- ^ Pre-filled message
  }

-- | Create SMS content
smsContent :: String -> QRContent
smsContent number = ContentSMS { number, body: Nothing }

-- | Create SMS with pre-filled body
smsWithBody :: String -> String -> QRContent
smsWithBody number body = ContentSMS { number, body: Just body }

-- | Encode SMS to sms: URI
encodeSMS :: SMSContent -> String
encodeSMS c =
  let
    base = "sms:" <> c.number
    bodyParam = maybe "" (\b -> "?body=" <> encodeURIComponent b) c.body
  in
    base <> bodyParam

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create plain text content
textContent :: String -> QRContent
textContent = ContentText
