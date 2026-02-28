-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // qrcode // content // slack
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slack Content — QR encoding for Slack deep links.
-- |
-- | ## Encoding Format
-- |
-- | slack:// URI scheme:
-- | - Channel: slack://channel?team=WORKSPACE&id=CHANNEL
-- | - DM: slack://channel?team=WORKSPACE&id=USER_ID
-- |
-- | Note: Slack deep links have limited support for pre-filled messages.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional fields)

module Hydrogen.Element.Compound.QRCode.Content.Types.Slack
  ( -- * Slack Action Type
    SlackAction(SlackOpenChannel, SlackComposeMessage, SlackTriggerWorkflow)
  
  -- * Slack Content
  , SlackContent
  , slackChannel
  , slackUser
  , slackCompose
  
  -- * Encoding
  , encodeSlack
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing), maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // slack action
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slack action type.
data SlackAction
  = SlackOpenChannel         -- ^ Just open the channel
  | SlackComposeMessage      -- ^ Open composer
  | SlackTriggerWorkflow     -- ^ Trigger a workflow

derive instance eqSlackAction :: Eq SlackAction

instance showSlackAction :: Show SlackAction where
  show SlackOpenChannel = "open"
  show SlackComposeMessage = "compose"
  show SlackTriggerWorkflow = "workflow"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // slack content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slack deep link content.
type SlackContent =
  { workspace :: String        -- ^ Workspace ID or name
  , channel :: Maybe String    -- ^ Channel name (without #)
  , user :: Maybe String       -- ^ User ID for DM
  , message :: Maybe String    -- ^ Pre-filled message
  , action :: SlackAction
  }

-- | Create Slack channel link
slackChannel :: String -> String -> SlackContent
slackChannel workspace channel =
  { workspace
  , channel: Just channel
  , user: Nothing
  , message: Nothing
  , action: SlackOpenChannel
  }

-- | Create Slack DM link
slackUser :: String -> String -> SlackContent
slackUser workspace user =
  { workspace
  , channel: Nothing
  , user: Just user
  , message: Nothing
  , action: SlackOpenChannel
  }

-- | Create Slack compose link
slackCompose :: String -> String -> String -> SlackContent
slackCompose workspace channel message =
  { workspace
  , channel: Just channel
  , user: Nothing
  , message: Just message
  , action: SlackComposeMessage
  }

-- | Encode Slack to slack:// URI
encodeSlack :: SlackContent -> String
encodeSlack c =
  let
    base = "slack://channel?team=" <> c.workspace
    channelPart = maybe "" (\ch -> "&id=" <> ch) c.channel
    userPart = maybe "" (\u -> "&id=" <> u) c.user
    -- Note: Slack deep links have limited support for pre-filled messages
    -- This is a best-effort encoding
  in
    base <> channelPart <> userPart
