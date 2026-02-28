-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // qrcode // content // webhook
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Webhook Content — QR encoding for webhook triggers.
-- |
-- | ## Design Note
-- |
-- | QR codes can only encode URLs. The actual webhook triggering happens
-- | when the user opens the URL, which should point to a service that
-- | performs the webhook call (e.g., a serverless function).
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)

module Hydrogen.Element.Compound.QRCode.Content.Types.Webhook
  ( -- * HTTP Method
    HTTPMethod(GET, POST, PUT, DELETE, PATCH)
  
  -- * Webhook Content
  , WebhookContent
  , webhookGet
  , webhookPost
  
  -- * Encoding
  , encodeWebhook
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // http method
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTTP method for webhooks.
data HTTPMethod
  = GET
  | POST
  | PUT
  | DELETE
  | PATCH

derive instance eqHTTPMethod :: Eq HTTPMethod

instance showHTTPMethod :: Show HTTPMethod where
  show GET = "GET"
  show POST = "POST"
  show PUT = "PUT"
  show DELETE = "DELETE"
  show PATCH = "PATCH"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // webhook content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Webhook trigger content.
-- |
-- | Note: QR codes can only encode URLs. The actual webhook triggering
-- | happens when the user opens the URL, which should point to a service
-- | that performs the webhook call (e.g., a serverless function).
type WebhookContent =
  { url :: String
  , method :: HTTPMethod
  , description :: String      -- ^ Human-readable description of what happens
  }

-- | Create GET webhook
webhookGet :: String -> String -> WebhookContent
webhookGet url description =
  { url, method: GET, description }

-- | Create POST webhook
webhookPost :: String -> String -> WebhookContent
webhookPost url description =
  { url, method: POST, description }

-- | Encode webhook to URL
-- |
-- | The URL should be a trigger endpoint that performs the actual webhook.
encodeWebhook :: WebhookContent -> String
encodeWebhook c = c.url
