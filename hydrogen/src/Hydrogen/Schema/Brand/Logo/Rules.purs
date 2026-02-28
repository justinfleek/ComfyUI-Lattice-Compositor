-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // brand // logo // rules
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo Rules (§13): Watermark and social media rules.
-- |
-- | From SMART Brand Ingestion Framework §13:
-- |   - WatermarkRule: Opacity and lockup for watermark usage
-- |   - SocialRule: Platform-specific logo usage rules

module Hydrogen.Schema.Brand.Logo.Rules
  ( -- * Watermark Opacity
    WatermarkOpacity
  , mkWatermarkOpacity
  , unWatermarkOpacity
  
    -- * Watermark Rule
  , WatermarkRule
  , mkWatermarkRule
  , watermarkOpacity
  , watermarkLockup
  , showWatermarkRule
  
    -- * Social Platform
  , SocialPlatform(..)
  , allSocialPlatforms
  , platformToString
  
    -- * Social Rule
  , SocialRule
  , mkSocialRule
  , socialPlatform
  , socialLockup
  , showSocialRule
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  , compare
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Brand.Logo.Lockup (LockupName, unLockupName)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // watermark opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Watermark opacity atom.
-- |
-- | Opacity for watermark usage.
-- | Bounded: 0.01 to 1.0 (must be visible but not overwhelming).
newtype WatermarkOpacity = WatermarkOpacity Number

derive instance eqWatermarkOpacity :: Eq WatermarkOpacity
derive instance ordWatermarkOpacity :: Ord WatermarkOpacity

instance showWatermarkOpacity :: Show WatermarkOpacity where
  show (WatermarkOpacity o) = "WatermarkOpacity(" <> show o <> ")"

-- | Smart constructor for watermark opacity.
mkWatermarkOpacity :: Number -> Maybe WatermarkOpacity
mkWatermarkOpacity n =
  if n >= 0.01 && n <= 1.0
  then Just (WatermarkOpacity n)
  else Nothing

-- | Unwrap opacity.
unWatermarkOpacity :: WatermarkOpacity -> Number
unWatermarkOpacity (WatermarkOpacity o) = o

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // watermark rule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Watermark rule molecule.
-- |
-- | Specification for logo usage as watermark.
type WatermarkRule =
  { opacity :: WatermarkOpacity
  , lockupRef :: LockupName  -- Which lockup to use for watermarks
  }

-- | Create a watermark rule.
mkWatermarkRule :: WatermarkOpacity -> LockupName -> WatermarkRule
mkWatermarkRule o l = { opacity: o, lockupRef: l }

-- | Get watermark opacity.
watermarkOpacity :: WatermarkRule -> WatermarkOpacity
watermarkOpacity w = w.opacity

-- | Get watermark lockup reference.
watermarkLockup :: WatermarkRule -> LockupName
watermarkLockup w = w.lockupRef

-- | Show watermark rule (debug format).
showWatermarkRule :: WatermarkRule -> String
showWatermarkRule w =
  "WatermarkRule { opacity: " <> show (unWatermarkOpacity w.opacity) <>
  ", lockup: \"" <> unLockupName w.lockupRef <> "\" }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // social platform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Social platform atom.
-- |
-- | Major social media platforms with distinct sizing requirements.
data SocialPlatform
  = Twitter
  | LinkedIn
  | Facebook
  | Instagram
  | YouTube
  | TikTok
  | Discord
  | Slack

derive instance eqSocialPlatform :: Eq SocialPlatform

instance ordSocialPlatform :: Ord SocialPlatform where
  compare p1 p2 = compare (platformToInt p1) (platformToInt p2)
    where
      platformToInt :: SocialPlatform -> Int
      platformToInt Twitter = 0
      platformToInt LinkedIn = 1
      platformToInt Facebook = 2
      platformToInt Instagram = 3
      platformToInt YouTube = 4
      platformToInt TikTok = 5
      platformToInt Discord = 6
      platformToInt Slack = 7

instance showSocialPlatform :: Show SocialPlatform where
  show = platformToString

-- | All social platforms for enumeration.
allSocialPlatforms :: Array SocialPlatform
allSocialPlatforms = 
  [ Twitter
  , LinkedIn
  , Facebook
  , Instagram
  , YouTube
  , TikTok
  , Discord
  , Slack
  ]

-- | Convert platform to string.
platformToString :: SocialPlatform -> String
platformToString Twitter = "twitter"
platformToString LinkedIn = "linkedin"
platformToString Facebook = "facebook"
platformToString Instagram = "instagram"
platformToString YouTube = "youtube"
platformToString TikTok = "tiktok"
platformToString Discord = "discord"
platformToString Slack = "slack"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // social rule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Social rule molecule.
-- |
-- | Platform-specific logo usage rule.
type SocialRule =
  { platform :: SocialPlatform
  , lockupRef :: LockupName  -- Which lockup to use for this platform
  }

-- | Create a social rule.
mkSocialRule :: SocialPlatform -> LockupName -> SocialRule
mkSocialRule p l = { platform: p, lockupRef: l }

-- | Get platform.
socialPlatform :: SocialRule -> SocialPlatform
socialPlatform s = s.platform

-- | Get lockup reference.
socialLockup :: SocialRule -> LockupName
socialLockup s = s.lockupRef

-- | Show social rule (debug format).
showSocialRule :: SocialRule -> String
showSocialRule s =
  "SocialRule { platform: " <> platformToString s.platform <>
  ", lockup: \"" <> unLockupName s.lockupRef <> "\" }"
