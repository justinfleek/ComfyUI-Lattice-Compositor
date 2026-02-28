-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // qrcode // document // logo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Document Logo — Logo overlay configuration for QR codes.
-- |
-- | ## Logo Types
-- |
-- | - LogoImage: Image file (PNG, SVG, data URI)
-- | - LogoText: Text rendered as logo
-- | - LogoShape: Custom SVG path shape
-- | - LogoIcon: Icon from icon set
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional stroke)

module Hydrogen.Element.Compound.QRCode.Document.Logo
  ( -- * Logo Configuration
    LogoConfig(..)
  
  -- * Logo Constructors
  , imageLogo
  , textLogo
  , shapeLogo
  , iconLogo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // logo config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logo configuration for center overlay.
data LogoConfig
  = LogoImage
      { src :: String          -- ^ Image URL or data URI
      , width :: Number        -- ^ Width in pixels
      , height :: Number       -- ^ Height in pixels
      , padding :: Number      -- ^ Padding around logo
      , borderRadius :: Number -- ^ Corner radius
      }
  | LogoText
      { text :: String         -- ^ Text to display
      , fontSize :: Number     -- ^ Font size in pixels
      , fontWeight :: String   -- ^ Font weight (normal, bold, 600, etc.)
      , fontFamily :: String   -- ^ Font family
      , color :: String        -- ^ Text color
      }
  | LogoShape
      { svgPath :: String      -- ^ SVG path data
      , width :: Number
      , height :: Number
      , fill :: String         -- ^ Fill color
      , stroke :: Maybe String -- ^ Optional stroke
      }
  | LogoIcon
      { name :: String         -- ^ Icon name (from icon set)
      , size :: Number         -- ^ Icon size
      , color :: String        -- ^ Icon color
      }

derive instance eqLogoConfig :: Eq LogoConfig

instance showLogoConfig :: Show LogoConfig where
  show (LogoImage _) = "image"
  show (LogoText r) = "text:" <> r.text
  show (LogoShape _) = "shape"
  show (LogoIcon r) = "icon:" <> r.name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // logo constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create image logo
imageLogo :: String -> Number -> Number -> LogoConfig
imageLogo src width height = LogoImage
  { src, width, height, padding: 4.0, borderRadius: 4.0 }

-- | Create text logo
textLogo :: String -> Number -> String -> LogoConfig
textLogo text fontSize fontWeight = LogoText
  { text, fontSize, fontWeight, fontFamily: "system-ui, sans-serif", color: "#000000" }

-- | Create shape logo from SVG path
shapeLogo :: String -> Number -> Number -> String -> LogoConfig
shapeLogo svgPath width height fill = LogoShape
  { svgPath, width, height, fill, stroke: Nothing }

-- | Create icon logo
iconLogo :: String -> Number -> String -> LogoConfig
iconLogo name size color = LogoIcon { name, size, color }
