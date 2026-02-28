-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // qrcode // document // styles
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Document Styles — Visual style configuration for QR codes.
-- |
-- | ## Style Options
-- |
-- | - QRStyle: Overall visual preset (classic, rounded, dots, etc.)
-- | - QRColors: Foreground/background colors
-- | - ModuleShape: Shape of individual modules
-- | - FinderStyle: Style of finder patterns (corners)
-- | - ModuleStyles: Per-module-type style configuration
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.Maybe (optional colors)

module Hydrogen.Element.Compound.QRCode.Document.Styles
  ( -- * QR Style Preset
    QRStyle(..)
  
  -- * Color Configuration
  , QRColors
  , defaultColors
  
  -- * Module Shapes
  , ModuleShape(..)
  
  -- * Finder Styles
  , FinderStyle(..)
  
  -- * Module Style Configuration
  , ModuleStyles
  , defaultModuleStyles
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
--                                                                   // qr style
-- ═════════════════════════════════════════════════════════════════════════════

-- | QR code visual style presets.
data QRStyle
  = StyleClassic      -- ^ Sharp square modules
  | StyleRounded      -- ^ Rounded corner modules
  | StyleDots         -- ^ Circular modules
  | StyleOrganic      -- ^ Merged bezier blob modules
  | StyleGradient     -- ^ Gradient-filled modules
  | StyleArtistic     -- ^ Full artistic with constraint awareness

derive instance eqQRStyle :: Eq QRStyle

instance showQRStyle :: Show QRStyle where
  show StyleClassic = "classic"
  show StyleRounded = "rounded"
  show StyleDots = "dots"
  show StyleOrganic = "organic"
  show StyleGradient = "gradient"
  show StyleArtistic = "artistic"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // qr colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color configuration for QR code.
type QRColors =
  { foreground :: String       -- ^ Module color (CSS color string)
  , background :: String       -- ^ Background color
  , finderForeground :: Maybe String  -- ^ Optional different finder color
  , finderBackground :: Maybe String  -- ^ Optional different finder background
  }

-- | Default black and white colors
defaultColors :: QRColors
defaultColors =
  { foreground: "#000000"
  , background: "#ffffff"
  , finderForeground: Nothing
  , finderBackground: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // module shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Module shape options.
data ModuleShape
  = ModuleSquare              -- ^ Standard square
  | ModuleRoundedSquare       -- ^ Rounded corners
  | ModuleCircle              -- ^ Circle/dot
  | ModuleDiamond             -- ^ 45-degree rotated square
  | ModuleHeart               -- ^ Heart shape
  | ModuleStar                -- ^ Star shape
  | ModuleHexagon             -- ^ Hexagon
  | ModuleCustomPath String   -- ^ Custom SVG path

derive instance eqModuleShape :: Eq ModuleShape

instance showModuleShape :: Show ModuleShape where
  show ModuleSquare = "square"
  show ModuleRoundedSquare = "rounded"
  show ModuleCircle = "circle"
  show ModuleDiamond = "diamond"
  show ModuleHeart = "heart"
  show ModuleStar = "star"
  show ModuleHexagon = "hexagon"
  show (ModuleCustomPath _) = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // finder style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Finder pattern style options.
data FinderStyle
  = FinderClassic             -- ^ Standard concentric squares
  | FinderRounded             -- ^ Rounded squares
  | FinderCircular            -- ^ Concentric circles
  | FinderDots                -- ^ Dot pattern
  | FinderCustom String String String  -- ^ Outer, middle, inner SVG paths

derive instance eqFinderStyle :: Eq FinderStyle

instance showFinderStyle :: Show FinderStyle where
  show FinderClassic = "classic"
  show FinderRounded = "rounded"
  show FinderCircular = "circular"
  show FinderDots = "dots"
  show (FinderCustom _ _ _) = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // module styles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-module-type style configuration.
type ModuleStyles =
  { dataModule :: ModuleShape
  , alignmentModule :: ModuleShape
  , timingModule :: ModuleShape
  , finderStyle :: FinderStyle
  }

-- | Default module styles
defaultModuleStyles :: ModuleStyles
defaultModuleStyles =
  { dataModule: ModuleSquare
  , alignmentModule: ModuleSquare
  , timingModule: ModuleSquare
  , finderStyle: FinderClassic
  }
