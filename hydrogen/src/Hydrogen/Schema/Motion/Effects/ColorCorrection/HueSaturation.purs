-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--           // hydrogen // schema // motion // effects // color // hue-saturation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hue/Saturation Effect — Industry-standard HSL color adjustment.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Hue/Saturation effect with:
-- |
-- | - **Master controls**: Affect all colors
-- | - **Per-color controls**: Reds, Yellows, Greens, Cyans, Blues, Magentas
-- | - **Colorize mode**: Tint entire image with single hue
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | hue | Number | -180 | 180 | wraps | 0 |
-- | | saturation | Number | -100 | 100 | clamps | 0 |
-- | | lightness | Number | -100 | 100 | clamps | 0 |
-- |
-- | ## Colorize Mode
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | colorizeHue | Number | 0 | 359 | wraps | 0 |
-- | | colorizeSaturation | Number | 0 | 100 | clamps | 25 |
-- | | colorizeLightness | Number | -100 | 100 | clamps | 0 |

module Hydrogen.Schema.Motion.Effects.ColorCorrection.HueSaturation
  ( -- * Color Channel
    ColorChannel(..)
  , allColorChannels
  , colorChannelToString
  
  -- * Channel Adjustment
  , ChannelAdjustment(..)
  , defaultChannelAdjustment
  , mkChannelAdjustment
  
  -- * Colorize Settings
  , ColorizeSettings(..)
  , defaultColorizeSettings
  , mkColorizeSettings
  
  -- * Hue/Saturation Effect
  , HueSaturationEffect(..)
  , defaultHueSaturationEffect
  , mkHueSaturationEffect
  
  -- * Accessors
  , masterAdjustment
  , redsAdjustment
  , yellowsAdjustment
  , greensAdjustment
  , cyansAdjustment
  , bluesAdjustment
  , magentasAdjustment
  , colorizeEnabled
  , colorizeSettings
  
  -- * Channel Accessors
  , channelHue
  , channelSaturation
  , channelLightness
  
  -- * Operations
  , setMasterAdjustment
  , setChannelAdjustment
  , enableColorize
  , disableColorize
  , setColorizeHue
  , setColorizeSaturation
  
  -- * Presets
  , hueSatDesaturate
  , hueSatVibrant
  , hueSatSepia
  , hueSatCoolTone
  , hueSatWarmTone
  , hueSatNightVision
  
  -- * Queries
  , isChannelNeutral
  , isEffectNeutral
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , not
  , (<>)
  , (==)
  , (&&)
  )

import Hydrogen.Schema.Color.Hue 
  ( Hue
  , hue
  , HueShift
  , hueShift
  , noHueShift
  , unwrapHueShift
  )
import Hydrogen.Schema.Dimension.Percentage
  ( Percent
  , percent
  , SignedPercent
  , signedPercent
  , unwrapSignedPercent
  , zeroSignedPercent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color channel for per-color adjustment.
data ColorChannel
  = CCMaster     -- ^ All colors
  | CCReds       -- ^ Red hues
  | CCYellows    -- ^ Yellow hues
  | CCGreens     -- ^ Green hues
  | CCCyans      -- ^ Cyan hues
  | CCBlues      -- ^ Blue hues
  | CCMagentas   -- ^ Magenta hues

derive instance eqColorChannel :: Eq ColorChannel
derive instance ordColorChannel :: Ord ColorChannel

instance showColorChannel :: Show ColorChannel where
  show = colorChannelToString

-- | All color channels for enumeration.
allColorChannels :: Array ColorChannel
allColorChannels = 
  [ CCMaster, CCReds, CCYellows, CCGreens, CCCyans, CCBlues, CCMagentas ]

-- | Convert to string.
colorChannelToString :: ColorChannel -> String
colorChannelToString CCMaster = "Master"
colorChannelToString CCReds = "Reds"
colorChannelToString CCYellows = "Yellows"
colorChannelToString CCGreens = "Greens"
colorChannelToString CCCyans = "Cyans"
colorChannelToString CCBlues = "Blues"
colorChannelToString CCMagentas = "Magentas"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // channel // adjustment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue/Saturation/Lightness adjustment for a color channel.
-- |
-- | All properties are animatable.
newtype ChannelAdjustment = ChannelAdjustment
  { hue :: HueShift              -- ^ Hue shift (-180 to 180, wraps)
  , saturation :: SignedPercent  -- ^ Saturation adjustment (-100 to 100)
  , lightness :: SignedPercent   -- ^ Lightness adjustment (-100 to 100)
  }

derive instance eqChannelAdjustment :: Eq ChannelAdjustment

instance showChannelAdjustment :: Show ChannelAdjustment where
  show (ChannelAdjustment c) =
    "Adjustment { H: " <> show c.hue
    <> ", S: " <> show c.saturation
    <> ", L: " <> show c.lightness <> " }"

-- | Default channel adjustment (no change).
defaultChannelAdjustment :: ChannelAdjustment
defaultChannelAdjustment = ChannelAdjustment
  { hue: noHueShift
  , saturation: zeroSignedPercent
  , lightness: zeroSignedPercent
  }

-- | Create channel adjustment with bounds validation.
mkChannelAdjustment :: Number -> Number -> Number -> ChannelAdjustment
mkChannelAdjustment h s l = ChannelAdjustment
  { hue: hueShift h
  , saturation: signedPercent s
  , lightness: signedPercent l
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // channel // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get hue shift.
channelHue :: ChannelAdjustment -> HueShift
channelHue (ChannelAdjustment c) = c.hue

-- | Get saturation adjustment.
channelSaturation :: ChannelAdjustment -> SignedPercent
channelSaturation (ChannelAdjustment c) = c.saturation

-- | Get lightness adjustment.
channelLightness :: ChannelAdjustment -> SignedPercent
channelLightness (ChannelAdjustment c) = c.lightness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // colorize // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Colorize mode settings.
-- |
-- | Tints entire image with a single hue.
newtype ColorizeSettings = ColorizeSettings
  { hue :: Hue                   -- ^ Colorize hue (0-359, wraps)
  , saturation :: Percent        -- ^ Colorize saturation (0-100)
  , lightness :: SignedPercent   -- ^ Lightness adjustment (-100 to 100)
  }

derive instance eqColorizeSettings :: Eq ColorizeSettings

instance showColorizeSettings :: Show ColorizeSettings where
  show (ColorizeSettings c) =
    "Colorize { H: " <> show c.hue
    <> ", S: " <> show c.saturation
    <> ", L: " <> show c.lightness <> " }"

-- | Default colorize settings.
defaultColorizeSettings :: ColorizeSettings
defaultColorizeSettings = ColorizeSettings
  { hue: hue 0
  , saturation: percent 25.0
  , lightness: zeroSignedPercent
  }

-- | Create colorize settings with bounds validation.
mkColorizeSettings :: Int -> Number -> Number -> ColorizeSettings
mkColorizeSettings h s l = ColorizeSettings
  { hue: hue h
  , saturation: percent s
  , lightness: signedPercent l
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // hue-saturation // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Hue/Saturation effect with per-channel control.
newtype HueSaturationEffect = HueSaturationEffect
  { master :: ChannelAdjustment    -- ^ Master (all colors)
  , reds :: ChannelAdjustment      -- ^ Reds
  , yellows :: ChannelAdjustment   -- ^ Yellows
  , greens :: ChannelAdjustment    -- ^ Greens
  , cyans :: ChannelAdjustment     -- ^ Cyans
  , blues :: ChannelAdjustment     -- ^ Blues
  , magentas :: ChannelAdjustment  -- ^ Magentas
  , colorize :: Boolean            -- ^ Enable colorize mode
  , colorizeSettings :: ColorizeSettings
  }

derive instance eqHueSaturationEffect :: Eq HueSaturationEffect

instance showHueSaturationEffect :: Show HueSaturationEffect where
  show (HueSaturationEffect e) =
    "HueSaturationEffect { colorize: " <> show e.colorize <> " }"

-- | Default hue/saturation effect (no adjustment).
defaultHueSaturationEffect :: HueSaturationEffect
defaultHueSaturationEffect = HueSaturationEffect
  { master: defaultChannelAdjustment
  , reds: defaultChannelAdjustment
  , yellows: defaultChannelAdjustment
  , greens: defaultChannelAdjustment
  , cyans: defaultChannelAdjustment
  , blues: defaultChannelAdjustment
  , magentas: defaultChannelAdjustment
  , colorize: false
  , colorizeSettings: defaultColorizeSettings
  }

-- | Create hue/saturation effect with master adjustment.
mkHueSaturationEffect :: ChannelAdjustment -> HueSaturationEffect
mkHueSaturationEffect masterAdj = HueSaturationEffect
  { master: masterAdj
  , reds: defaultChannelAdjustment
  , yellows: defaultChannelAdjustment
  , greens: defaultChannelAdjustment
  , cyans: defaultChannelAdjustment
  , blues: defaultChannelAdjustment
  , magentas: defaultChannelAdjustment
  , colorize: false
  , colorizeSettings: defaultColorizeSettings
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // effect // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get master adjustment.
masterAdjustment :: HueSaturationEffect -> ChannelAdjustment
masterAdjustment (HueSaturationEffect e) = e.master

-- | Get reds adjustment.
redsAdjustment :: HueSaturationEffect -> ChannelAdjustment
redsAdjustment (HueSaturationEffect e) = e.reds

-- | Get yellows adjustment.
yellowsAdjustment :: HueSaturationEffect -> ChannelAdjustment
yellowsAdjustment (HueSaturationEffect e) = e.yellows

-- | Get greens adjustment.
greensAdjustment :: HueSaturationEffect -> ChannelAdjustment
greensAdjustment (HueSaturationEffect e) = e.greens

-- | Get cyans adjustment.
cyansAdjustment :: HueSaturationEffect -> ChannelAdjustment
cyansAdjustment (HueSaturationEffect e) = e.cyans

-- | Get blues adjustment.
bluesAdjustment :: HueSaturationEffect -> ChannelAdjustment
bluesAdjustment (HueSaturationEffect e) = e.blues

-- | Get magentas adjustment.
magentasAdjustment :: HueSaturationEffect -> ChannelAdjustment
magentasAdjustment (HueSaturationEffect e) = e.magentas

-- | Is colorize mode enabled?
colorizeEnabled :: HueSaturationEffect -> Boolean
colorizeEnabled (HueSaturationEffect e) = e.colorize

-- | Get colorize settings.
colorizeSettings :: HueSaturationEffect -> ColorizeSettings
colorizeSettings (HueSaturationEffect e) = e.colorizeSettings

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // effect // setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set master adjustment.
setMasterAdjustment :: ChannelAdjustment -> HueSaturationEffect -> HueSaturationEffect
setMasterAdjustment adj (HueSaturationEffect e) = 
  HueSaturationEffect e { master = adj }

-- | Set adjustment for a specific color channel.
setChannelAdjustment :: ColorChannel -> ChannelAdjustment -> HueSaturationEffect -> HueSaturationEffect
setChannelAdjustment CCMaster adj (HueSaturationEffect e) = 
  HueSaturationEffect e { master = adj }
setChannelAdjustment CCReds adj (HueSaturationEffect e) = 
  HueSaturationEffect e { reds = adj }
setChannelAdjustment CCYellows adj (HueSaturationEffect e) = 
  HueSaturationEffect e { yellows = adj }
setChannelAdjustment CCGreens adj (HueSaturationEffect e) = 
  HueSaturationEffect e { greens = adj }
setChannelAdjustment CCCyans adj (HueSaturationEffect e) = 
  HueSaturationEffect e { cyans = adj }
setChannelAdjustment CCBlues adj (HueSaturationEffect e) = 
  HueSaturationEffect e { blues = adj }
setChannelAdjustment CCMagentas adj (HueSaturationEffect e) = 
  HueSaturationEffect e { magentas = adj }

-- | Enable colorize mode.
enableColorize :: HueSaturationEffect -> HueSaturationEffect
enableColorize (HueSaturationEffect e) = 
  HueSaturationEffect e { colorize = true }

-- | Disable colorize mode.
disableColorize :: HueSaturationEffect -> HueSaturationEffect
disableColorize (HueSaturationEffect e) = 
  HueSaturationEffect e { colorize = false }

-- | Set colorize hue.
setColorizeHue :: Hue -> HueSaturationEffect -> HueSaturationEffect
setColorizeHue h (HueSaturationEffect e) =
  let (ColorizeSettings cs) = e.colorizeSettings
  in HueSaturationEffect e 
       { colorizeSettings = ColorizeSettings cs { hue = h } }

-- | Set colorize saturation.
setColorizeSaturation :: Percent -> HueSaturationEffect -> HueSaturationEffect
setColorizeSaturation s (HueSaturationEffect e) =
  let (ColorizeSettings cs) = e.colorizeSettings
  in HueSaturationEffect e 
       { colorizeSettings = ColorizeSettings cs { saturation = s } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Desaturate (grayscale).
hueSatDesaturate :: HueSaturationEffect
hueSatDesaturate = HueSaturationEffect
  { master: mkChannelAdjustment 0.0 (-100.0) 0.0
  , reds: defaultChannelAdjustment
  , yellows: defaultChannelAdjustment
  , greens: defaultChannelAdjustment
  , cyans: defaultChannelAdjustment
  , blues: defaultChannelAdjustment
  , magentas: defaultChannelAdjustment
  , colorize: false
  , colorizeSettings: defaultColorizeSettings
  }

-- | Vibrant colors (boost saturation).
hueSatVibrant :: HueSaturationEffect
hueSatVibrant = HueSaturationEffect
  { master: mkChannelAdjustment 0.0 40.0 0.0
  , reds: defaultChannelAdjustment
  , yellows: defaultChannelAdjustment
  , greens: defaultChannelAdjustment
  , cyans: defaultChannelAdjustment
  , blues: defaultChannelAdjustment
  , magentas: defaultChannelAdjustment
  , colorize: false
  , colorizeSettings: defaultColorizeSettings
  }

-- | Sepia tone (colorize).
hueSatSepia :: HueSaturationEffect
hueSatSepia = HueSaturationEffect
  { master: defaultChannelAdjustment
  , reds: defaultChannelAdjustment
  , yellows: defaultChannelAdjustment
  , greens: defaultChannelAdjustment
  , cyans: defaultChannelAdjustment
  , blues: defaultChannelAdjustment
  , magentas: defaultChannelAdjustment
  , colorize: true
  , colorizeSettings: mkColorizeSettings 30 25.0 0.0
  }

-- | Cool tone (shift toward blue).
hueSatCoolTone :: HueSaturationEffect
hueSatCoolTone = HueSaturationEffect
  { master: mkChannelAdjustment (-15.0) 0.0 0.0
  , reds: defaultChannelAdjustment
  , yellows: mkChannelAdjustment (-10.0) (-20.0) 0.0
  , greens: defaultChannelAdjustment
  , cyans: mkChannelAdjustment 0.0 20.0 0.0
  , blues: mkChannelAdjustment 0.0 20.0 0.0
  , magentas: defaultChannelAdjustment
  , colorize: false
  , colorizeSettings: defaultColorizeSettings
  }

-- | Warm tone (shift toward orange).
hueSatWarmTone :: HueSaturationEffect
hueSatWarmTone = HueSaturationEffect
  { master: mkChannelAdjustment 15.0 0.0 0.0
  , reds: mkChannelAdjustment 0.0 20.0 0.0
  , yellows: mkChannelAdjustment 10.0 20.0 0.0
  , greens: defaultChannelAdjustment
  , cyans: mkChannelAdjustment 0.0 (-20.0) 0.0
  , blues: mkChannelAdjustment 0.0 (-20.0) 0.0
  , magentas: defaultChannelAdjustment
  , colorize: false
  , colorizeSettings: defaultColorizeSettings
  }

-- | Night vision (green tint).
hueSatNightVision :: HueSaturationEffect
hueSatNightVision = HueSaturationEffect
  { master: defaultChannelAdjustment
  , reds: defaultChannelAdjustment
  , yellows: defaultChannelAdjustment
  , greens: defaultChannelAdjustment
  , cyans: defaultChannelAdjustment
  , blues: defaultChannelAdjustment
  , magentas: defaultChannelAdjustment
  , colorize: true
  , colorizeSettings: mkColorizeSettings 120 50.0 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is channel adjustment neutral (no change)?
isChannelNeutral :: ChannelAdjustment -> Boolean
isChannelNeutral (ChannelAdjustment c) =
  unwrapHueShift c.hue == 0.0 
  && unwrapSignedPercent c.saturation == 0.0 
  && unwrapSignedPercent c.lightness == 0.0

-- | Is entire effect neutral (no adjustment)?
isEffectNeutral :: HueSaturationEffect -> Boolean
isEffectNeutral (HueSaturationEffect e) =
  not e.colorize &&
  isChannelNeutral e.master &&
  isChannelNeutral e.reds &&
  isChannelNeutral e.yellows &&
  isChannelNeutral e.greens &&
  isChannelNeutral e.cyans &&
  isChannelNeutral e.blues &&
  isChannelNeutral e.magentas


