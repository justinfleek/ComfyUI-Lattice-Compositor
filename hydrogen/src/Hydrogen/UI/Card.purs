-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // ui // card
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Component — Pure Element Version
-- |
-- | A composable card component with header, content, and footer sections.
-- | Built using the pure Element abstraction for multi-target rendering.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.UI.Card as Card
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Simple card
-- | Card.card []
-- |   [ Card.cardHeader []
-- |       [ Card.cardTitle "Welcome"
-- |       , Card.cardDescription "Getting started guide"
-- |       ]
-- |   , Card.cardContent []
-- |       [ E.p_ [] [ E.text "Your content here..." ] ]
-- |   , Card.cardFooter []
-- |       [ Button.button [ Button.onClick Save ] [ E.text "Save" ] ]
-- |   ]
-- | ```
module Hydrogen.UI.Card
  ( -- * Card Container
    card
  
  -- * Card Sections
  , cardHeader
  , cardTitle
  , cardDescription
  , cardContent
  , cardFooter
  
  -- * Configuration
  , CardConfig
  , defaultConfig
  
  -- * Config Modifiers
  , className
  , padding
  , shadow
  , bordered
  , hoverable
  
  -- * Variants
  , CardPadding(PaddingNone, PaddingSm, PaddingMd, PaddingLg)
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card padding options
data CardPadding
  = PaddingNone
  | PaddingSm
  | PaddingMd
  | PaddingLg

-- | Get Tailwind classes for padding
paddingClasses :: CardPadding -> String
paddingClasses = case _ of
  PaddingNone -> "p-0"
  PaddingSm -> "p-4"
  PaddingMd -> "p-6"
  PaddingLg -> "p-8"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card configuration
type CardConfig =
  { padding :: CardPadding
  , shadow :: Boolean
  , bordered :: Boolean
  , hoverable :: Boolean
  , className :: String
  }

-- | Default card configuration
defaultConfig :: CardConfig
defaultConfig =
  { padding: PaddingNone
  , shadow: true
  , bordered: true
  , hoverable: false
  , className: ""
  }

-- | Configuration modifier type
type ConfigMod = CardConfig -> CardConfig

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // config // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add custom CSS class
className :: String -> ConfigMod
className c config = config { className = config.className <> " " <> c }

-- | Set padding
padding :: CardPadding -> ConfigMod
padding p config = config { padding = p }

-- | Enable/disable shadow
shadow :: Boolean -> ConfigMod
shadow s config = config { shadow = s }

-- | Enable/disable border
bordered :: Boolean -> ConfigMod
bordered b config = config { bordered = b }

-- | Enable hover effect
hoverable :: Boolean -> ConfigMod
hoverable h config = config { hoverable = h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base card classes
baseClasses :: String
baseClasses = "rounded-lg bg-card text-card-foreground"

-- | Card container
-- |
-- | The main card wrapper that contains header, content, and footer sections.
card :: forall msg. Array ConfigMod -> Array (E.Element msg) -> E.Element msg
card mods children =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    shadowClass = if config.shadow then "shadow-sm" else ""
    borderClass = if config.bordered then "border" else ""
    hoverClass = if config.hoverable then "transition-shadow hover:shadow-md" else ""
    allClasses = baseClasses 
      <> " " <> paddingClasses config.padding
      <> " " <> shadowClass
      <> " " <> borderClass
      <> " " <> hoverClass
      <> " " <> config.className
  in
    E.div_ [ E.class_ allClasses ] children

-- | Card header section
-- |
-- | Contains title and optional description. Adds padding and spacing.
cardHeader :: forall msg. Array (E.Attribute msg) -> Array (E.Element msg) -> E.Element msg
cardHeader attrs children =
  E.div_ ([ E.class_ "flex flex-col space-y-1.5 p-6" ] <> attrs) children

-- | Card title
-- |
-- | Large heading text for the card.
cardTitle :: forall msg. String -> E.Element msg
cardTitle text =
  E.h3_ 
    [ E.class_ "text-2xl font-semibold leading-none tracking-tight" ] 
    [ E.text text ]

-- | Card description
-- |
-- | Muted description text below the title.
cardDescription :: forall msg. String -> E.Element msg
cardDescription text =
  E.p_ 
    [ E.class_ "text-sm text-muted-foreground" ] 
    [ E.text text ]

-- | Card content section
-- |
-- | Main content area with horizontal padding.
cardContent :: forall msg. Array (E.Attribute msg) -> Array (E.Element msg) -> E.Element msg
cardContent attrs children =
  E.div_ ([ E.class_ "p-6 pt-0" ] <> attrs) children

-- | Card footer section
-- |
-- | Footer area for actions, typically contains buttons.
cardFooter :: forall msg. Array (E.Attribute msg) -> Array (E.Element msg) -> E.Element msg
cardFooter attrs children =
  E.div_ ([ E.class_ "flex items-center p-6 pt-0" ] <> attrs) children
