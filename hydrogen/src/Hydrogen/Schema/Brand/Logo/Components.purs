-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // brand // logo // components
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo Components (§9): Building blocks of a logo.
-- |
-- | From SMART Brand Ingestion Framework §9:
-- |   - Icon: The symbol/mark element
-- |   - Wordmark: The typographic treatment of the brand name
-- |   - Symbolism: The narrative behind the icon choice

module Hydrogen.Schema.Brand.Logo.Components
  ( -- * Logo Component
    LogoComponent(..)
  , allLogoComponents
  , componentToString
  , componentFromString
  
    -- * Icon Description
  , IconDescription
  , mkIconDescription
  , unIconDescription
  
    -- * Wordmark Description
  , WordmarkDescription
  , mkWordmarkDescription
  , unWordmarkDescription
  
    -- * Logo Symbolism
  , LogoSymbolism
  , mkLogoSymbolism
  , unLogoSymbolism
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>)
  , (<=)
  , (&&)
  , (<>)
  , compare
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // logo component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logo component atom.
-- |
-- | The fundamental building blocks of a logo:
-- |   Icon: The symbol/mark element
-- |   Wordmark: The typographic treatment of the brand name
data LogoComponent
  = Icon
  | Wordmark

derive instance eqLogoComponent :: Eq LogoComponent

instance ordLogoComponent :: Ord LogoComponent where
  compare c1 c2 = compare (componentToInt c1) (componentToInt c2)
    where
      componentToInt :: LogoComponent -> Int
      componentToInt Icon = 0
      componentToInt Wordmark = 1

instance showLogoComponent :: Show LogoComponent where
  show = componentToString

-- | All logo components for enumeration.
allLogoComponents :: Array LogoComponent
allLogoComponents = [Icon, Wordmark]

-- | Convert component to string.
componentToString :: LogoComponent -> String
componentToString Icon = "icon"
componentToString Wordmark = "wordmark"

-- | Parse component from string.
componentFromString :: String -> Maybe LogoComponent
componentFromString s = case String.toLower s of
  "icon" -> Just Icon
  "wordmark" -> Just Wordmark
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // icon description
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon description atom.
-- |
-- | Description of the icon/symbol element and its meaning.
-- | Bounded: 1-500 characters.
newtype IconDescription = IconDescription String

derive instance eqIconDescription :: Eq IconDescription
derive instance ordIconDescription :: Ord IconDescription

instance showIconDescription :: Show IconDescription where
  show (IconDescription d) = "IconDescription(" <> d <> ")"

-- | Smart constructor for icon description.
mkIconDescription :: String -> Maybe IconDescription
mkIconDescription s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 500
     then Just (IconDescription trimmed)
     else Nothing

-- | Unwrap icon description.
unIconDescription :: IconDescription -> String
unIconDescription (IconDescription d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // wordmark description
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wordmark description atom.
-- |
-- | Description of the typographic treatment of the brand name.
-- | Bounded: 1-500 characters.
newtype WordmarkDescription = WordmarkDescription String

derive instance eqWordmarkDescription :: Eq WordmarkDescription
derive instance ordWordmarkDescription :: Ord WordmarkDescription

instance showWordmarkDescription :: Show WordmarkDescription where
  show (WordmarkDescription d) = "WordmarkDescription(" <> d <> ")"

-- | Smart constructor for wordmark description.
mkWordmarkDescription :: String -> Maybe WordmarkDescription
mkWordmarkDescription s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 500
     then Just (WordmarkDescription trimmed)
     else Nothing

-- | Unwrap wordmark description.
unWordmarkDescription :: WordmarkDescription -> String
unWordmarkDescription (WordmarkDescription d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // logo symbolism
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logo symbolism atom.
-- |
-- | The narrative behind the icon choice, connecting to brand values.
-- | Bounded: 1-1000 characters.
newtype LogoSymbolism = LogoSymbolism String

derive instance eqLogoSymbolism :: Eq LogoSymbolism
derive instance ordLogoSymbolism :: Ord LogoSymbolism

instance showLogoSymbolism :: Show LogoSymbolism where
  show (LogoSymbolism s) = "LogoSymbolism(" <> s <> ")"

-- | Smart constructor for logo symbolism.
mkLogoSymbolism :: String -> Maybe LogoSymbolism
mkLogoSymbolism s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 1000
     then Just (LogoSymbolism trimmed)
     else Nothing

-- | Unwrap logo symbolism.
unLogoSymbolism :: LogoSymbolism -> String
unLogoSymbolism (LogoSymbolism s) = s
