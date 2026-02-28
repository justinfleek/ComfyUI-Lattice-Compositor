-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // locale
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internationalization (i18n) support
-- |
-- | Type-safe translations with pluralization, interpolation, and locale management.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.I18n.Locale as I18n
-- |
-- | -- Create i18n instance
-- | i18n <- I18n.create
-- |   { defaultLocale: "en"
-- |   , fallbackLocale: "en"
-- |   , translations: 
-- |       { en: { greeting: "Hello", items: { one: "1 item", other: "{count} items" } }
-- |       , es: { greeting: "Hola", items: { one: "1 artículo", other: "{count} artículos" } }
-- |       }
-- |   }
-- |
-- | -- Translate
-- | greeting <- I18n.t i18n "greeting"  -- "Hello"
-- |
-- | -- With interpolation
-- | message <- I18n.t' i18n "welcome" { name: "Alice" }  -- "Welcome, Alice!"
-- |
-- | -- Pluralization
-- | items <- I18n.plural i18n "items" 5  -- "5 items"
-- |
-- | -- Change locale
-- | I18n.setLocale i18n "es"
-- | ```
module Hydrogen.I18n.Locale
  ( -- * Types
    I18n
  , I18nConfig
  , Locale
  , TranslationKey
  , Translations
    -- * Initialization
  , create
  , createWithLoader
    -- * Translation
  , t
  , t'
  , tMaybe
  , plural
  , pluralWith
    -- * Locale Management
  , getLocale
  , setLocale
  , getAvailableLocales
  , onLocaleChange
    -- * Formatting
  , formatNumber
  , formatCurrency
  , formatDate
  , formatRelativeTime
    -- * Utilities
  , hasTranslation
  , getDirection
  , isRTL
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.String as String
import Data.String.Regex (Regex, regex, replace)
import Data.String.Regex.Flags (global)
import Data.Either (hush)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object as Object

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | I18n instance
newtype I18n = I18n
  { locale :: Ref Locale
  , config :: I18nConfig
  , translations :: Ref Translations
  , listeners :: Ref (Array { id :: Int, callback :: Locale -> Effect Unit })
  }

-- | I18n configuration
type I18nConfig =
  { defaultLocale :: Locale
  , fallbackLocale :: Locale
  , interpolationPrefix :: String
  , interpolationSuffix :: String
  }

-- | Locale identifier (e.g., "en", "en-US", "es")
type Locale = String

-- | Translation key (dot-separated path, e.g., "common.buttons.submit")
type TranslationKey = String

-- | Translations map: locale -> key -> value
type Translations = Map.Map Locale (Map.Map TranslationKey String)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // initialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default configuration
defaultConfig :: I18nConfig
defaultConfig =
  { defaultLocale: "en"
  , fallbackLocale: "en"
  , interpolationPrefix: "{"
  , interpolationSuffix: "}"
  }

-- | Create an I18n instance with inline translations
create :: I18nConfig -> Translations -> Effect I18n
create config translations = do
  localeRef <- Ref.new config.defaultLocale
  translationsRef <- Ref.new translations
  listenersRef <- Ref.new []
  pure $ I18n
    { locale: localeRef
    , config
    , translations: translationsRef
    , listeners: listenersRef
    }

-- | Create with async translation loader
createWithLoader 
  :: I18nConfig 
  -> (Locale -> Aff (Map.Map TranslationKey String))
  -> Effect I18n
createWithLoader config _loader = do
  -- Start with empty translations, load on demand
  create config Map.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // translation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate a key
t :: I18n -> TranslationKey -> Effect String
t i18n key = do
  result <- tMaybe i18n key
  pure $ fromMaybe key result

-- | Translate with interpolation values
t' :: I18n -> TranslationKey -> Object.Object String -> Effect String
t' i18n@(I18n { config }) key values = do
  translation <- t i18n key
  pure $ interpolate config.interpolationPrefix config.interpolationSuffix translation values

-- | Try to translate, returning Maybe
tMaybe :: I18n -> TranslationKey -> Effect (Maybe String)
tMaybe (I18n { locale, config, translations }) key = do
  currentLocale <- Ref.read locale
  trans <- Ref.read translations
  
  -- Try current locale, then fallback
  let result = lookupTranslation trans currentLocale key
  case result of
    Just _ -> pure result
    Nothing -> pure $ lookupTranslation trans config.fallbackLocale key

-- | Lookup translation in nested structure
lookupTranslation :: Translations -> Locale -> TranslationKey -> Maybe String
lookupTranslation translations loc key = do
  localeMap <- Map.lookup loc translations
  Map.lookup key localeMap

-- | Pluralize a translation
plural :: I18n -> TranslationKey -> Int -> Effect String
plural i18n key count = pluralWith i18n key count Object.empty

-- | Pluralize with additional interpolation
pluralWith :: I18n -> TranslationKey -> Int -> Object.Object String -> Effect String
pluralWith i18n baseKey count values = do
  let pluralKey = baseKey <> "." <> pluralForm count
  let valuesWithCount = Object.insert "count" (show count) values
  t' i18n pluralKey valuesWithCount

-- | Determine plural form (simplified English rules)
pluralForm :: Int -> String
pluralForm n
  | n == 0 = "zero"
  | n == 1 = "one"
  | n == 2 = "two"
  | n < 5 = "few"
  | otherwise = "other"

-- | Interpolate values into a string
interpolate :: String -> String -> String -> Object.Object String -> String
interpolate prefix suffix template values =
  Object.foldMap (\k v -> replaceOne (prefix <> k <> suffix) v) values template
  where
  replaceOne :: String -> String -> String -> String
  replaceOne pattern replacement str = 
    String.replaceAll (String.Pattern pattern) (String.Replacement replacement) str

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // locale management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current locale
getLocale :: I18n -> Effect Locale
getLocale (I18n { locale }) = Ref.read locale

-- | Set current locale
setLocale :: I18n -> Locale -> Effect Unit
setLocale (I18n { locale, listeners }) newLocale = do
  Ref.write newLocale locale
  subs <- Ref.read listeners
  for_ subs \listener -> listener.callback newLocale
  where
  for_ arr f = void $ Array.foldM (\_ x -> f x) unit arr

-- | Get all available locales
getAvailableLocales :: I18n -> Effect (Array Locale)
getAvailableLocales (I18n { translations }) = do
  trans <- Ref.read translations
  pure $ Array.fromFoldable $ Map.keys trans

-- | Subscriber with ID
type I18nListener = { id :: Int, callback :: Locale -> Effect Unit }

-- | Subscribe to locale changes
onLocaleChange :: I18n -> (Locale -> Effect Unit) -> Effect (Effect Unit)
onLocaleChange (I18n { listeners }) callback = do
  subs <- Ref.read listeners
  let nextId = case Array.last subs of
        Nothing -> 0
        Just s -> s.id + 1
  let sub = { id: nextId, callback }
  Ref.modify_ (flip Array.snoc sub) listeners
  pure $ Ref.modify_ (Array.filter (\s -> s.id /= nextId)) listeners

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format a number according to locale
formatNumber :: I18n -> Number -> Effect String
formatNumber i18n n = do
  locale <- getLocale i18n
  pure $ formatNumberImpl locale n

-- | Format currency
formatCurrency :: I18n -> Number -> String -> Effect String
formatCurrency i18n amount currency = do
  locale <- getLocale i18n
  pure $ formatCurrencyImpl locale amount currency

-- | Format a date
formatDate :: I18n -> String -> String -> Effect String
formatDate i18n dateStr format = do
  locale <- getLocale i18n
  pure $ formatDateImpl locale dateStr format

-- | Format relative time (e.g., "3 days ago")
formatRelativeTime :: I18n -> Int -> String -> Effect String
formatRelativeTime i18n value unit = do
  locale <- getLocale i18n
  pure $ formatRelativeTimeImpl locale value unit

-- FFI implementations (simplified - would use Intl API)
foreign import formatNumberImpl :: Locale -> Number -> String
foreign import formatCurrencyImpl :: Locale -> Number -> String -> String
foreign import formatDateImpl :: Locale -> String -> String -> String
foreign import formatRelativeTimeImpl :: Locale -> Int -> String -> String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a translation exists
hasTranslation :: I18n -> TranslationKey -> Effect Boolean
hasTranslation i18n key = do
  result <- tMaybe i18n key
  pure $ case result of
    Just _ -> true
    Nothing -> false

-- | Get text direction for current locale
getDirection :: I18n -> Effect String
getDirection i18n = do
  locale <- getLocale i18n
  pure $ if isRTLLocale locale then "rtl" else "ltr"

-- | Check if current locale is RTL
isRTL :: I18n -> Effect Boolean
isRTL i18n = do
  locale <- getLocale i18n
  pure $ isRTLLocale locale

-- | RTL locale check
isRTLLocale :: Locale -> Boolean
isRTLLocale locale =
  let lang = String.take 2 locale
  in Array.elem lang ["ar", "he", "fa", "ur"]
