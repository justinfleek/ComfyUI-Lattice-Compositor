-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // typography // font-source
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontSource - where fonts come from and how to load them.
-- |
-- | Fonts fall into two categories:
-- |
-- | **System Fonts** — Pre-installed on user devices, no loading required.
-- | These are enumerable (finite set of well-known fonts).
-- |
-- | **Custom Fonts** — Require loading via @font-face, Google Fonts, Adobe
-- | Fonts, or self-hosting. Infinite possibilities, need import config.
-- |
-- | This distinction matters for:
-- | - Build-time optimization (system fonts need no assets)
-- | - Fallback strategies (custom fonts need loading states)
-- | - Brand validation (can we guarantee this font renders?)

module Hydrogen.Schema.Typography.FontSource
  ( FontSource(..)
  , SystemFont(..)
  , CustomFont
  , ImportMethod(..)
  , FontFaceConfig
  , FontFormat(..)
  , customFont
  , customFontFamily
  , customFontImport
  , toFontFamily
  , requiresImport
  , toLegacyCssImport
  -- Common system fonts
  , arial
  , helvetica
  , georgia
  , timesNewRoman
  , courierNew
  , verdana
  , tahoma
  , trebuchetMs
  , arialBlack
  , impact
  , comicSansMs
  , lucidaConsole
  , monaco
  , menlo
  , sfPro
  , segoeUi
  , roboto
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<<<)
  , (<>)
  )

import Hydrogen.Schema.Typography.FontFamily (FontFamily)
import Hydrogen.Schema.Typography.FontFamily as FontFamily

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // font source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of a font — system-installed or requires import
data FontSource
  = System SystemFont
  | Custom CustomFont

derive instance eqFontSource :: Eq FontSource

instance showFontSource :: Show FontSource where
  show (System sf) = "System " <> show sf
  show (Custom cf) = "Custom " <> show cf

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // system fonts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Well-known system fonts that are pre-installed on common operating systems.
-- |
-- | These fonts don't require any loading or @font-face declarations.
-- | They're enumerable because we know exactly which fonts are typically
-- | available across platforms.
data SystemFont
  -- Sans-serif (Windows/Mac/Linux)
  = Arial
  | Helvetica
  | Verdana
  | Tahoma
  | TrebuchetMs
  | ArialBlack
  | Impact
  -- Serif
  | Georgia
  | TimesNewRoman
  | Palatino
  | BookAntiqua
  -- Monospace
  | CourierNew
  | LucidaConsole
  | Monaco
  | Menlo
  | Consolas
  -- Modern system UI
  | SFPro           -- macOS/iOS
  | SegoeUi         -- Windows
  | Roboto          -- Android/Chrome OS
  | Ubuntu          -- Ubuntu Linux
  | Cantarell       -- GNOME
  -- Novelty (use sparingly)
  | ComicSansMs
  | Papyrus
  | BrushScript

derive instance eqSystemFont :: Eq SystemFont
derive instance ordSystemFont :: Ord SystemFont

instance showSystemFont :: Show SystemFont where
  show Arial = "Arial"
  show Helvetica = "Helvetica"
  show Verdana = "Verdana"
  show Tahoma = "Tahoma"
  show TrebuchetMs = "Trebuchet MS"
  show ArialBlack = "Arial Black"
  show Impact = "Impact"
  show Georgia = "Georgia"
  show TimesNewRoman = "Times New Roman"
  show Palatino = "Palatino"
  show BookAntiqua = "Book Antiqua"
  show CourierNew = "Courier New"
  show LucidaConsole = "Lucida Console"
  show Monaco = "Monaco"
  show Menlo = "Menlo"
  show Consolas = "Consolas"
  show SFPro = "SF Pro"
  show SegoeUi = "Segoe UI"
  show Roboto = "Roboto"
  show Ubuntu = "Ubuntu"
  show Cantarell = "Cantarell"
  show ComicSansMs = "Comic Sans MS"
  show Papyrus = "Papyrus"
  show BrushScript = "Brush Script MT"

-- | Convert system font to FontFamily
systemFontToFamily :: SystemFont -> FontFamily
systemFontToFamily = FontFamily.fontFamily <<< show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // custom fonts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom font requiring import
-- |
-- | Custom fonts are NOT enumerable — any font file can be loaded.
-- | They require explicit import configuration.
newtype CustomFont = CustomFont
  { family :: FontFamily
  , import' :: ImportMethod
  }

derive instance eqCustomFont :: Eq CustomFont

instance showCustomFont :: Show CustomFont where
  show (CustomFont { family }) = "CustomFont " <> show family

-- | How to import a custom font
data ImportMethod
  = GoogleFonts String           -- ^ Google Fonts URL parameter (e.g., "Archivo:wght@400;700")
  | AdobeFonts String            -- ^ Adobe Fonts project ID
  | SelfHosted String            -- ^ URL to font file or CSS
  | FontFace FontFaceConfig      -- ^ Inline @font-face declaration

derive instance eqImportMethod :: Eq ImportMethod

instance showImportMethod :: Show ImportMethod where
  show (GoogleFonts spec) = "GoogleFonts " <> show spec
  show (AdobeFonts id) = "AdobeFonts " <> show id
  show (SelfHosted url) = "SelfHosted " <> show url
  show (FontFace _) = "FontFace {...}"

-- | Configuration for @font-face declaration
type FontFaceConfig =
  { src :: String        -- ^ URL to font file
  , format :: FontFormat -- ^ Font file format
  , weight :: String     -- ^ Font weight range (e.g., "400 700" for variable)
  , style :: String      -- ^ Font style (normal, italic)
  , display :: String    -- ^ Font-display strategy (swap, block, fallback, optional)
  }

-- | Font file formats
data FontFormat
  = WOFF2    -- ^ Preferred modern format
  | WOFF     -- ^ Wide compatibility
  | TTF      -- ^ TrueType
  | OTF      -- ^ OpenType
  | EOT      -- ^ Legacy IE

derive instance eqFontFormat :: Eq FontFormat

instance showFontFormat :: Show FontFormat where
  show WOFF2 = "woff2"
  show WOFF = "woff"
  show TTF = "truetype"
  show OTF = "opentype"
  show EOT = "embedded-opentype"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a custom font source
customFont :: FontFamily -> ImportMethod -> CustomFont
customFont family import' = CustomFont { family, import' }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the font family from a custom font
customFontFamily :: CustomFont -> FontFamily
customFontFamily (CustomFont { family }) = family

-- | Get the import method from a custom font
customFontImport :: CustomFont -> ImportMethod
customFontImport (CustomFont { import' }) = import'

-- | Convert any font source to a FontFamily
toFontFamily :: FontSource -> FontFamily
toFontFamily (System sf) = systemFontToFamily sf
toFontFamily (Custom cf) = customFontFamily cf

-- | Does this font source require an import?
requiresImport :: FontSource -> Boolean
requiresImport (System _) = false
requiresImport (Custom _) = true

-- NOT an FFI boundary - pure string generation.
-- | Generate CSS import for a font source
-- |
-- | Returns Nothing for system fonts, Just the import statement for custom fonts.
toLegacyCssImport :: FontSource -> String
toLegacyCssImport (System _) = ""
toLegacyCssImport (Custom (CustomFont { family, import' })) = case import' of
  GoogleFonts spec ->
    "@import url('https://fonts.googleapis.com/css2?family=" <> spec <> "&display=swap');"
  AdobeFonts projectId ->
    "@import url('https://use.typekit.net/" <> projectId <> ".css');"
  SelfHosted url ->
    "@import url('" <> url <> "');"
  FontFace config ->
    "@font-face {\n" <>
    "  font-family: " <> FontFamily.toLegacyCss family <> ";\n" <>
    "  src: url('" <> config.src <> "') format('" <> show config.format <> "');\n" <>
    "  font-weight: " <> config.weight <> ";\n" <>
    "  font-style: " <> config.style <> ";\n" <>
    "  font-display: " <> config.display <> ";\n" <>
    "}"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // system font constants
-- ═════════════════════════════════════════════════════════════════════════════

-- Sans-serif
arial :: FontSource
arial = System Arial

helvetica :: FontSource
helvetica = System Helvetica

verdana :: FontSource
verdana = System Verdana

tahoma :: FontSource
tahoma = System Tahoma

trebuchetMs :: FontSource
trebuchetMs = System TrebuchetMs

arialBlack :: FontSource
arialBlack = System ArialBlack

impact :: FontSource
impact = System Impact

-- Serif
georgia :: FontSource
georgia = System Georgia

timesNewRoman :: FontSource
timesNewRoman = System TimesNewRoman

-- Monospace
courierNew :: FontSource
courierNew = System CourierNew

lucidaConsole :: FontSource
lucidaConsole = System LucidaConsole

monaco :: FontSource
monaco = System Monaco

menlo :: FontSource
menlo = System Menlo

-- Modern system UI
sfPro :: FontSource
sfPro = System SFPro

segoeUi :: FontSource
segoeUi = System SegoeUi

roboto :: FontSource
roboto = System Roboto

-- Novelty
comicSansMs :: FontSource
comicSansMs = System ComicSansMs
