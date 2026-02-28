-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // composition // source // interactive
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interactive Sources — Widget, Form, Canvas, Terminal.
-- |
-- | User-interactive elements that respond to input.

module Hydrogen.Composition.Source.Interactive
  ( -- * Widget
    WidgetSpec
  , WidgetRef(..)
  , widget
  
  -- * Form
  , FormSpec
  , FormField(..)
  , form
  
  -- * Canvas
  , CanvasSpec
  , canvas
  
  -- * Terminal
  , TerminalSpec
  , terminal
  
  -- * Code Editor
  , CodeEditorSpec
  , code
  
  -- * Markdown
  , MarkdownSpec
  , markdown
  
  -- * Browser
  , BrowserSpec
  , browser
  
  -- * PDF Viewer
  , PDFSpec
  , pdf
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))

import Hydrogen.Schema.Color.Opacity (Opacity)
import Hydrogen.Composition.Source.Data (DataRef(..))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // widget
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Widget reference (points to a registered widget component).
newtype WidgetRef = WidgetRef String

derive instance eqWidgetRef :: Eq WidgetRef
derive instance ordWidgetRef :: Ord WidgetRef

instance showWidgetRef :: Show WidgetRef where
  show (WidgetRef w) = "(WidgetRef " <> show w <> ")"

-- | Widget source (embeds a custom component).
type WidgetSpec =
  { widgetRef :: WidgetRef
  , props :: DataRef            -- Props data
  , opacity :: Opacity
  }

-- | Create a widget source.
widget :: WidgetRef -> DataRef -> Opacity -> WidgetSpec
widget widgetRef props opacity = { widgetRef, props, opacity }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // form
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Form field type.
data FormField
  = FieldText String            -- Text input with label
  | FieldNumber String          -- Number input
  | FieldEmail String           -- Email input
  | FieldPassword String        -- Password input
  | FieldTextarea String        -- Multiline text
  | FieldSelect String          -- Dropdown
  | FieldCheckbox String        -- Checkbox
  | FieldRadio String           -- Radio group
  | FieldSlider String          -- Range slider
  | FieldDate String            -- Date picker
  | FieldTime String            -- Time picker
  | FieldDatetime String        -- DateTime picker
  | FieldFile String            -- File upload
  | FieldColor String           -- Color picker

derive instance eqFormField :: Eq FormField

instance showFormField :: Show FormField where
  show (FieldText _) = "text"
  show (FieldNumber _) = "number"
  show (FieldEmail _) = "email"
  show (FieldPassword _) = "password"
  show (FieldTextarea _) = "textarea"
  show (FieldSelect _) = "select"
  show (FieldCheckbox _) = "checkbox"
  show (FieldRadio _) = "radio"
  show (FieldSlider _) = "slider"
  show (FieldDate _) = "date"
  show (FieldTime _) = "time"
  show (FieldDatetime _) = "datetime"
  show (FieldFile _) = "file"
  show (FieldColor _) = "color"

-- | Form source.
type FormSpec =
  { formId :: String
  , fields :: Array FormField
  , data :: DataRef             -- Form values
  , submitLabel :: String
  , layout :: String            -- "vertical", "horizontal", "grid"
  , opacity :: Opacity
  }

-- | Create a form source.
form :: String -> Array FormField -> DataRef -> Opacity -> FormSpec
form formId fields d opacity =
  { formId, fields, data: d, opacity
  , submitLabel: "Submit", layout: "vertical" }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // canvas
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Drawing canvas source.
type CanvasSpec =
  { canvasId :: String
  , width :: Int
  , height :: Int
  , background :: String        -- CSS color or "transparent"
  , tools :: Array String       -- Available tools
  , opacity :: Opacity
  }

-- | Create a canvas source.
canvas :: String -> Int -> Int -> Opacity -> CanvasSpec
canvas canvasId width height opacity =
  { canvasId, width, height, opacity
  , background: "transparent"
  , tools: ["brush", "eraser", "line", "rect", "ellipse"] }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // terminal
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Terminal emulator source.
type TerminalSpec =
  { sessionId :: String
  , shell :: String             -- "bash", "zsh", "powershell"
  , rows :: Int
  , cols :: Int
  , fontSize :: Int
  , fontFamily :: String
  , theme :: String             -- "dark", "light", "monokai", etc.
  , opacity :: Opacity
  }

-- | Create a terminal source.
terminal :: String -> String -> Opacity -> TerminalSpec
terminal sessionId shell opacity =
  { sessionId, shell, opacity
  , rows: 24, cols: 80, fontSize: 14, fontFamily: "monospace", theme: "dark" }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // code editor
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Code editor source.
type CodeEditorSpec =
  { content :: DataRef
  , language :: String          -- "javascript", "python", "purescript", etc.
  , theme :: String             -- "vs-dark", "github-light", etc.
  , readOnly :: Boolean
  , showLineNumbers :: Boolean
  , showMinimap :: Boolean
  , wordWrap :: Boolean
  , fontSize :: Int
  , opacity :: Opacity
  }

-- | Create a code editor source.
code :: DataRef -> String -> Opacity -> CodeEditorSpec
code content language opacity =
  { content, language, opacity
  , theme: "vs-dark", readOnly: false
  , showLineNumbers: true, showMinimap: false
  , wordWrap: false, fontSize: 14 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // markdown
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Markdown renderer source.
type MarkdownSpec =
  { content :: DataRef
  , sanitize :: Boolean         -- Sanitize HTML
  , highlight :: Boolean        -- Syntax highlighting
  , linkTarget :: String        -- "_blank", "_self"
  , opacity :: Opacity
  }

-- | Create a markdown source.
markdown :: DataRef -> Opacity -> MarkdownSpec
markdown content opacity =
  { content, opacity
  , sanitize: true, highlight: true, linkTarget: "_blank" }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // browser
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Embedded browser source (iframe).
type BrowserSpec =
  { url :: String
  , sandbox :: Boolean          -- Sandbox restrictions
  , allowScripts :: Boolean
  , allowForms :: Boolean
  , allowPopups :: Boolean
  , opacity :: Opacity
  }

-- | Create a browser source.
browser :: String -> Opacity -> BrowserSpec
browser url opacity =
  { url, opacity
  , sandbox: true, allowScripts: false, allowForms: false, allowPopups: false }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                          // pdf
-- ═══════════════════════════════════════════════════════════════════════════════

-- | PDF viewer source.
type PDFSpec =
  { assetId :: String
  , page :: Int                 -- Current page
  , zoom :: Number              -- Zoom level (1.0 = 100%)
  , showToolbar :: Boolean
  , showThumbnails :: Boolean
  , opacity :: Opacity
  }

-- | Create a PDF viewer source.
pdf :: String -> Opacity -> PDFSpec
pdf assetId opacity =
  { assetId, opacity
  , page: 1, zoom: 1.0, showToolbar: true, showThumbnails: false }
