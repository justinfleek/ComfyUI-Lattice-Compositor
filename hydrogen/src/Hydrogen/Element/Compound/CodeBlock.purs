-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // element // code-block
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen CodeBlock Component
-- |
-- | Display formatted code with optional line numbers and copy button.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.CodeBlock as CodeBlock
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic code block
-- | CodeBlock.codeBlock
-- |   [ CodeBlock.codeContent "const x = 42;"
-- |   , CodeBlock.language CodeBlock.JavaScript
-- |   ]
-- |
-- | -- With line numbers
-- | CodeBlock.codeBlock
-- |   [ CodeBlock.codeContent multilineCode
-- |   , CodeBlock.language CodeBlock.PureScript
-- |   , CodeBlock.showLineNumbers true
-- |   ]
-- |
-- | -- With filename header
-- | CodeBlock.codeBlock
-- |   [ CodeBlock.codeContent configCode
-- |   , CodeBlock.language CodeBlock.JSON
-- |   , CodeBlock.filename "package.json"
-- |   , CodeBlock.showCopy true
-- |   , CodeBlock.onCopy HandleCopy
-- |   ]
-- |
-- | -- Inline code
-- | CodeBlock.inlineCode "npm install"
-- | ```
module Hydrogen.Element.Compound.CodeBlock
  ( -- * CodeBlock Components
    codeBlock
  , inlineCode
    -- * Types
  , Language(PlainText, JavaScript, TypeScript, PureScript, Haskell, Python, Rust, Go, HTMLLang, CSSLang, JSON, YAML, Markdown, Bash, SQL)
  , Theme(Light, Dark, Auto)
    -- * Props
  , CodeBlockProps
  , CodeBlockProp
  , defaultProps
    -- * Prop Builders
  , codeContent
  , language
  , filename
  , showLineNumbers
  , showCopy
  , highlightLines
  , codeMaxHeight
  , codeWrap
  , codeTheme
  , className
  , onCopy
  ) where

import Prelude
  ( class Eq
  , show
  , (<>)
  , (+)
  , (==)
  )

import Data.Array (foldl, mapWithIndex, elem)
import Data.Maybe (Maybe(Nothing, Just))
import Data.String.Pattern (Pattern(Pattern))
import Data.String.Common (split)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Supported languages
data Language
  = PlainText
  | JavaScript
  | TypeScript
  | PureScript
  | Haskell
  | Python
  | Rust
  | Go
  | HTMLLang
  | CSSLang
  | JSON
  | YAML
  | Markdown
  | Bash
  | SQL

derive instance eqLanguage :: Eq Language

-- | Get language display name
languageName :: Language -> String
languageName = case _ of
  PlainText -> "text"
  JavaScript -> "javascript"
  TypeScript -> "typescript"
  PureScript -> "purescript"
  Haskell -> "haskell"
  Python -> "python"
  Rust -> "rust"
  Go -> "go"
  HTMLLang -> "html"
  CSSLang -> "css"
  JSON -> "json"
  YAML -> "yaml"
  Markdown -> "markdown"
  Bash -> "bash"
  SQL -> "sql"

-- | Theme options
data Theme
  = Light
  | Dark
  | Auto

derive instance eqTheme :: Eq Theme

-- | Get theme classes
themeClasses :: Theme -> String
themeClasses = case _ of
  Light -> "bg-zinc-50 text-zinc-900"
  Dark -> "bg-zinc-900 text-zinc-100"
  Auto -> "bg-muted text-foreground"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | CodeBlock properties
type CodeBlockProps msg =
  { code :: String
  , language :: Language
  , filename :: Maybe String
  , showLineNumbers :: Boolean
  , showCopy :: Boolean
  , highlightLines :: Array Int
  , maxHeight :: Maybe String
  , wrap :: Boolean
  , theme :: Theme
  , className :: String
  , onCopy :: Maybe msg
  }

-- | Property modifier
type CodeBlockProp msg = CodeBlockProps msg -> CodeBlockProps msg

-- | Default properties
defaultProps :: forall msg. CodeBlockProps msg
defaultProps =
  { code: ""
  , language: PlainText
  , filename: Nothing
  , showLineNumbers: false
  , showCopy: true
  , highlightLines: []
  , maxHeight: Nothing
  , wrap: false
  , theme: Auto
  , className: ""
  , onCopy: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set code content
codeContent :: forall msg. String -> CodeBlockProp msg
codeContent c props = props { code = c }

-- | Set language
language :: forall msg. Language -> CodeBlockProp msg
language l props = props { language = l }

-- | Set filename for header
filename :: forall msg. String -> CodeBlockProp msg
filename f props = props { filename = Just f }

-- | Show line numbers
showLineNumbers :: forall msg. Boolean -> CodeBlockProp msg
showLineNumbers s props = props { showLineNumbers = s }

-- | Show copy button
showCopy :: forall msg. Boolean -> CodeBlockProp msg
showCopy s props = props { showCopy = s }

-- | Set lines to highlight (1-indexed)
highlightLines :: forall msg. Array Int -> CodeBlockProp msg
highlightLines h props = props { highlightLines = h }

-- | Set max height (enables scrolling)
codeMaxHeight :: forall msg. String -> CodeBlockProp msg
codeMaxHeight m props = props { maxHeight = Just m }

-- | Enable word wrap
codeWrap :: forall msg. Boolean -> CodeBlockProp msg
codeWrap w props = props { wrap = w }

-- | Set theme
codeTheme :: forall msg. Theme -> CodeBlockProp msg
codeTheme t props = props { theme = t }

-- | Add custom class
className :: forall msg. String -> CodeBlockProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set copy handler
onCopy :: forall msg. msg -> CodeBlockProp msg
onCopy handler props = props { onCopy = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container classes
containerClasses :: String
containerClasses =
  "relative rounded-lg border overflow-hidden"

-- | Header classes
headerClasses :: String
headerClasses =
  "flex items-center justify-between px-4 py-2 border-b bg-muted/50"

-- | Filename classes
filenameClasses :: String
filenameClasses =
  "text-sm font-mono text-muted-foreground"

-- | Language badge classes
languageBadgeClasses :: String
languageBadgeClasses =
  "text-xs font-mono text-muted-foreground bg-muted px-2 py-0.5 rounded"

-- | Code container classes
codeContainerClasses :: String
codeContainerClasses =
  "relative overflow-x-auto"

-- | Pre classes
preClasses :: String
preClasses =
  "p-4 font-mono text-sm leading-relaxed"

-- | Line number gutter classes
gutterClasses :: String
gutterClasses =
  "select-none text-right pr-4 text-muted-foreground/50"

-- | Highlighted line classes
highlightedLineClasses :: String
highlightedLineClasses =
  "bg-primary/10"

-- | Copy button classes
copyButtonClasses :: String
copyButtonClasses =
  "absolute top-2 right-2 p-2 rounded-md bg-background/80 hover:bg-background text-muted-foreground hover:text-foreground transition-colors opacity-0 group-hover:opacity-100"

-- | Inline code classes
inlineCodeClasses :: String
inlineCodeClasses =
  "font-mono text-sm bg-muted px-1.5 py-0.5 rounded"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inline code element
-- |
-- | A styled inline code snippet.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
inlineCode :: forall msg. String -> E.Element msg
inlineCode content =
  E.code_
    [ E.class_ inlineCodeClasses ]
    [ E.text content ]

-- | Full code block component
-- |
-- | A code block with optional line numbers, filename header, and copy button.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
codeBlock :: forall msg. Array (CodeBlockProp msg) -> E.Element msg
codeBlock propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    lines = split (Pattern "\n") props.code
    
    containerCls = 
      containerClasses 
      <> " " <> themeClasses props.theme
      <> " " <> props.className
    
    containerStyle = case props.maxHeight of
      Just h -> [ E.style "max-height" h, E.style "overflow-y" "auto" ]
      Nothing -> []
    
    renderLine :: Int -> String -> E.Element msg
    renderLine idx lineContent =
      let
        lineNum = idx + 1
        isHighlighted = elem lineNum props.highlightLines
        lineCls = if isHighlighted then highlightedLineClasses else ""
      in
        E.div_
          [ E.classes [ "flex", lineCls ] ]
          [ if props.showLineNumbers
              then
                E.span_
                  [ E.classes [ gutterClasses, "w-8 flex-shrink-0" ] ]
                  [ E.text (show lineNum) ]
              else E.text ""
          , E.span_
              [ E.class_ (if props.wrap then "whitespace-pre-wrap break-all" else "whitespace-pre") ]
              [ E.text (if lineContent == "" then " " else lineContent) ]
          ]
    
    copyButton :: E.Element msg
    copyButton =
      let
        clickHandler = case props.onCopy of
          Just handler -> [ E.onClick handler ]
          Nothing -> []
      in
        E.button_
          ( [ E.class_ copyButtonClasses
            , E.attr "type" "button"
            , E.ariaLabel "Copy code"
            ] <> clickHandler
          )
          [ copyIcon ]
    
    header :: E.Element msg
    header =
      case props.filename of
        Just fname ->
          E.div_
            [ E.class_ headerClasses ]
            [ E.span_ [ E.class_ filenameClasses ] [ E.text fname ]
            , E.span_ [ E.class_ languageBadgeClasses ] [ E.text (languageName props.language) ]
            ]
        Nothing -> E.text ""
  in
    E.div_
      [ E.classes [ containerCls, "group" ] ]
      [ header
      , E.div_
          ( [ E.class_ codeContainerClasses ] <> containerStyle )
          [ E.pre_
              [ E.class_ preClasses ]
              [ E.code_
                  [ E.dataAttr "language" (languageName props.language) ]
                  (mapWithIndex renderLine lines)
              ]
          ]
      , if props.showCopy
          then copyButton
          else E.text ""
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Copy icon
copyIcon :: forall msg. E.Element msg
copyIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "fill" "none"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.rect_
        [ E.attr "x" "9"
        , E.attr "y" "9"
        , E.attr "width" "13"
        , E.attr "height" "13"
        , E.attr "rx" "2"
        , E.attr "ry" "2"
        ]
    , E.path_
        [ E.attr "d" "M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1" ]
    ]
