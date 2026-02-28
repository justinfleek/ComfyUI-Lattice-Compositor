-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // component // signature
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Signature — Pure Element signature pad component.
-- |
-- | ## Design Philosophy
-- |
-- | Signature capture is a canvas-based drawing component. In the pure Element
-- | model, we describe the signature pad as data — configuration, stroke data,
-- | visual state. The runtime interprets this and provides actual canvas
-- | drawing functionality.
-- |
-- | ## Architecture
-- |
-- | ```
-- | SignatureConfig → signaturePad → Element msg
-- |                                      ↓
-- |                          Runtime canvas interpretation
-- |                                      ↓
-- |                          Mouse/touch → stroke recording
-- | ```
-- |
-- | The Element embeds all configuration as data attributes. The runtime:
-- | 1. Finds elements with `data-signature="true"`
-- | 2. Initializes canvas drawing handlers
-- | 3. Records strokes to the data model
-- | 4. Triggers callbacks via custom events
-- |
-- | ## Features
-- |
-- | - Canvas-based drawing with smooth curves
-- | - Configurable pen color and thickness
-- | - Eraser mode
-- | - Guide line for signing
-- | - Read-only display mode
-- | - Touch and stylus support
-- | - Pressure sensitivity (when available)
-- | - Export as PNG/SVG/JSON
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Signature as Sig
-- |
-- | -- Basic signature pad
-- | mySignature = Sig.signaturePad Sig.defaultConfig
-- |
-- | -- Custom configuration
-- | customSig = Sig.signaturePad
-- |   (Sig.defaultConfig
-- |     # Sig.withPenColor "#0000ff"
-- |     # Sig.withPenThickness 3.0
-- |     # Sig.withSize 500 250)
-- |
-- | -- With toolbar
-- | withToolbar = Sig.signaturePadWithToolbar
-- |   Sig.defaultConfig
-- |   Sig.defaultToolbarConfig
-- |
-- | -- Read-only display
-- | display = Sig.signatureDisplay existingStrokeData
-- | ```

module Hydrogen.Element.Compound.Signature
  ( -- * Components
    signaturePad
  , signaturePadWithToolbar
  , signatureToolbar
  , signatureDisplay
  , signatureCanvas
  
  -- * Configuration (re-exported from Types)
  , module Types
  
  -- * Icons (re-exported)
  , module Icons
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , identity
  , (<>)
  , (<<<)
  )

import Data.Number as Number

import Hydrogen.Render.Element as E
import Data.Maybe (Maybe(Just, Nothing), maybe, isJust)
import Hydrogen.Element.Compound.Signature.Types
  ( Point
  , Stroke
  , StrokeData
  , SignatureConfig
  , ToolbarConfig
  , GuideStyle(Dotted, Dashed, Solid, Hidden)
  , ToolbarPosition(Top, Bottom)
  , ExportFormat(PNG, SVG, JSON)
  , defaultConfig
  , defaultToolbarConfig
  , withPenColor
  , withPenThickness
  , withBackgroundColor
  , withSize
  , withGuide
  , withGuideStyle
  , withReadOnly
  , withEraserMode
  , withStrokeData
  , withClassName
  , withPressureSensitivity
  , withOnChange
  , withOnClear
  , withOnUndo
  , withToolbarPosition
  , withToolbarClassName
  , withColorPicker
  , withThicknessSlider
  , withEraserButton
  , withClearButton
  , withUndoButton
  , withOnColorChange
  , withOnThicknessChange
  , withOnEraserToggle
  , withToolbarOnClear
  , withToolbarOnUndo
  , encodeStrokeData
  , encodePoint
  , encodeStroke
  ) as Types
import Hydrogen.Element.Compound.Signature.Icons
  ( eraserIcon
  , undoIcon
  , trashIcon
  , penIcon
  , colorPickerIcon
  ) as Icons

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signature pad component.
-- |
-- | Renders a complete signature capture interface with canvas and guide line.
-- | The runtime interprets data attributes to enable drawing functionality.
-- |
-- | Event handlers in the config are indicated via data attributes:
-- | - `data-has-onchange="true"` when onChange handler is present
-- | - Runtime dispatches CustomEvents that the Hydrogen runtime intercepts
signaturePad :: forall msg. Types.SignatureConfig msg -> E.Element msg
signaturePad cfg =
  E.div_
    [ E.classes
        [ "signature-pad relative inline-block rounded-lg border border-input overflow-hidden"
        , cursorClass cfg
        , cfg.className
        ]
    , E.attr "data-signature" "true"
    , E.attr "data-pen-color" cfg.penColor
    , E.attr "data-pen-thickness" (show cfg.penThickness)
    , E.attr "data-background-color" cfg.backgroundColor
    , E.attr "data-eraser" (if cfg.eraserMode then "true" else "false")
    , E.attr "data-readonly" (if cfg.readOnly then "true" else "false")
    , E.attr "data-show-guide" (if cfg.showGuide then "true" else "false")
    , E.attr "data-guide-style" (show cfg.guideStyle)
    , E.attr "data-pressure-sensitivity" (if cfg.pressureSensitivity then "true" else "false")
    , E.attr "data-width" (show cfg.width)
    , E.attr "data-height" (show cfg.height)
    -- Event handler presence flags for runtime
    , E.attr "data-has-onchange" (if isJust cfg.onChange then "true" else "false")
    , E.attr "data-has-onclear" (if isJust cfg.onClear then "true" else "false")
    , E.attr "data-has-onundo" (if isJust cfg.onUndo then "true" else "false")
    -- Serialize pre-existing stroke data if present
    , maybe (E.attr "data-strokes" "") 
            (\sd -> E.attr "data-strokes" (Types.encodeStrokeData sd)) 
            cfg.strokeData
    , E.style "width" (show cfg.width <> "px")
    , E.style "height" (show cfg.height <> "px")
    , E.style "background-color" cfg.backgroundColor
    , E.ariaLabel "Signature pad"
    , E.role "img"
    ]
    [ signatureCanvas cfg
    , guideLine cfg
    , signHereHint cfg
    ]

-- | Canvas element for signature drawing.
signatureCanvas :: forall msg. Types.SignatureConfig msg -> E.Element msg
signatureCanvas cfg =
  E.element "canvas"
    [ E.class_ "signature-canvas w-full h-full touch-none"
    , E.attr "width" (show cfg.width)
    , E.attr "height" (show cfg.height)
    ]
    []

-- | Guide line element.
guideLine :: forall msg. Types.SignatureConfig msg -> E.Element msg
guideLine cfg =
  if cfg.showGuide
    then E.div_
      [ E.classes
          [ "signature-guide absolute bottom-1/4 left-4 right-4"
          , guideStyleClass cfg.guideStyle
          ]
      ]
      []
    else E.empty

-- | "Sign here" hint text.
signHereHint :: forall msg. Types.SignatureConfig msg -> E.Element msg
signHereHint cfg =
  E.div_
    [ E.class_ "signature-hint absolute bottom-2 left-4 text-xs text-muted-foreground pointer-events-none select-none"
    ]
    [ E.text (if cfg.readOnly then "" else "Sign here") ]

-- | Signature pad with integrated toolbar.
-- |
-- | Combines signature pad with color picker, thickness slider, and action buttons.
signaturePadWithToolbar :: forall msg. Types.SignatureConfig msg -> Types.ToolbarConfig msg -> E.Element msg
signaturePadWithToolbar sigCfg toolbarCfg =
  E.div_
    [ E.class_ "signature-pad-container flex flex-col gap-2" ]
    (case toolbarCfg.position of
      Types.Top -> [ signatureToolbar toolbarCfg, signaturePad sigCfg ]
      Types.Bottom -> [ signaturePad sigCfg, signatureToolbar toolbarCfg ])

-- | Signature toolbar component.
-- |
-- | Controls for color, thickness, eraser, clear, and undo.
-- | Event handlers are wired to toolbar buttons via onClick attributes.
signatureToolbar :: forall msg. Types.ToolbarConfig msg -> E.Element msg
signatureToolbar cfg =
  E.div_
    [ E.classes
        [ "signature-toolbar flex items-center gap-2 p-2 bg-muted rounded-lg"
        , cfg.className
        ]
    , E.attr "data-signature-toolbar" "true"
    , E.attr "data-has-oncolorchange" (if isJust cfg.onColorChange then "true" else "false")
    , E.attr "data-has-onthicknesschange" (if isJust cfg.onThicknessChange then "true" else "false")
    , E.attr "data-has-onerasertoggle" (if isJust cfg.onEraserToggle then "true" else "false")
    ]
    [ colorPickerControl cfg
    , thicknessControl cfg
    , spacer
    , eraserButton cfg
    , undoButton cfg
    , clearButton cfg
    ]

-- | Read-only signature display.
-- |
-- | For displaying existing signatures without editing capability.
-- | The stroke data is serialized as JSON in data-strokes for the runtime
-- | to parse and replay onto the canvas.
signatureDisplay :: forall msg. Types.StrokeData -> E.Element msg
signatureDisplay strokeData =
  E.div_
    [ E.class_ "signature-display inline-block rounded-lg border border-input bg-background"
    , E.attr "data-signature-display" "true"
    , E.attr "data-strokes" (Types.encodeStrokeData strokeData)
    , E.attr "data-width" (show strokeData.width)
    , E.attr "data-height" (show strokeData.height)
    , E.style "width" (show strokeData.width <> "px")
    , E.style "height" (show strokeData.height <> "px")
    , E.ariaLabel "Signature"
    , E.role "img"
    ]
    [ E.element "canvas"
        [ E.class_ "w-full h-full"
        , E.attr "width" (show strokeData.width)
        , E.attr "height" (show strokeData.height)
        ]
        []
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // toolbar components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color picker control with optional onChange handler.
colorPickerControl :: forall msg. Types.ToolbarConfig msg -> E.Element msg
colorPickerControl cfg =
  if cfg.showColorPicker
    then E.label_
      [ E.class_ "signature-color-picker relative" ]
      [ E.div_
          [ E.classes
              [ "w-8 h-8 rounded-md border border-input cursor-pointer"
              , "bg-current ring-offset-background"
              , "focus-within:ring-2 focus-within:ring-ring focus-within:ring-offset-2"
              ]
          ]
          []
      , E.input_
          ([ E.type_ "color"
          , E.class_ "sr-only"
          , E.ariaLabel "Pen color"
          ] <> colorChangeHandler cfg.onColorChange)
      ]
    else E.empty

-- | Thickness slider control with optional onChange handler.
thicknessControl :: forall msg. Types.ToolbarConfig msg -> E.Element msg
thicknessControl cfg =
  if cfg.showThicknessSlider
    then E.div_
      [ E.class_ "signature-thickness flex items-center gap-2" ]
      [ E.span_ [ E.class_ "text-xs text-muted-foreground" ] [ E.text "Thin" ]
      , E.input_
          ([ E.type_ "range"
          , E.attr "min" "1"
          , E.attr "max" "10"
          , E.attr "step" "0.5"
          , E.class_ "w-20 h-2 cursor-pointer"
          , E.ariaLabel "Pen thickness"
          ] <> thicknessChangeHandler cfg.onThicknessChange)
      , E.span_ [ E.class_ "text-xs text-muted-foreground" ] [ E.text "Thick" ]
      ]
    else E.empty

-- | Spacer element for flex layout.
spacer :: forall msg. E.Element msg
spacer = E.div_ [ E.class_ "flex-1" ] []

-- | Eraser toggle button with optional onClick handler.
eraserButton :: forall msg. Types.ToolbarConfig msg -> E.Element msg
eraserButton cfg =
  if cfg.showEraser
    then E.button_
      ([ E.classes
          [ "signature-eraser p-2 rounded-md hover:bg-accent transition-colors"
          , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
          ]
      , E.type_ "button"
      , E.ariaLabel "Toggle eraser"
      , E.attr "data-eraser-toggle" "true"
      ])
      [ Icons.eraserIcon ]
    else E.empty

-- | Undo button with optional onClick handler.
undoButton :: forall msg. Types.ToolbarConfig msg -> E.Element msg
undoButton cfg =
  if cfg.showUndo
    then E.button_
      ([ E.classes
          [ "signature-undo p-2 rounded-md hover:bg-accent transition-colors"
          , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
          ]
      , E.type_ "button"
      , E.ariaLabel "Undo"
      ] <> clickHandler cfg.onUndo)
      [ Icons.undoIcon ]
    else E.empty

-- | Clear button with optional onClick handler.
clearButton :: forall msg. Types.ToolbarConfig msg -> E.Element msg
clearButton cfg =
  if cfg.showClear
    then E.button_
      ([ E.classes
          [ "signature-clear p-2 rounded-md hover:bg-destructive/10 text-destructive transition-colors"
          , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring"
          ]
      , E.type_ "button"
      , E.ariaLabel "Clear signature"
      ] <> clickHandler cfg.onClear)
      [ Icons.trashIcon ]
    else E.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // handler helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create onClick handler if message is present.
clickHandler :: forall msg. Maybe msg -> Array (E.Attribute msg)
clickHandler = case _ of
  Just msg -> [ E.onClick msg ]
  Nothing -> []

-- | Create onInput handler for color change if present.
-- | Note: The handler receives the input value as String.
colorChangeHandler :: forall msg. Maybe (String -> msg) -> Array (E.Attribute msg)
colorChangeHandler = case _ of
  Just handler -> [ E.onInput handler ]
  Nothing -> []

-- | Create onInput handler for thickness change.
-- | Note: The handler receives the input value as String, caller must parse to Number.
thicknessChangeHandler :: forall msg. Maybe (Number -> msg) -> Array (E.Attribute msg)
thicknessChangeHandler = case _ of
  Just handler -> [ E.onInput (handler <<< parseNumber) ]
  Nothing -> []

-- | Parse a string to Number, defaulting to 2.0 for invalid input.
-- | Uses Data.Number.fromString for pure parsing.
parseNumber :: String -> Number
parseNumber s = maybe 2.0 identity (Number.fromString s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cursor class based on mode.
cursorClass :: forall msg. Types.SignatureConfig msg -> String
cursorClass cfg =
  if cfg.readOnly then "cursor-default"
  else if cfg.eraserMode then "cursor-cell"
  else "cursor-crosshair"

-- | Guide style to CSS class.
guideStyleClass :: Types.GuideStyle -> String
guideStyleClass = case _ of
  Types.Dotted -> "border-t-2 border-dotted border-muted-foreground/30"
  Types.Dashed -> "border-t-2 border-dashed border-muted-foreground/30"
  Types.Solid -> "border-t border-muted-foreground/30"
  Types.Hidden -> "hidden"
