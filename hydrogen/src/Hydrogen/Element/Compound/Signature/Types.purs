-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // component // signature // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Signature Types — Data structures for signature pad configuration.
-- |
-- | ## Design Philosophy
-- |
-- | Signature capture is fundamentally about recording stroke data — points
-- | with optional pressure values, organized into strokes with color and
-- | thickness. This module defines the pure data types; the runtime interprets
-- | them for canvas rendering.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Point → Stroke → StrokeData
-- |   ↓
-- | SignatureConfig → Element msg
-- |   ↓
-- | Runtime canvas interpretation
-- | ```

module Hydrogen.Element.Compound.Signature.Types
  ( -- * Core Types
    Point
  , Stroke
  , StrokeData
  
  -- * Configuration
  , SignatureConfig
  , defaultConfig
  
  -- * Toolbar Configuration
  , ToolbarConfig
  , defaultToolbarConfig
  
  -- * Enums
  , GuideStyle
      ( Dotted
      , Dashed
      , Solid
      , Hidden
      )
  , ToolbarPosition
      ( Top
      , Bottom
      )
  , ExportFormat
      ( PNG
      , SVG
      , JSON
      )
  
  -- * Config Helpers
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
  
  -- * Signature Event Handlers
  , withOnChange
  , withOnClear
  , withOnUndo
  
  -- * Toolbar Config Helpers
  , withToolbarPosition
  , withToolbarClassName
  , withColorPicker
  , withThicknessSlider
  , withEraserButton
  , withClearButton
  , withUndoButton
  
  -- * Toolbar Event Handlers
  , withOnColorChange
  , withOnThicknessChange
  , withOnEraserToggle
  , withToolbarOnClear
  , withToolbarOnUndo
  
  -- * Stroke Data Serialization
  , encodeStrokeData
  , encodePoint
  , encodeStroke
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , (<>)
  )

import Data.Array (intercalate)
import Data.Maybe (Maybe(Nothing, Just), maybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point with optional pressure (for stylus/touch support).
-- |
-- | Pressure ranges from 0.0 (no pressure) to 1.0 (full pressure).
-- | When pressure is available, stroke thickness can vary dynamically.
type Point =
  { x :: Number
  , y :: Number
  , pressure :: Maybe Number
  }

-- | Single stroke — a continuous line segment drawn without lifting.
-- |
-- | Each stroke records the sequence of points, the pen color at time of
-- | drawing, and the base thickness (may be modulated by pressure).
type Stroke =
  { points :: Array Point
  , color :: String
  , thickness :: Number
  }

-- | Complete stroke data for serialization and replay.
-- |
-- | Contains all strokes plus the canvas dimensions for proper scaling
-- | when replaying on different-sized canvases.
type StrokeData =
  { strokes :: Array Stroke
  , width :: Int
  , height :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // enums
-- ═════════════════════════════════════════════════════════════════════════════

-- | Guide line style — visual hint for where to sign.
data GuideStyle
  = Dotted    -- ^ Dotted line (default)
  | Dashed    -- ^ Dashed line
  | Solid     -- ^ Solid line
  | Hidden    -- ^ No guide line

derive instance eqGuideStyle :: Eq GuideStyle
derive instance ordGuideStyle :: Ord GuideStyle

instance showGuideStyle :: Show GuideStyle where
  show Dotted = "dotted"
  show Dashed = "dashed"
  show Solid = "solid"
  show Hidden = "hidden"

-- | Toolbar position relative to signature pad.
data ToolbarPosition
  = Top       -- ^ Toolbar above pad
  | Bottom    -- ^ Toolbar below pad (default)

derive instance eqToolbarPosition :: Eq ToolbarPosition
derive instance ordToolbarPosition :: Ord ToolbarPosition

instance showToolbarPosition :: Show ToolbarPosition where
  show Top = "top"
  show Bottom = "bottom"

-- | Export format for signature data.
data ExportFormat
  = PNG       -- ^ Raster image (default)
  | SVG       -- ^ Vector graphics
  | JSON      -- ^ Stroke data for replay

derive instance eqExportFormat :: Eq ExportFormat
derive instance ordExportFormat :: Ord ExportFormat

instance showExportFormat :: Show ExportFormat where
  show PNG = "png"
  show SVG = "svg"
  show JSON = "json"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete signature pad configuration.
-- |
-- | All visual and behavioral parameters for the signature component.
-- | The `msg` type parameter allows event handlers to produce application
-- | messages when signature events occur.
type SignatureConfig msg =
  { penColor :: String           -- ^ Hex color for pen strokes
  , penThickness :: Number       -- ^ Base stroke width in pixels
  , eraserMode :: Boolean        -- ^ Whether eraser is active
  , showGuide :: Boolean         -- ^ Show signing guide line
  , guideStyle :: GuideStyle     -- ^ Style of guide line
  , readOnly :: Boolean          -- ^ Disable drawing (display only)
  , strokeData :: Maybe StrokeData -- ^ Pre-existing signature data
  , backgroundColor :: String    -- ^ Canvas background color
  , width :: Int                 -- ^ Canvas width in pixels
  , height :: Int                -- ^ Canvas height in pixels
  , pressureSensitivity :: Boolean -- ^ Enable pressure-based thickness
  , className :: String          -- ^ Additional CSS classes
  -- Event handlers
  , onChange :: Maybe (StrokeData -> msg)  -- ^ Called when signature changes
  , onClear :: Maybe msg                    -- ^ Called when signature is cleared
  , onUndo :: Maybe msg                     -- ^ Called when stroke is undone
  }

-- | Sensible defaults for signature capture.
defaultConfig :: forall msg. SignatureConfig msg
defaultConfig =
  { penColor: "#000000"
  , penThickness: 2.0
  , eraserMode: false
  , showGuide: true
  , guideStyle: Dotted
  , readOnly: false
  , strokeData: Nothing
  , backgroundColor: "#ffffff"
  , width: 400
  , height: 200
  , pressureSensitivity: true
  , className: ""
  , onChange: Nothing
  , onClear: Nothing
  , onUndo: Nothing
  }

-- | Toolbar configuration.
-- |
-- | Controls which toolbar elements are visible and their arrangement.
-- | The `msg` type parameter allows event handlers to produce application
-- | messages when toolbar actions occur.
type ToolbarConfig msg =
  { showColorPicker :: Boolean
  , showThicknessSlider :: Boolean
  , showEraser :: Boolean
  , showClear :: Boolean
  , showUndo :: Boolean
  , position :: ToolbarPosition
  , className :: String
  -- Event handlers
  , onColorChange :: Maybe (String -> msg)   -- ^ Called when color changes
  , onThicknessChange :: Maybe (Number -> msg) -- ^ Called when thickness changes
  , onEraserToggle :: Maybe (Boolean -> msg) -- ^ Called when eraser mode toggles
  , onClear :: Maybe msg                     -- ^ Called when clear button clicked
  , onUndo :: Maybe msg                      -- ^ Called when undo button clicked
  }

-- | Default toolbar with all controls visible.
defaultToolbarConfig :: forall msg. ToolbarConfig msg
defaultToolbarConfig =
  { showColorPicker: true
  , showThicknessSlider: true
  , showEraser: true
  , showClear: true
  , showUndo: true
  , position: Bottom
  , className: ""
  , onColorChange: Nothing
  , onThicknessChange: Nothing
  , onEraserToggle: Nothing
  , onClear: Nothing
  , onUndo: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // config helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set pen color (hex string).
withPenColor :: forall msg. String -> SignatureConfig msg -> SignatureConfig msg
withPenColor c cfg = cfg { penColor = c }

-- | Set pen thickness in pixels.
withPenThickness :: forall msg. Number -> SignatureConfig msg -> SignatureConfig msg
withPenThickness t cfg = cfg { penThickness = t }

-- | Set background color (hex string).
withBackgroundColor :: forall msg. String -> SignatureConfig msg -> SignatureConfig msg
withBackgroundColor c cfg = cfg { backgroundColor = c }

-- | Set canvas dimensions.
withSize :: forall msg. Int -> Int -> SignatureConfig msg -> SignatureConfig msg
withSize w h cfg = cfg { width = w, height = h }

-- | Enable or disable guide line.
withGuide :: forall msg. Boolean -> SignatureConfig msg -> SignatureConfig msg
withGuide g cfg = cfg { showGuide = g }

-- | Set guide line style.
withGuideStyle :: forall msg. GuideStyle -> SignatureConfig msg -> SignatureConfig msg
withGuideStyle s cfg = cfg { guideStyle = s }

-- | Set read-only mode (display only, no drawing).
withReadOnly :: forall msg. Boolean -> SignatureConfig msg -> SignatureConfig msg
withReadOnly r cfg = cfg { readOnly = r }

-- | Set pre-existing stroke data for display/editing.
withStrokeData :: forall msg. StrokeData -> SignatureConfig msg -> SignatureConfig msg
withStrokeData d cfg = cfg { strokeData = Just d }

-- | Add custom CSS class.
withClassName :: forall msg. String -> SignatureConfig msg -> SignatureConfig msg
withClassName c cfg = cfg { className = cfg.className <> " " <> c }

-- | Enable or disable eraser mode.
withEraserMode :: forall msg. Boolean -> SignatureConfig msg -> SignatureConfig msg
withEraserMode e cfg = cfg { eraserMode = e }

-- | Enable or disable pressure sensitivity.
withPressureSensitivity :: forall msg. Boolean -> SignatureConfig msg -> SignatureConfig msg
withPressureSensitivity p cfg = cfg { pressureSensitivity = p }

-- | Set onChange handler (called when signature changes).
withOnChange :: forall msg. (StrokeData -> msg) -> SignatureConfig msg -> SignatureConfig msg
withOnChange handler cfg = cfg { onChange = Just handler }

-- | Set onClear handler (called when signature is cleared).
withOnClear :: forall msg. msg -> SignatureConfig msg -> SignatureConfig msg
withOnClear handler cfg = cfg { onClear = Just handler }

-- | Set onUndo handler (called when stroke is undone).
withOnUndo :: forall msg. msg -> SignatureConfig msg -> SignatureConfig msg
withOnUndo handler cfg = cfg { onUndo = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // toolbar config helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set toolbar position.
withToolbarPosition :: forall msg. ToolbarPosition -> ToolbarConfig msg -> ToolbarConfig msg
withToolbarPosition p cfg = cfg { position = p }

-- | Add custom CSS class to toolbar.
withToolbarClassName :: forall msg. String -> ToolbarConfig msg -> ToolbarConfig msg
withToolbarClassName c cfg = cfg { className = cfg.className <> " " <> c }

-- | Show or hide color picker.
withColorPicker :: forall msg. Boolean -> ToolbarConfig msg -> ToolbarConfig msg
withColorPicker v cfg = cfg { showColorPicker = v }

-- | Show or hide thickness slider.
withThicknessSlider :: forall msg. Boolean -> ToolbarConfig msg -> ToolbarConfig msg
withThicknessSlider v cfg = cfg { showThicknessSlider = v }

-- | Show or hide eraser button.
withEraserButton :: forall msg. Boolean -> ToolbarConfig msg -> ToolbarConfig msg
withEraserButton v cfg = cfg { showEraser = v }

-- | Show or hide clear button.
withClearButton :: forall msg. Boolean -> ToolbarConfig msg -> ToolbarConfig msg
withClearButton v cfg = cfg { showClear = v }

-- | Show or hide undo button.
withUndoButton :: forall msg. Boolean -> ToolbarConfig msg -> ToolbarConfig msg
withUndoButton v cfg = cfg { showUndo = v }

-- | Set onColorChange handler.
withOnColorChange :: forall msg. (String -> msg) -> ToolbarConfig msg -> ToolbarConfig msg
withOnColorChange handler cfg = cfg { onColorChange = Just handler }

-- | Set onThicknessChange handler.
withOnThicknessChange :: forall msg. (Number -> msg) -> ToolbarConfig msg -> ToolbarConfig msg
withOnThicknessChange handler cfg = cfg { onThicknessChange = Just handler }

-- | Set onEraserToggle handler.
withOnEraserToggle :: forall msg. (Boolean -> msg) -> ToolbarConfig msg -> ToolbarConfig msg
withOnEraserToggle handler cfg = cfg { onEraserToggle = Just handler }

-- | Set toolbar onClear handler.
withToolbarOnClear :: forall msg. msg -> ToolbarConfig msg -> ToolbarConfig msg
withToolbarOnClear handler cfg = cfg { onClear = Just handler }

-- | Set toolbar onUndo handler.
withToolbarOnUndo :: forall msg. msg -> ToolbarConfig msg -> ToolbarConfig msg
withToolbarOnUndo handler cfg = cfg { onUndo = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // stroke data serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Encode a point to JSON string format.
-- |
-- | Format: {"x":123.45,"y":67.89,"pressure":0.5} or {"x":123.45,"y":67.89}
encodePoint :: Point -> String
encodePoint p =
  "{\"x\":" <> show p.x <> 
  ",\"y\":" <> show p.y <>
  maybe "" (\pr -> ",\"pressure\":" <> show pr) p.pressure <>
  "}"

-- | Encode a stroke to JSON string format.
-- |
-- | Format: {"points":[...],"color":"#000","thickness":2.0}
encodeStroke :: Stroke -> String
encodeStroke s =
  "{\"points\":[" <> intercalate "," (map encodePoint s.points) <> "]" <>
  ",\"color\":\"" <> s.color <> "\"" <>
  ",\"thickness\":" <> show s.thickness <>
  "}"

-- | Encode complete stroke data to JSON string.
-- |
-- | Format: {"strokes":[...],"width":400,"height":200}
encodeStrokeData :: StrokeData -> String
encodeStrokeData sd =
  "{\"strokes\":[" <> intercalate "," (map encodeStroke sd.strokes) <> "]" <>
  ",\"width\":" <> show sd.width <>
  ",\"height\":" <> show sd.height <>
  "}"
