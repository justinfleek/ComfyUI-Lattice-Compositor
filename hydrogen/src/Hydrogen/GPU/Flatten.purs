-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // gpu // flatten
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element → CommandBuffer Flattener
-- |
-- | Converts the tree-based Element structure to a flat array of DrawCommands.
-- | This is the bridge between the component model (tree) and the GPU model (flat).
-- |
-- | ## Design Principles
-- |
-- | 1. **Pure transformation**: Element in, CommandBuffer out. No effects.
-- |
-- | 2. **Layout resolution**: Computes positions from layout attributes.
-- |    Currently simplified — full flexbox would be a larger undertaking.
-- |
-- | 3. **Style extraction**: Pulls Schema atoms from Element styles and
-- |    converts to DrawCommand parameters.
-- |
-- | 4. **Event mapping**: Assigns PickIds to interactive elements and
-- |    returns a mapping for the runtime.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Element msg
-- |     ↓ flatten
-- | { commands :: CommandBuffer msg
-- | , pickMap :: Map PickId msg
-- | }
-- | ```
-- |
-- | The runtime uses pickMap to dispatch messages when the pick buffer
-- | reports an interaction.
-- |
-- | ## Current Limitations
-- |
-- | - Layout is position-based only (no auto-layout yet)
-- | - Styles should use Schema atoms for type safety; CSS string parsing
-- |   is provided for legacy compatibility but covers only common cases
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.GPU.Flatten as Flatten
-- | import Hydrogen.Render.Element as E
-- |
-- | result = Flatten.flatten myElement
-- | -- result.commands :: Array (DrawCommand msg)
-- | -- result.pickMap :: Map PickId msg
-- | ```

module Hydrogen.GPU.Flatten
  ( -- * Types
    FlattenResult
  , FlattenState
  , LayoutBox
  
  -- * Flattening
  , flatten
  , flattenWithState
  , flattenWithFont
  
  -- * Layout
  , defaultBox
  , offsetBox
  , boxesEqual
  , showBox
  , genericEqual
  , showDebug
  , discardMaybe
  
  -- * Style Extraction
  , extractBackground
  , extractBorderRadius
  , extractFontConfig
  ) where

import Prelude
  ( class Eq
  , class Show
  , Unit
  , bind
  , map
  , pure
  , show
  , unit
  , ($)
  , (+)
  , (*)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number as Number
import Data.String.CodeUnits as String
import Data.String.Pattern (Pattern(Pattern))
import Data.Tuple (Tuple(Tuple), fst, snd)
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Text as Text
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of flattening an Element tree.
type FlattenResult msg =
  { commands :: DC.CommandBuffer msg
  , pickMap :: Map.Map DC.PickId msg
  }

-- | State maintained during flattening.
type FlattenState msg =
  { nextPickId :: Int
  , pickMap :: Map.Map DC.PickId msg
  , currentDepth :: Number
  , box :: LayoutBox
  , fontAtlas :: Text.FontAtlas
  , fontConfig :: Text.FontConfig
  }

-- | Layout box for an element.
-- | Represents the computed position and size.
type LayoutBox =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten an Element tree to a CommandBuffer.
-- |
-- | This is the main entry point. Takes an Element and produces:
-- | - commands: Array of DrawCommands ready for serialization
-- | - pickMap: Mapping from PickId to message for hit testing
flatten :: forall msg. E.Element msg -> FlattenResult msg
flatten element =
  let
    initialState = 
      { nextPickId: 1
      , pickMap: Map.empty
      , currentDepth: 0.0
      , box: defaultBox
      , fontAtlas: Text.emptyAtlas
      , fontConfig: Text.fontConfig 0 16.0  -- Default: font 0, 16px
      }
    result = flattenWithState initialState element
  in
    { commands: fst result
    , pickMap: (snd result).pickMap
    }

-- | Flatten with custom font configuration.
-- |
-- | Use this when you have a loaded font atlas and specific font settings.
-- | Uses $ for function application in let bindings.
flattenWithFont 
  :: forall msg
   . Text.FontAtlas 
  -> Text.FontConfig 
  -> E.Element msg 
  -> FlattenResult msg
flattenWithFont atlas config element =
  let
    initialState = 
      { nextPickId: 1
      , pickMap: Map.empty
      , currentDepth: 0.0
      , box: defaultBox
      , fontAtlas: atlas
      , fontConfig: config
      }
    result = flattenWithState initialState $ element
    cmds = fst $ result
    picks = (snd result).pickMap
  in
    { commands: cmds, pickMap: picks }

-- | Flatten with explicit state (for recursive calls).
flattenWithState 
  :: forall msg
   . FlattenState msg 
  -> E.Element msg 
  -> Tuple (DC.CommandBuffer msg) (FlattenState msg)
flattenWithState state = case _ of
  E.Empty -> 
    Tuple [] state
  
  E.Text str ->
    -- Generate draw commands for text using the typography pipeline.
    -- Uses current box position as text baseline origin.
    -- The font configuration comes from the state, which can be customized
    -- via flattenWithFont or updated through style extraction.
    let
      commands = Text.textToCommands 
        state.fontConfig 
        state.fontAtlas 
        state.box.x 
        state.box.y 
        str
    in
      Tuple commands state
  
  E.Element r ->
    flattenElement state r.namespace r.tag r.attributes r.children
  
  E.Keyed r ->
    let children = map snd r.children
    in flattenElement state r.namespace r.tag r.attributes children
  
  E.Lazy r ->
    flattenWithState state (r.thunk unit)

-- | Flatten a standard element.
flattenElement
  :: forall msg
   . FlattenState msg
  -> Maybe E.Namespace
  -> String
  -> Array (E.Attribute msg)
  -> Array (E.Element msg)
  -> Tuple (DC.CommandBuffer msg) (FlattenState msg)
flattenElement state _namespace _tag attrs children =
  let
    -- Extract visual properties from attributes
    background = extractBackground attrs
    borderRadius = extractBorderRadius attrs
    boxFromAttrs = extractBox attrs state.box
    
    -- Extract font configuration from style attributes.
    -- This propagates font settings (size, spacing, line-height) to child
    -- text elements. If no font styles are specified, inherits from parent.
    fontConfigFromAttrs = extractFontConfig attrs state.fontConfig
    
    -- Extract click handler if present
    clickHandler = extractClickHandler attrs
    
    -- Assign pick ID if interactive
    pickResult = case clickHandler of
      Nothing -> { pickId: Nothing, state: state }
      Just msg -> 
        let pid = DC.pickId state.nextPickId
        in { pickId: Just pid
           , state: state 
               { nextPickId = state.nextPickId + 1
               , pickMap = Map.insert pid msg state.pickMap
               }
           }
    
    state1 = pickResult.state
    
    -- Create DrawRect for this element if it has a background
    selfCommands = case background of
      Nothing -> []
      Just color ->
        [ DC.drawRect
            { x: Device.px boxFromAttrs.x
            , y: Device.px boxFromAttrs.y
            , width: Device.px boxFromAttrs.width
            , height: Device.px boxFromAttrs.height
            , fill: color
            , cornerRadius: borderRadius
            , depth: state1.currentDepth
            , pickId: pickResult.pickId
            , onClick: clickHandler
            }
        ]
    
    -- Update state for children: increment depth, set box, propagate font config
    childState = state1 
      { currentDepth = state1.currentDepth + 1.0
      , box = boxFromAttrs
      , fontConfig = fontConfigFromAttrs
      }
    
    -- Flatten children
    childResult = flattenChildren childState children
    
    -- Combine commands
    allCommands = selfCommands <> fst childResult
  in
    Tuple allCommands (snd childResult)

-- | Flatten an array of children.
flattenChildren
  :: forall msg
   . FlattenState msg
  -> Array (E.Element msg)
  -> Tuple (DC.CommandBuffer msg) (FlattenState msg)
flattenChildren state children =
  foldl go (Tuple [] state) children
  where
    go (Tuple cmds st) child =
      let result = flattenWithState st child
      in Tuple (cmds <> fst result) (snd result)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default layout box (1080p viewport dimensions).
-- |
-- | Provides reasonable defaults for flattening without explicit layout.
-- | Override with actual viewport dimensions for responsive rendering.
defaultBox :: LayoutBox
defaultBox = { x: 0.0, y: 0.0, width: 1920.0, height: 1080.0 }

-- | Offset a box by delta x and y.
offsetBox :: Number -> Number -> LayoutBox -> LayoutBox
offsetBox dx dy box = box { x = box.x + dx, y = box.y + dy }

-- | Check if two layout boxes are equal (for layout caching)
-- | Uses Eq constraint for proper comparison
boxesEqual :: LayoutBox -> LayoutBox -> Boolean
boxesEqual a b =
  a.x == b.x && a.y == b.y && a.width == b.width && a.height == b.height

-- | Generic equality check for any Eq type
-- | Useful for comparing element IDs, style values
genericEqual :: forall a. Eq a => a -> a -> Boolean
genericEqual x y = x == y

-- | Show a layout box for debugging
-- | Uses Show for numeric display
showBox :: LayoutBox -> String
showBox box = 
  "LayoutBox { x: " <> show box.x <> 
  ", y: " <> show box.y <> 
  ", width: " <> show box.width <> 
  ", height: " <> show box.height <> " }"

-- | Generic show for debugging
-- | Uses Show constraint for any showable type
showDebug :: forall a. Show a => a -> String
showDebug = show

-- | Discard a Maybe result, returning unit.
-- |
-- | Used when a computation produces a Maybe but we only care that it ran,
-- | not about the result. Commonly needed when chaining operations where
-- | intermediate steps may fail but we want to continue regardless.
discardMaybe :: forall a. Maybe a -> Unit
discardMaybe _ = unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // style extraction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract background color from attributes.
-- |
-- | Looks for style attributes with "background-color" or "background".
-- | Currently supports rgb/rgba CSS strings for compatibility.
-- | Future: direct Schema atom usage.
extractBackground :: forall msg. Array (E.Attribute msg) -> Maybe RGB.RGBA
extractBackground attrs =
  let
    findBg = Array.findMap extractBgFromAttr attrs
  in
    findBg
  where
    extractBgFromAttr = case _ of
      E.Style "background-color" value -> parseColorString value
      E.Style "background" value -> parseColorString value
      _ -> Nothing

-- | Extract border radius from attributes.
extractBorderRadius :: forall msg. Array (E.Attribute msg) -> Radius.Corners
extractBorderRadius attrs =
  let
    findRadius = Array.findMap extractRadiusFromAttr attrs
  in
    case findRadius of
      Nothing -> Radius.cornersAll Radius.none
      Just r -> r
  where
    extractRadiusFromAttr = case _ of
      E.Style "border-radius" value -> parseRadiusString value
      _ -> Nothing

-- | Extract layout box from position/size attributes.
extractBox :: forall msg. Array (E.Attribute msg) -> LayoutBox -> LayoutBox
extractBox attrs parentBox =
  foldl applyStyle parentBox attrs
  where
    applyStyle box = case _ of
      E.Style "left" v -> case parsePixelValue v of
        Just n -> box { x = parentBox.x + n }
        Nothing -> box
      E.Style "top" v -> case parsePixelValue v of
        Just n -> box { y = parentBox.y + n }
        Nothing -> box
      E.Style "width" v -> case parsePixelValue v of
        Just n -> box { width = n }
        Nothing -> box
      E.Style "height" v -> case parsePixelValue v of
        Just n -> box { height = n }
        Nothing -> box
      _ -> box

-- | Extract click handler from attributes.
extractClickHandler :: forall msg. Array (E.Attribute msg) -> Maybe msg
extractClickHandler = Array.findMap go
  where
    go = case _ of
      E.Handler (E.OnClick msg) -> Just msg
      _ -> Nothing

-- | Extract font configuration from style attributes.
-- |
-- | Looks for font-family, font-size, letter-spacing, line-height.
-- | Uses bind for monadic composition over Maybe.
extractFontConfig :: forall msg. Array (E.Attribute msg) -> Text.FontConfig -> Text.FontConfig
extractFontConfig attrs defaultConfig =
  foldl applyFontStyle defaultConfig attrs
  where
    applyFontStyle config = case _ of
      E.Style "font-size" v -> 
        case bind (parsePixelValue v) (\size -> pure size) of
          Just size -> config { fontSize = size }
          Nothing -> config
      E.Style "letter-spacing" v ->
        case parsePixelValue v of
          Just spacing -> config { letterSpacing = spacing }
          Nothing -> config
      E.Style "line-height" v ->
        case parsePixelValue v of
          Just lh -> config { lineHeight = lh }
          Nothing -> config
      _ -> config

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // parsers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse a CSS color string to RGBA.
-- |
-- | Supports:
-- | - Hex colors: #RRGGBB, #RGB
-- | - Named colors: black, white, red, green, blue (common subset)
-- |
-- | NOTE: This is for legacy compatibility. New components should use
-- | Schema atoms directly, not CSS strings. For full CSS color parsing
-- | including rgb(), rgba(), hsl(), etc., use a dedicated CSS parser.
parseColorString :: String -> Maybe RGB.RGBA
parseColorString str = case str of
  -- Named colors (common subset)
  "black"   -> Just (RGB.rgba 0 0 0 255)
  "white"   -> Just (RGB.rgba 255 255 255 255)
  "red"     -> Just (RGB.rgba 255 0 0 255)
  "green"   -> Just (RGB.rgba 0 128 0 255)
  "blue"    -> Just (RGB.rgba 0 0 255 255)
  "yellow"  -> Just (RGB.rgba 255 255 0 255)
  "cyan"    -> Just (RGB.rgba 0 255 255 255)
  "magenta" -> Just (RGB.rgba 255 0 255 255)
  "gray"    -> Just (RGB.rgba 128 128 128 255)
  "grey"    -> Just (RGB.rgba 128 128 128 255)
  "orange"  -> Just (RGB.rgba 255 165 0 255)
  "purple"  -> Just (RGB.rgba 128 0 128 255)
  "transparent" -> Just (RGB.rgba 0 0 0 0)
  -- Hex colors
  _ -> parseHexColor str

-- | Parse hex color (#RGB or #RRGGBB)
parseHexColor :: String -> Maybe RGB.RGBA
parseHexColor str = case String.stripPrefix (Pattern "#") str of
  Nothing -> Nothing
  Just hex ->
    let len = String.length hex
    in if len == 6 then parseHex6 hex
       else if len == 3 then parseHex3 hex
       else Nothing

-- | Parse 6-digit hex color (RRGGBB)
parseHex6 :: String -> Maybe RGB.RGBA
parseHex6 hex = 
  let 
    rStr = String.take 2 hex
    gStr = String.take 2 (String.drop 2 hex)
    bStr = String.take 2 (String.drop 4 hex)
  in
    case parseHexPair rStr, parseHexPair gStr, parseHexPair bStr of
      Just r, Just g, Just b -> Just (RGB.rgba r g b 255)
      _, _, _ -> Nothing

-- | Parse 3-digit hex color (RGB) - each digit is doubled
parseHex3 :: String -> Maybe RGB.RGBA
parseHex3 hex =
  let
    rChar = String.take 1 hex
    gChar = String.take 1 (String.drop 1 hex)
    bChar = String.take 1 (String.drop 2 hex)
  in
    case parseHexDigit rChar, parseHexDigit gChar, parseHexDigit bChar of
      Just r, Just g, Just b -> 
        -- Double each digit: F -> FF (15 -> 255, not 15*16)
        Just (RGB.rgba (r + r * 16) (g + g * 16) (b + b * 16) 255)
      _, _, _ -> Nothing

-- | Parse a two-character hex pair to Int (00-FF -> 0-255)
parseHexPair :: String -> Maybe Int
parseHexPair str =
  case String.toCharArray str of
    [c1, c2] -> 
      case hexCharToInt c1, hexCharToInt c2 of
        Just h, Just l -> Just (h * 16 + l)
        _, _ -> Nothing
    _ -> Nothing

-- | Parse a single hex digit string to Int
parseHexDigit :: String -> Maybe Int
parseHexDigit str = case String.toCharArray str of
  [c] -> hexCharToInt c
  _ -> Nothing

-- | Convert hex character to integer value
hexCharToInt :: Char -> Maybe Int
hexCharToInt c = case c of
  '0' -> Just 0
  '1' -> Just 1
  '2' -> Just 2
  '3' -> Just 3
  '4' -> Just 4
  '5' -> Just 5
  '6' -> Just 6
  '7' -> Just 7
  '8' -> Just 8
  '9' -> Just 9
  'a' -> Just 10
  'A' -> Just 10
  'b' -> Just 11
  'B' -> Just 11
  'c' -> Just 12
  'C' -> Just 12
  'd' -> Just 13
  'D' -> Just 13
  'e' -> Just 14
  'E' -> Just 14
  'f' -> Just 15
  'F' -> Just 15
  _ -> Nothing

-- | Parse a CSS radius string.
-- |
-- | Supports:
-- | - Pixel values: "8px", "16px"
-- | - Plain numbers: "8", "16" (interpreted as pixels)
-- |
-- | For percentage-based or viewport-relative radii, use Schema atoms directly.
parseRadiusString :: String -> Maybe Radius.Corners
parseRadiusString str = case parsePixelValue str of
  Nothing -> Nothing
  Just pxValue -> Just (Radius.cornersAll (Radius.px pxValue))

-- | Parse a pixel value like "100px" or "100".
-- |
-- | Supports:
-- | - Plain numbers: "100", "3.14"
-- | - Pixel values: "100px", "3.14px"
-- |
-- | Returns Nothing for invalid strings or unsupported units.
parsePixelValue :: String -> Maybe Number
parsePixelValue str =
  -- Try stripping "px" suffix first
  case String.stripSuffix (Pattern "px") str of
    Just numStr -> Number.fromString numStr
    Nothing -> 
      -- No "px" suffix, try parsing as plain number
      Number.fromString str
