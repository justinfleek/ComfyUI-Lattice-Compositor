-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // colorpicker // harmony
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorHarmony — Color harmony palette generator and display.
-- |
-- | ## Design Philosophy
-- |
-- | Color harmonies are mathematically related colors that work well together.
-- | Based on color wheel relationships:
-- |
-- | - **Complementary**: Opposite on wheel (180°)
-- | - **Analogous**: Adjacent colors (±30°)
-- | - **Triadic**: Three equally spaced (120° apart)
-- | - **Split-Complementary**: Complement's neighbors
-- | - **Tetradic**: Four colors forming rectangle
-- | - **Square**: Four colors at 90° intervals
-- |
-- | All calculations operate in HSL space for intuitive hue rotation.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | baseColor     | Color     | HSL               | Starting color         |
-- | | harmonyType   | -         | HarmonyType       | Relationship type      |
-- | | swatchSize    | Dimension | SwatchSize        | Display size           |

module Hydrogen.Element.Compound.ColorPicker.Harmony
  ( -- * Component
    harmonyPalette
  
  -- * Props
  , HarmonyProps
  , HarmonyProp
  , defaultHarmonyProps
  
  -- * Harmony Types
  , HarmonyType(Complementary, Analogous, Triadic, SplitComplementary, Tetradic, Square, Monochromatic)
  
  -- * Prop Builders
  , baseColor
  , harmonyType
  , swatchSize
  , showLabels
  , onSelect
  
  -- * Harmony Calculations (pure)
  , complementary
  , analogous
  , triadic
  , splitComplementary
  , tetradic
  , square
  , monochromatic
  
  -- * Utility
  , harmonyColors
  , harmonyName
  , harmonyAngleOffset
  , harmonySaturationWeight
  , harmonyBaseHue
  , harmonyBaseSaturation
  , harmonyAngularDistance
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , negate
  , (<>)
  , ($)
  , (-)
  , (+)
  , (<)
  , (>)
  , (/)
  , (*)
  )

import Data.Array (foldl)
import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Dimension.Swatch as SwatchDim
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // harmony types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color harmony relationship types
data HarmonyType
  = Complementary      -- ^ Opposite on wheel (180°)
  | Analogous          -- ^ Adjacent colors (±30°)
  | Triadic            -- ^ Three at 120° intervals
  | SplitComplementary -- ^ Complement's neighbors
  | Tetradic           -- ^ Rectangle on wheel
  | Square             -- ^ Four at 90° intervals
  | Monochromatic      -- ^ Same hue, varied lightness

derive instance eqHarmonyType :: Eq HarmonyType

instance showHarmonyType :: Show HarmonyType where
  show Complementary = "Complementary"
  show Analogous = "Analogous"
  show Triadic = "Triadic"
  show SplitComplementary = "Split-Complementary"
  show Tetradic = "Tetradic"
  show Square = "Square"
  show Monochromatic = "Monochromatic"

-- | Get display name for harmony type
harmonyName :: HarmonyType -> String
harmonyName = show

-- | Calculate the angular offset for each color in a harmony
-- | Returns the hue offset from base in degrees for each color
-- | Useful for visualizing harmony relationships on a color wheel
harmonyAngleOffset :: HarmonyType -> Array Int
harmonyAngleOffset Complementary = [0, 180]
harmonyAngleOffset Analogous = [negate 30, 0, 30]
harmonyAngleOffset Triadic = [0, 120, 240]
harmonyAngleOffset SplitComplementary = [0, 150, 210]
harmonyAngleOffset Tetradic = [0, 60, 180, 240]
harmonyAngleOffset Square = [0, 90, 180, 270]
harmonyAngleOffset Monochromatic = [0, 0, 0, 0, 0]

-- | Calculate a weighted saturation factor for a harmony type
-- | Returns a weight from 0.85 to 1.0 based on the harmony's angular spread
-- | Wider spreads (like complementary) get higher visual weight
harmonySaturationWeight :: HarmonyType -> Number
harmonySaturationWeight harmony =
  let
    -- Get the maximum angular spread for this harmony
    offsets = harmonyAngleOffset harmony
    maxOffset = findMaxOffset offsets 0
    -- Normalize: 0° spread = 0.85, 180° spread = 1.0
    weight = 0.85 + (intToNumber maxOffset / 180.0 * 0.15)
  in
    weight
  where
    findMaxOffset :: Array Int -> Int -> Int
    findMaxOffset arr currentMax =
      case Array.uncons arr of
        Nothing -> currentMax
        Just { head, tail } ->
          let absVal = if head < 0 then negate head else head
              newMax = if absVal > currentMax then absVal else currentMax
          in findMaxOffset tail newMax
    
    intToNumber :: Int -> Number
    intToNumber n = Hue.toNumber $ Hue.hue (if n > 359 then 359 else if n < 0 then 0 else n)

-- | Get raw hue value from an HSL color for calculations
-- | Useful for computing custom harmony relationships
harmonyBaseHue :: HSL.HSL -> Int
harmonyBaseHue color = Hue.unwrap $ HSL.hue color

-- | Get raw saturation value from an HSL color
-- | Useful for determining if harmony adjustments are needed
harmonyBaseSaturation :: HSL.HSL -> Int
harmonyBaseSaturation color = Sat.unwrap $ HSL.saturation color

-- | Calculate angular distance between two hues in a harmony
-- | Returns the absolute difference in degrees (0-180)
harmonyAngularDistance :: Int -> Int -> Int
harmonyAngularDistance hue1 hue2 =
  let
    diff = hue1 - hue2
    absDiff = if diff < 0 then negate diff else diff
  in
    if absDiff > 180 then 360 - absDiff else absDiff

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Harmony palette properties
type HarmonyProps msg =
  { -- Color
    baseColor :: HSL.HSL
  , harmonyType :: HarmonyType
  
  -- Dimensions
  , swatchSize :: SwatchDim.SwatchSize
  , gap :: Device.Pixel
  
  -- Appearance
  , borderRadius :: Maybe Radius.Radius
  , showLabels :: Boolean
  
  -- Behavior
  , onSelect :: Maybe (HSL.HSL -> msg)
  }

-- | Property modifier
type HarmonyProp msg = HarmonyProps msg -> HarmonyProps msg

-- | Default harmony properties
defaultHarmonyProps :: forall msg. HarmonyProps msg
defaultHarmonyProps =
  { baseColor: HSL.hsl 0 100 50
  , harmonyType: Complementary
  , swatchSize: SwatchDim.swatchSize 40.0
  , gap: Device.px 8.0
  , borderRadius: Nothing
  , showLabels: true
  , onSelect: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set base color
baseColor :: forall msg. HSL.HSL -> HarmonyProp msg
baseColor c props = props { baseColor = c }

-- | Set harmony type
harmonyType :: forall msg. HarmonyType -> HarmonyProp msg
harmonyType t props = props { harmonyType = t }

-- | Set swatch size
swatchSize :: forall msg. SwatchDim.SwatchSize -> HarmonyProp msg
swatchSize s props = props { swatchSize = s }

-- | Set whether to show labels
showLabels :: forall msg. Boolean -> HarmonyProp msg
showLabels b props = props { showLabels = b }

-- | Set selection handler
onSelect :: forall msg. (HSL.HSL -> msg) -> HarmonyProp msg
onSelect handler props = props { onSelect = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // harmony calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get colors for a harmony type
harmonyColors :: HarmonyType -> HSL.HSL -> Array HSL.HSL
harmonyColors Complementary c = complementary c
harmonyColors Analogous c = analogous c
harmonyColors Triadic c = triadic c
harmonyColors SplitComplementary c = splitComplementary c
harmonyColors Tetradic c = tetradic c
harmonyColors Square c = square c
harmonyColors Monochromatic c = monochromatic c

-- | Complementary: base + opposite (180°)
complementary :: HSL.HSL -> Array HSL.HSL
complementary c =
  [ c
  , HSL.rotateHue 180 c
  ]

-- | Analogous: base + neighbors (±30°)
analogous :: HSL.HSL -> Array HSL.HSL
analogous c =
  [ HSL.rotateHue (-30) c
  , c
  , HSL.rotateHue 30 c
  ]

-- | Triadic: three colors at 120° intervals
triadic :: HSL.HSL -> Array HSL.HSL
triadic c =
  [ c
  , HSL.rotateHue 120 c
  , HSL.rotateHue 240 c
  ]

-- | Split-complementary: base + complement's neighbors
splitComplementary :: HSL.HSL -> Array HSL.HSL
splitComplementary c =
  [ c
  , HSL.rotateHue 150 c
  , HSL.rotateHue 210 c
  ]

-- | Tetradic: rectangle on color wheel
tetradic :: HSL.HSL -> Array HSL.HSL
tetradic c =
  [ c
  , HSL.rotateHue 60 c
  , HSL.rotateHue 180 c
  , HSL.rotateHue 240 c
  ]

-- | Square: four colors at 90° intervals
square :: HSL.HSL -> Array HSL.HSL
square c =
  [ c
  , HSL.rotateHue 90 c
  , HSL.rotateHue 180 c
  , HSL.rotateHue 270 c
  ]

-- | Monochromatic: same hue, varied lightness
monochromatic :: HSL.HSL -> Array HSL.HSL
monochromatic c =
  let
    h = HSL.hue c
    s = HSL.saturation c
  in
    [ HSL.fromComponents h s (Light.lightness 20)
    , HSL.fromComponents h s (Light.lightness 35)
    , HSL.fromComponents h s (Light.lightness 50)
    , HSL.fromComponents h s (Light.lightness 65)
    , HSL.fromComponents h s (Light.lightness 80)
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a harmony palette
-- |
-- | Displays the base color and its harmonious companions in a row.
harmonyPalette :: forall msg. Array (HarmonyProp msg) -> E.Element msg
harmonyPalette propModifiers =
  let
    props = foldl (\p f -> f p) defaultHarmonyProps propModifiers
    
    -- Get harmony colors
    colors = harmonyColors props.harmonyType props.baseColor
    
    -- Dimensions
    sizePx = show (SwatchDim.swatchSizeValue props.swatchSize) <> "px"
    gapPx = show (Device.unwrapPixel props.gap) <> "px"
    
    radiusStyle = case props.borderRadius of
      Just r -> Radius.toLegacyCss r
      Nothing -> "4px"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ -- Label
        if props.showLabels
          then E.div_
            [ E.style "font-size" "12px"
            , E.style "color" "#666"
            , E.style "font-weight" "500"
            ]
            [ E.text (harmonyName props.harmonyType) ]
          else E.span_ [] []
        
        -- Color swatches
      , E.div_
          [ E.style "display" "flex"
          , E.style "gap" gapPx
          ]
          (map (renderHarmonySwatch sizePx radiusStyle) colors)
      ]

-- | Render a single harmony swatch
renderHarmonySwatch :: forall msg. String -> String -> HSL.HSL -> E.Element msg
renderHarmonySwatch sizePx radiusStyle color =
  E.div_
    [ E.style "width" sizePx
    , E.style "height" sizePx
    , E.style "background" (HSL.toLegacyCss color)
    , E.style "border-radius" radiusStyle
    , E.style "border" "1px solid rgba(0,0,0,0.1)"
    , E.style "cursor" "pointer"
    , E.style "transition" "transform 0.1s"
    ]
    []
