-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // straylight // playground // main
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Straylight Playground — WebGL Showcase for 186 Schema Atoms
-- |
-- | This demonstrates Hydrogen's pure Element architecture:
-- | - Element composed entirely from Schema atoms
-- | - No strings (except text content)
-- | - No CSS, no escape hatches
-- | - WebGL rendering via pure data interpretation
-- |
-- | Architecture:
-- | 1. PureScript defines Element + Schema atoms (pure types)
-- | 2. This app generates Element values
-- | 3. Runtime interprets Element → WebGL draw calls

module Main where

import Prelude

import Data.Array (mapWithIndex, range)
import Data.Int (toNumber) as Int
import Effect (Effect)
import Effect.Console as Console

import Hydrogen.Element.Pure as E
import Hydrogen.Element.Pure
  ( opacityFull
  , clipNone
  , maskNone
  , lineHeightNormal
  , letterSpacingNone
  , degreesZero
  )
import Hydrogen.Schema.Color.Channel (unwrap) as Channel
import Hydrogen.Schema.Color.Conversion (hslToRgb)
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.SRGB as SRGB
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device (px, addPx)
import Hydrogen.Schema.Dimension.Vector.Vec2 (vec2)
import Hydrogen.Schema.Typography.FontFamily as FontFamily
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight
import Hydrogen.Schema.Geometry.Position (Alignment(AlignStart, AlignCenter, AlignEnd))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // app // state
-- ═════════════════════════════════════════════════════════════════════════════

type State =
  { selectedPillar :: Pillar
  , theme :: Theme
  }

data Pillar
  = ColorPillar
  | DimensionPillar
  | GeometryPillar
  | TypographyPillar
  | MaterialPillar
  | ElevationPillar
  | TemporalPillar
  | ReactivePillar
  | GesturalPillar
  | HapticPillar
  | SpatialPillar
  | BrandPillar

derive instance eqPillar :: Eq Pillar

data Theme
  = Mono
  | Accent
  | Soft
  | Brutal
  | Glass

derive instance eqTheme :: Eq Theme

data Msg
  = SelectPillar Pillar
  | SelectTheme Theme
  | NoOp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pillar // names
-- ═════════════════════════════════════════════════════════════════════════════

pillarName :: Pillar -> String
pillarName = case _ of
  ColorPillar -> "Color"
  DimensionPillar -> "Dimension"
  GeometryPillar -> "Geometry"
  TypographyPillar -> "Typography"
  MaterialPillar -> "Material"
  ElevationPillar -> "Elevation"
  TemporalPillar -> "Temporal"
  ReactivePillar -> "Reactive"
  GesturalPillar -> "Gestural"
  HapticPillar -> "Haptic"
  SpatialPillar -> "Spatial"
  BrandPillar -> "Brand"

allPillars :: Array Pillar
allPillars =
  [ ColorPillar
  , DimensionPillar
  , GeometryPillar
  , TypographyPillar
  , MaterialPillar
  , ElevationPillar
  , TemporalPillar
  , ReactivePillar
  , GesturalPillar
  , HapticPillar
  , SpatialPillar
  , BrandPillar
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // elm // arch
-- ═════════════════════════════════════════════════════════════════════════════

init :: State
init =
  { selectedPillar: ColorPillar
  , theme: Glass
  }

update :: Msg -> State -> State
update msg state = case msg of
  SelectPillar pillar -> state { selectedPillar = pillar }
  SelectTheme theme -> state { theme = theme }
  NoOp -> state

view :: State -> E.Element Msg
view state = E.Group
  { children:
      [ renderSidebar state
      , renderContent state
      ]
  , position: vec2 (px 0.0) (px 0.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // sidebar
-- ═════════════════════════════════════════════════════════════════════════════

renderSidebar :: State -> E.Element Msg
renderSidebar state = E.Group
  { children:
      [ sidebarBackground
      , sidebarTitle
      , pillarNav state
      ]
  , position: vec2 (px 0.0) (px 0.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

sidebarBackground :: E.Element Msg
sidebarBackground = E.Rectangle
  { position: vec2 (px 0.0) (px 0.0)
  , size: vec2 (px 280.0) (px 1080.0)
  , fill: E.SolidWithAlpha
      (SRGB.srgb 20 20 25)
      (Opacity.opacity 80)
  , corners: E.Sharp
  , stroke: E.NoStroke
  , shadow: E.NoShadow
  , filters: E.NoFilters
  , opacity: opacityFull
  , clipContent: false
  }

sidebarTitle :: E.Element Msg
sidebarTitle = E.Text
  { content: "HYDROGEN"
  , position: vec2 (px 24.0) (px 32.0)
  , fontFamily: FontFamily.fontFamily "Inter"
  , fontSize: FontSize.fontSize 24.0
  , fontWeight: FontWeight.fontWeight 700
  , lineHeight: lineHeightNormal
  , letterSpacing: letterSpacingNone
  , color: SRGB.srgb 255 255 255
  , opacity: opacityFull
  , maxWidth: px 0.0
  , shadow: E.NoShadow
  , horizontalAlign: AlignStart
  , verticalAlign: AlignStart
  }

pillarNav :: State -> E.Element Msg
pillarNav state = E.Group
  { children: mapWithIndex (renderPillarButton state) allPillars
  , position: vec2 (px 0.0) (px 80.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderPillarButton :: State -> Int -> Pillar -> E.Element Msg
renderPillarButton state index pillar =
  let
    isSelected = state.selectedPillar == pillar
    yOffset = px (toNumber index * 44.0)
    bgColor = if isSelected
      then SRGB.srgb 59 130 246
      else SRGB.srgb 40 40 50
    textColor = SRGB.srgb 255 255 255
  in
    E.Group
      { children:
          [ E.Rectangle
              { position: vec2 (px 12.0) yOffset
              , size: vec2 (px 256.0) (px 40.0)
              , fill: E.Solid bgColor
              , corners: E.Sharp
              , stroke: E.NoStroke
              , shadow: E.NoShadow
              , filters: E.NoFilters
              , opacity: opacityFull
              , clipContent: false
              }
          , E.Text
              { content: pillarName pillar
              , position: vec2 (px 24.0) (addPx yOffset (px 26.0))
              , fontFamily: FontFamily.fontFamily "Inter"
              , fontSize: FontSize.fontSize 14.0
              , fontWeight: FontWeight.fontWeight (if isSelected then 600 else 400)
              , lineHeight: lineHeightNormal
              , letterSpacing: letterSpacingNone
              , color: textColor
              , opacity: opacityFull
              , maxWidth: px 0.0
              , shadow: E.NoShadow
              , horizontalAlign: AlignStart
              , verticalAlign: AlignStart
              }
          ]
      , position: vec2 (px 0.0) (px 0.0)
      , opacity: opacityFull
      , clipPath: clipNone
      , mask: maskNone
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // content
-- ═════════════════════════════════════════════════════════════════════════════

renderContent :: State -> E.Element Msg
renderContent state = case state.selectedPillar of
  ColorPillar -> renderColorPillar
  DimensionPillar -> renderDimensionPillar
  GeometryPillar -> renderGeometryPillar
  TypographyPillar -> renderTypographyPillar
  MaterialPillar -> renderMaterialPillar
  ElevationPillar -> renderElevationPillar
  TemporalPillar -> renderTemporalPillar
  ReactivePillar -> renderReactivePillar
  GesturalPillar -> renderGesturalPillar
  HapticPillar -> renderHapticPillar
  SpatialPillar -> renderSpatialPillar
  BrandPillar -> renderBrandPillar

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // color // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderColorPillar :: E.Element Msg
renderColorPillar = E.Group
  { children:
      [ pillarTitle "Color"
      , pillarDescription "Color science, theory, and application. 47 atoms across HSL, RGB, CMYK, LAB, LCH, OKLAB, OKLCH, XYZ, YUV, and more."
      , hueSwatches
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

-- | Render 360 hue swatches from the Hue atom
-- |
-- | Each swatch is a Rectangle filled with a color derived from:
-- | - Hue: 0-359 (the variable)
-- | - Saturation: 100% (fully saturated)
-- | - Lightness: 50% (maximum chroma)
-- |
-- | This demonstrates the Hue atom's full range and the HSL→RGB conversion.
hueSwatches :: E.Element Msg
hueSwatches = E.Group
  { children: map renderHueSwatch (range 0 359)
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderHueSwatch :: Int -> E.Element Msg
renderHueSwatch hueValue =
  let
    -- Create HSL color: full saturation, 50% lightness for maximum chroma
    hslColor = HSL.hsl hueValue 100 50
    -- Convert HSL to RGB for display
    rgbColor = hslToRgb hslColor
    -- Convert RGB to SRGB for Element
    srgbColor = SRGB.srgb 
      (Channel.unwrap (RGB.red rgbColor)) 
      (Channel.unwrap (RGB.green rgbColor)) 
      (Channel.unwrap (RGB.blue rgbColor))
    -- Layout: 20 swatches per row, 18 rows total
    col = hueValue `mod` 20
    row = hueValue / 20
    xPos = px (toNumber col * 32.0)
    yPos = px (toNumber row * 32.0)
  in
    E.Rectangle
      { position: vec2 xPos yPos
      , size: vec2 (px 30.0) (px 30.0)
      , fill: E.Solid srgbColor
      , corners: E.Sharp
      , stroke: E.NoStroke
      , shadow: E.NoShadow
      , filters: E.NoFilters
      , opacity: opacityFull
      , clipContent: false
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dimension // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderDimensionPillar :: E.Element Msg
renderDimensionPillar = E.Group
  { children:
      [ pillarTitle "Dimension"
      , pillarDescription "Measurement, spacing, and layout. SI units, device units, relative units, viewport units."
      , dimensionShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

dimensionShowcase :: E.Element Msg
dimensionShowcase = E.Group
  { children:
      [ renderDimensionBox 0 "8px" 8.0
      , renderDimensionBox 1 "16px" 16.0
      , renderDimensionBox 2 "24px" 24.0
      , renderDimensionBox 3 "32px" 32.0
      , renderDimensionBox 4 "48px" 48.0
      , renderDimensionBox 5 "64px" 64.0
      , renderDimensionBox 6 "96px" 96.0
      , renderDimensionBox 7 "128px" 128.0
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderDimensionBox :: Int -> String -> Number -> E.Element Msg
renderDimensionBox index label size =
  let
    yPos = px (toNumber index * 140.0)
  in
    E.Group
      { children:
          [ E.Rectangle
              { position: vec2 (px 0.0) yPos
              , size: vec2 (px size) (px size)
              , fill: E.Solid (SRGB.srgb 59 130 246)
              , corners: E.Sharp
              , stroke: E.NoStroke
              , shadow: E.NoShadow
              , filters: E.NoFilters
              , opacity: opacityFull
              , clipContent: false
              }
          , E.Text
              { content: label
              , position: vec2 (px (size + 16.0)) (addPx yPos (px (size / 2.0 + 5.0)))
              , fontFamily: FontFamily.fontFamily "Inter"
              , fontSize: FontSize.fontSize 14.0
              , fontWeight: FontWeight.fontWeight 500
              , lineHeight: lineHeightNormal
              , letterSpacing: letterSpacingNone
              , color: SRGB.srgb 200 200 200
              , opacity: opacityFull
              , maxWidth: px 0.0
              , shadow: E.NoShadow
              , horizontalAlign: AlignStart
              , verticalAlign: AlignStart
              }
          ]
      , position: vec2 (px 0.0) (px 0.0)
      , opacity: opacityFull
      , clipPath: clipNone
      , mask: maskNone
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // geometry // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderGeometryPillar :: E.Element Msg
renderGeometryPillar = E.Group
  { children:
      [ pillarTitle "Geometry"
      , pillarDescription "Shape, form, and spatial transformation. Points, lines, curves, polygons, transforms."
      , geometryShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

geometryShowcase :: E.Element Msg
geometryShowcase = E.Group
  { children:
      [ E.Rectangle
          { position: vec2 (px 0.0) (px 0.0)
          , size: vec2 (px 100.0) (px 100.0)
          , fill: E.Solid (SRGB.srgb 239 68 68)
          , corners: E.Sharp
          , stroke: E.NoStroke
          , shadow: E.NoShadow
          , filters: E.NoFilters
          , opacity: opacityFull
          , clipContent: false
          }
      , E.Circle
          { center: vec2 (px 200.0) (px 50.0)
          , radius: px 50.0
          , fill: E.Solid (SRGB.srgb 34 197 94)
          , stroke: E.NoStroke
          , shadow: E.NoShadow
          , filters: E.NoFilters
          , opacity: opacityFull
          }
      , E.Rectangle
          { position: vec2 (px 300.0) (px 0.0)
          , size: vec2 (px 100.0) (px 100.0)
          , fill: E.Solid (SRGB.srgb 59 130 246)
          , corners: E.Sharp
          , stroke: E.NoStroke
          , shadow: E.NoShadow
          , filters: E.NoFilters
          , opacity: opacityFull
          , clipContent: false
          }
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // typography // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderTypographyPillar :: E.Element Msg
renderTypographyPillar = E.Group
  { children:
      [ pillarTitle "Typography"
      , pillarDescription "Text rendering and typographic hierarchy. Font families, weights, sizes, line heights."
      , typographyShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

typographyShowcase :: E.Element Msg
typographyShowcase = E.Group
  { children:
      [ renderTypeSample 0 "Display" 48.0 800
      , renderTypeSample 1 "Heading 1" 36.0 700
      , renderTypeSample 2 "Heading 2" 30.0 600
      , renderTypeSample 3 "Heading 3" 24.0 600
      , renderTypeSample 4 "Body Large" 18.0 400
      , renderTypeSample 5 "Body" 16.0 400
      , renderTypeSample 6 "Body Small" 14.0 400
      , renderTypeSample 7 "Caption" 12.0 400
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderTypeSample :: Int -> String -> Number -> Int -> E.Element Msg
renderTypeSample index label size weight =
  let
    yPos = px (toNumber index * 60.0)
  in
    E.Text
      { content: label
      , position: vec2 (px 0.0) yPos
      , fontFamily: FontFamily.fontFamily "Inter"
      , fontSize: FontSize.fontSize size
      , fontWeight: FontWeight.fontWeight weight
      , lineHeight: lineHeightNormal
      , letterSpacing: letterSpacingNone
      , color: SRGB.srgb 255 255 255
      , opacity: opacityFull
      , maxWidth: px 0.0
      , shadow: E.NoShadow
      , horizontalAlign: AlignStart
      , verticalAlign: AlignStart
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // material // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderMaterialPillar :: E.Element Msg
renderMaterialPillar = E.Group
  { children:
      [ pillarTitle "Material"
      , pillarDescription "Surface appearance and texture. Blur, gradients, noise, borders, fills."
      , materialShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

materialShowcase :: E.Element Msg
materialShowcase = E.Group
  { children:
      [ E.Rectangle
          { position: vec2 (px 0.0) (px 0.0)
          , size: vec2 (px 150.0) (px 150.0)
          , fill: E.Solid (SRGB.srgb 100 100 120)
          , corners: E.Sharp
          , stroke: E.NoStroke
          , shadow: E.NoShadow
          , filters: E.NoFilters
          , opacity: opacityFull
          , clipContent: false
          }
      , E.Rectangle
          { position: vec2 (px 170.0) (px 0.0)
          , size: vec2 (px 150.0) (px 150.0)
          , fill: E.SolidWithAlpha (SRGB.srgb 100 100 120) (Opacity.opacity 50)
          , corners: E.Sharp
          , stroke: E.NoStroke
          , shadow: E.NoShadow
          , filters: E.NoFilters
          , opacity: opacityFull
          , clipContent: false
          }
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // elevation // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderElevationPillar :: E.Element Msg
renderElevationPillar = E.Group
  { children:
      [ pillarTitle "Elevation"
      , pillarDescription "Depth, shadow, and visual hierarchy. Z-index, shadows, perspective, depth of field."
      , elevationShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

elevationShowcase :: E.Element Msg
elevationShowcase = E.Group
  { children:
      [ renderElevationCard 0 "Level 0" (SRGB.srgb 50 50 60)
      , renderElevationCard 1 "Level 1" (SRGB.srgb 60 60 70)
      , renderElevationCard 2 "Level 2" (SRGB.srgb 70 70 80)
      , renderElevationCard 3 "Level 3" (SRGB.srgb 80 80 90)
      , renderElevationCard 4 "Level 4" (SRGB.srgb 90 90 100)
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderElevationCard :: Int -> String -> SRGB.SRGB -> E.Element Msg
renderElevationCard index label bgColor =
  let
    xPos = px (toNumber index * 140.0)
  in
    E.Group
      { children:
          [ E.Rectangle
              { position: vec2 xPos (px 0.0)
              , size: vec2 (px 120.0) (px 120.0)
              , fill: E.Solid bgColor
              , corners: E.Sharp
              , stroke: E.NoStroke
              , shadow: E.NoShadow
              , filters: E.NoFilters
              , opacity: opacityFull
              , clipContent: false
              }
          , E.Text
              { content: label
              , position: vec2 (addPx xPos (px 10.0)) (px 70.0)
              , fontFamily: FontFamily.fontFamily "Inter"
              , fontSize: FontSize.fontSize 12.0
              , fontWeight: FontWeight.fontWeight 500
              , lineHeight: lineHeightNormal
              , letterSpacing: letterSpacingNone
              , color: SRGB.srgb 200 200 200
              , opacity: opacityFull
              , maxWidth: px 0.0
              , shadow: E.NoShadow
              , horizontalAlign: AlignStart
              , verticalAlign: AlignStart
              }
          ]
      , position: vec2 (px 0.0) (px 0.0)
      , opacity: opacityFull
      , clipPath: clipNone
      , mask: maskNone
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // temporal // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderTemporalPillar :: E.Element Msg
renderTemporalPillar = E.Group
  { children:
      [ pillarTitle "Temporal"
      , pillarDescription "Time, motion, and animation. Duration, easing, keyframes, spring physics."
      , temporalShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

temporalShowcase :: E.Element Msg
temporalShowcase = E.Group
  { children:
      [ E.Text
          { content: "Animation primitives: Duration, Easing, Keyframes"
          , position: vec2 (px 0.0) (px 0.0)
          , fontFamily: FontFamily.fontFamily "Inter"
          , fontSize: FontSize.fontSize 16.0
          , fontWeight: FontWeight.fontWeight 400
          , lineHeight: lineHeightNormal
          , letterSpacing: letterSpacingNone
          , color: SRGB.srgb 180 180 180
          , opacity: opacityFull
          , maxWidth: px 0.0
          , shadow: E.NoShadow
          , horizontalAlign: AlignStart
          , verticalAlign: AlignStart
          }
      , E.Text
          { content: "Spring physics: Mass, Stiffness, Damping"
          , position: vec2 (px 0.0) (px 30.0)
          , fontFamily: FontFamily.fontFamily "Inter"
          , fontSize: FontSize.fontSize 16.0
          , fontWeight: FontWeight.fontWeight 400
          , lineHeight: lineHeightNormal
          , letterSpacing: letterSpacingNone
          , color: SRGB.srgb 180 180 180
          , opacity: opacityFull
          , maxWidth: px 0.0
          , shadow: E.NoShadow
          , horizontalAlign: AlignStart
          , verticalAlign: AlignStart
          }
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // reactive // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderReactivePillar :: E.Element Msg
renderReactivePillar = E.Group
  { children:
      [ pillarTitle "Reactive"
      , pillarDescription "State and feedback. Enabled, visible, selected, loading, progress, validation."
      , reactiveShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

reactiveShowcase :: E.Element Msg
reactiveShowcase = E.Group
  { children:
      [ renderStateIndicator 0 "Enabled" (SRGB.srgb 34 197 94)
      , renderStateIndicator 1 "Disabled" (SRGB.srgb 100 100 100)
      , renderStateIndicator 2 "Loading" (SRGB.srgb 250 204 21)
      , renderStateIndicator 3 "Error" (SRGB.srgb 239 68 68)
      , renderStateIndicator 4 "Success" (SRGB.srgb 34 197 94)
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderStateIndicator :: Int -> String -> SRGB.SRGB -> E.Element Msg
renderStateIndicator index label color =
  let
    yPos = px (toNumber index * 50.0)
  in
    E.Group
      { children:
          [ E.Circle
              { center: vec2 (px 12.0) (addPx yPos (px 12.0))
              , radius: px 8.0
              , fill: E.Solid color
              , stroke: E.NoStroke
              , shadow: E.NoShadow
              , filters: E.NoFilters
              , opacity: opacityFull
              }
          , E.Text
              { content: label
              , position: vec2 (px 32.0) (addPx yPos (px 16.0))
              , fontFamily: FontFamily.fontFamily "Inter"
              , fontSize: FontSize.fontSize 14.0
              , fontWeight: FontWeight.fontWeight 400
              , lineHeight: lineHeightNormal
              , letterSpacing: letterSpacingNone
              , color: SRGB.srgb 200 200 200
              , opacity: opacityFull
              , maxWidth: px 0.0
              , shadow: E.NoShadow
              , horizontalAlign: AlignStart
              , verticalAlign: AlignStart
              }
          ]
      , position: vec2 (px 0.0) (px 0.0)
      , opacity: opacityFull
      , clipPath: clipNone
      , mask: maskNone
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gestural // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderGesturalPillar :: E.Element Msg
renderGesturalPillar = E.Group
  { children:
      [ pillarTitle "Gestural"
      , pillarDescription "Touch, pointer, and gestures. Tap, swipe, pinch, rotate, pan, drag."
      , gesturalShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

gesturalShowcase :: E.Element Msg
gesturalShowcase = E.Group
  { children:
      [ renderGestureLabel 0 "Tap"
      , renderGestureLabel 1 "Double Tap"
      , renderGestureLabel 2 "Long Press"
      , renderGestureLabel 3 "Swipe"
      , renderGestureLabel 4 "Pinch"
      , renderGestureLabel 5 "Rotate"
      , renderGestureLabel 6 "Pan"
      , renderGestureLabel 7 "Drag"
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderGestureLabel :: Int -> String -> E.Element Msg
renderGestureLabel index label =
  let
    yPos = px (toNumber index * 36.0)
  in
    E.Text
      { content: "• " <> label
      , position: vec2 (px 0.0) yPos
      , fontFamily: FontFamily.fontFamily "Inter"
      , fontSize: FontSize.fontSize 16.0
      , fontWeight: FontWeight.fontWeight 400
      , lineHeight: lineHeightNormal
      , letterSpacing: letterSpacingNone
      , color: SRGB.srgb 180 180 180
      , opacity: opacityFull
      , maxWidth: px 0.0
      , shadow: E.NoShadow
      , horizontalAlign: AlignStart
      , verticalAlign: AlignStart
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // haptic // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderHapticPillar :: E.Element Msg
renderHapticPillar = E.Group
  { children:
      [ pillarTitle "Haptic"
      , pillarDescription "Tactile feedback primitives. Impact, selection, notification, success, warning, error."
      , hapticShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

hapticShowcase :: E.Element Msg
hapticShowcase = E.Group
  { children:
      [ renderHapticType 0 "Light Impact"
      , renderHapticType 1 "Medium Impact"
      , renderHapticType 2 "Heavy Impact"
      , renderHapticType 3 "Selection"
      , renderHapticType 4 "Success"
      , renderHapticType 5 "Warning"
      , renderHapticType 6 "Error"
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderHapticType :: Int -> String -> E.Element Msg
renderHapticType index label =
  let
    yPos = px (toNumber index * 36.0)
  in
    E.Text
      { content: "◉ " <> label
      , position: vec2 (px 0.0) yPos
      , fontFamily: FontFamily.fontFamily "Inter"
      , fontSize: FontSize.fontSize 16.0
      , fontWeight: FontWeight.fontWeight 400
      , lineHeight: lineHeightNormal
      , letterSpacing: letterSpacingNone
      , color: SRGB.srgb 180 180 180
      , opacity: opacityFull
      , maxWidth: px 0.0
      , shadow: E.NoShadow
      , horizontalAlign: AlignStart
      , verticalAlign: AlignStart
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // spatial // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderSpatialPillar :: E.Element Msg
renderSpatialPillar = E.Group
  { children:
      [ pillarTitle "Spatial"
      , pillarDescription "3D space, AR/VR primitives. Position3D, rotation, scale, PBR materials, lighting."
      , spatialShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

spatialShowcase :: E.Element Msg
spatialShowcase = E.Group
  { children:
      [ renderSpatialProperty 0 "Metallic"
      , renderSpatialProperty 1 "Roughness"
      , renderSpatialProperty 2 "Emissive Strength"
      , renderSpatialProperty 3 "IOR (Index of Refraction)"
      , renderSpatialProperty 4 "Transmission"
      , renderSpatialProperty 5 "Subsurface"
      , renderSpatialProperty 6 "Anisotropy"
      , renderSpatialProperty 7 "Clear Coat"
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

renderSpatialProperty :: Int -> String -> E.Element Msg
renderSpatialProperty index label =
  let
    yPos = px (toNumber index * 36.0)
  in
    E.Text
      { content: "▸ " <> label
      , position: vec2 (px 0.0) yPos
      , fontFamily: FontFamily.fontFamily "Inter"
      , fontSize: FontSize.fontSize 16.0
      , fontWeight: FontWeight.fontWeight 400
      , lineHeight: lineHeightNormal
      , letterSpacing: letterSpacingNone
      , color: SRGB.srgb 180 180 180
      , opacity: opacityFull
      , maxWidth: px 0.0
      , shadow: E.NoShadow
      , horizontalAlign: AlignStart
      , verticalAlign: AlignStart
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // brand // pillar
-- ═════════════════════════════════════════════════════════════════════════════

renderBrandPillar :: E.Element Msg
renderBrandPillar = E.Group
  { children:
      [ pillarTitle "Brand"
      , pillarDescription "Identity composition layer. The 12th pillar that composes all others into cohesive brand identity."
      , brandShowcase
      ]
  , position: vec2 (px 320.0) (px 40.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

brandShowcase :: E.Element Msg
brandShowcase = E.Group
  { children:
      [ E.Text
          { content: "Brand = Color + Dimension + Geometry + Typography + Material + Elevation + Temporal + Reactive + Gestural + Haptic + Spatial"
          , position: vec2 (px 0.0) (px 0.0)
          , fontFamily: FontFamily.fontFamily "Inter"
          , fontSize: FontSize.fontSize 14.0
          , fontWeight: FontWeight.fontWeight 400
          , lineHeight: lineHeightNormal
          , letterSpacing: letterSpacingNone
          , color: SRGB.srgb 150 150 150
          , opacity: opacityFull
          , maxWidth: px 0.0
          , shadow: E.NoShadow
          , horizontalAlign: AlignStart
          , verticalAlign: AlignStart
          }
      , E.Text
          { content: "When agents compose these atoms, they build deterministic brand identities."
          , position: vec2 (px 0.0) (px 40.0)
          , fontFamily: FontFamily.fontFamily "Inter"
          , fontSize: FontSize.fontSize 16.0
          , fontWeight: FontWeight.fontWeight 500
          , lineHeight: lineHeightNormal
          , letterSpacing: letterSpacingNone
          , color: SRGB.srgb 200 200 200
          , opacity: opacityFull
          , maxWidth: px 0.0
          , shadow: E.NoShadow
          , horizontalAlign: AlignStart
          , verticalAlign: AlignStart
          }
      ]
  , position: vec2 (px 0.0) (px 100.0)
  , opacity: opacityFull
  , clipPath: clipNone
  , mask: maskNone
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

pillarTitle :: String -> E.Element Msg
pillarTitle title = E.Text
  { content: title
  , position: vec2 (px 0.0) (px 0.0)
  , fontFamily: FontFamily.fontFamily "Inter"
  , fontSize: FontSize.fontSize 32.0
  , fontWeight: FontWeight.fontWeight 600
  , lineHeight: lineHeightNormal
  , letterSpacing: letterSpacingNone
  , color: SRGB.srgb 255 255 255
  , opacity: opacityFull
  , maxWidth: px 0.0
  , shadow: E.NoShadow
  , horizontalAlign: AlignStart
  , verticalAlign: AlignStart
  }

pillarDescription :: String -> E.Element Msg
pillarDescription desc = E.Text
  { content: desc
  , position: vec2 (px 0.0) (px 50.0)
  , fontFamily: FontFamily.fontFamily "Inter"
  , fontSize: FontSize.fontSize 16.0
  , fontWeight: FontWeight.fontWeight 400
  , lineHeight: lineHeightNormal
  , letterSpacing: letterSpacingNone
  , color: SRGB.srgb 160 160 160
  , opacity: opacityFull
  , maxWidth: px 0.0
  , shadow: E.NoShadow
  , horizontalAlign: AlignStart
  , verticalAlign: AlignStart
  }

toNumber :: Int -> Number
toNumber = Int.toNumber

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // runtime
-- ═════════════════════════════════════════════════════════════════════════════

main :: Effect Unit
main = do
  Console.log "Straylight Playground starting..."
  Console.log "Element type: Pure Schema atoms"
  Console.log "Rendering: WebGL"
  
  let element = view init
  Console.log $ "Root element: " <> show element
  
  Console.log "Ready. (Runtime pending)"
