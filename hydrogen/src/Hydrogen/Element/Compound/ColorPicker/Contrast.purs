-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // colorpicker // contrast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ContrastChecker — WCAG contrast ratio calculator and display.
-- |
-- | ## Design Philosophy
-- |
-- | Accessibility requires sufficient contrast between foreground and background.
-- | WCAG 2.1 defines minimum contrast ratios:
-- |
-- | - **AA Normal**: 4.5:1 (body text)
-- | - **AA Large**: 3:1 (18pt+ or 14pt bold)
-- | - **AAA Normal**: 7:1 (enhanced)
-- | - **AAA Large**: 4.5:1 (enhanced large text)
-- |
-- | ## Relative Luminance Formula
-- |
-- | L = 0.2126 * R + 0.7152 * G + 0.0722 * B
-- | where R, G, B are linearized (gamma-corrected) values.

module Hydrogen.Element.Compound.ColorPicker.Contrast
  ( -- * Component
    contrastChecker
  
  -- * Props  
  , ContrastProps
  , ContrastProp
  , defaultContrastProps
  
  -- * Prop Builders
  , foreground
  , background
  , showRatio
  , showGrades
  
  -- * Calculations (pure)
  , contrastRatio
  , relativeLuminance
  , meetsAA
  , meetsAALarge
  , meetsAAA
  , meetsAAALarge
  
  -- * Grade Type
  , WCAGGrade(Fail, AALarge, AA, AAALarge, AAA)
  , gradeFor
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude

import Data.Array (foldl)
import Data.Int (toNumber, floor) as Int
import Data.Number (pow)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // wcag grades
-- ═════════════════════════════════════════════════════════════════════════════

-- | WCAG conformance grades
data WCAGGrade
  = Fail
  | AALarge
  | AA
  | AAALarge  
  | AAA

derive instance eqWCAGGrade :: Eq WCAGGrade
derive instance ordWCAGGrade :: Ord WCAGGrade

instance showWCAGGrade :: Show WCAGGrade where
  show Fail = "Fail"
  show AALarge = "AA Large"
  show AA = "AA"
  show AAALarge = "AAA Large"
  show AAA = "AAA"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contrast checker properties
-- | Note: msg parameter kept for consistency with other component prop types,
-- | even though contrast checker has no event handlers currently
type ContrastProps :: forall k. k -> Type
type ContrastProps msg =
  { foreground :: RGB.RGB
  , background :: RGB.RGB
  , showRatio :: Boolean
  , showGrades :: Boolean
  }

-- | Property modifier
type ContrastProp :: forall k. k -> Type
type ContrastProp msg = ContrastProps msg -> ContrastProps msg

-- | Default properties
defaultContrastProps :: forall msg. ContrastProps msg
defaultContrastProps =
  { foreground: RGB.rgb 0 0 0
  , background: RGB.rgb 255 255 255
  , showRatio: true
  , showGrades: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set foreground color
foreground :: forall msg. RGB.RGB -> ContrastProp msg
foreground c props = props { foreground = c }

-- | Set background color
background :: forall msg. RGB.RGB -> ContrastProp msg
background c props = props { background = c }

-- | Set whether to show ratio
showRatio :: forall msg. Boolean -> ContrastProp msg
showRatio b props = props { showRatio = b }

-- | Set whether to show grades
showGrades :: forall msg. Boolean -> ContrastProp msg
showGrades b props = props { showGrades = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // luminance calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate relative luminance per WCAG 2.1
-- |
-- | L = 0.2126 * R + 0.7152 * G + 0.0722 * B
-- | where R, G, B are linearized from sRGB.
relativeLuminance :: RGB.RGB -> Number
relativeLuminance color =
  let
    r = linearize (Int.toNumber (Channel.unwrap (RGB.red color)) / 255.0)
    g = linearize (Int.toNumber (Channel.unwrap (RGB.green color)) / 255.0)
    b = linearize (Int.toNumber (Channel.unwrap (RGB.blue color)) / 255.0)
  in
    0.2126 * r + 0.7152 * g + 0.0722 * b

-- | Linearize sRGB channel value
-- |
-- | if C <= 0.03928 then C/12.92 else ((C+0.055)/1.055)^2.4
linearize :: Number -> Number
linearize c =
  if c <= 0.03928
    then c / 12.92
    else pow ((c + 0.055) / 1.055) 2.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // contrast calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate contrast ratio between two colors
-- |
-- | Ratio = (L1 + 0.05) / (L2 + 0.05)
-- | where L1 is the lighter luminance.
contrastRatio :: RGB.RGB -> RGB.RGB -> Number
contrastRatio c1 c2 =
  let
    l1 = relativeLuminance c1
    l2 = relativeLuminance c2
    lighter = if l1 > l2 then l1 else l2
    darker = if l1 > l2 then l2 else l1
  in
    (lighter + 0.05) / (darker + 0.05)

-- | Check if contrast meets WCAG AA for normal text (4.5:1)
meetsAA :: RGB.RGB -> RGB.RGB -> Boolean
meetsAA c1 c2 = contrastRatio c1 c2 >= 4.5

-- | Check if contrast meets WCAG AA for large text (3:1)
meetsAALarge :: RGB.RGB -> RGB.RGB -> Boolean
meetsAALarge c1 c2 = contrastRatio c1 c2 >= 3.0

-- | Check if contrast meets WCAG AAA for normal text (7:1)
meetsAAA :: RGB.RGB -> RGB.RGB -> Boolean
meetsAAA c1 c2 = contrastRatio c1 c2 >= 7.0

-- | Check if contrast meets WCAG AAA for large text (4.5:1)
meetsAAALarge :: RGB.RGB -> RGB.RGB -> Boolean
meetsAAALarge c1 c2 = contrastRatio c1 c2 >= 4.5

-- | Get the highest WCAG grade achieved
gradeFor :: RGB.RGB -> RGB.RGB -> WCAGGrade
gradeFor c1 c2 =
  let ratio = contrastRatio c1 c2
  in
    if ratio >= 7.0 then AAA
    else if ratio >= 4.5 then AA
    else if ratio >= 3.0 then AALarge
    else Fail

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render contrast checker display
contrastChecker :: forall msg. Array (ContrastProp msg) -> E.Element msg
contrastChecker propModifiers =
  let
    props = foldl (\p f -> f p) defaultContrastProps propModifiers
    ratio = contrastRatio props.foreground props.background
    grade = gradeFor props.foreground props.background
    
    -- Format ratio to 2 decimal places
    ratioStr = formatRatio ratio
    
    -- Grade color for visual indication
    gradeColor = case grade of
      AAA -> "#22c55e"
      AA -> "#84cc16"
      AAALarge -> "#84cc16"
      AALarge -> "#eab308"
      Fail -> "#ef4444"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      , E.style "padding" "12px"
      , E.style "border-radius" "8px"
      , E.style "border" "1px solid #e5e7eb"
      ]
      [ -- Preview
        renderPreview props
        
        -- Ratio display with grade color indicator
      , if props.showRatio
          then E.div_
            [ E.style "font-size" "24px"
            , E.style "font-weight" "600"
            , E.style "text-align" "center"
            , E.style "color" gradeColor
            ]
            [ E.text (ratioStr <> ":1") ]
          else E.span_ [] []
        
        -- Grade badges
      , if props.showGrades
          then renderGrades grade
          else E.span_ [] []
      ]

-- | Render color preview with sample text
renderPreview :: forall msg. ContrastProps msg -> E.Element msg
renderPreview props =
  E.div_
    [ E.style "background" (RGB.toLegacyCss props.background)
    , E.style "color" (RGB.toLegacyCss props.foreground)
    , E.style "padding" "16px"
    , E.style "border-radius" "4px"
    , E.style "text-align" "center"
    ]
    [ E.div_
        [ E.style "font-size" "18px"
        , E.style "font-weight" "600"
        , E.style "margin-bottom" "4px"
        ]
        [ E.text "Sample Text" ]
    , E.div_
        [ E.style "font-size" "14px" ]
        [ E.text "The quick brown fox jumps over the lazy dog." ]
    ]

-- | Render WCAG grade badges
renderGrades :: forall msg. WCAGGrade -> E.Element msg
renderGrades grade =
  E.div_
    [ E.style "display" "flex"
    , E.style "justify-content" "center"
    , E.style "gap" "8px"
    ]
    [ renderGradeBadge "AA" (grade >= AA)
    , renderGradeBadge "AA Large" (grade >= AALarge)
    , renderGradeBadge "AAA" (grade >= AAA)
    ]

-- | Render a single grade badge
renderGradeBadge :: forall msg. String -> Boolean -> E.Element msg
renderGradeBadge label passes =
  let
    bgColor = if passes then "#22c55e" else "#e5e7eb"
    textColor = if passes then "#fff" else "#9ca3af"
  in
    E.span_
      [ E.style "padding" "4px 8px"
      , E.style "border-radius" "4px"
      , E.style "font-size" "12px"
      , E.style "font-weight" "500"
      , E.style "background" bgColor
      , E.style "color" textColor
      ]
      [ E.text label ]

-- | Format ratio to 2 decimal places
formatRatio :: Number -> String
formatRatio n =
  let
    -- Multiply by 100, floor, divide by 100
    scaled = n * 100.0
    floored = Int.toNumber (Int.floor scaled)
    rounded = floored / 100.0
  in show rounded
