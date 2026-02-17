/-
  Lattice.Text - Text layer types and animators

  Max 500 lines.

  Source: ui/src/types/text.ts (264 lines)
-/

import Lattice.Primitives

namespace Lattice.Text

open Lattice.Primitives

/-! ## Enumerations -/

/-- Font style -/
inductive FontStyle where
  | normal
  | italic
  deriving Repr, BEq, DecidableEq

/-- Text alignment -/
inductive TextAlign where
  | left
  | center
  | right
  deriving Repr, BEq, DecidableEq

/-- Anchor point grouping -/
inductive AnchorPointGrouping where
  | character
  | word
  | line
  | all
  deriving Repr, BEq, DecidableEq

/-- Fill and stroke order -/
inductive FillAndStroke where
  | fillOverStroke
  | strokeOverFill
  deriving Repr, BEq, DecidableEq

/-- Inter-character blending mode -/
inductive InterCharacterBlending where
  | normal
  | multiply
  | screen
  | overlay
  deriving Repr, BEq, DecidableEq

/-- Text case transformation -/
inductive TextCase where
  | normal
  | uppercase
  | lowercase
  | smallCaps
  deriving Repr, BEq, DecidableEq

/-- Vertical alignment -/
inductive VerticalAlign where
  | normal
  | superscript
  | subscript
  deriving Repr, BEq, DecidableEq

/-- Range selector mode (percent or index) -/
inductive RangeSelectorMode where
  | percent
  | index
  deriving Repr, BEq, DecidableEq

/-- Selection basis -/
inductive SelectionBasedOn where
  | characters
  | charactersExcludingSpaces
  | words
  | lines
  deriving Repr, BEq, DecidableEq

/-- Selection shape -/
inductive SelectionShape where
  | square
  | rampUp
  | rampDown
  | triangle
  | round
  | smooth
  deriving Repr, BEq, DecidableEq

/-- Selector combination mode -/
inductive SelectorMode where
  | add
  | subtract
  | intersect
  | min
  | max
  | difference
  deriving Repr, BEq, DecidableEq

/-- Text animator preset types -/
inductive TextAnimatorPresetType where
  | typewriter
  | fadeInByCharacter
  | fadeInByWord
  | bounceIn
  | wave
  | scaleIn
  | rotateIn
  | slideInLeft
  | slideInRight
  | blurIn
  | randomFade
  deriving Repr, BEq, DecidableEq

/-! ## Per-character Blur -/

/-- Per-character blur values -/
structure CharacterBlur where
  x : Float
  y : Float
  x_ge_0 : x ≥ 0
  x_finite : x.isFinite
  y_ge_0 : y ≥ 0
  y_finite : y.isFinite
  deriving Repr

/-! ## Grouping Alignment -/

/-- Grouping alignment percentages -/
structure GroupingAlignment where
  x : Float  -- 0-100%
  y : Float  -- 0-100%
  x_ge_0 : x ≥ 0
  x_le_100 : x ≤ 100
  x_finite : x.isFinite
  y_ge_0 : y ≥ 0
  y_le_100 : y ≤ 100
  y_finite : y.isFinite
  deriving Repr

/-! ## Ease Settings -/

/-- Easing settings for text selectors -/
structure EaseSettings where
  high : Float  -- 0-100
  low : Float   -- 0-100
  high_ge_0 : high ≥ 0
  high_le_100 : high ≤ 100
  high_finite : high.isFinite
  low_ge_0 : low ≥ 0
  low_le_100 : low ≤ 100
  low_finite : low.isFinite
  deriving Repr

/-! ## Text Range Selector -/

/-- Text range selector -/
structure TextRangeSelector where
  mode : RangeSelectorMode
  startPropertyId : NonEmptyString       -- AnimatableProperty ID
  endPropertyId : NonEmptyString
  offsetPropertyId : NonEmptyString
  basedOn : SelectionBasedOn
  shape : SelectionShape
  selectorMode : Option SelectorMode
  amount : Float                         -- 0-100%
  smoothness : Float                     -- 0-100%
  randomizeOrder : Bool
  randomSeed : Nat
  ease : EaseSettings
  amount_ge_0 : amount ≥ 0
  amount_le_100 : amount ≤ 100
  amount_finite : amount.isFinite
  smoothness_ge_0 : smoothness ≥ 0
  smoothness_le_100 : smoothness ≤ 100
  smoothness_finite : smoothness.isFinite
  deriving Repr

/-! ## Text Wiggly Selector -/

/-- Wiggly selector for random text animation -/
structure TextWigglySelector where
  enabled : Bool
  mode : SelectorMode
  maxAmount : Float                      -- 0-100%
  minAmount : Float                      -- 0-100%
  wigglesPerSecond : Float
  correlation : Float                    -- 0-100%
  lockDimensions : Bool
  basedOn : SelectionBasedOn
  randomSeed : Nat
  maxAmount_ge_0 : maxAmount ≥ 0
  maxAmount_le_100 : maxAmount ≤ 100
  maxAmount_finite : maxAmount.isFinite
  minAmount_ge_0 : minAmount ≥ 0
  minAmount_le_100 : minAmount ≤ 100
  minAmount_finite : minAmount.isFinite
  minAmount_le_maxAmount : minAmount ≤ maxAmount
  wigglesPerSecond_ge_0 : wigglesPerSecond ≥ 0
  wigglesPerSecond_finite : wigglesPerSecond.isFinite
  correlation_ge_0 : correlation ≥ 0
  correlation_le_100 : correlation ≤ 100
  correlation_finite : correlation.isFinite
  deriving Repr

/-! ## Text Expression Selector -/

/-- Expression selector for programmatic text animation -/
structure TextExpressionSelector where
  enabled : Bool
  mode : SelectorMode
  amountExpression : String              -- Expression string
  basedOn : SelectionBasedOn
  deriving Repr

/-! ## Text Animator Properties -/

/-- Text animator property IDs (all are AnimatableProperty IDs) -/
structure TextAnimatorProperties where
  -- Transform properties
  positionPropertyId : Option NonEmptyString
  anchorPointPropertyId : Option NonEmptyString
  scalePropertyId : Option NonEmptyString
  rotationPropertyId : Option NonEmptyString
  skewPropertyId : Option NonEmptyString
  skewAxisPropertyId : Option NonEmptyString
  -- Style properties
  opacityPropertyId : Option NonEmptyString
  fillColorPropertyId : Option NonEmptyString
  fillBrightnessPropertyId : Option NonEmptyString
  fillSaturationPropertyId : Option NonEmptyString
  fillHuePropertyId : Option NonEmptyString
  strokeColorPropertyId : Option NonEmptyString
  strokeWidthPropertyId : Option NonEmptyString
  -- Character properties
  trackingPropertyId : Option NonEmptyString
  lineAnchorPropertyId : Option NonEmptyString
  lineSpacingPropertyId : Option NonEmptyString
  characterOffsetPropertyId : Option NonEmptyString
  blurPropertyId : Option NonEmptyString
  deriving Repr

/-! ## Text Animator -/

/-- Text animator (per-character animation) -/
structure TextAnimator where
  id : NonEmptyString
  name : NonEmptyString
  enabled : Bool
  rangeSelector : TextRangeSelector
  wigglySelector : Option TextWigglySelector
  expressionSelector : Option TextExpressionSelector
  properties : TextAnimatorProperties
  deriving Repr

/-! ## Text Data -/

/-- Complete text data -/
structure TextData where
  -- Source text
  text : String
  fontFamily : NonEmptyString
  fontSize : Float
  fontWeight : NonEmptyString
  fontStyle : FontStyle
  fill : HexColor
  stroke : String                        -- Empty string = no stroke
  strokeWidth : Float
  -- Character properties
  tracking : Float
  lineSpacing : Float
  lineAnchor : Float                     -- 0-100%
  characterOffset : Int                  -- Integer shift
  characterValue : Int                   -- Unicode shift
  blur : CharacterBlur
  -- Paragraph (legacy aliases)
  letterSpacing : Float                  -- Alias for tracking
  lineHeight : Float                     -- Alias for lineSpacing
  textAlign : TextAlign
  -- Path options
  pathLayerId : String                   -- Empty = no path
  pathReversed : Bool
  pathPerpendicularToPath : Bool
  pathForceAlignment : Bool
  pathFirstMargin : Float                -- Pixels from path start
  pathLastMargin : Float                 -- Pixels from path end
  pathOffset : Float                     -- 0-100%
  pathAlign : TextAlign
  -- More options (advanced)
  anchorPointGrouping : Option AnchorPointGrouping
  groupingAlignment : Option GroupingAlignment
  fillAndStroke : Option FillAndStroke
  interCharacterBlending : Option InterCharacterBlending
  -- 3D text
  perCharacter3D : Bool
  -- Advanced character properties
  baselineShift : Option Float
  textCase : Option TextCase
  verticalAlign : Option VerticalAlign
  -- OpenType features
  kerning : Bool
  ligatures : Bool
  discretionaryLigatures : Bool
  smallCapsFeature : Bool
  stylisticSet : Nat                     -- 0-20 (0 = none)
  -- Advanced paragraph properties
  firstLineIndent : Option Float
  spaceBefore : Option Float
  spaceAfter : Option Float
  -- Text animators
  animators : Array TextAnimator
  -- Proofs
  fontSize_positive : fontSize > 0
  fontSize_finite : fontSize.isFinite
  strokeWidth_ge_0 : strokeWidth ≥ 0
  strokeWidth_finite : strokeWidth.isFinite
  tracking_finite : tracking.isFinite
  lineSpacing_positive : lineSpacing > 0
  lineSpacing_finite : lineSpacing.isFinite
  lineAnchor_ge_0 : lineAnchor ≥ 0
  lineAnchor_le_100 : lineAnchor ≤ 100
  lineAnchor_finite : lineAnchor.isFinite
  letterSpacing_finite : letterSpacing.isFinite
  lineHeight_positive : lineHeight > 0
  lineHeight_finite : lineHeight.isFinite
  pathFirstMargin_ge_0 : pathFirstMargin ≥ 0
  pathFirstMargin_finite : pathFirstMargin.isFinite
  pathLastMargin_ge_0 : pathLastMargin ≥ 0
  pathLastMargin_finite : pathLastMargin.isFinite
  pathOffset_ge_0 : pathOffset ≥ 0
  pathOffset_le_100 : pathOffset ≤ 100
  pathOffset_finite : pathOffset.isFinite
  stylisticSet_le_20 : stylisticSet ≤ 20
  deriving Repr

/-! ## Default Values -/

/-- Default character blur (no blur) -/
def defaultCharacterBlur : CharacterBlur :=
  { x := 0, y := 0,
    x_ge_0 := by decide, x_finite := by decide,
    y_ge_0 := by decide, y_finite := by decide }

/-- Default grouping alignment (centered) -/
def defaultGroupingAlignment : GroupingAlignment :=
  { x := 50, y := 50,
    x_ge_0 := by decide, x_le_100 := by decide, x_finite := by decide,
    y_ge_0 := by decide, y_le_100 := by decide, y_finite := by decide }

end Lattice.Text
