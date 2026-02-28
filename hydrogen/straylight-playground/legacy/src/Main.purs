-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // showcase
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Showcase.Main where

import Prelude

import Data.Array (foldl, index)
import Data.Int (toNumber, floor) as Int
import Data.Maybe (Maybe(..), maybe, fromMaybe)
import Data.String.CodeUnits (toCharArray, fromCharArray)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Exception (throw)
import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Web.DOM.NonElementParentNode (getElementById)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toNonElementParentNode)
import Web.HTML.HTMLElement (fromElement)
import Web.HTML.Window (document)

import Hydrogen.Element.Compound.Button as Button
import Hydrogen.Icon.Icons as Icon
import Hydrogen.Icon.Icon as I

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

data SheetDirection = SheetRight | SheetLeft | SheetTop | SheetBottom

derive instance eqSheetDirection :: Eq SheetDirection

data Theme 
  = ThemeGlass      -- Current gradient glassmorphism
  | ThemeMonochrome -- Minimal black/white/gray (Linear, Raycast)
  | ThemeAccent     -- Neutral + single bold accent
  | ThemeSoft       -- Muted, paper-like (Notion)
  | ThemeBrutalist  -- High contrast, sharp edges

derive instance eqTheme :: Eq Theme

-- Gradient type
data GradientType = LinearGradient | RadialGradient | ConicGradient

derive instance eqGradientType :: Eq GradientType

-- Gradient color stop
type GradientStop =
  { color :: String    -- Hex color
  , position :: Int    -- 0-100 percent
  }

-- Text case transformation options
data TextCase
  = CaseNone        -- As typed
  | CaseLower       -- lowercase
  | CaseUpper       -- UPPERCASE
  | CaseTitle       -- Title Case
  | CaseSentence    -- Sentence case

derive instance eqTextCase :: Eq TextCase

-- Animation easing presets
data EasingType
  = EaseLinear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseBounce
  | EaseElastic
  | EaseSpring

derive instance eqEasingType :: Eq EasingType

-- Button playground state
type ButtonPlayground =
  { variant :: Button.ButtonVariant
  , size :: Button.ButtonSize
  , disabled :: Boolean
  , loading :: Boolean
  , label :: String
  , radius :: Int           -- 0-24 px
  , animationSpeed :: Int   -- 50-500 ms
  , animationEasing :: EasingType  -- Easing curve
  , bgColor :: String       -- Preview background color (hex)
  , buttonColor :: String   -- Button background color (hex)
  , textColor :: String     -- Button text color (hex)
  , maxWidth :: Int         -- 0 = auto, otherwise px (for 2-line wrap)
  -- Shadow (full control)
  , shadowEnabled :: Boolean
  , shadowColor :: String   -- Hex color
  , shadowOpacity :: Int    -- 0-100 percent
  , shadowBlur :: Int       -- 0-50 px
  , shadowSpread :: Int     -- -10 to 20 px
  , shadowOffsetX :: Int    -- -20 to 20 px
  , shadowOffsetY :: Int    -- -20 to 20 px
  , shadowInset :: Boolean  -- Inner shadow
  -- Stroke/Border (toggle-based)
  , strokeEnabled :: Boolean
  , strokeWidth :: Number   -- 0.0-4.0 px (float)
  , strokeColor :: String   -- Border color (hex)
  -- Typography
  , fontFamily :: String    -- Font family name
  , fontWeight :: Int       -- 400-700
  , fontSize :: Int         -- 12-20 px
  , letterSpacing :: Int    -- -2 to 4 (0.01em units)
  , textCase :: TextCase    -- Text transformation
  , italic :: Boolean
  , underline :: Boolean
  , strikethrough :: Boolean
  -- Glow effect
  , glowEnabled :: Boolean
  , glowColor :: String     -- Hex color
  , glowBlur :: Int         -- 0-50 px
  , glowSpread :: Int       -- 0-20 px
  , glowOpacity :: Int      -- 0-100 percent
  -- Gradient
  , gradientEnabled :: Boolean
  , gradientType :: GradientType
  , gradientAngle :: Int    -- 0-360 degrees (for linear)
  , gradientStops :: Array GradientStop
  }

type State =
  { currentSection :: Section
  , numberInputValue :: Int
  , dialogOpen :: Boolean
  , sheetOpen :: Boolean
  , sheetDirection :: SheetDirection
  , theme :: Theme
  , buttonPlayground :: ButtonPlayground
  }

data Section
  = Overview
  | ButtonSection
  | IconSection
  | Inputs
  | Feedback
  | Layout
  | DataDisplay
  | Overlay

derive instance eqSection :: Eq Section

data Action
  = SetSection Section
  | IncrementNumber
  | DecrementNumber
  | OpenDialog
  | CloseDialog
  | OpenSheet SheetDirection
  | CloseSheet
  | SetTheme Theme
  -- Button playground actions
  | SetButtonVariant Button.ButtonVariant
  | SetButtonSize Button.ButtonSize
  | ToggleButtonDisabled
  | ToggleButtonLoading
  | SetButtonLabel String
  | SetButtonRadius Int
  | SetButtonAnimationSpeed Int
  | SetButtonAnimationEasing EasingType
  | SetButtonBgColor String
  | SetButtonColor String
  | SetTextColor String
  | SetButtonMaxWidth Int
  -- Shadow actions (full control)
  | ToggleButtonShadow
  | SetButtonShadowColor String
  | SetButtonShadowOpacity Int
  | SetButtonShadowBlur Int
  | SetButtonShadowSpread Int
  | SetButtonShadowOffsetX Int
  | SetButtonShadowOffsetY Int
  | ToggleButtonShadowInset
  -- Stroke actions (toggle-based)
  | ToggleButtonStroke
  | SetButtonStrokeWidth Number
  | SetButtonStrokeColor String
  -- Typography actions
  | SetButtonFontFamily String
  | SetButtonFontWeight Int
  | SetButtonFontSize Int
  | SetButtonLetterSpacing Int
  | SetButtonTextCase TextCase
  | ToggleButtonItalic
  | ToggleButtonUnderline
  | ToggleButtonStrikethrough
  -- Glow actions
  | ToggleButtonGlow
  | SetButtonGlowColor String
  | SetButtonGlowBlur Int
  | SetButtonGlowSpread Int
  | SetButtonGlowOpacity Int
  -- Gradient actions
  | ToggleButtonGradient
  | SetButtonGradientType GradientType
  | SetButtonGradientAngle Int
  | SetGradientStopColor Int String  -- index, color
  | SetGradientStopPosition Int Int  -- index, position
  | AddGradientStop
  | RemoveGradientStop Int           -- index

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall q i o m. MonadAff m => H.Component q i o m
component =
  H.mkComponent
    { initialState: \_ -> 
        { currentSection: Overview
        , numberInputValue: 42
        , dialogOpen: false
        , sheetOpen: false
        , sheetDirection: SheetRight
        , theme: ThemeMonochrome  -- Start with minimal
        , buttonPlayground:
            { variant: Button.Default
            , size: Button.Md
            , disabled: false
            , loading: false
            , label: "Click me"
            , radius: 8
            , animationSpeed: 150
            , animationEasing: EaseOut
            , bgColor: "#1a1a1a"
            , buttonColor: "#ffffff"
            , textColor: "#000000"
            , maxWidth: 0
            -- Shadow defaults (full control)
            , shadowEnabled: false
            , shadowColor: "#000000"
            , shadowOpacity: 25
            , shadowBlur: 10
            , shadowSpread: 0
            , shadowOffsetX: 0
            , shadowOffsetY: 4
            , shadowInset: false
            -- Stroke defaults (toggle-based)
            , strokeEnabled: false
            , strokeWidth: 1.0
            , strokeColor: "#ffffff"
            -- Typography
            , fontFamily: "Inter"
            , fontWeight: 500
            , fontSize: 14
            , letterSpacing: 0
            , textCase: CaseNone
            , italic: false
            , underline: false
            , strikethrough: false
            -- Glow defaults
            , glowEnabled: false
            , glowColor: "#8b5cf6"
            , glowBlur: 20
            , glowSpread: 0
            , glowOpacity: 50
            -- Gradient defaults
            , gradientEnabled: false
            , gradientType: LinearGradient
            , gradientAngle: 135
            , gradientStops: 
                [ { color: "#8b5cf6", position: 0 }
                , { color: "#3b82f6", position: 100 }
                ]
            }
        }
    , render
    , eval: H.mkEval $ H.defaultEval { handleAction = handleAction }
    }

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  SetSection section ->
    H.modify_ _ { currentSection = section }
  IncrementNumber ->
    H.modify_ \s -> s { numberInputValue = s.numberInputValue + 1 }
  DecrementNumber ->
    H.modify_ \s -> s { numberInputValue = s.numberInputValue - 1 }
  OpenDialog ->
    H.modify_ _ { dialogOpen = true }
  CloseDialog ->
    H.modify_ _ { dialogOpen = false }
  OpenSheet dir ->
    H.modify_ _ { sheetOpen = true, sheetDirection = dir }
  CloseSheet ->
    H.modify_ _ { sheetOpen = false }
  SetTheme t ->
    H.modify_ _ { theme = t }
  -- Button playground actions
  SetButtonVariant v ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { variant = v } }
  SetButtonSize sz ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { size = sz } }
  ToggleButtonDisabled ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { disabled = not s.buttonPlayground.disabled } }
  ToggleButtonLoading ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { loading = not s.buttonPlayground.loading } }
  SetButtonLabel lbl ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { label = lbl } }
  SetButtonRadius r ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { radius = r } }
  SetButtonAnimationSpeed spd ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { animationSpeed = spd } }
  SetButtonAnimationEasing e ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { animationEasing = e } }
  SetButtonBgColor c ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { bgColor = c } }
  SetButtonColor c ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { buttonColor = c } }
  SetTextColor c ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { textColor = c } }
  SetButtonMaxWidth w ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { maxWidth = w } }
  -- Shadow actions (full control)
  ToggleButtonShadow ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowEnabled = not s.buttonPlayground.shadowEnabled } }
  SetButtonShadowColor c ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowColor = c } }
  SetButtonShadowOpacity o ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowOpacity = o } }
  SetButtonShadowBlur b ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowBlur = b } }
  SetButtonShadowSpread sp ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowSpread = sp } }
  SetButtonShadowOffsetX x ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowOffsetX = x } }
  SetButtonShadowOffsetY y ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowOffsetY = y } }
  ToggleButtonShadowInset ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { shadowInset = not s.buttonPlayground.shadowInset } }
  -- Stroke actions (toggle-based)
  ToggleButtonStroke ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { strokeEnabled = not s.buttonPlayground.strokeEnabled } }
  SetButtonStrokeWidth w ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { strokeWidth = w } }
  SetButtonStrokeColor c ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { strokeColor = c } }
  -- Typography actions
  SetButtonFontFamily f ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { fontFamily = f } }
  SetButtonFontWeight w ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { fontWeight = w } }
  SetButtonFontSize sz ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { fontSize = sz } }
  SetButtonLetterSpacing sp ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { letterSpacing = sp } }
  SetButtonTextCase tc ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { textCase = tc } }
  ToggleButtonItalic ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { italic = not s.buttonPlayground.italic } }
  ToggleButtonUnderline ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { underline = not s.buttonPlayground.underline } }
  ToggleButtonStrikethrough ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { strikethrough = not s.buttonPlayground.strikethrough } }
  -- Glow actions
  ToggleButtonGlow ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { glowEnabled = not s.buttonPlayground.glowEnabled } }
  SetButtonGlowColor c ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { glowColor = c } }
  SetButtonGlowBlur b ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { glowBlur = b } }
  SetButtonGlowSpread sp ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { glowSpread = sp } }
  SetButtonGlowOpacity o ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { glowOpacity = o } }
  -- Gradient actions
  ToggleButtonGradient ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { gradientEnabled = not s.buttonPlayground.gradientEnabled } }
  SetButtonGradientType t ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { gradientType = t } }
  SetButtonGradientAngle a ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { gradientAngle = a } }
  SetGradientStopColor idx c ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { gradientStops = updateStopColor idx c s.buttonPlayground.gradientStops } }
  SetGradientStopPosition idx p ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { gradientStops = updateStopPosition idx p s.buttonPlayground.gradientStops } }
  AddGradientStop ->
    H.modify_ \s -> 
      let stops = s.buttonPlayground.gradientStops
          newStop = { color: "#ec4899", position: 50 }
      in s { buttonPlayground = s.buttonPlayground { gradientStops = stops <> [newStop] } }
  RemoveGradientStop idx ->
    H.modify_ \s -> s { buttonPlayground = s.buttonPlayground { gradientStops = removeAtIndex idx s.buttonPlayground.gradientStops } }

-- Helper to update gradient stop color at index
updateStopColor :: Int -> String -> Array GradientStop -> Array GradientStop
updateStopColor idx newColor stops = 
  mapWithIndex (\i stop -> if i == idx then stop { color = newColor } else stop) stops

-- Helper to update gradient stop position at index
updateStopPosition :: Int -> Int -> Array GradientStop -> Array GradientStop
updateStopPosition idx newPos stops = 
  mapWithIndex (\i stop -> if i == idx then stop { position = newPos } else stop) stops

-- Helper to remove item at index
removeAtIndex :: forall a. Int -> Array a -> Array a
removeAtIndex idx arr = 
  mapWithIndex (\i x -> if i == idx then [] else [x]) arr # join

-- Map with index helper
mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
mapWithIndex f arr = 
  let indexed = zipWithIndex arr
  in map (\{index: i, value: v} -> f i v) indexed

-- Zip array with indices
zipWithIndex :: forall a. Array a -> Array { index :: Int, value :: a }
zipWithIndex arr = zipWith (\i v -> { index: i, value: v }) (range 0 (length arr - 1)) arr
  where
    length :: forall x. Array x -> Int
    length = foldl (\acc _ -> acc + 1) 0

-- Range helper
range :: Int -> Int -> Array Int
range start end = if start > end then [] else [start] <> range (start + 1) end

-- Join helper for arrays
join :: forall a. Array (Array a) -> Array a
join = foldl (<>) []

-- Zip helper
zipWith :: forall a b c. (a -> b -> c) -> Array a -> Array b -> Array c
zipWith f as bs = case { a: uncons as, b: uncons bs } of
  { a: Just { head: a, tail: as' }, b: Just { head: b, tail: bs' } } -> 
    [f a b] <> zipWith f as' bs'
  _ -> []

-- Array uncons helper
uncons :: forall a. Array a -> Maybe { head :: a, tail :: Array a }
uncons arr = case index arr 0 of
  Just h -> Just { head: h, tail: drop 1 arr }
  Nothing -> Nothing

-- Drop helper
drop :: forall a. Int -> Array a -> Array a
drop n arr = if n <= 0 then arr else case uncons arr of
  Just { tail } -> drop (n - 1) tail
  Nothing -> []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // render
-- ═══════════════════════════════════════════════════════════════════════════════

themeClass :: Theme -> String
themeClass = case _ of
  ThemeGlass -> "theme-glass"
  ThemeMonochrome -> "theme-mono"
  ThemeAccent -> "theme-accent"
  ThemeSoft -> "theme-soft"
  ThemeBrutalist -> "theme-brutal"

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName $ "min-h-screen flex flex-col " <> themeClass state.theme) ]
    [ renderNav state.theme
    , HH.div
        [ HP.class_ (H.ClassName "flex flex-1") ]
        [ renderSidebar state.currentSection
        , HH.main
            [ HP.class_ (H.ClassName "flex-1 p-8 pb-16 overflow-auto") ]
            [ renderContent state ]
        ]
    , renderFooter
    , renderOverlays state
    ]

renderNav :: forall m. Theme -> H.ComponentHTML Action () m
renderNav currentTheme =
  HH.nav
    [ HP.class_ (H.ClassName "nav sticky top-0 z-50 px-6 py-4 flex items-center justify-between") ]
    [ HH.div
        [ HP.class_ (H.ClassName "flex items-center gap-3") ]
        [ HH.span
            [ HP.class_ (H.ClassName "text-xl font-bold brand-text") ]
            [ HH.text "Hydrogen" ]
        , HH.span
            [ HP.class_ (H.ClassName "version-badge") ]
            [ HH.text "v0.1.0" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "flex items-center gap-2") ]
        [ -- Theme switcher
          themeButton ThemeMonochrome "Mono" currentTheme
        , themeButton ThemeAccent "Accent" currentTheme
        , themeButton ThemeSoft "Soft" currentTheme
        , themeButton ThemeBrutalist "Brutal" currentTheme
        , themeButton ThemeGlass "Glass" currentTheme
        , HH.span [ HP.class_ (H.ClassName "mx-2 text-muted") ] [ HH.text "|" ]
        , HH.a
            [ HP.class_ (H.ClassName "text-sm link")
            , HP.href "https://github.com/straylight-software/hydrogen"
            ]
            [ HH.text "GitHub" ]
        ]
    ]

themeButton :: forall m. Theme -> String -> Theme -> H.ComponentHTML Action () m
themeButton theme label currentTheme =
  HH.button
    [ HP.class_ (H.ClassName $ "theme-btn" <> if theme == currentTheme then " active" else "")
    , HE.onClick \_ -> SetTheme theme
    ]
    [ HH.text label ]

renderSidebar :: forall m. Section -> H.ComponentHTML Action () m
renderSidebar current =
  HH.aside
    [ HP.class_ (H.ClassName "glass-sidebar w-64 min-h-[calc(100vh-73px)] hidden lg:block") ]
    [ HH.div
        [ HP.class_ (H.ClassName "section-label") ]
        [ HH.text "Getting Started" ]
    , sidebarItem Overview "Overview" current
    , HH.div
        [ HP.class_ (H.ClassName "section-label") ]
        [ HH.text "Playground" ]
    , sidebarItem ButtonSection "Button" current
    , sidebarItem IconSection "Icons" current
    , HH.div
        [ HP.class_ (H.ClassName "section-label") ]
        [ HH.text "Components" ]
    , sidebarItem Inputs "Inputs" current
    , sidebarItem Feedback "Feedback" current
    , sidebarItem Layout "Layout" current
    , sidebarItem DataDisplay "Data Display" current
    , sidebarItem Overlay "Overlay" current
    ]

sidebarItem :: forall m. Section -> String -> Section -> H.ComponentHTML Action () m
sidebarItem section label current =
  HH.button
    [ HP.class_ (H.ClassName $ "sidebar-item" <> if section == current then " active" else "")
    , HE.onClick \_ -> SetSection section
    ]
    [ HH.text label ]

renderContent :: forall m. State -> H.ComponentHTML Action () m
renderContent state = case state.currentSection of
  Overview -> renderOverview
  ButtonSection -> renderButtonPlayground state
  IconSection -> renderIconLibrary
  Inputs -> renderInputs state
  Feedback -> renderFeedback
  Layout -> renderLayout
  DataDisplay -> renderDataDisplay
  Overlay -> renderOverlaySection

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // overview
-- ═══════════════════════════════════════════════════════════════════════════════

renderOverview :: forall m. H.ComponentHTML Action () m
renderOverview =
  HH.div
    [ HP.class_ (H.ClassName "max-w-4xl mx-auto animate-fade-in") ]
    [ -- Hero
      HH.div
        [ HP.class_ (H.ClassName "mb-12") ]
        [ HH.h1
            [ HP.class_ (H.ClassName "text-4xl font-bold mb-4") ]
            [ HH.span [ HP.class_ (H.ClassName "gradient-text") ] [ HH.text "Hydrogen" ]
            , HH.text " Components"
            ]
        , HH.p
            [ HP.class_ (H.ClassName "text-lg text-white/60 max-w-2xl") ]
            [ HH.text "A PureScript/Halogen web framework for building correct web applications. Type-safe, lawful, beautiful." ]
        ]
    -- Stats
    , HH.div
        [ HP.class_ (H.ClassName "stats-grid mb-12") ]
        [ statCard "146" "Modules"
        , statCard "51" "Components"
        , statCard "31" "Categories"
        , statCard "0" "Runtime Errors"
        ]
    -- Quick preview cards
    , HH.h2
        [ HP.class_ (H.ClassName "text-2xl font-semibold mb-6") ]
        [ HH.text "Quick Preview" ]
    , HH.div
        [ HP.class_ (H.ClassName "grid grid-cols-1 md:grid-cols-2 gap-6") ]
        [ componentCard "Button" "Primary action component with variants"
            (HH.div
              [ HP.class_ (H.ClassName "flex flex-wrap gap-4") ]
              [ Button.button [ Button.shadow true ] [ HH.text "Primary" ]
              , Button.button [ Button.variant Button.Secondary ] [ HH.text "Secondary" ]
              , Button.button [ Button.variant Button.Outline ] [ HH.text "Outline" ]
              ])
            "Button.button [ shadow true ] [ HH.text \"Click\" ]"
        , componentCard "Input" "Text input with glass styling"
            (HH.input
              [ HP.class_ (H.ClassName "glass-input w-full")
              , HP.placeholder "Type something..."
              ])
            "Input.input [ Input.placeholder \"...\" ]"
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // button playground
-- ═══════════════════════════════════════════════════════════════════════════════

renderButtonPlayground :: forall m. State -> H.ComponentHTML Action () m
renderButtonPlayground state =
  let
    bp = state.buttonPlayground
    codePreview = generateButtonCode bp
    -- Calculate contrast between text and button background
    contrastRatio = getContrastRatio bp.textColor bp.buttonColor
    meetsAA = contrastRatio >= 4.5
    meetsAAA = contrastRatio >= 7.0
  in
    HH.div
      [ HP.class_ (H.ClassName "playground-container animate-fade-in") ]
      [ -- Title
        HH.h1
          [ HP.class_ (H.ClassName "text-2xl font-bold mb-4") ]
          [ HH.text "Button Playground" ]
      -- Main preview panel: Buttons LEFT, Accessibility RIGHT
      , HH.div
          [ HP.class_ (H.ClassName "preview-split-panel") ]
          [ -- Left: Button preview area
            HH.div
              [ HP.class_ (H.ClassName "preview-left")
              , HP.attr (HH.AttrName "style") ("background-color: " <> bp.bgColor <> ";")
              ]
              [ -- Button with custom colors applied via inline styles
                HH.div
                  [ HP.class_ (H.ClassName "custom-button-wrapper")
                  , HP.attr (HH.AttrName "style") (buildButtonStyles bp)
                  ]
                  [ Button.button
                      [ Button.variant bp.variant
                      , Button.size bp.size
                      , Button.shadow bp.shadowEnabled
                      , Button.disabled bp.disabled
                      , Button.loading bp.loading
                      , Button.className "playground-preview-btn"
                      ]
                      [ if bp.size == Button.Icon then starIcon else HH.text bp.label ]
                  ]
              ]
          -- Right: Accessibility panel
          , HH.div
              [ HP.class_ (H.ClassName "preview-right") ]
              [ HH.div
                  [ HP.class_ (H.ClassName "a11y-panel") ]
                  [ -- Contrast ratio - big and prominent
                    HH.div
                      [ HP.class_ (H.ClassName "a11y-contrast-main") ]
                      [ HH.div
                          [ HP.class_ (H.ClassName "a11y-contrast-label") ]
                          [ HH.text "Contrast Ratio" ]
                      , HH.div
                          [ HP.class_ (H.ClassName $ "a11y-contrast-value " <> contrastClass contrastRatio) ]
                          [ HH.text (formatContrastRatio contrastRatio) ]
                      ]
                  -- WCAG badges
                  , HH.div
                      [ HP.class_ (H.ClassName "a11y-wcag-row") ]
                      [ HH.div
                          [ HP.class_ (H.ClassName $ "a11y-wcag-badge " <> if meetsAA then "pass" else "fail") ]
                          [ HH.div [ HP.class_ (H.ClassName "wcag-level") ] [ HH.text "AA" ]
                          , HH.div [ HP.class_ (H.ClassName "wcag-status") ] 
                              [ HH.text $ if meetsAA then "PASS" else "FAIL" ]
                          , HH.div [ HP.class_ (H.ClassName "wcag-req") ] [ HH.text "4.5:1 required" ]
                          ]
                      , HH.div
                          [ HP.class_ (H.ClassName $ "a11y-wcag-badge " <> if meetsAAA then "pass" else "fail") ]
                          [ HH.div [ HP.class_ (H.ClassName "wcag-level") ] [ HH.text "AAA" ]
                          , HH.div [ HP.class_ (H.ClassName "wcag-status") ] 
                              [ HH.text $ if meetsAAA then "PASS" else "FAIL" ]
                          , HH.div [ HP.class_ (H.ClassName "wcag-req") ] [ HH.text "7:1 required" ]
                          ]
                      ]
                  -- Color details
                  , HH.div
                      [ HP.class_ (H.ClassName "a11y-colors") ]
                      [ colorDetail "Text Color" bp.textColor
                      , colorDetail "Button Color" bp.buttonColor
                      , colorDetail "Background" bp.bgColor
                      ]
                  ]
              ]
          ]
      -- Code preview
      , HH.div
          [ HP.class_ (H.ClassName "code-preview") ]
          [ HH.pre_ [ HH.text codePreview ] ]
      -- Two control panels - wider layout
      , HH.div
          [ HP.class_ (H.ClassName "playground-panels-wide") ]
          [ -- Left panel: Button basics + Typography
            HH.div
              [ HP.class_ (H.ClassName "playground-panel-wide") ]
              [ HH.div
                  [ HP.class_ (H.ClassName "panel-header") ]
                  [ HH.text "Button" ]
              , HH.div
                  [ HP.class_ (H.ClassName "panel-content-grid") ]
                  [ -- Row 1: Variant + Size
                    HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Variant" (renderVariantSelector bp.variant)
                      , playgroundControl "Size" (renderSizeSelector bp.size)
                      ]
                  -- Row 2: Label + States
                  , HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Label"
                          (HH.input
                            [ HP.class_ (H.ClassName "glass-input w-full")
                            , HP.value bp.label
                            , HE.onValueInput SetButtonLabel
                            ])
                      , playgroundControl "States"
                          (HH.div
                            [ HP.class_ (H.ClassName "flex flex-wrap gap-2") ]
                            [ toggleControl "Disabled" bp.disabled ToggleButtonDisabled
                            , toggleControl "Loading" bp.loading ToggleButtonLoading
                            ])
                      ]
                  -- Row 3: Colors
                  , HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Button Color" (renderColorPicker bp.buttonColor SetButtonColor)
                      , playgroundControl "Text Color" (renderColorPicker bp.textColor SetTextColor)
                      ]
                  -- Row 4: Background + Radius
                  , HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Preview BG" (renderColorPicker bp.bgColor SetButtonBgColor)
                      , playgroundControl "Border Radius" (renderSlider bp.radius 0 24 "px" SetButtonRadius)
                      ]
                  -- Row 5: Max Width + Animation
                  , HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Max Width" (renderSlider bp.maxWidth 0 300 "px" SetButtonMaxWidth)
                      , playgroundControl "Duration" (renderSlider bp.animationSpeed 50 500 "ms" SetButtonAnimationSpeed)
                      ]
                  -- Row 6: Easing
                  , HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Easing" (renderEasingSelector bp.animationEasing)
                      , HH.text ""
                      ]
                  ]
              , HH.div
                  [ HP.class_ (H.ClassName "panel-header panel-header-sub") ]
                  [ HH.text "Typography" ]
              , HH.div
                  [ HP.class_ (H.ClassName "panel-content-grid") ]
                  [ -- Row 1: Font Family + Weight
                    HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Font Family" (renderFontFamilySelector bp.fontFamily)
                      , playgroundControl "Font Weight" (renderFontWeightSelector bp.fontWeight)
                      ]
                  -- Row 2: Font Size + Letter Spacing
                  , HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Font Size" (renderSlider bp.fontSize 12 20 "px" SetButtonFontSize)
                      , playgroundControl "Letter Spacing" (renderSlider bp.letterSpacing (-2) 4 "em" SetButtonLetterSpacing)
                      ]
                  -- Row 3: Text Case + Styles
                  , HH.div
                      [ HP.class_ (H.ClassName "control-row") ]
                      [ playgroundControl "Text Case" (renderTextCaseSelector bp.textCase)
                      , playgroundControl "Text Style"
                          (HH.div
                            [ HP.class_ (H.ClassName "flex flex-wrap gap-2") ]
                            [ toggleControl "Italic" bp.italic ToggleButtonItalic
                            , toggleControl "Underline" bp.underline ToggleButtonUnderline
                            , toggleControl "Strike" bp.strikethrough ToggleButtonStrikethrough
                            ])
                      ]
                  ]
              ]
          -- Right panel: Effects (Stroke + Glow + Gradient)
          , HH.div
              [ HP.class_ (H.ClassName "playground-panel-wide") ]
              [ HH.div
                  [ HP.class_ (H.ClassName "panel-header") ]
                  [ HH.text "Effects" ]
              , HH.div
                  [ HP.class_ (H.ClassName "panel-content") ]
                  [ -- Shadow Effect (full control)
                    HH.div
                      [ HP.class_ (H.ClassName "effect-section") ]
                      [ HH.div
                          [ HP.class_ (H.ClassName "effect-header") ]
                          [ toggleControl "Shadow" bp.shadowEnabled ToggleButtonShadow ]
                      , if bp.shadowEnabled
                          then HH.div
                            [ HP.class_ (H.ClassName "effect-controls-grid") ]
                            [ HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Color" (renderColorPicker bp.shadowColor SetButtonShadowColor)
                                , playgroundControl "Opacity" (renderSlider bp.shadowOpacity 0 100 "%" SetButtonShadowOpacity)
                                ]
                            , HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Blur" (renderSlider bp.shadowBlur 0 50 "px" SetButtonShadowBlur)
                                , playgroundControl "Spread" (renderSlider bp.shadowSpread (-10) 20 "px" SetButtonShadowSpread)
                                ]
                            , HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Offset X" (renderSlider bp.shadowOffsetX (-20) 20 "px" SetButtonShadowOffsetX)
                                , playgroundControl "Offset Y" (renderSlider bp.shadowOffsetY (-20) 20 "px" SetButtonShadowOffsetY)
                                ]
                            , HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Inset"
                                    (HH.div
                                      [ HP.class_ (H.ClassName "flex flex-wrap gap-2") ]
                                      [ toggleControl "Inner Shadow" bp.shadowInset ToggleButtonShadowInset ])
                                , HH.text ""
                                ]
                            ]
                          else HH.text ""
                      ]
                  -- Stroke Effect (toggle-based)
                  , HH.div [ HP.class_ (H.ClassName "panel-divider") ] []
                  , HH.div
                      [ HP.class_ (H.ClassName "effect-section") ]
                      [ HH.div
                          [ HP.class_ (H.ClassName "effect-header") ]
                          [ toggleControl "Stroke" bp.strokeEnabled ToggleButtonStroke ]
                      , if bp.strokeEnabled
                          then HH.div
                            [ HP.class_ (H.ClassName "effect-controls-grid") ]
                            [ HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Width" (renderNumberSlider bp.strokeWidth 0.0 4.0 "px" SetButtonStrokeWidth)
                                , playgroundControl "Color" (renderColorPicker bp.strokeColor SetButtonStrokeColor)
                                ]
                            ]
                          else HH.text ""
                      ]
                  -- Glow Effect
                  , HH.div [ HP.class_ (H.ClassName "panel-divider") ] []
                  , HH.div
                      [ HP.class_ (H.ClassName "effect-section") ]
                      [ HH.div
                          [ HP.class_ (H.ClassName "effect-header") ]
                          [ toggleControl "Glow" bp.glowEnabled ToggleButtonGlow ]
                      , if bp.glowEnabled
                          then HH.div
                            [ HP.class_ (H.ClassName "effect-controls-grid") ]
                            [ HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Color" (renderColorPicker bp.glowColor SetButtonGlowColor)
                                , playgroundControl "Blur" (renderSlider bp.glowBlur 0 50 "px" SetButtonGlowBlur)
                                ]
                            , HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Spread" (renderSlider bp.glowSpread 0 20 "px" SetButtonGlowSpread)
                                , playgroundControl "Opacity" (renderSlider bp.glowOpacity 0 100 "%" SetButtonGlowOpacity)
                                ]
                            ]
                          else HH.text ""
                      ]
                  -- Gradient section
                  , HH.div [ HP.class_ (H.ClassName "panel-divider") ] []
                  , HH.div
                      [ HP.class_ (H.ClassName "effect-section") ]
                      [ HH.div
                          [ HP.class_ (H.ClassName "effect-header") ]
                          [ toggleControl "Gradient" bp.gradientEnabled ToggleButtonGradient ]
                      , if bp.gradientEnabled
                          then HH.div
                            [ HP.class_ (H.ClassName "effect-controls-grid") ]
                            [ HH.div
                                [ HP.class_ (H.ClassName "control-row") ]
                                [ playgroundControl "Type" (renderGradientTypeSelector bp.gradientType)
                                , playgroundControl "Angle" (renderSlider bp.gradientAngle 0 360 "°" SetButtonGradientAngle)
                                ]
                            , HH.div
                                [ HP.class_ (H.ClassName "gradient-stops-section") ]
                                [ HH.div
                                    [ HP.class_ (H.ClassName "gradient-stops-header") ]
                                    [ HH.span_ [ HH.text "Color Stops" ]
                                    , HH.button
                                        [ HP.class_ (H.ClassName "add-stop-btn")
                                        , HE.onClick \_ -> AddGradientStop
                                        ]
                                        [ HH.text "+" ]
                                    ]
                                , HH.div
                                    [ HP.class_ (H.ClassName "gradient-stops-list") ]
                                    (renderGradientStops bp.gradientStops)
                                ]
                            ]
                          else HH.text ""
                      ]
                  ]
              ]
          ]
      ]

-- Helper to get contrast class based on ratio
contrastClass :: Number -> String
contrastClass ratio
  | ratio >= 7.0 = "contrast-excellent"
  | ratio >= 4.5 = "contrast-good"
  | ratio >= 3.0 = "contrast-fair"
  | otherwise = "contrast-poor"

-- Color detail row for accessibility panel
colorDetail :: forall m. String -> String -> H.ComponentHTML Action () m
colorDetail label color =
  HH.div
    [ HP.class_ (H.ClassName "color-detail-row") ]
    [ HH.span [ HP.class_ (H.ClassName "color-detail-label") ] [ HH.text label ]
    , HH.div [ HP.class_ (H.ClassName "color-detail-value") ]
        [ HH.span 
            [ HP.class_ (H.ClassName "color-chip")
            , HP.attr (HH.AttrName "style") ("background-color: " <> color <> ";")
            ] []
        , HH.span [ HP.class_ (H.ClassName "color-hex") ] [ HH.text color ]
        ]
    ]

-- Render button with a specific visual state class
renderPlaygroundButtonState :: forall m. ButtonPlayground -> String -> String -> H.ComponentHTML Action () m
renderPlaygroundButtonState bp label stateClass =
  let
    -- Build custom style string for typography, stroke, and effects
    textTransform = textCaseToCss bp.textCase
    fontStyle = if bp.italic then "italic" else "normal"
    textDecoration = 
      if bp.underline && bp.strikethrough then "underline line-through"
      else if bp.underline then "underline"
      else if bp.strikethrough then "line-through"
      else "none"
    
    -- Stroke effect (toggle-based)
    strokeStyle = if bp.strokeEnabled
      then "--btn-stroke-width: " <> showNumber bp.strokeWidth <> "px;" <>
           "--btn-stroke-color: " <> bp.strokeColor <> ";" <>
           "--btn-stroke-enabled: 1;"
      else "--btn-stroke-enabled: 0;"
    
    -- Glow effect (box-shadow)
    glowStyle = if bp.glowEnabled 
      then "--btn-glow-color: " <> bp.glowColor <> ";" <>
           "--btn-glow-blur: " <> show bp.glowBlur <> "px;" <>
           "--btn-glow-spread: " <> show bp.glowSpread <> "px;" <>
           "--btn-glow-opacity: " <> show bp.glowOpacity <> ";" <>
           "--btn-glow-enabled: 1;"
      else "--btn-glow-enabled: 0;"
    
    -- Gradient background
    gradientStyle = if bp.gradientEnabled
      then "--btn-gradient: " <> buildGradientCSS bp.gradientType bp.gradientAngle bp.gradientStops <> ";" <>
           "--btn-gradient-enabled: 1;"
      else "--btn-gradient-enabled: 0;"
    
    -- Max width (0 = auto)
    maxWidthStyle = if bp.maxWidth > 0
      then "--btn-max-width: " <> show bp.maxWidth <> "px;"
      else "--btn-max-width: none;"
    
    customStyles = 
      "--btn-bg-color: " <> bp.buttonColor <> ";" <>
      "--btn-text-color: " <> bp.textColor <> ";" <>
      "--btn-font-family: " <> bp.fontFamily <> ";" <>
      "--btn-font-weight: " <> show bp.fontWeight <> ";" <>
      "--btn-font-size: " <> show bp.fontSize <> "px;" <>
      "--btn-font-style: " <> fontStyle <> ";" <>
      "--btn-text-decoration: " <> textDecoration <> ";" <>
      "--btn-letter-spacing: " <> show bp.letterSpacing <> ";" <>
      "--btn-radius: " <> show bp.radius <> "px;" <>
      "--btn-text-transform: " <> textTransform <> ";" <>
      maxWidthStyle <>
      strokeStyle <>
      glowStyle <>
      gradientStyle
    labelText = bp.label
  in
    HH.div
      [ HP.class_ (H.ClassName "preview-button-wrapper")
      , HP.attr (HH.AttrName "style") customStyles
      ]
      [ Button.button
          [ Button.variant bp.variant
          , Button.size bp.size
          , Button.shadow bp.shadowEnabled
          , Button.className ("playground-button playground-button-custom " <> stateClass)
          ]
          [ if bp.size == Button.Icon then starIcon else HH.text labelText ]
      , HH.span [ HP.class_ (H.ClassName "preview-state-label") ] [ HH.text label ]
      ]

-- Star icon for Icon-size buttons (more recognizable than cursor)
starIcon :: forall w i. HH.HTML w i
starIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "currentColor"
    , HP.attr (HH.AttrName "class") "w-5 h-5"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M12 2l3.09 6.26L22 9.27l-5 4.87 1.18 6.88L12 17.77l-6.18 3.25L7 14.14 2 9.27l6.91-1.01L12 2z" ]
        []
    ]

-- Build inline styles for the preview button wrapper
-- Uses CSS custom properties that cascade to the button
buildButtonStyles :: ButtonPlayground -> String
buildButtonStyles bp =
  let
    -- Core colors - these override the variant colors
    colorStyles = 
      "--playground-btn-bg: " <> bp.buttonColor <> ";" <>
      "--playground-btn-text: " <> bp.textColor <> ";" <>
      "--playground-btn-radius: " <> show bp.radius <> "px;"
    
    -- Animation timing
    easingStr = easingToCss bp.animationEasing
    animationStyles = 
      "--playground-btn-animation: " <> show bp.animationSpeed <> "ms;" <>
      "--playground-btn-easing: " <> easingStr <> ";"
    
    -- Shadow (full control)
    shadowStyles = if bp.shadowEnabled
      then let
             insetStr = if bp.shadowInset then "inset " else ""
           in "--playground-btn-shadow: " <> insetStr <> 
                show bp.shadowOffsetX <> "px " <> 
                show bp.shadowOffsetY <> "px " <> 
                show bp.shadowBlur <> "px " <> 
                show bp.shadowSpread <> "px " <> 
                hexToRgba bp.shadowColor bp.shadowOpacity <> ";"
      else "--playground-btn-shadow: none;"
    
    -- Stroke/border styles
    strokeStyles = if bp.strokeEnabled
      then "--playground-btn-border: " <> showNumber bp.strokeWidth <> "px solid " <> bp.strokeColor <> ";"
      else "--playground-btn-border: none;"
    
    -- Glow effect
    glowStyles = if bp.glowEnabled
      then "--playground-btn-glow: 0 0 " <> show bp.glowBlur <> "px " <> show bp.glowSpread <> "px " <> 
           hexToRgba bp.glowColor bp.glowOpacity <> ";"
      else "--playground-btn-glow: none;"
    
    -- Typography
    fontStyle = if bp.italic then "italic" else "normal"
    textDecoration = 
      if bp.underline && bp.strikethrough then "underline line-through"
      else if bp.underline then "underline"
      else if bp.strikethrough then "line-through"
      else "none"
    textTransform = textCaseToCss bp.textCase
    
    typoStyles = 
      "--playground-btn-font: " <> bp.fontFamily <> ";" <>
      "--playground-btn-weight: " <> show bp.fontWeight <> ";" <>
      "--playground-btn-size: " <> show bp.fontSize <> "px;" <>
      "--playground-btn-style: " <> fontStyle <> ";" <>
      "--playground-btn-decoration: " <> textDecoration <> ";" <>
      "--playground-btn-transform: " <> textTransform <> ";" <>
      "--playground-btn-spacing: " <> show bp.letterSpacing <> ";"
    
    -- Gradient background (overrides solid color)
    gradientStyles = if bp.gradientEnabled
      then "--playground-btn-gradient: " <> buildGradientCSS bp.gradientType bp.gradientAngle bp.gradientStops <> ";"
      else "--playground-btn-gradient: none;"
    
    -- Max width
    maxWidthStyles = if bp.maxWidth > 0
      then "--playground-btn-max-width: " <> show bp.maxWidth <> "px;"
      else "--playground-btn-max-width: none;"
  in
    colorStyles <> animationStyles <> shadowStyles <> strokeStyles <> glowStyles <> typoStyles <> gradientStyles <> maxWidthStyles

-- Convert TextCase to CSS text-transform value
textCaseToCss :: TextCase -> String
textCaseToCss = case _ of
  CaseNone -> "none"
  CaseLower -> "lowercase"
  CaseUpper -> "uppercase"
  CaseTitle -> "capitalize"
  CaseSentence -> "none"  -- No CSS equivalent, would need JS

-- Convert EasingType to CSS easing function
easingToCss :: EasingType -> String
easingToCss = case _ of
  EaseLinear -> "linear"
  EaseIn -> "ease-in"
  EaseOut -> "ease-out"
  EaseInOut -> "ease-in-out"
  EaseBounce -> "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
  EaseElastic -> "cubic-bezier(0.68, -0.6, 0.32, 1.6)"
  EaseSpring -> "cubic-bezier(0.175, 0.885, 0.32, 1.275)"

-- Convert hex color + opacity to rgba string
hexToRgba :: String -> Int -> String
hexToRgba hex opacity =
  let
    r = hexToR hex
    g = hexToG hex
    b = hexToB hex
    a = toNumber opacity / 100.0
  in "rgba(" <> show r <> ", " <> show g <> ", " <> show b <> ", " <> showNumber a <> ")"

-- Build CSS gradient string from type, angle, and stops
buildGradientCSS :: GradientType -> Int -> Array GradientStop -> String
buildGradientCSS gradType angle stops =
  let
    stopsStr = joinWith ", " (map (\s -> s.color <> " " <> show s.position <> "%") stops)
  in case gradType of
    LinearGradient -> "linear-gradient(" <> show angle <> "deg, " <> stopsStr <> ")"
    RadialGradient -> "radial-gradient(circle, " <> stopsStr <> ")"
    ConicGradient -> "conic-gradient(from " <> show angle <> "deg, " <> stopsStr <> ")"

-- Map helper for arrays
map :: forall a b. (a -> b) -> Array a -> Array b
map f arr = foldl (\acc x -> acc <> [f x]) [] arr

-- Convert string to uppercase (simple implementation)
toUpperCase :: String -> String
toUpperCase str = 
  let chars = toCharArray str
  in fromCharArray (map toUpperChar chars)

-- Convert single char to uppercase
toUpperChar :: Char -> Char
toUpperChar c = case c of
  'a' -> 'A'
  'b' -> 'B'
  'c' -> 'C'
  'd' -> 'D'
  'e' -> 'E'
  'f' -> 'F'
  'g' -> 'G'
  'h' -> 'H'
  'i' -> 'I'
  'j' -> 'J'
  'k' -> 'K'
  'l' -> 'L'
  'm' -> 'M'
  'n' -> 'N'
  'o' -> 'O'
  'p' -> 'P'
  'q' -> 'Q'
  'r' -> 'R'
  's' -> 'S'
  't' -> 'T'
  'u' -> 'U'
  'v' -> 'V'
  'w' -> 'W'
  'x' -> 'X'
  'y' -> 'Y'
  'z' -> 'Z'
  _ -> c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // wcag contrast calc
-- ═══════════════════════════════════════════════════════════════════════════════

-- FFI imports for proper WCAG calculation using JavaScript's Math.pow
foreign import calculateContrastRatioFFI :: String -> String -> Number
foreign import formatContrastRatioFFI :: Number -> String

-- | Truncate Number to Int (pure)
truncate :: Number -> Int
truncate = Int.floor

-- | Convert Int to Number (pure)
toNumber :: Int -> Number
toNumber = Int.toNumber

-- Get contrast ratio between text and background (via FFI)
getContrastRatio :: String -> String -> Number
getContrastRatio = calculateContrastRatioFFI

-- Format contrast ratio for display (via FFI)
formatContrastRatio :: Number -> String
formatContrastRatio = formatContrastRatioFFI

-- Check if meets WCAG AA (4.5:1 for normal text)
checkWcagAA :: String -> String -> Boolean
checkWcagAA textColor bgColor = calculateContrastRatioFFI textColor bgColor >= 4.5

-- Check if meets WCAG AAA (7:1 for normal text)  
checkWcagAAA :: String -> String -> Boolean
checkWcagAAA textColor bgColor = calculateContrastRatioFFI textColor bgColor >= 7.0

-- WCAG badge
wcagBadge :: forall m. String -> Boolean -> H.ComponentHTML Action () m
wcagBadge level passes =
  HH.span
    [ HP.class_ (H.ClassName $ "wcag-badge " <> if passes then "pass" else "fail") ]
    [ HH.text $ level <> if passes then " Pass" else " Fail" ]

-- Accessibility icon
accessibilityIcon :: forall w i. HH.HTML w i
accessibilityIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "class") "accessibility-icon"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "4.5"
        , HP.attr (HH.AttrName "r") "2.5"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M12 7v6m0 0l-3 5m3-5l3 5M5 9h14"
        ]
        []
    ]

-- Render the playground button with current state (scaled up for preview)
renderPlaygroundButton :: forall m. ButtonPlayground -> H.ComponentHTML Action () m
renderPlaygroundButton bp =
  Button.button
    [ Button.variant bp.variant
    , Button.size bp.size
    , Button.shadow bp.shadowEnabled
    , Button.disabled bp.disabled
    , Button.loading bp.loading
    , Button.className "playground-button"
    ]
    [ if bp.size == Button.Icon then cursorClickIcon else HH.text bp.label ]

-- Cursor/click icon for Icon size buttons
cursorClickIcon :: forall w i. HH.HTML w i
cursorClickIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "class") "w-5 h-5"
    ]
    [ -- Pointer/cursor icon
      HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M4 4l7.07 17 2.51-7.39L21 11.07z" ]
        []
    ]

-- Generate PureScript code for current button config
generateButtonCode :: ButtonPlayground -> String
generateButtonCode bp =
  let
    variantStr = case bp.variant of
      Button.Default -> ""
      Button.Secondary -> "Button.variant Button.Secondary"
      Button.Outline -> "Button.variant Button.Outline"
      Button.Destructive -> "Button.variant Button.Destructive"
      Button.Ghost -> "Button.variant Button.Ghost"
      Button.Link -> "Button.variant Button.Link"
    sizeStr = case bp.size of
      Button.Md -> ""
      Button.Sm -> "Button.size Button.Sm"
      Button.Lg -> "Button.size Button.Lg"
      Button.Icon -> "Button.size Button.Icon"
    shadowStr = if bp.shadowEnabled then "Button.shadow true" else ""
    disabledStr = if bp.disabled then "Button.disabled true" else ""
    loadingStr = if bp.loading then "Button.loading true" else ""
    props = [ variantStr, sizeStr, shadowStr, disabledStr, loadingStr ]
    nonEmpty = filterEmpty props
    propsStr = if nonEmpty == [] then "[]" else "[ " <> joinWith ", " nonEmpty <> " ]"
  in
    "Button.button " <> propsStr <> " [ HH.text \"" <> bp.label <> "\" ]"

-- Helper to filter empty strings
filterEmpty :: Array String -> Array String
filterEmpty arr = foldl (\acc s -> if s == "" then acc else acc <> [s]) [] arr

-- Helper to join strings with separator
joinWith :: String -> Array String -> String
joinWith sep arr = case arr of
  [] -> ""
  _ -> foldl (\acc s -> if acc == "" then s else acc <> sep <> s) "" arr

-- Control wrapper
playgroundControl :: forall m. String -> H.ComponentHTML Action () m -> H.ComponentHTML Action () m
playgroundControl label content =
  HH.div
    [ HP.class_ (H.ClassName "playground-control") ]
    [ HH.label 
        [ HP.class_ (H.ClassName "playground-control-label") ] 
        [ HH.text label ]
    , content
    ]

-- Variant selector (segmented control)
renderVariantSelector :: forall m. Button.ButtonVariant -> H.ComponentHTML Action () m
renderVariantSelector current =
  HH.div
    [ HP.class_ (H.ClassName "segmented-control") ]
    [ segmentedOption "Default" (current == Button.Default) (SetButtonVariant Button.Default)
    , segmentedOption "Secondary" (current == Button.Secondary) (SetButtonVariant Button.Secondary)
    , segmentedOption "Outline" (current == Button.Outline) (SetButtonVariant Button.Outline)
    , segmentedOption "Destructive" (current == Button.Destructive) (SetButtonVariant Button.Destructive)
    , segmentedOption "Ghost" (current == Button.Ghost) (SetButtonVariant Button.Ghost)
    , segmentedOption "Link" (current == Button.Link) (SetButtonVariant Button.Link)
    ]

-- Size selector
renderSizeSelector :: forall m. Button.ButtonSize -> H.ComponentHTML Action () m
renderSizeSelector current =
  HH.div
    [ HP.class_ (H.ClassName "segmented-control") ]
    [ segmentedOption "Sm" (current == Button.Sm) (SetButtonSize Button.Sm)
    , segmentedOption "Md" (current == Button.Md) (SetButtonSize Button.Md)
    , segmentedOption "Lg" (current == Button.Lg) (SetButtonSize Button.Lg)
    , segmentedOption "Icon" (current == Button.Icon) (SetButtonSize Button.Icon)
    ]

-- Font weight selector
renderFontWeightSelector :: forall m. Int -> H.ComponentHTML Action () m
renderFontWeightSelector current =
  HH.div
    [ HP.class_ (H.ClassName "segmented-control") ]
    [ segmentedOption "Light" (current == 300) (SetButtonFontWeight 300)
    , segmentedOption "Regular" (current == 400) (SetButtonFontWeight 400)
    , segmentedOption "Medium" (current == 500) (SetButtonFontWeight 500)
    , segmentedOption "Semi" (current == 600) (SetButtonFontWeight 600)
    , segmentedOption "Bold" (current == 700) (SetButtonFontWeight 700)
    ]

-- Font family selector (dropdown)
renderFontFamilySelector :: forall m. String -> H.ComponentHTML Action () m
renderFontFamilySelector current =
  HH.select
    [ HP.class_ (H.ClassName "font-family-select")
    , HP.value current
    , HE.onValueInput SetButtonFontFamily
    ]
    [ HH.optgroup [ HP.attr (HH.AttrName "label") "Sans-Serif" ]
        [ fontOption "Inter" current
        , fontOption "system-ui" current
        , fontOption "Helvetica Neue" current
        , fontOption "Arial" current
        , fontOption "Segoe UI" current
        , fontOption "Roboto" current
        , fontOption "SF Pro Display" current
        ]
    , HH.optgroup [ HP.attr (HH.AttrName "label") "Serif" ]
        [ fontOption "Georgia" current
        , fontOption "Times New Roman" current
        , fontOption "Palatino" current
        ]
    , HH.optgroup [ HP.attr (HH.AttrName "label") "Monospace" ]
        [ fontOption "JetBrains Mono" current
        , fontOption "SF Mono" current
        , fontOption "Consolas" current
        , fontOption "Monaco" current
        ]
    ]

fontOption :: forall m. String -> String -> H.ComponentHTML Action () m
fontOption fontName current =
  HH.option
    [ HP.value fontName
    , HP.selected (fontName == current)
    ]
    [ HH.text fontName ]

-- Gradient type selector
renderGradientTypeSelector :: forall m. GradientType -> H.ComponentHTML Action () m
renderGradientTypeSelector current =
  HH.div
    [ HP.class_ (H.ClassName "segmented-control") ]
    [ segmentedOption "Linear" (current == LinearGradient) (SetButtonGradientType LinearGradient)
    , segmentedOption "Radial" (current == RadialGradient) (SetButtonGradientType RadialGradient)
    , segmentedOption "Conic" (current == ConicGradient) (SetButtonGradientType ConicGradient)
    ]

-- Text case selector
renderTextCaseSelector :: forall m. TextCase -> H.ComponentHTML Action () m
renderTextCaseSelector current =
  HH.div
    [ HP.class_ (H.ClassName "segmented-control") ]
    [ segmentedOption "Aa" (current == CaseNone) (SetButtonTextCase CaseNone)
    , segmentedOption "aa" (current == CaseLower) (SetButtonTextCase CaseLower)
    , segmentedOption "AA" (current == CaseUpper) (SetButtonTextCase CaseUpper)
    , segmentedOption "Aa Bb" (current == CaseTitle) (SetButtonTextCase CaseTitle)
    ]

-- Animation easing selector
renderEasingSelector :: forall m. EasingType -> H.ComponentHTML Action () m
renderEasingSelector current =
  HH.div
    [ HP.class_ (H.ClassName "segmented-control segmented-control-wrap") ]
    [ segmentedOption "Linear" (current == EaseLinear) (SetButtonAnimationEasing EaseLinear)
    , segmentedOption "Ease In" (current == EaseIn) (SetButtonAnimationEasing EaseIn)
    , segmentedOption "Ease Out" (current == EaseOut) (SetButtonAnimationEasing EaseOut)
    , segmentedOption "In-Out" (current == EaseInOut) (SetButtonAnimationEasing EaseInOut)
    , segmentedOption "Bounce" (current == EaseBounce) (SetButtonAnimationEasing EaseBounce)
    , segmentedOption "Elastic" (current == EaseElastic) (SetButtonAnimationEasing EaseElastic)
    , segmentedOption "Spring" (current == EaseSpring) (SetButtonAnimationEasing EaseSpring)
    ]

-- Render gradient stops list
renderGradientStops :: forall m. Array GradientStop -> Array (H.ComponentHTML Action () m)
renderGradientStops stops =
  mapWithIndex renderGradientStop stops
  where
    canRemove = lengthArr stops > 2
    
    renderGradientStop :: Int -> GradientStop -> H.ComponentHTML Action () m
    renderGradientStop idx stop =
      HH.div
        [ HP.class_ (H.ClassName "gradient-stop-row") ]
        [ HH.div
            [ HP.class_ (H.ClassName "gradient-stop-color") ]
            [ HH.input
                [ HP.class_ (H.ClassName "color-input-small")
                , HP.type_ HP.InputColor
                , HP.value stop.color
                , HE.onValueInput (SetGradientStopColor idx)
                ]
            ]
        , HH.div
            [ HP.class_ (H.ClassName "gradient-stop-position") ]
            [ HH.input
                [ HP.class_ (H.ClassName "position-slider")
                , HP.type_ HP.InputRange
                , HP.attr (HH.AttrName "min") "0"
                , HP.attr (HH.AttrName "max") "100"
                , HP.value (show stop.position)
                , HE.onValueInput (\s -> SetGradientStopPosition idx (parseIntOrDefault stop.position s))
                ]
            , HH.span 
                [ HP.class_ (H.ClassName "position-value") ] 
                [ HH.text (show stop.position <> "%") ]
            ]
        , if canRemove
            then HH.button
              [ HP.class_ (H.ClassName "remove-stop-btn")
              , HE.onClick \_ -> RemoveGradientStop idx
              ]
              [ HH.text "×" ]
            else HH.text ""
        ]

-- Array length helper
lengthArr :: forall a. Array a -> Int
lengthArr = foldl (\acc _ -> acc + 1) 0

-- Segmented control option
segmentedOption :: forall m. String -> Boolean -> Action -> H.ComponentHTML Action () m
segmentedOption label isActive action =
  HH.button
    [ HP.class_ (H.ClassName $ "segmented-option" <> if isActive then " active" else "")
    , HE.onClick \_ -> action
    ]
    [ HH.text label ]

-- Toggle control (checkbox-style)
toggleControl :: forall m. String -> Boolean -> Action -> H.ComponentHTML Action () m
toggleControl label isOn action =
  HH.button
    [ HP.class_ (H.ClassName $ "toggle-control" <> if isOn then " active" else "")
    , HE.onClick \_ -> action
    ]
    [ HH.span [ HP.class_ (H.ClassName "toggle-indicator") ] []
    , HH.text label
    ]

-- Slider control for integers
renderSlider :: forall m. Int -> Int -> Int -> String -> (Int -> Action) -> H.ComponentHTML Action () m
renderSlider value minVal maxVal unit action =
  HH.div
    [ HP.class_ (H.ClassName "slider-control") ]
    [ HH.input
        [ HP.class_ (H.ClassName "slider-input")
        , HP.type_ HP.InputRange
        , HP.attr (HH.AttrName "min") (show minVal)
        , HP.attr (HH.AttrName "max") (show maxVal)
        , HP.attr (HH.AttrName "step") "1"
        , HP.value (show value)
        , HE.onValueInput \s -> action (parseIntOrDefault value s)
        ]
    , HH.span 
        [ HP.class_ (H.ClassName "slider-value") ] 
        [ HH.text $ show value <> unit ]
    ]

-- Slider control for floating point numbers
renderNumberSlider :: forall m. Number -> Number -> Number -> String -> (Number -> Action) -> H.ComponentHTML Action () m
renderNumberSlider value minVal maxVal unit action =
  HH.div
    [ HP.class_ (H.ClassName "slider-control") ]
    [ HH.input
        [ HP.class_ (H.ClassName "slider-input")
        , HP.type_ HP.InputRange
        , HP.attr (HH.AttrName "min") (showNumber minVal)
        , HP.attr (HH.AttrName "max") (showNumber maxVal)
        , HP.attr (HH.AttrName "step") "0.1"
        , HP.value (showNumber value)
        , HE.onValueInput \s -> action (parseNumberOrDefault value s)
        ]
    , HH.span 
        [ HP.class_ (H.ClassName "slider-value") ] 
        [ HH.text $ showNumber value <> unit ]
    ]

-- Show number with 1 decimal place
showNumber :: Number -> String
showNumber n = 
  let wholePart = truncate n
      decimal = truncate ((n - toNumber wholePart) * 10.0)
  in show wholePart <> "." <> show (if decimal < 0 then -decimal else decimal)

-- Parse number with default
parseNumberOrDefault :: Number -> String -> Number
parseNumberOrDefault def str = case parseNumber str of
  Just n -> n
  Nothing -> def

-- Simple number parsing
parseNumber :: String -> Maybe Number
parseNumber str =
  case parseInt str of
    Just n -> Just (toNumber n)
    Nothing -> Nothing

-- Simplified color picker: native color input + hex text field
renderColorPicker :: forall m. String -> (String -> Action) -> H.ComponentHTML Action () m
renderColorPicker current action =
  HH.div
    [ HP.class_ (H.ClassName "color-picker-inline") ]
    [ HH.input
        [ HP.class_ (H.ClassName "color-input-native")
        , HP.type_ HP.InputColor
        , HP.value current
        , HE.onValueInput action
        ]
    , HH.input
        [ HP.class_ (H.ClassName "color-hex-input")
        , HP.value current
        , HP.placeholder "#000000"
        , HE.onValueInput action
        ]
    ]

-- RGB input field (read-only display for now)
rgbInput :: forall m. String -> Int -> H.ComponentHTML Action () m
rgbInput label value =
  HH.div
    [ HP.class_ (H.ClassName "rgb-input-group") ]
    [ HH.span [ HP.class_ (H.ClassName "rgb-label") ] [ HH.text label ]
    , HH.input
        [ HP.class_ (H.ClassName "rgb-input")
        , HP.value (show value)
        , HP.attr (HH.AttrName "readonly") "true"
        ]
    ]

-- Parse hex to RGB components
hexToR :: String -> Int
hexToR hex = parseHexPair (takeHexPair hex 1)

hexToG :: String -> Int
hexToG hex = parseHexPair (takeHexPair hex 3)

hexToB :: String -> Int
hexToB hex = parseHexPair (takeHexPair hex 5)

-- Extract 2 chars from hex string starting at position
takeHexPair :: String -> Int -> String
takeHexPair str pos = 
  let 
    chars = toCharArray str
    c1 = fromMaybe '0' (index chars pos)
    c2 = fromMaybe '0' (index chars (pos + 1))
  in fromCharArray [c1, c2]

-- Convert hex pair to int (0-255)
parseHexPair :: String -> Int
parseHexPair "00" = 0
parseHexPair "1a" = 26
parseHexPair "33" = 51
parseHexPair "66" = 102
parseHexPair "99" = 153
parseHexPair "ff" = 255
parseHexPair "FF" = 255
parseHexPair "0a" = 10
parseHexPair "0A" = 10
parseHexPair _ = 0  -- Fallback

-- Palette icon (color picker)
paletteIcon :: forall w i. HH.HTML w i
paletteIcon =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "class") "palette-icon"
    ]
    [ -- Palette shape
      HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "13.5"
        , HP.attr (HH.AttrName "cy") "6.5"
        , HP.attr (HH.AttrName "r") "0.5"
        , HP.attr (HH.AttrName "fill") "currentColor"
        ]
        []
    , HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "17.5"
        , HP.attr (HH.AttrName "cy") "10.5"
        , HP.attr (HH.AttrName "r") "0.5"
        , HP.attr (HH.AttrName "fill") "currentColor"
        ]
        []
    , HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "8.5"
        , HP.attr (HH.AttrName "cy") "7.5"
        , HP.attr (HH.AttrName "r") "0.5"
        , HP.attr (HH.AttrName "fill") "currentColor"
        ]
        []
    , HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "6.5"
        , HP.attr (HH.AttrName "cy") "12.5"
        , HP.attr (HH.AttrName "r") "0.5"
        , HP.attr (HH.AttrName "fill") "currentColor"
        ]
        []
    , HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M12 2C6.5 2 2 6.5 2 12s4.5 10 10 10c.926 0 1.648-.746 1.648-1.688 0-.437-.18-.835-.437-1.125-.29-.289-.438-.652-.438-1.125a1.64 1.64 0 0 1 1.668-1.668h1.996c3.051 0 5.555-2.503 5.555-5.555C21.965 6.012 17.461 2 12 2z"
        ]
        []
    ]

-- Individual color swatch
colorSwatch :: forall m. String -> String -> (String -> Action) -> H.ComponentHTML Action () m
colorSwatch color current action =
  HH.button
    [ HP.class_ (H.ClassName $ "color-swatch" <> if color == current then " active" else "")
    , HP.attr (HH.AttrName "style") ("background-color: " <> color <> ";")
    , HE.onClick \_ -> action color
    ]
    []

-- Parse int with default fallback
parseIntOrDefault :: Int -> String -> Int
parseIntOrDefault def str = case parseInt str of
  Just n -> n
  Nothing -> def

-- Simple parseInt using character-based parsing
parseInt :: String -> Maybe Int
parseInt str = 
  let chars = toCharArray str
  in case uncons chars of
    Nothing -> Nothing  -- Empty string
    Just { head: c, tail: rest } -> case charToDigit c of
      Just d -> parseDigitsRest rest d
      Nothing -> Nothing

parseDigitsRest :: Array Char -> Int -> Maybe Int
parseDigitsRest chars acc = case uncons chars of
  Nothing -> Just acc
  Just { head: c, tail: rest } -> case charToDigit c of
    Just d -> parseDigitsRest rest (acc * 10 + d)
    Nothing -> Nothing

charToDigit :: Char -> Maybe Int
charToDigit '0' = Just 0
charToDigit '1' = Just 1
charToDigit '2' = Just 2
charToDigit '3' = Just 3
charToDigit '4' = Just 4
charToDigit '5' = Just 5
charToDigit '6' = Just 6
charToDigit '7' = Just 7
charToDigit '8' = Just 8
charToDigit '9' = Just 9
charToDigit _ = Nothing

-- Variant card for gallery
variantCard :: forall m. String -> Button.ButtonVariant -> H.ComponentHTML Action () m
variantCard label v =
  HH.div
    [ HP.class_ (H.ClassName "variant-card") ]
    [ Button.button [ Button.variant v ] [ HH.text label ]
    , HH.div 
        [ HP.class_ (H.ClassName "text-xs text-white/40 mt-3 text-center") ] 
        [ HH.text label ]
    ]

-- Size demo for gallery
sizeDemo :: forall m. String -> Button.ButtonSize -> H.ComponentHTML Action () m
sizeDemo label sz =
  HH.div
    [ HP.class_ (H.ClassName "text-center") ]
    [ Button.button [ Button.size sz ] [ HH.text label ]
    , HH.div 
        [ HP.class_ (H.ClassName "text-xs text-white/40 mt-2") ] 
        [ HH.text label ]
    ]

statCard :: forall m. String -> String -> H.ComponentHTML Action () m
statCard value label =
  HH.div
    [ HP.class_ (H.ClassName "stat-card") ]
    [ HH.div [ HP.class_ (H.ClassName "stat-value") ] [ HH.text value ]
    , HH.div [ HP.class_ (H.ClassName "stat-label") ] [ HH.text label ]
    ]

componentCard :: forall m. String -> String -> H.ComponentHTML Action () m -> String -> H.ComponentHTML Action () m
componentCard title description preview code =
  HH.div
    [ HP.class_ (H.ClassName "component-card") ]
    [ HH.div
        [ HP.class_ (H.ClassName "component-card-header") ]
        [ HH.h3 [ HP.class_ (H.ClassName "component-card-title") ] [ HH.text title ]
        , HH.p [ HP.class_ (H.ClassName "component-card-description") ] [ HH.text description ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "component-card-preview") ]
        [ preview ]
    , HH.div
        [ HP.class_ (H.ClassName "component-card-code") ]
        [ HH.pre_ [ HH.text code ] ]
    ]

renderFooter :: forall m. H.ComponentHTML Action () m
renderFooter =
  HH.footer
    [ HP.class_ (H.ClassName "glass-footer") ]
    [ HH.div
        [ HP.class_ (H.ClassName "footer-content") ]
        [ HH.div
            [ HP.class_ (H.ClassName "footer-text") ]
            [ HH.text "Built with "
            , HH.span [ HP.class_ (H.ClassName "gradient-text font-medium") ] [ HH.text "Hydrogen" ]
            , HH.text " — PureScript/Halogen for correct web applications"
            ]
        , HH.div
            [ HP.class_ (H.ClassName "flex items-center gap-4") ]
            [ HH.a
                [ HP.class_ (H.ClassName "footer-link")
                , HP.href "https://github.com/straylight-software/hydrogen"
                ]
                [ HH.text "GitHub" ]
            , HH.a
                [ HP.class_ (H.ClassName "footer-link")
                , HP.href "https://straylight.software"
                ]
                [ HH.text "Straylight" ]
            ]
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // inputs
-- ═══════════════════════════════════════════════════════════════════════════════

renderInputs :: forall m. State -> H.ComponentHTML Action () m
renderInputs state =
  HH.div
    [ HP.class_ (H.ClassName "max-w-4xl mx-auto animate-fade-in") ]
    [ HH.h1
        [ HP.class_ (H.ClassName "text-3xl font-bold mb-2") ]
        [ HH.text "Input Components" ]
    , HH.p
        [ HP.class_ (H.ClassName "text-white/60 mb-8") ]
        [ HH.text "Form inputs and controls for capturing user data." ]
    , HH.div
        [ HP.class_ (H.ClassName "grid grid-cols-1 md:grid-cols-2 gap-6") ]
        [ componentCard "Search Input" "Search with icon and clear button"
            (HH.div
              [ HP.class_ (H.ClassName "search-input-wrapper w-full") ]
              [ HH.span 
                  [ HP.class_ (H.ClassName "search-icon") ] 
                  [ searchIconSvg ]
              , HH.input
                  [ HP.class_ (H.ClassName "glass-input search-input w-full")
                  , HP.placeholder "Search components..."
                  ]
              ])
            "SearchInput.searchInput [ ... ]"
        , componentCard "Number Input" "Numeric input with +/- controls"
            (HH.div
              [ HP.class_ (H.ClassName "flex items-center gap-3") ]
              [ HH.button 
                  [ HP.class_ (H.ClassName "glow-button px-4 py-2")
                  , HE.onClick \_ -> DecrementNumber
                  ] 
                  [ HH.text "−" ]
              , HH.div
                  [ HP.class_ (H.ClassName "glass-input w-20 text-center font-mono") ]
                  [ HH.text (show state.numberInputValue) ]
              , HH.button 
                  [ HP.class_ (H.ClassName "glow-button px-4 py-2")
                  , HE.onClick \_ -> IncrementNumber
                  ] 
                  [ HH.text "+" ]
              ])
            "NumberInput.numberInput [ ... ]"
        , componentCard "Password Input" "Password with visibility toggle"
            (HH.div
              [ HP.class_ (H.ClassName "relative w-full") ]
              [ HH.input
                  [ HP.class_ (H.ClassName "glass-input w-full pr-12")
                  , HP.type_ HP.InputPassword
                  , HP.placeholder "Enter password..."
                  ]
              , HH.button
                  [ HP.class_ (H.ClassName "absolute right-3 top-1/2 -translate-y-1/2 eye-icon bg-transparent border-none cursor-pointer") ]
                  [ eyeIconSvg ]
              ])
            "PasswordInput.passwordInput [ ... ]"
        , componentCard "Tag Input" "Multi-tag input with add/remove"
            (HH.div
              [ HP.class_ (H.ClassName "flex flex-wrap gap-2") ]
              [ HH.span [ HP.class_ (H.ClassName "glass-badge tag-purple") ] [ HH.text "PureScript ×" ]
              , HH.span [ HP.class_ (H.ClassName "glass-badge tag-blue") ] [ HH.text "Halogen ×" ]
              , HH.span [ HP.class_ (H.ClassName "glass-badge tag-green") ] [ HH.text "Nix ×" ]
              , HH.span [ HP.class_ (H.ClassName "glass-badge opacity-60 cursor-pointer") ] [ HH.text "+ Add" ]
              ])
            "TagInput.tagInput [ ... ]"
        ]
    ]

-- SVG Icons (use HP.attr for class on SVG elements, not HP.class_)
searchIconSvg :: forall w i. HH.HTML w i
searchIconSvg =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "class") "w-5 h-5"
    ]
    [ HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "11"
        , HP.attr (HH.AttrName "cy") "11"
        , HP.attr (HH.AttrName "r") "8"
        ]
        []
    , HH.element (HH.ElemName "line")
        [ HP.attr (HH.AttrName "x1") "21"
        , HP.attr (HH.AttrName "y1") "21"
        , HP.attr (HH.AttrName "x2") "16.65"
        , HP.attr (HH.AttrName "y2") "16.65"
        ]
        []
    ]

eyeIconSvg :: forall w i. HH.HTML w i
eyeIconSvg =
  HH.element (HH.ElemName "svg")
    [ HP.attr (HH.AttrName "xmlns") "http://www.w3.org/2000/svg"
    , HP.attr (HH.AttrName "viewBox") "0 0 24 24"
    , HP.attr (HH.AttrName "fill") "none"
    , HP.attr (HH.AttrName "stroke") "currentColor"
    , HP.attr (HH.AttrName "stroke-width") "2"
    , HP.attr (HH.AttrName "stroke-linecap") "round"
    , HP.attr (HH.AttrName "stroke-linejoin") "round"
    , HP.attr (HH.AttrName "class") "w-5 h-5"
    ]
    [ HH.element (HH.ElemName "path")
        [ HP.attr (HH.AttrName "d") "M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z" ]
        []
    , HH.element (HH.ElemName "circle")
        [ HP.attr (HH.AttrName "cx") "12"
        , HP.attr (HH.AttrName "cy") "12"
        , HP.attr (HH.AttrName "r") "3"
        ]
        []
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // feedback
-- ═══════════════════════════════════════════════════════════════════════════════

renderFeedback :: forall m. H.ComponentHTML Action () m
renderFeedback =
  HH.div
    [ HP.class_ (H.ClassName "max-w-4xl mx-auto animate-fade-in") ]
    [ HH.h1
        [ HP.class_ (H.ClassName "text-3xl font-bold mb-2") ]
        [ HH.text "Feedback Components" ]
    , HH.p
        [ HP.class_ (H.ClassName "text-white/60 mb-8") ]
        [ HH.text "Loading states, progress indicators, and alerts." ]
    , HH.div
        [ HP.class_ (H.ClassName "grid grid-cols-1 md:grid-cols-2 gap-6") ]
        [ componentCard "Loading Bar" "Determinate and indeterminate progress"
            (HH.div
              [ HP.class_ (H.ClassName "w-full space-y-6") ]
              [ -- Indeterminate with label
                HH.div_
                  [ HH.div 
                      [ HP.class_ (H.ClassName "text-xs text-white/50 mb-2") ] 
                      [ HH.text "Indeterminate" ]
                  , HH.div
                      [ HP.class_ (H.ClassName "loading-bar-track") ]
                      [ HH.div [ HP.class_ (H.ClassName "loading-bar-indeterminate") ] [] ]
                  ]
              -- Determinate with label
              , HH.div_
                  [ HH.div 
                      [ HP.class_ (H.ClassName "text-xs text-white/50 mb-2") ] 
                      [ HH.text "Determinate (66%)" ]
                  , HH.div
                      [ HP.class_ (H.ClassName "loading-bar-track") ]
                      [ HH.div 
                          [ HP.class_ (H.ClassName "loading-bar-determinate")
                          , HP.attr (HH.AttrName "style") "width: 66%"
                          ] 
                          [] 
                      ]
                  ]
              ])
            "LoadingBar.loadingBar [ progress 66 ]"
        , componentCard "Skeleton" "Loading placeholder"
            (HH.div
              [ HP.class_ (H.ClassName "space-y-3 w-full") ]
              [ HH.div [ HP.class_ (H.ClassName "skeleton h-4 w-3/4") ] []
              , HH.div [ HP.class_ (H.ClassName "skeleton h-4 w-1/2") ] []
              , HH.div [ HP.class_ (H.ClassName "skeleton h-4 w-5/6") ] []
              ])
            "Skeleton.skeleton [ ... ]"
        , componentCard "Spinner" "Loading indicator"
            (HH.div
              [ HP.class_ (H.ClassName "flex items-center gap-6") ]
              [ HH.div [ HP.class_ (H.ClassName "spinner w-6 h-6") , HP.attr (HH.AttrName "style") "border-top-color: #8b5cf6" ] []
              , HH.div [ HP.class_ (H.ClassName "spinner w-8 h-8") , HP.attr (HH.AttrName "style") "border-top-color: #3b82f6" ] []
              , HH.div [ HP.class_ (H.ClassName "spinner w-10 h-10") , HP.attr (HH.AttrName "style") "border-top-color: #ec4899" ] []
              ])
            "Spinner.spinner [ size Large ]"
        , componentCard "Alert" "Status messages"
            (HH.div
              [ HP.class_ (H.ClassName "space-y-3 w-full") ]
              [ HH.div 
                  [ HP.class_ (H.ClassName "alert alert-success pl-5") ]
                  [ HH.text "Success: Operation completed successfully" ]
              , HH.div 
                  [ HP.class_ (H.ClassName "alert alert-error pl-5") ]
                  [ HH.text "Error: Something went wrong" ]
              , HH.div 
                  [ HP.class_ (H.ClassName "alert alert-warning pl-5") ]
                  [ HH.text "Warning: Please review your input" ]
              ])
            "Alert.alert [ variant Success ] [ ... ]"
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // layout
-- ═══════════════════════════════════════════════════════════════════════════════

renderLayout :: forall m. H.ComponentHTML Action () m
renderLayout =
  HH.div
    [ HP.class_ (H.ClassName "max-w-4xl mx-auto animate-fade-in") ]
    [ HH.h1
        [ HP.class_ (H.ClassName "text-3xl font-bold mb-2") ]
        [ HH.text "Layout Components" ]
    , HH.p
        [ HP.class_ (H.ClassName "text-white/60 mb-8") ]
        [ HH.text "Structural components for organizing content." ]
    , HH.div
        [ HP.class_ (H.ClassName "grid grid-cols-1 md:grid-cols-2 gap-6") ]
        [ componentCard "Card" "Basic content container"
            (HH.div
              [ HP.class_ (H.ClassName "glass-card p-4 w-full") ]
              [ HH.h4 [ HP.class_ (H.ClassName "font-semibold mb-2") ] [ HH.text "Card Title" ]
              , HH.p [ HP.class_ (H.ClassName "text-sm text-white/60") ] [ HH.text "Card content with description text." ]
              , HH.div 
                  [ HP.class_ (H.ClassName "flex gap-2 mt-3") ]
                  [ Button.button [ Button.size Button.Sm ] [ HH.text "Action" ]
                  , Button.button [ Button.size Button.Sm, Button.variant Button.Outline ] [ HH.text "Cancel" ]
                  ]
              ])
            "Card.card [] [ ... ]"
        , componentCard "Blog Card" "Article preview with image"
            (HH.div
              [ HP.class_ (H.ClassName "blog-card w-full") ]
              [ HH.div 
                  [ HP.class_ (H.ClassName "blog-card-image") ] 
                  [ HH.text "Featured Image" ]
              , HH.div
                  [ HP.class_ (H.ClassName "blog-card-content") ]
                  [ HH.h4 [ HP.class_ (H.ClassName "blog-card-title") ] [ HH.text "Getting Started with PureScript" ]
                  , HH.p [ HP.class_ (H.ClassName "blog-card-excerpt") ] [ HH.text "Learn the fundamentals of functional programming with PureScript..." ]
                  , HH.div 
                      [ HP.class_ (H.ClassName "blog-card-meta") ]
                      [ HH.span_ [ HH.text "5 min read" ]
                      , HH.span_ [ HH.text "Feb 21, 2026" ]
                      ]
                  ]
              ])
            "BlogCard.blogCard { title, excerpt, ... }"
        , componentCard "Media Card" "Video/image with play overlay"
            (HH.div
              [ HP.class_ (H.ClassName "media-card w-full") ]
              [ HH.div 
                  [ HP.class_ (H.ClassName "media-card-play") ]
                  [ HH.text "▶" ]
              ])
            "MediaCard.mediaCard { src, type_ } []"
        , componentCard "Feature Card" "Icon + title + description"
            (HH.div
              [ HP.class_ (H.ClassName "feature-card w-full") ]
              [ HH.div [ HP.class_ (H.ClassName "feature-card-icon") ] [ HH.text "⚡" ]
              , HH.h4 [ HP.class_ (H.ClassName "feature-card-title") ] [ HH.text "Lightning Fast" ]
              , HH.p [ HP.class_ (H.ClassName "feature-card-description") ] [ HH.text "Optimized for performance with lazy loading and code splitting." ]
              ])
            "FeatureCard.featureCard { icon, title } []"
        , componentCard "Grid Layout" "Responsive multi-column"
            (HH.div
              [ HP.class_ (H.ClassName "grid grid-cols-3 gap-2 w-full") ]
              [ HH.div [ HP.class_ (H.ClassName "h-16 bg-white/5 rounded flex items-center justify-center text-xs text-white/40") ] [ HH.text "1" ]
              , HH.div [ HP.class_ (H.ClassName "h-16 bg-white/5 rounded flex items-center justify-center text-xs text-white/40") ] [ HH.text "2" ]
              , HH.div [ HP.class_ (H.ClassName "h-16 bg-white/5 rounded flex items-center justify-center text-xs text-white/40") ] [ HH.text "3" ]
              , HH.div [ HP.class_ (H.ClassName "h-16 bg-white/5 rounded flex items-center justify-center text-xs text-white/40 col-span-2") ] [ HH.text "4 (span 2)" ]
              , HH.div [ HP.class_ (H.ClassName "h-16 bg-white/5 rounded flex items-center justify-center text-xs text-white/40") ] [ HH.text "5" ]
              ])
            "Grid.grid [ cols 3, gap 2 ] [ ... ]"
        , componentCard "Stack Layout" "Vertical/horizontal stacking"
            (HH.div
              [ HP.class_ (H.ClassName "flex flex-col gap-2 w-full") ]
              [ HH.div [ HP.class_ (H.ClassName "h-10 bg-white/5 rounded flex items-center justify-center text-xs text-white/40") ] [ HH.text "Stack Item 1" ]
              , HH.div [ HP.class_ (H.ClassName "h-10 bg-white/5 rounded flex items-center justify-center text-xs text-white/40") ] [ HH.text "Stack Item 2" ]
              , HH.div [ HP.class_ (H.ClassName "h-10 bg-white/5 rounded flex items-center justify-center text-xs text-white/40") ] [ HH.text "Stack Item 3" ]
              ])
            "Stack.stack [ direction Vertical ] [ ... ]"
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // data display
-- ═══════════════════════════════════════════════════════════════════════════════

renderDataDisplay :: forall m. H.ComponentHTML Action () m
renderDataDisplay =
  HH.div
    [ HP.class_ (H.ClassName "max-w-4xl mx-auto animate-fade-in") ]
    [ HH.h1
        [ HP.class_ (H.ClassName "text-3xl font-bold mb-2") ]
        [ HH.text "Data Display" ]
    , HH.p
        [ HP.class_ (H.ClassName "text-white/60 mb-8") ]
        [ HH.text "Components for displaying and formatting data." ]
    , HH.div
        [ HP.class_ (H.ClassName "grid grid-cols-1 md:grid-cols-2 gap-6") ]
        [ componentCard "Stat Card" "Metric display with trends"
            (HH.div
              [ HP.class_ (H.ClassName "grid grid-cols-2 gap-3 w-full") ]
              [ HH.div
                  [ HP.class_ (H.ClassName "stat-card") ]
                  [ HH.div [ HP.class_ (H.ClassName "stat-value") ] [ HH.text "$45.2K" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-label") ] [ HH.text "Revenue" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-trend stat-trend-up") ] [ HH.text "↑ 12.5%" ]
                  ]
              , HH.div
                  [ HP.class_ (H.ClassName "stat-card") ]
                  [ HH.div [ HP.class_ (H.ClassName "stat-value") ] [ HH.text "2,847" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-label") ] [ HH.text "Users" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-trend stat-trend-up") ] [ HH.text "↑ 8.2%" ]
                  ]
              , HH.div
                  [ HP.class_ (H.ClassName "stat-card") ]
                  [ HH.div [ HP.class_ (H.ClassName "stat-value") ] [ HH.text "98.5%" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-label") ] [ HH.text "Uptime" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-trend stat-trend-neutral") ] [ HH.text "— stable" ]
                  ]
              , HH.div
                  [ HP.class_ (H.ClassName "stat-card") ]
                  [ HH.div [ HP.class_ (H.ClassName "stat-value") ] [ HH.text "142ms" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-label") ] [ HH.text "Latency" ]
                  , HH.div [ HP.class_ (H.ClassName "stat-trend stat-trend-down") ] [ HH.text "↓ 5.1%" ]
                  ]
              ])
            "StatCard.statCard [] { ... }"
        , componentCard "Code Block" "Syntax highlighted code"
            (HH.div
              [ HP.class_ (H.ClassName "component-card-code rounded w-full text-left") ]
              [ HH.pre_ 
                  [ HH.span [ HP.class_ (H.ClassName "code-keyword") ] [ HH.text "module " ]
                  , HH.span [ HP.class_ (H.ClassName "code-type") ] [ HH.text "Main " ]
                  , HH.span [ HP.class_ (H.ClassName "code-keyword") ] [ HH.text "where" ]
                  , HH.text "\n\n"
                  , HH.span [ HP.class_ (H.ClassName "code-function") ] [ HH.text "main" ]
                  , HH.text " "
                  , HH.span [ HP.class_ (H.ClassName "code-operator") ] [ HH.text "::" ]
                  , HH.text " "
                  , HH.span [ HP.class_ (H.ClassName "code-type") ] [ HH.text "Effect Unit" ]
                  , HH.text "\n"
                  , HH.span [ HP.class_ (H.ClassName "code-function") ] [ HH.text "main" ]
                  , HH.text " "
                  , HH.span [ HP.class_ (H.ClassName "code-operator") ] [ HH.text "=" ]
                  , HH.text " log "
                  , HH.span [ HP.class_ (H.ClassName "code-string") ] [ HH.text "\"Hello\"" ]
                  ] 
              ])
            "CodeBlock.codeBlock [ lang PS ] [ ... ]"
        , componentCard "Badge" "Status indicators and labels"
            (HH.div
              [ HP.class_ (H.ClassName "flex flex-wrap items-center gap-2") ]
              [ HH.span [ HP.class_ (H.ClassName "glass-badge") ] [ HH.text "Default" ]
              , HH.span [ HP.class_ (H.ClassName "badge badge-success") ] [ HH.text "Success" ]
              , HH.span [ HP.class_ (H.ClassName "badge badge-error") ] [ HH.text "Error" ]
              , HH.span [ HP.class_ (H.ClassName "badge badge-warning") ] [ HH.text "Warning" ]
              , HH.span [ HP.class_ (H.ClassName "badge badge-info") ] [ HH.text "Info" ]
              ])
            "Badge.badge [ variant Success ] [ ... ]"
        , componentCard "Avatar" "User profile images"
            (HH.div
              [ HP.class_ (H.ClassName "flex items-center gap-3") ]
              [ HH.div [ HP.class_ (H.ClassName "w-8 h-8 rounded-full bg-gradient-to-br from-violet-500 to-blue-500 flex items-center justify-center text-xs font-medium") ] [ HH.text "JD" ]
              , HH.div [ HP.class_ (H.ClassName "w-10 h-10 rounded-full bg-gradient-to-br from-pink-500 to-orange-500 flex items-center justify-center text-sm font-medium") ] [ HH.text "AB" ]
              , HH.div [ HP.class_ (H.ClassName "w-12 h-12 rounded-full bg-gradient-to-br from-green-500 to-teal-500 flex items-center justify-center font-medium") ] [ HH.text "XY" ]
              ])
            "Avatar.avatar [ initials \"JD\" ] []"
        , componentCard "Progress Variants" "Circular and step progress"
            (HH.div
              [ HP.class_ (H.ClassName "flex items-center gap-6 w-full justify-center") ]
              [ -- Circular progress
                HH.div
                  [ HP.class_ (H.ClassName "progress-circular")
                  , HP.attr (HH.AttrName "style") "--progress: 75%"
                  ]
                  [ HH.div [ HP.class_ (H.ClassName "progress-circular-inner") ] [ HH.text "75%" ] ]
              -- Step progress
              , HH.div
                  [ HP.class_ (H.ClassName "progress-steps") ]
                  [ HH.div [ HP.class_ (H.ClassName "progress-step completed") ] []
                  , HH.div [ HP.class_ (H.ClassName "progress-step completed") ] []
                  , HH.div [ HP.class_ (H.ClassName "progress-step active") ] []
                  , HH.div [ HP.class_ (H.ClassName "progress-step") ] []
                  , HH.div [ HP.class_ (H.ClassName "progress-step") ] []
                  ]
              ])
            "Progress.circular [ value 75 ] []"
        ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // overlay
-- ═══════════════════════════════════════════════════════════════════════════════

renderOverlaySection :: forall m. H.ComponentHTML Action () m
renderOverlaySection =
  HH.div
    [ HP.class_ (H.ClassName "max-w-4xl mx-auto animate-fade-in") ]
    [ HH.h1
        [ HP.class_ (H.ClassName "text-3xl font-bold mb-2") ]
        [ HH.text "Overlay Components" ]
    , HH.p
        [ HP.class_ (H.ClassName "text-white/60 mb-8") ]
        [ HH.text "Modals, dialogs, sheets, and tooltips." ]
    , HH.div
        [ HP.class_ (H.ClassName "grid grid-cols-1 md:grid-cols-2 gap-6") ]
        [ componentCard "Dialog" "Centered modal dialog"
            (Button.button [ Button.onClick \_ -> OpenDialog ] [ HH.text "Open Dialog" ])
            "Dialog.dialog [ open true ] [ ... ]"
        , componentCard "Sheet" "Slide-out panels from any direction"
            (HH.div
              [ HP.class_ (H.ClassName "flex flex-wrap gap-2") ]
              [ Button.button [ Button.size Button.Sm, Button.onClick \_ -> OpenSheet SheetRight ] [ HH.text "Right" ]
              , Button.button [ Button.size Button.Sm, Button.variant Button.Outline, Button.onClick \_ -> OpenSheet SheetLeft ] [ HH.text "Left" ]
              , Button.button [ Button.size Button.Sm, Button.variant Button.Outline, Button.onClick \_ -> OpenSheet SheetTop ] [ HH.text "Top" ]
              , Button.button [ Button.size Button.Sm, Button.variant Button.Outline, Button.onClick \_ -> OpenSheet SheetBottom ] [ HH.text "Bottom" ]
              ])
            "Sheet.sheet [ side Right ] [ ... ]"
        ]
    ]

-- Render overlay modals when open
renderOverlays :: forall m. State -> H.ComponentHTML Action () m
renderOverlays state =
  HH.div_
    [ if state.dialogOpen then renderDialog else HH.text ""
    , if state.sheetOpen then renderSheet state.sheetDirection else HH.text ""
    ]

renderDialog :: forall m. H.ComponentHTML Action () m
renderDialog =
  HH.div_
    [ -- Backdrop
      HH.div 
        [ HP.class_ (H.ClassName "modal-backdrop")
        , HE.onClick \_ -> CloseDialog
        ] 
        []
    -- Content
    , HH.div
        [ HP.class_ (H.ClassName "modal-content") ]
        [ HH.button
            [ HP.class_ (H.ClassName "modal-close")
            , HE.onClick \_ -> CloseDialog
            ]
            [ HH.text "×" ]
        , HH.h2
            [ HP.class_ (H.ClassName "text-xl font-bold mb-4 gradient-text") ]
            [ HH.text "Dialog Title" ]
        , HH.p
            [ HP.class_ (H.ClassName "text-white/70 mb-6") ]
            [ HH.text "This is a modal dialog. Click outside or the X to close." ]
        , HH.div
            [ HP.class_ (H.ClassName "flex gap-3 justify-end") ]
            [ Button.button [ Button.variant Button.Outline, Button.onClick \_ -> CloseDialog ] [ HH.text "Cancel" ]
            , Button.button [ Button.onClick \_ -> CloseDialog ] [ HH.text "Confirm" ]
            ]
        ]
    ]

renderSheet :: forall m. SheetDirection -> H.ComponentHTML Action () m
renderSheet dir =
  let
    dirClass = case dir of
      SheetRight -> "sheet-right"
      SheetLeft -> "sheet-left"
      SheetTop -> "sheet-top"
      SheetBottom -> "sheet-bottom"
    dirLabel = case dir of
      SheetRight -> "Right"
      SheetLeft -> "Left"
      SheetTop -> "Top"
      SheetBottom -> "Bottom"
  in
    HH.div_
      [ -- Backdrop
        HH.div 
          [ HP.class_ (H.ClassName "sheet-backdrop")
          , HE.onClick \_ -> CloseSheet
          ] 
          []
      -- Content
      , HH.div
          [ HP.class_ (H.ClassName $ "sheet-content " <> dirClass) ]
          [ HH.button
              [ HP.class_ (H.ClassName "modal-close")
              , HE.onClick \_ -> CloseSheet
              ]
              [ HH.text "×" ]
          , HH.h2
              [ HP.class_ (H.ClassName "text-xl font-bold mb-4 gradient-text") ]
              [ HH.text $ "Sheet from " <> dirLabel ]
          , HH.p
              [ HP.class_ (H.ClassName "text-white/70 mb-6") ]
              [ HH.text "Sheets can slide in from any direction. Perfect for forms, filters, or detailed views." ]
          , HH.div
              [ HP.class_ (H.ClassName "space-y-4") ]
              [ HH.div_
                  [ HH.label [ HP.class_ (H.ClassName "text-sm text-white/60 block mb-2") ] [ HH.text "Name" ]
                  , HH.input [ HP.class_ (H.ClassName "glass-input w-full"), HP.placeholder "Enter name..." ]
                  ]
              , HH.div_
                  [ HH.label [ HP.class_ (H.ClassName "text-sm text-white/60 block mb-2") ] [ HH.text "Email" ]
                  , HH.input [ HP.class_ (H.ClassName "glass-input w-full"), HP.placeholder "Enter email..." ]
                  ]
              , Button.button [ Button.className "w-full", Button.onClick \_ -> CloseSheet ] [ HH.text "Save Changes" ]
              ]
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // icon library
-- ═══════════════════════════════════════════════════════════════════════════════

renderIconLibrary :: forall m. H.ComponentHTML Action () m
renderIconLibrary =
  HH.div
    [ HP.class_ (H.ClassName "max-w-6xl mx-auto animate-fade-in") ]
    [ HH.h1
        [ HP.class_ (H.ClassName "text-3xl font-bold mb-2") ]
        [ HH.text "Icon Library" ]
    , HH.p
        [ HP.class_ (H.ClassName "text-white/60 mb-8") ]
        [ HH.text "Hydrogen icons with multiple sizes. Tree-shakeable — only imported icons are bundled." ]
    
    -- Size reference
    , HH.div
        [ HP.class_ (H.ClassName "glass-card p-6 mb-8") ]
        [ HH.h2
            [ HP.class_ (H.ClassName "text-lg font-semibold mb-4") ]
            [ HH.text "Sizes" ]
        , HH.div
            [ HP.class_ (H.ClassName "flex items-end gap-6") ]
            [ iconWithLabel "Xs" (Icon.check [ I.size I.Xs ])
            , iconWithLabel "Sm" (Icon.check [ I.size I.Sm ])
            , iconWithLabel "Md" (Icon.check [ I.size I.Md ])
            , iconWithLabel "Lg" (Icon.check [ I.size I.Lg ])
            , iconWithLabel "Xl" (Icon.check [ I.size I.Xl ])
            , iconWithLabel "Xxl" (Icon.check [ I.size I.Xxl ])
            ]
        ]
    
    -- Actions
    , iconSection "Actions" 
        [ iconItem "check" (Icon.check [])
        , iconItem "x" (Icon.x [])
        , iconItem "plus" (Icon.plus [])
        , iconItem "minus" (Icon.minus [])
        , iconItem "edit" (Icon.edit [])
        , iconItem "trash" (Icon.trash [])
        , iconItem "copy" (Icon.copy [])
        , iconItem "save" (Icon.save [])
        , iconItem "download" (Icon.download [])
        , iconItem "upload" (Icon.upload [])
        , iconItem "search" (Icon.search [])
        , iconItem "filter" (Icon.filter [])
        , iconItem "refresh" (Icon.refresh [])
        , iconItem "undo" (Icon.undo [])
        , iconItem "redo" (Icon.redo [])
        ]
    
    -- Arrows
    , iconSection "Arrows"
        [ iconItem "arrowUp" (Icon.arrowUp [])
        , iconItem "arrowDown" (Icon.arrowDown [])
        , iconItem "arrowLeft" (Icon.arrowLeft [])
        , iconItem "arrowRight" (Icon.arrowRight [])
        , iconItem "chevronUp" (Icon.chevronUp [])
        , iconItem "chevronDown" (Icon.chevronDown [])
        , iconItem "chevronLeft" (Icon.chevronLeft [])
        , iconItem "chevronRight" (Icon.chevronRight [])
        , iconItem "chevronsUp" (Icon.chevronsUp [])
        , iconItem "chevronsDown" (Icon.chevronsDown [])
        , iconItem "chevronsLeft" (Icon.chevronsLeft [])
        , iconItem "chevronsRight" (Icon.chevronsRight [])
        , iconItem "externalLink" (Icon.externalLink [])
        ]
    
    -- Status
    , iconSection "Status"
        [ iconItem "alertCircle" (Icon.alertCircle [])
        , iconItem "alertTriangle" (Icon.alertTriangle [])
        , iconItem "info" (Icon.info [])
        , iconItem "helpCircle" (Icon.helpCircle [])
        , iconItem "checkCircle" (Icon.checkCircle [])
        , iconItem "xCircle" (Icon.xCircle [])
        , iconItem "clock" (Icon.clock [])
        , iconItem "loader" (Icon.loader [])
        ]
    
    -- Objects
    , iconSection "Objects"
        [ iconItem "file" (Icon.file [])
        , iconItem "folder" (Icon.folder [])
        , iconItem "folderOpen" (Icon.folderOpen [])
        , iconItem "image" (Icon.image [])
        , iconItem "video" (Icon.video [])
        , iconItem "music" (Icon.music [])
        , iconItem "document" (Icon.document [])
        , iconItem "archive" (Icon.archive [])
        , iconItem "calendar" (Icon.calendar [])
        , iconItem "mail" (Icon.mail [])
        , iconItem "phone" (Icon.phone [])
        , iconItem "link" (Icon.link [])
        , iconItem "globe" (Icon.globe [])
        , iconItem "home" (Icon.home [])
        , iconItem "settings" (Icon.settings [])
        , iconItem "user" (Icon.user [])
        , iconItem "users" (Icon.users [])
        , iconItem "heart" (Icon.heart [])
        , iconItem "star" (Icon.star [])
        , iconItem "bookmark" (Icon.bookmark [])
        , iconItem "tag" (Icon.tag [])
        , iconItem "bell" (Icon.bell [])
        , iconItem "lock" (Icon.lock [])
        , iconItem "unlock" (Icon.unlock [])
        , iconItem "key" (Icon.key [])
        , iconItem "eye" (Icon.eye [])
        , iconItem "eyeOff" (Icon.eyeOff [])
        ]
    
    -- Media
    , iconSection "Media"
        [ iconItem "play" (Icon.play [])
        , iconItem "pause" (Icon.pause [])
        , iconItem "stop" (Icon.stop [])
        , iconItem "skipBack" (Icon.skipBack [])
        , iconItem "skipForward" (Icon.skipForward [])
        , iconItem "volume" (Icon.volume [])
        , iconItem "volumeX" (Icon.volumeX [])
        , iconItem "mic" (Icon.mic [])
        , iconItem "micOff" (Icon.micOff [])
        , iconItem "camera" (Icon.camera [])
        , iconItem "cameraOff" (Icon.cameraOff [])
        ]
    
    -- Layout
    , iconSection "Layout"
        [ iconItem "menu" (Icon.menu [])
        , iconItem "moreHorizontal" (Icon.moreHorizontal [])
        , iconItem "moreVertical" (Icon.moreVertical [])
        , iconItem "grid" (Icon.grid [])
        , iconItem "list" (Icon.list [])
        , iconItem "columns" (Icon.columns [])
        , iconItem "sidebar" (Icon.sidebar [])
        , iconItem "maximize" (Icon.maximize [])
        , iconItem "minimize" (Icon.minimize [])
        , iconItem "expand" (Icon.expand [])
        , iconItem "shrink" (Icon.shrink [])
        ]
    
    -- Data
    , iconSection "Data"
        [ iconItem "barChart" (Icon.barChart [])
        , iconItem "lineChart" (Icon.lineChart [])
        , iconItem "pieChart" (Icon.pieChart [])
        , iconItem "trendingUp" (Icon.trendingUp [])
        , iconItem "trendingDown" (Icon.trendingDown [])
        , iconItem "activity" (Icon.activity [])
        ]
    
    -- Misc
    , iconSection "Misc"
        [ iconItem "sun" (Icon.sun [])
        , iconItem "moon" (Icon.moon [])
        , iconItem "zap" (Icon.zap [])
        , iconItem "cloud" (Icon.cloud [])
        , iconItem "cloudOff" (Icon.cloudOff [])
        , iconItem "wifi" (Icon.wifi [])
        , iconItem "wifiOff" (Icon.wifiOff [])
        , iconItem "bluetooth" (Icon.bluetooth [])
        , iconItem "battery" (Icon.battery [])
        , iconItem "batteryLow" (Icon.batteryLow [])
        , iconItem "batteryCharging" (Icon.batteryCharging [])
        , iconItem "power" (Icon.power [])
        , iconItem "terminal" (Icon.terminal [])
        , iconItem "code" (Icon.code [])
        , iconItem "git" (Icon.git [])
        , iconItem "gitBranch" (Icon.gitBranch [])
        ]
    
    -- Usage footer
    , HH.div
        [ HP.class_ (H.ClassName "glass-card p-6 mt-8") ]
        [ HH.h2
            [ HP.class_ (H.ClassName "text-lg font-semibold mb-4") ]
            [ HH.text "Usage" ]
        , HH.div
            [ HP.class_ (H.ClassName "space-y-4") ]
            [ codeSnippet "Import"
                "import Hydrogen.Icon.Icons as Icon\nimport Hydrogen.Icon.Icon as I"
            , codeSnippet "Basic usage"
                "Icon.check []"
            , codeSnippet "With size"
                "Icon.check [ I.size I.Lg ]"
            , codeSnippet "With custom class"
                "Icon.check [ I.className \"text-green-500\" ]"
            , codeSnippet "With accessibility"
                "Icon.check [ I.ariaLabel \"Completed\" ]"
            , codeSnippet "Combined props"
                "Icon.alertCircle [ I.size I.Xl, I.className \"text-red-500\" ]"
            ]
        ]
    ]

-- | Helper to render a code snippet with label
codeSnippet :: forall w i. String -> String -> HH.HTML w i
codeSnippet label code =
  HH.div
    [ HP.class_ (H.ClassName "flex flex-col gap-1") ]
    [ HH.span
        [ HP.class_ (H.ClassName "text-xs text-white/50 font-medium") ]
        [ HH.text label ]
    , HH.pre
        [ HP.class_ (H.ClassName "bg-black/30 border border-white/10 rounded-lg px-4 py-3 font-mono text-sm text-white/80 overflow-x-auto") ]
        [ HH.text code ]
    ]

-- | Helper to render an icon section with title and grid
iconSection :: forall w i. String -> Array (HH.HTML w i) -> HH.HTML w i
iconSection title icons =
  HH.div
    [ HP.class_ (H.ClassName "mb-8") ]
    [ HH.h2
        [ HP.class_ (H.ClassName "text-lg font-semibold mb-4 text-white/80") ]
        [ HH.text title ]
    , HH.div
        [ HP.class_ (H.ClassName "grid grid-cols-4 sm:grid-cols-6 md:grid-cols-8 lg:grid-cols-10 gap-3") ]
        icons
    ]

-- | Helper to render a single icon with its name
iconItem :: forall w i. String -> HH.HTML w i -> HH.HTML w i
iconItem name icon =
  HH.div
    [ HP.class_ (H.ClassName "flex flex-col items-center gap-2 p-3 rounded-lg hover:bg-white/5 transition-colors cursor-default") ]
    [ HH.div
        [ HP.class_ (H.ClassName "text-white/90") ]
        [ icon ]
    , HH.span
        [ HP.class_ (H.ClassName "text-xs text-white/50 text-center truncate w-full") ]
        [ HH.text name ]
    ]

-- | Helper to render icon with size label
iconWithLabel :: forall w i. String -> HH.HTML w i -> HH.HTML w i
iconWithLabel label icon =
  HH.div
    [ HP.class_ (H.ClassName "flex flex-col items-center gap-2") ]
    [ HH.div
        [ HP.class_ (H.ClassName "text-white/90") ]
        [ icon ]
    , HH.span
        [ HP.class_ (H.ClassName "text-xs text-white/50") ]
        [ HH.text label ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // main
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import clearAppElement :: Effect Unit

main :: Effect Unit
main = HA.runHalogenAff do
  _ <- HA.awaitBody
  H.liftEffect clearAppElement
  appEl <- H.liftEffect do
    win <- window
    doc <- document win
    maybeEl <- getElementById "app" (toNonElementParentNode doc)
    el <- maybe (throw "Could not find #app element") pure maybeEl
    maybe (throw "#app is not an HTMLElement") pure (fromElement el)
  runUI component unit appEl
