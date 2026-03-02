module Example.Main where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))
import Web.DOM.ParentNode (QuerySelector(..))

import Radix.Pure.Dialog as Dialog
import Radix.Pure.Tabs as Tabs

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

data Action
  = HandleDialogOutput Dialog.Output
  | HandleTabsOutput Tabs.Output

type State =
  { dialogOpen :: Boolean
  , tabsValue :: String
  }

type Slots =
  ( dialog :: Dialog.Slot Unit
  , tabs :: Tabs.Slot Unit
  )

_dialog :: Proxy "dialog"
_dialog = Proxy

_tabs :: Proxy "tabs"
_tabs = Proxy

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall query input output m. MonadAff m => H.Component query input output m
component = H.mkComponent
  { initialState: \_ -> { dialogOpen: false, tabsValue: "overview" }
  , render
  , eval: H.mkEval H.defaultEval { handleAction = handleAction }
  }

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.class_ (HH.ClassName "space-y-8") ]
    [ -- Dialog Section
      HH.div
        [ HP.class_ (HH.ClassName "card bg-base-100 shadow-xl") ]
        [ HH.div
            [ HP.class_ (HH.ClassName "card-body") ]
            [ HH.h2 
                [ HP.class_ (HH.ClassName "card-title") ] 
                [ HH.text "Dialog Component" ]
            , HH.p_ 
                [ HH.text "Modal dialog with focus trap, scroll lock, and screen reader isolation." ]
            , HH.div
                [ HP.class_ (HH.ClassName "card-actions") ]
                [ HH.slot _dialog unit Dialog.component Dialog.defaultInput HandleDialogOutput ]
            , HH.div
                [ HP.class_ (HH.ClassName "badge badge-outline mt-2") ]
                [ HH.text $ "State: " <> if state.dialogOpen then "Open" else "Closed" ]
            ]
        ]
    
    -- Tabs Section
    , HH.div
        [ HP.class_ (HH.ClassName "card bg-base-100 shadow-xl") ]
        [ HH.div
            [ HP.class_ (HH.ClassName "card-body") ]
            [ HH.h2 
                [ HP.class_ (HH.ClassName "card-title") ] 
                [ HH.text "Tabs Component" ]
            , HH.p_ 
                [ HH.text "Keyboard-navigable tabs with full ARIA support." ]
            , HH.slot _tabs unit Tabs.component tabsInput HandleTabsOutput
            , HH.div
                [ HP.class_ (HH.ClassName "badge badge-outline mt-4") ]
                [ HH.text $ "Active: " <> state.tabsValue ]
            ]
        ]
    
    -- Features list
    , HH.div
        [ HP.class_ (HH.ClassName "card bg-base-100 shadow-xl") ]
        [ HH.div
            [ HP.class_ (HH.ClassName "card-body") ]
            [ HH.h2 
                [ HP.class_ (HH.ClassName "card-title") ] 
                [ HH.text "Features" ]
            , HH.ul
                [ HP.class_ (HH.ClassName "list-disc list-inside space-y-1") ]
                [ HH.li_ [ HH.text "Pure PureScript/Halogen - No React runtime" ]
                , HH.li_ [ HH.text "Focus trap with Tab loop" ]
                , HH.li_ [ HH.text "Scroll lock when dialog open" ]
                , HH.li_ [ HH.text "ARIA attributes for accessibility" ]
                , HH.li_ [ HH.text "Keyboard navigation (Escape, Arrow keys)" ]
                , HH.li_ [ HH.text "DaisyUI + Tailwind styling" ]
                ]
            ]
        ]
    ]
  where
  tabsInput = Tabs.defaultInput
    { tabs =
        [ { value: "overview", label: "Overview", disabled: false }
        , { value: "features", label: "Features", disabled: false }
        , { value: "api", label: "API", disabled: false }
        ]
    , defaultValue = Just "overview"
    }

handleAction :: forall output m. MonadAff m => Action -> H.HalogenM State Action Slots output m Unit
handleAction = case _ of
  HandleDialogOutput (Dialog.OpenChanged open) -> H.modify_ _ { dialogOpen = open }
  HandleDialogOutput _ -> pure unit
  HandleTabsOutput (Tabs.ValueChanged v) -> H.modify_ _ { tabsValue = v }

-- ═══════════════════════════════════════════════════════════════════════════════
-- MAIN
-- ═══════════════════════════════════════════════════════════════════════════════

main :: Effect Unit
main = HA.runHalogenAff do
  HA.awaitLoad
  mbElem <- HA.selectElement (QuerySelector "#app")
  case mbElem of
    Nothing -> HA.awaitBody >>= runUI component unit
    Just elem -> runUI component unit elem
