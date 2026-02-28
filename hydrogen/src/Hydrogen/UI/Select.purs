-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // ui // select
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Select Component — Pure Element Version
-- |
-- | Searchable select/combobox with single/multi-select modes.
-- | Renders using the pure Element abstraction for target-agnostic UI.
-- |
-- | ## Features
-- |
-- | - Single and multi-select modes
-- | - Option groups with labels
-- | - Searchable/filterable options
-- | - Keyboard navigation ready
-- | - Accessible (ARIA combobox pattern)
-- |
-- | ## Usage with Halogen
-- |
-- | ```purescript
-- | import Hydrogen.UI.Select as Select
-- | import Hydrogen.Target.Halogen as TH
-- |
-- | mySelect :: Select.Element Action
-- | mySelect = Select.select
-- |   [ Select.options
-- |       [ Select.option "apple" "Apple"
-- |       , Select.option "banana" "Banana"
-- |       ]
-- |   , Select.value "apple"
-- |   , Select.onSelect HandleSelect
-- |   ]
-- |
-- | render :: State -> H.ComponentHTML Action Slots m
-- | render state = TH.toHalogen mySelect
-- | ```
-- |
-- | ## Multi-Select
-- |
-- | ```purescript
-- | Select.select
-- |   [ Select.options fruits
-- |   , Select.multiSelect true
-- |   , Select.values ["apple", "banana"]
-- |   , Select.onMultiSelect HandleMultiSelect
-- |   ]
-- | ```
module Hydrogen.UI.Select
  ( -- * Select Components
    select
  , selectTrigger
  , selectContent
  , selectItem
  , selectGroup
  , selectLabel
  , selectSeparator
  
  -- * Option Types
  , SelectOption
  , SelectOptionGroup
  , option
  , optionWithMeta
  , optionGroup
  
  -- * Configuration
  , SelectConfig
  , defaultConfig
  
  -- * Config Modifiers
  , options
  , optionGroups
  , value
  , values
  , placeholder
  , disabled
  , searchable
  , multiSelect
  , open
  , className
  , onSelect
  , onMultiSelect
  , onOpenChange
  ) where

import Prelude
  ( (<>)
  , (==)
  , (/=)
  , (&&)
  , not
  , map
  , show
  )

import Data.Array (foldl, filter, length, null, concatMap, elem, (:))
import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // option types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single selectable option
type SelectOption =
  { value :: String
  , label :: String
  , disabled :: Boolean
  , meta :: Maybe String
  }

-- | A group of options with a label
type SelectOptionGroup =
  { label :: String
  , options :: Array SelectOption
  }

-- | Create a simple option
option :: String -> String -> SelectOption
option val lbl = { value: val, label: lbl, disabled: false, meta: Nothing }

-- | Create an option with metadata
optionWithMeta :: String -> String -> String -> SelectOption
optionWithMeta val lbl meta = { value: val, label: lbl, disabled: false, meta: Just meta }

-- | Create an option group
optionGroup :: String -> Array SelectOption -> SelectOptionGroup
optionGroup lbl opts = { label: lbl, options: opts }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select configuration
type SelectConfig msg =
  { options :: Array SelectOption
  , optionGroups :: Array SelectOptionGroup
  , value :: Maybe String
  , values :: Array String
  , placeholder :: String
  , disabled :: Boolean
  , searchable :: Boolean
  , multiSelect :: Boolean
  , open :: Maybe Boolean
  , className :: String
  , onSelect :: Maybe (String -> msg)
  , onMultiSelect :: Maybe (Array String -> msg)
  , onOpenChange :: Maybe (Boolean -> msg)
  }

-- | Default select configuration
defaultConfig :: forall msg. SelectConfig msg
defaultConfig =
  { options: []
  , optionGroups: []
  , value: Nothing
  , values: []
  , placeholder: "Select..."
  , disabled: false
  , searchable: false
  , multiSelect: false
  , open: Nothing
  , className: ""
  , onSelect: Nothing
  , onMultiSelect: Nothing
  , onOpenChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // config modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration modifier type
type ConfigMod cfg = cfg -> cfg

-- | Set available options
options :: forall msg. Array SelectOption -> ConfigMod (SelectConfig msg)
options opts cfg = cfg { options = opts }

-- | Set option groups
optionGroups :: forall msg. Array SelectOptionGroup -> ConfigMod (SelectConfig msg)
optionGroups groups cfg = cfg { optionGroups = groups }

-- | Set selected value (single select)
value :: forall msg. String -> ConfigMod (SelectConfig msg)
value v cfg = cfg { value = Just v }

-- | Set selected values (multi-select)
values :: forall msg. Array String -> ConfigMod (SelectConfig msg)
values vs cfg = cfg { values = vs }

-- | Set placeholder text
placeholder :: forall msg. String -> ConfigMod (SelectConfig msg)
placeholder p cfg = cfg { placeholder = p }

-- | Set disabled state
disabled :: forall msg. Boolean -> ConfigMod (SelectConfig msg)
disabled d cfg = cfg { disabled = d }

-- | Enable search functionality
searchable :: forall msg. Boolean -> ConfigMod (SelectConfig msg)
searchable s cfg = cfg { searchable = s }

-- | Enable multi-select mode
multiSelect :: forall msg. Boolean -> ConfigMod (SelectConfig msg)
multiSelect m cfg = cfg { multiSelect = m }

-- | Control open state
open :: forall msg. Boolean -> ConfigMod (SelectConfig msg)
open o cfg = cfg { open = Just o }

-- | Add custom class
className :: forall msg. String -> ConfigMod (SelectConfig msg)
className c cfg = cfg { className = cfg.className <> " " <> c }

-- | Set select handler (single)
onSelect :: forall msg. (String -> msg) -> ConfigMod (SelectConfig msg)
onSelect handler cfg = cfg { onSelect = Just handler }

-- | Set select handler (multi)
onMultiSelect :: forall msg. (Array String -> msg) -> ConfigMod (SelectConfig msg)
onMultiSelect handler cfg = cfg { onMultiSelect = Just handler }

-- | Set open change handler
onOpenChange :: forall msg. (Boolean -> msg) -> ConfigMod (SelectConfig msg)
onOpenChange handler cfg = cfg { onOpenChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trigger button classes
triggerClasses :: String
triggerClasses =
  "flex h-10 w-full items-center justify-between rounded-md border " <>
  "border-input bg-background px-3 py-2 text-sm ring-offset-background " <>
  "placeholder:text-muted-foreground focus:outline-none focus:ring-2 " <>
  "focus:ring-ring focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Content dropdown classes
contentClasses :: String
contentClasses =
  "relative z-50 max-h-96 min-w-[8rem] overflow-hidden rounded-md border " <>
  "bg-popover text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95"

-- | Item classes
itemClasses :: String
itemClasses =
  "relative flex w-full cursor-default select-none items-center rounded-sm " <>
  "py-1.5 pl-8 pr-2 text-sm outline-none focus:bg-accent focus:text-accent-foreground " <>
  "data-[disabled]:pointer-events-none data-[disabled]:opacity-50"

-- | Group label classes
groupLabelClasses :: String
groupLabelClasses = "py-1.5 pl-8 pr-2 text-sm font-semibold text-muted-foreground"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chevron down icon
chevronDown :: forall msg. E.Element msg
chevronDown =
  E.span_
    [ E.class_ "h-4 w-4 opacity-50" ]
    [ E.text "\x25BC" ] -- Unicode down triangle

-- | Check icon for selected items
checkIcon :: forall msg. E.Element msg
checkIcon =
  E.span_
    [ E.class_ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ]
    [ E.text "\x2713" ] -- Unicode checkmark

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // primitive components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select trigger button (standalone)
selectTrigger :: forall msg.
  Array (ConfigMod (SelectConfig msg)) ->
  Array (E.Element msg) ->
  E.Element msg
selectTrigger configMods children =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
    isOpen = fromMaybe false cfg.open
  in
    E.button_
      ( [ E.class_ (triggerClasses <> " " <> cfg.className)
        , E.type_ "button"
        , E.attr "role" "combobox"
        , E.attr "aria-expanded" (show isOpen)
        , E.attr "aria-haspopup" "listbox"
        ]
        <> disabledAttr cfg.disabled
        <> openChangeHandler cfg
      )
      ( children <> [ chevronDown ] )

-- | Select content/dropdown (standalone)
selectContent :: forall msg.
  Array (ConfigMod (SelectConfig msg)) ->
  Array (E.Element msg) ->
  E.Element msg
selectContent configMods children =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
  in
    E.div_
      [ E.class_ (contentClasses <> " " <> cfg.className)
      , E.attr "role" "listbox"
      ]
      [ E.div_
          [ E.class_ "p-1" ]
          children
      ]

-- | Select item/option (standalone)
selectItem :: forall msg.
  { value :: String, selected :: Boolean, disabled :: Boolean } ->
  Array (E.Element msg) ->
  E.Element msg
selectItem opts children =
  let
    selectedClass = if opts.selected then "bg-accent text-accent-foreground" else ""
  in
    E.div_
      ( [ E.class_ (itemClasses <> " " <> selectedClass)
        , E.attr "role" "option"
        , E.attr "aria-selected" (show opts.selected)
        , E.tabIndex 0
        ]
        <> disabledDataAttr opts.disabled
      )
      ( (if opts.selected then [ checkIcon ] else []) <> children )

-- | Select group container
selectGroup :: forall msg. Array (E.Element msg) -> E.Element msg
selectGroup children =
  E.div_
    [ E.attr "role" "group" ]
    children

-- | Select group label
selectLabel :: forall msg. String -> E.Element msg
selectLabel labelText =
  E.div_
    [ E.class_ groupLabelClasses ]
    [ E.text labelText ]

-- | Select separator
selectSeparator :: forall msg. E.Element msg
selectSeparator =
  E.div_
    [ E.class_ "-mx-1 my-1 h-px bg-muted" ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // composed component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full select component
select :: forall msg. Array (ConfigMod (SelectConfig msg)) -> E.Element msg
select configMods =
  let
    cfg = foldl (\c f -> f c) defaultConfig configMods
    isOpen = fromMaybe false cfg.open
    
    -- Get all options (flat or from groups)
    allOptions =
      if null cfg.optionGroups
        then cfg.options
        else concatMap _.options cfg.optionGroups
    
    -- Selected label for display
    selectedLabel = getSelectedLabel cfg allOptions
    
    -- Render options based on structure
    renderedOptions =
      if null cfg.optionGroups
        then map (renderOption cfg) cfg.options
        else renderGroups cfg
  in
    E.div_
      [ E.class_ ("relative " <> cfg.className) ]
      [ -- Trigger button
        E.button_
          ( [ E.class_ triggerClasses
            , E.type_ "button"
            , E.attr "role" "combobox"
            , E.attr "aria-expanded" (show isOpen)
            , E.attr "aria-haspopup" "listbox"
            ]
            <> disabledAttr cfg.disabled
            <> openChangeHandler cfg
          )
          [ E.span_ [ E.class_ "truncate" ] [ E.text selectedLabel ]
          , chevronDown
          ]
      -- Dropdown (only if open)
      , if isOpen
          then renderDropdown cfg renderedOptions
          else E.empty
      ]

-- | Get display label for current selection
getSelectedLabel :: forall msg. SelectConfig msg -> Array SelectOption -> String
getSelectedLabel cfg allOptions =
  case cfg.value of
    Just v ->
      case Array.find (\o -> o.value == v) allOptions of
        Just opt -> opt.label
        Nothing -> cfg.placeholder
    Nothing ->
      if cfg.multiSelect && not (null cfg.values)
        then show (length cfg.values) <> " selected"
        else cfg.placeholder

-- | Render dropdown content
renderDropdown :: forall msg. SelectConfig msg -> Array (E.Element msg) -> E.Element msg
renderDropdown cfg renderedOptions =
  E.div_
    [ E.class_ ("absolute mt-1 w-full " <> contentClasses) ]
    ( searchInput cfg <>
      [ E.div_
          [ E.class_ "max-h-60 overflow-auto p-1"
          , E.attr "role" "listbox"
          ]
          renderedOptions
      ]
    )

-- | Search input (if searchable)
searchInput :: forall msg. SelectConfig msg -> Array (E.Element msg)
searchInput cfg =
  if cfg.searchable
    then
      [ E.div_
          [ E.class_ "flex items-center border-b px-3" ]
          [ E.input_
              [ E.class_ "flex h-10 w-full rounded-md bg-transparent py-3 text-sm outline-none placeholder:text-muted-foreground disabled:cursor-not-allowed disabled:opacity-50"
              , E.placeholder "Search..."
              , E.type_ "text"
              ]
          ]
      ]
    else []

-- | Render a single option with click handling
renderOption :: forall msg. SelectConfig msg -> SelectOption -> E.Element msg
renderOption cfg opt =
  let
    isSelected = case cfg.value of
      Just v -> v == opt.value
      Nothing -> elem opt.value cfg.values
    selectedClass = if isSelected then "bg-accent" else ""
  in
    E.div_
      ( [ E.class_ (itemClasses <> " " <> selectedClass)
        , E.attr "role" "option"
        , E.attr "aria-selected" (show isSelected)
        , E.tabIndex 0
        ]
        <> optionClickHandler cfg opt isSelected
      )
      [ if isSelected then checkIcon else E.empty
      , E.span_ [ E.class_ "ml-2" ] [ E.text opt.label ]
      ]

-- | Render option groups
renderGroups :: forall msg. SelectConfig msg -> Array (E.Element msg)
renderGroups cfg =
  concatMap
    (\grp -> [ selectLabel grp.label ] <> map (renderOption cfg) grp.options)
    cfg.optionGroups

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Disabled attribute
disabledAttr :: forall msg. Boolean -> Array (E.Attribute msg)
disabledAttr false = []
disabledAttr true = [ E.disabled true ]

-- | Data-disabled attribute for items
disabledDataAttr :: forall msg. Boolean -> Array (E.Attribute msg)
disabledDataAttr false = []
disabledDataAttr true = [ E.attr "data-disabled" "true" ]

-- | Open change click handler
openChangeHandler :: forall msg. SelectConfig msg -> Array (E.Attribute msg)
openChangeHandler cfg =
  case cfg.onOpenChange of
    Nothing -> []
    Just handler ->
      let isOpen = fromMaybe false cfg.open
      in [ E.onClick (handler (not isOpen)) ]

-- | Option click handler
optionClickHandler :: forall msg.
  SelectConfig msg ->
  SelectOption ->
  Boolean ->
  Array (E.Attribute msg)
optionClickHandler cfg opt isSelected =
  case cfg.onSelect of
    Just handler -> [ E.onClick (handler opt.value) ]
    Nothing ->
      case cfg.onMultiSelect of
        Just handler ->
          let
            newValues =
              if isSelected
                then filter (_ /= opt.value) cfg.values
                else opt.value : cfg.values
          in [ E.onClick (handler newValues) ]
        Nothing -> []
