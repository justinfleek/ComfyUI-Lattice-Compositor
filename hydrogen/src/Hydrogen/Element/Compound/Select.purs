-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // select
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Select/Combobox Component
-- |
-- | A feature-rich select component with search, keyboard navigation,
-- | single/multi-select modes, and option groups.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Select as Select
-- |
-- | -- Basic single select
-- | Select.select
-- |   [ Select.options [ Select.option "apple" "Apple"
-- |                    , Select.option "banana" "Banana"
-- |                    ]
-- |   , Select.selectedValue "apple"
-- |   , Select.onSelectValue HandleSelect
-- |   ]
-- |
-- | -- Multi-select with search
-- | Select.select
-- |   [ Select.options [ Select.option "red" "Red"
-- |                    , Select.option "green" "Green"
-- |                    , Select.option "blue" "Blue"
-- |                    ]
-- |   , Select.multiSelect true
-- |   , Select.selectedValues ["red", "blue"]
-- |   , Select.searchable true
-- |   , Select.onSelectMultiple HandleMultiSelect
-- |   ]
-- |
-- | -- With option groups
-- | Select.select
-- |   [ Select.optionGroups
-- |       [ Select.optionGroup "Fruits"
-- |           [ Select.option "apple" "Apple"
-- |           , Select.option "banana" "Banana"
-- |           ]
-- |       , Select.optionGroup "Vegetables"
-- |           [ Select.option "carrot" "Carrot"
-- |           , Select.option "broccoli" "Broccoli"
-- |           ]
-- |       ]
-- |   ]
-- | ```
module Hydrogen.Element.Compound.Select
  ( -- * Select Component
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
    -- * Props
  , SelectProps
  , SelectProp
  , defaultProps
    -- * Prop Builders
  , options
  , optionGroups
  , selectedValue
  , selectedValues
  , placeholder
  , selectDisabled
  , searchable
  , multiSelect
  , isOpen
  , selectClassName
  , onSelectValue
  , onSelectMultiple
  , onOpenChange
  , onSearchChange
    -- * State Types
  , SelectState
  , initialState
  ) where

import Prelude
  ( show
  , not
  , map
  , (<>)
  , (==)
  , (&&)
  )

import Data.Array (foldl, filter, length, null, concatMap, find, elem)
import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))
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

-- | Create an option with metadata (e.g., description, icon key)
optionWithMeta :: String -> String -> String -> SelectOption
optionWithMeta val lbl metaVal = { value: val, label: lbl, disabled: false, meta: Just metaVal }

-- | Create an option group
optionGroup :: String -> Array SelectOption -> SelectOptionGroup
optionGroup lbl opts = { label: lbl, options: opts }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Internal state for controlled components
type SelectState =
  { isOpen :: Boolean
  , searchQuery :: String
  , highlightedIndex :: Int
  }

-- | Initial state
initialState :: SelectState
initialState =
  { isOpen: false
  , searchQuery: ""
  , highlightedIndex: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select properties
type SelectProps msg =
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
  , onSearchChange :: Maybe (String -> msg)
  }

-- | Property modifier
type SelectProp msg = SelectProps msg -> SelectProps msg

-- | Default select properties
defaultProps :: forall msg. SelectProps msg
defaultProps =
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
  , onSearchChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set available options
options :: forall msg. Array SelectOption -> SelectProp msg
options opts props = props { options = opts }

-- | Set option groups (overrides flat options)
optionGroups :: forall msg. Array SelectOptionGroup -> SelectProp msg
optionGroups groups props = props { optionGroups = groups }

-- | Set selected value (single select mode)
selectedValue :: forall msg. String -> SelectProp msg
selectedValue v props = props { value = Just v }

-- | Set selected values (multi-select mode)
selectedValues :: forall msg. Array String -> SelectProp msg
selectedValues vs props = props { values = vs }

-- | Set placeholder text
placeholder :: forall msg. String -> SelectProp msg
placeholder p props = props { placeholder = p }

-- | Set disabled state
selectDisabled :: forall msg. Boolean -> SelectProp msg
selectDisabled d props = props { disabled = d }

-- | Enable search/filter functionality
searchable :: forall msg. Boolean -> SelectProp msg
searchable s props = props { searchable = s }

-- | Enable multi-select mode
multiSelect :: forall msg. Boolean -> SelectProp msg
multiSelect m props = props { multiSelect = m }

-- | Control open state (controlled mode)
isOpen :: forall msg. Boolean -> SelectProp msg
isOpen o props = props { open = Just o }

-- | Add custom class
selectClassName :: forall msg. String -> SelectProp msg
selectClassName c props = props { className = props.className <> " " <> c }

-- | Set select handler (single select)
onSelectValue :: forall msg. (String -> msg) -> SelectProp msg
onSelectValue handler props = props { onSelect = Just handler }

-- | Set select handler (multi-select)
onSelectMultiple :: forall msg. (Array String -> msg) -> SelectProp msg
onSelectMultiple handler props = props { onMultiSelect = Just handler }

-- | Set open state change handler
onOpenChange :: forall msg. (Boolean -> msg) -> SelectProp msg
onOpenChange handler props = props { onOpenChange = Just handler }

-- | Set search query change handler
onSearchChange :: forall msg. (String -> msg) -> SelectProp msg
onSearchChange handler props = props { onSearchChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base trigger button classes
triggerClasses :: String
triggerClasses =
  "flex h-10 w-full items-center justify-between rounded-md border border-input bg-background px-3 py-2 text-sm ring-offset-background placeholder:text-muted-foreground focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 disabled:cursor-not-allowed disabled:opacity-50"

-- | Content dropdown classes
contentClasses :: String
contentClasses =
  "relative z-50 max-h-96 min-w-[8rem] overflow-hidden rounded-md border bg-popover text-popover-foreground shadow-md animate-in fade-in-0 zoom-in-95"

-- | Item classes
itemClasses :: String
itemClasses =
  "relative flex w-full cursor-default select-none items-center rounded-sm py-1.5 pl-8 pr-2 text-sm outline-none focus:bg-accent focus:text-accent-foreground data-[disabled]:pointer-events-none data-[disabled]:opacity-50"

-- | Group label classes
groupLabelClasses :: String
groupLabelClasses =
  "py-1.5 pl-8 pr-2 text-sm font-semibold text-muted-foreground"

-- | Chevron down icon
chevronDown :: forall msg. E.Element msg
chevronDown =
  E.span_
    [ E.class_ "h-4 w-4 opacity-50" ]
    [ E.text "▼" ]

-- | Check icon for selected items
checkIcon :: forall msg. E.Element msg
checkIcon =
  E.span_
    [ E.class_ "absolute left-2 flex h-3.5 w-3.5 items-center justify-center" ]
    [ E.text "✓" ]

-- | Select trigger button
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
selectTrigger :: forall msg. Array (SelectProp msg) -> Array (E.Element msg) -> E.Element msg
selectTrigger propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    openState = case props.open of
      Just o -> o
      Nothing -> false
  in
    E.button_
      [ E.classes [ triggerClasses, props.className ]
      , E.type_ "button"
      , E.disabled props.disabled
      , E.role "combobox"
      , E.attr "aria-expanded" (show openState)
      , E.attr "aria-haspopup" "listbox"
      ]
      (children <> [ chevronDown ])

-- | Select content/dropdown
selectContent :: forall msg. Array (SelectProp msg) -> Array (E.Element msg) -> E.Element msg
selectContent propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
  in
    E.div_
      [ E.classes [ contentClasses, props.className ]
      , E.role "listbox"
      ]
      [ E.div_
          [ E.class_ "p-1" ]
          children
      ]

-- | Select item/option
selectItem :: forall msg. 
  { value :: String, selected :: Boolean, disabled :: Boolean } -> 
  Array (E.Element msg) -> 
  E.Element msg
selectItem opts children =
  let
    selectedClass = if opts.selected then "bg-accent text-accent-foreground" else ""
    disabledAttrs = if opts.disabled 
      then [ E.dataAttr "disabled" "true" ] 
      else []
    checkMark = if opts.selected then [ checkIcon ] else []
  in
    E.div_
      ([ E.classes [ itemClasses, selectedClass ]
      , E.role "option"
      , E.attr "aria-selected" (show opts.selected)
      , E.tabIndex 0
      ] <> disabledAttrs)
      (checkMark <> children)

-- | Select group container
selectGroup :: forall msg. Array (E.Element msg) -> E.Element msg
selectGroup children =
  E.div_
    [ E.role "group" ]
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

-- | Full select component (composing trigger + content)
select :: forall msg. Array (SelectProp msg) -> E.Element msg
select propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    openState = case props.open of
      Just o -> o
      Nothing -> false
    
    -- Get all options (from flat list or groups)
    allOptions = 
      if null props.optionGroups
        then props.options
        else concatMap _.options props.optionGroups
    
    -- Find selected option label for display
    selectedLabel = case props.value of
      Just v -> 
        case find (\o -> o.value == v) allOptions of
          Just opt -> opt.label
          Nothing -> props.placeholder
      Nothing -> 
        if props.multiSelect && not (null props.values)
          then show (length props.values) <> " selected"
          else props.placeholder
    
    -- Render a single option
    renderOpt :: SelectOption -> E.Element msg
    renderOpt opt =
      let
        isSelected = case props.value of
          Just v -> v == opt.value
          Nothing -> elem opt.value props.values
        
        clickHandler = case props.onSelect of
          Just handler -> [ E.onClick (handler opt.value) ]
          Nothing -> case props.onMultiSelect of
            Just handler -> 
              let 
                newValues = if isSelected
                  then filter (\v -> not (v == opt.value)) props.values
                  else Array.cons opt.value props.values
              in [ E.onClick (handler newValues) ]
            Nothing -> []
      in
        E.div_
          ([ E.classes [ itemClasses, if isSelected then "bg-accent" else "" ]
          , E.role "option"
          , E.attr "aria-selected" (show isSelected)
          , E.tabIndex 0
          ] <> clickHandler)
          [ if isSelected then checkIcon else E.empty
          , E.span_ [ E.class_ "ml-2" ] [ E.text opt.label ]
          ]
    
    -- Render option groups
    renderGroups :: Array (E.Element msg)
    renderGroups = 
      concatMap 
        (\grp -> 
          [ selectLabel grp.label ] <> map renderOpt grp.options
        ) 
        props.optionGroups
    
    -- Render flat options
    renderFlatOptions :: Array (E.Element msg)
    renderFlatOptions = map renderOpt props.options
    
    -- Search input (if searchable)
    searchInput :: Array (E.Element msg)
    searchInput = 
      if props.searchable
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
    
    -- Trigger click handler
    triggerClickHandler = case props.onOpenChange of
      Just handler -> [ E.onClick (handler (not openState)) ]
      Nothing -> []
    
    -- Dropdown content (only render if open)
    dropdownContent = 
      if openState
        then 
          [ E.div_
              [ E.classes [ "absolute mt-1 w-full", contentClasses ] ]
              (searchInput <>
                [ E.div_
                    [ E.class_ "max-h-60 overflow-auto p-1"
                    , E.role "listbox"
                    ]
                    (if null props.optionGroups
                      then renderFlatOptions
                      else renderGroups
                    )
                ]
              )
          ]
        else []
  in
    E.div_
      [ E.classes [ "relative", props.className ] ]
      ([ -- Trigger button
        E.button_
          ([ E.class_ triggerClasses
          , E.type_ "button"
          , E.disabled props.disabled
          , E.role "combobox"
          , E.attr "aria-expanded" (show openState)
          , E.attr "aria-haspopup" "listbox"
          ] <> triggerClickHandler)
          [ E.span_ [ E.class_ "truncate" ] [ E.text selectedLabel ]
          , chevronDown
          ]
      ] <> dropdownContent)
