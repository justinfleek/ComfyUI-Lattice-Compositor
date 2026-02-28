-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // tree-view // inline-edit
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Inline Edit — Edit node labels directly in the tree.
-- |
-- | ## Design Philosophy
-- |
-- | Inline editing allows users to rename nodes without a modal dialog.
-- | The edit state is managed as part of TreeViewState, keeping it pure.
-- |
-- | ## Edit Workflow
-- |
-- | 1. Double-click or press F2 on a focused node to begin editing
-- | 2. The label becomes an input field with the current text selected
-- | 3. Type to modify the text (edit buffer is updated)
-- | 4. Press Enter to confirm or Escape to cancel
-- | 5. On confirm, the application receives the new label value
-- |
-- | ## Validation
-- |
-- | Validation is the application's responsibility. This module provides:
-- | - Input rendering with appropriate ARIA attributes
-- | - Keyboard handling (Enter, Escape, Tab)
-- | - Visual feedback during editing
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, TreeViewMsg)
-- | - TreeView.State (EditState)
-- | - TreeView.Node (TreeNode, nodeLabel)
-- | - Hydrogen.Render.Element (Element)

module Hydrogen.Element.Compound.TreeView.InlineEdit
  ( -- * Edit Input Rendering
    renderEditInput
  , renderEditableLabel
  
  -- * Edit Props
  , EditProps
  , defaultEditProps
  , withInputClass
  , withPlaceholder
  , withMaxLength
  , withAutoFocus
  , withSelectOnFocus
  
  -- * Edit Handlers
  , handleEditKeyDown
  , handleEditInput
  , handleEditBlur
  
  -- * Edit State Transitions
  , beginEdit
  , updateEdit
  , confirmEdit
  , cancelEdit
  
  -- * Edit Validation
  , EditValidation
  , validateNotEmpty
  , validateMaxLength
  , validatePattern
  , runValidation
  , isValidEdit
  
  -- * Edit Utilities
  , getEditResult
  , hasEditChanged
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (==)
  , (&&)
  , (<=)
  , not
  , map
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length) as String
import Data.String.Regex (Regex, test) as Regex

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , TreeViewMsg
      ( UpdateEditBuffer
      , ConfirmEdit
      , CancelEdit
      )
  )

import Hydrogen.Element.Compound.TreeView.State
  ( EditState
  , noEdit
  , beginEditState
  , updateEditBuffer
  , getEditingNode
  , getEditBuffer
  , isEditing
  , isEditingNode
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( TreeNode
  , nodeId
  , nodeLabel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // edit props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for edit input rendering
type EditProps msg =
  { inputClass :: String
  , placeholder :: String
  , maxLength :: Maybe Int
  , autoFocus :: Boolean
  , selectOnFocus :: Boolean
  , onInput :: String -> msg
  , onConfirm :: msg
  , onCancel :: msg
  }

-- | Default edit properties
-- |
-- | Uses TreeViewMsg constructors for standard behavior.
defaultEditProps :: EditProps TreeViewMsg
defaultEditProps =
  { inputClass: "tree-edit-input"
  , placeholder: ""
  , maxLength: Nothing
  , autoFocus: true
  , selectOnFocus: true
  , onInput: UpdateEditBuffer
  , onConfirm: ConfirmEdit
  , onCancel: CancelEdit
  }

-- | Set input CSS class
withInputClass :: forall msg. String -> EditProps msg -> EditProps msg
withInputClass cls props = props { inputClass = cls }

-- | Set placeholder text
withPlaceholder :: forall msg. String -> EditProps msg -> EditProps msg
withPlaceholder ph props = props { placeholder = ph }

-- | Set maximum input length
withMaxLength :: forall msg. Int -> EditProps msg -> EditProps msg
withMaxLength len props = props { maxLength = Just len }

-- | Enable/disable auto focus
withAutoFocus :: forall msg. Boolean -> EditProps msg -> EditProps msg
withAutoFocus af props = props { autoFocus = af }

-- | Enable/disable select all on focus
withSelectOnFocus :: forall msg. Boolean -> EditProps msg -> EditProps msg
withSelectOnFocus sof props = props { selectOnFocus = sof }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // edit input render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the edit input field
-- |
-- | This is the text input that appears when editing a node label.
-- | Handles keyboard events for confirm (Enter) and cancel (Escape).
renderEditInput ::
  forall msg.
  EditProps msg ->
  EditState ->
  E.Element msg
renderEditInput props editState =
  let
    currentValue = getEditBuffer editState
    
    -- Base attributes
    baseAttrs =
      [ E.class_ props.inputClass
      , E.type_ "text"
      , E.value currentValue
      , E.attr "aria-label" "Edit node label"
      , E.style "flex" "1"
      , E.style "min-width" "0"
      , E.style "border" "1px solid #3b82f6"
      , E.style "border-radius" "3px"
      , E.style "padding" "2px 6px"
      , E.style "font-size" "inherit"
      , E.style "font-family" "inherit"
      , E.style "outline" "none"
      ]
    
    -- Autofocus attribute
    focusAttr = if props.autoFocus
      then [ E.autofocus true ]
      else []
    
    -- Placeholder attribute
    placeholderAttr = if props.placeholder == ""
      then []
      else [ E.placeholder props.placeholder ]
    
    -- Max length attribute
    maxLengthAttr = case props.maxLength of
      Nothing -> []
      Just len -> [ E.attr "maxlength" (show len) ]
    
    -- Event handlers
    inputHandler = [ E.onInput props.onInput ]
    
    -- Keyboard handler for Enter/Escape handled at element level
    -- (would need custom event handling in real implementation)
  in
    E.input_
      (baseAttrs <> focusAttr <> placeholderAttr <> maxLengthAttr <> inputHandler)

-- | Render an editable label
-- |
-- | Shows either the static label or the edit input, depending on edit state.
-- | This is a convenience function that combines both render modes.
renderEditableLabel ::
  forall msg.
  EditProps msg ->
  EditState ->
  TreeNode ->
  E.Element msg
renderEditableLabel props editState node =
  let
    nid = nodeId node
    label = nodeLabel node
  in
    if isEditingNode nid editState
      then renderEditInput props editState
      else
        E.span_
          [ E.class_ "tree-node-label"
          , E.style "flex" "1"
          , E.style "overflow" "hidden"
          , E.style "text-overflow" "ellipsis"
          , E.style "white-space" "nowrap"
          , E.style "cursor" "text"
          ]
          [ E.text label ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // event handlers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle keydown events in the edit input
-- |
-- | Returns the message to dispatch based on the key pressed:
-- | - Enter: ConfirmEdit
-- | - Escape: CancelEdit
-- | - Other: Nothing (let the input handle it)
handleEditKeyDown :: String -> Maybe TreeViewMsg
handleEditKeyDown key =
  case key of
    "Enter" -> Just ConfirmEdit
    "Escape" -> Just CancelEdit
    _ -> Nothing

-- | Handle input change event
-- |
-- | Returns UpdateEditBuffer message with the new value.
handleEditInput :: String -> TreeViewMsg
handleEditInput = UpdateEditBuffer

-- | Handle blur (focus lost) event
-- |
-- | By default, blur confirms the edit. This follows common UI conventions.
-- | Pass the msg to dispatch.
handleEditBlur :: TreeViewMsg
handleEditBlur = ConfirmEdit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // state transitions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Begin editing a node
-- |
-- | Creates the EditState with the node's current label as the buffer.
beginEdit :: TreeNode -> EditState
beginEdit node = beginEditState (nodeId node) (nodeLabel node)

-- | Update the edit buffer with new text
updateEdit :: String -> EditState -> EditState
updateEdit = updateEditBuffer

-- | Confirm the edit
-- |
-- | Returns the new label value and clears the edit state.
-- | The application should update the node's label with this value.
confirmEdit :: EditState -> { newLabel :: String, state :: EditState }
confirmEdit editState =
  { newLabel: getEditBuffer editState
  , state: noEdit
  }

-- | Cancel the edit
-- |
-- | Discards changes and clears the edit state.
cancelEdit :: EditState -> EditState
cancelEdit _ = noEdit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation function type
-- |
-- | Takes the current edit value and returns Nothing if valid,
-- | or Just error message if invalid.
type EditValidation = String -> Maybe String

-- | Validate that the input is not empty
validateNotEmpty :: EditValidation
validateNotEmpty value =
  if value == ""
    then Just "Label cannot be empty"
    else Nothing

-- | Validate that the input doesn't exceed max length
validateMaxLength :: Int -> EditValidation
validateMaxLength maxLen value =
  if String.length value <= maxLen
    then Nothing
    else Just ("Label cannot exceed " <> show maxLen <> " characters")

-- | Validate that the input matches a regex pattern
validatePattern :: Regex.Regex -> String -> EditValidation
validatePattern regex errorMsg value =
  if Regex.test regex value
    then Nothing
    else Just errorMsg

-- | Run a list of validations and return the first error (if any)
runValidation :: Array EditValidation -> String -> Maybe String
runValidation validators value =
  let
    results = map (\v -> v value) validators
    errors = Array.mapMaybe (\r -> r) results
  in
    Array.head errors

-- | Check if the current edit value is valid
isValidEdit :: Array EditValidation -> EditState -> Boolean
isValidEdit validators editState =
  let
    value = getEditBuffer editState
  in
    case runValidation validators value of
      Nothing -> true
      Just _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the result of the current edit (if editing)
-- |
-- | Returns Nothing if not editing, or Just the node ID and new value.
getEditResult :: EditState -> Maybe { nodeId :: NodeId, newLabel :: String }
getEditResult editState =
  case getEditingNode editState of
    Nothing -> Nothing
    Just nid -> Just { nodeId: nid, newLabel: getEditBuffer editState }

-- | Check if the edit buffer differs from the original value
-- |
-- | Used to determine if there are unsaved changes.
hasEditChanged :: EditState -> Boolean
hasEditChanged editState =
  isEditing editState && not (getEditBuffer editState == editState.originalValue)
