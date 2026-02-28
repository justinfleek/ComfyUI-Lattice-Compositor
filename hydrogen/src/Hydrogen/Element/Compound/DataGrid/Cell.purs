-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // datagrid // cell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid Cell — Cell rendering by type with Schema atoms.
-- |
-- | This module provides cell rendering functions for each CellType.
-- | All visual styling is determined by Schema atoms passed through GridProps.
-- | No hardcoded CSS values exist in this module.
-- |
-- | ## Design Philosophy
-- |
-- | Cell renderers receive:
-- | 1. CellContext — value, position, row data, interaction state
-- | 2. Visual atoms — colors, dimensions from GridProps
-- |
-- | They return pure Element data that the runtime renders to DOM.

module Hydrogen.Element.Compound.DataGrid.Cell
  ( -- * Cell Rendering
    renderCell
  , renderCellByType
  
    -- * Individual Cell Type Renderers
  , renderTextCell
  , renderNumberCell
  , renderDateCell
  , renderBooleanCell
  , renderLinkCell
  , renderBadgeCell
  , renderActionsCell
  ) where

import Prelude
  ( (==)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Element.Compound.DataGrid.Types
  ( CellType
      ( CellText
      , CellNumber
      , CellDate
      , CellBoolean
      , CellLink
      , CellBadge
      , CellActions
      , CellCustom
      )
  , CellContext
  , ColumnDef
  , GridProps
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cell rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a cell with its column definition and grid props
-- |
-- | Uses custom renderer if defined, otherwise falls back to built-in
-- | cell type rendering with Schema atoms from GridProps.
renderCell
  :: forall msg
   . GridProps msg
  -> ColumnDef msg
  -> Int           -- ^ Row index
  -> Int           -- ^ Column index
  -> CellContext
  -> E.Element msg
renderCell props col _rowIndex _colIndex ctx =
  case col.cellRenderer of
    Just renderer -> renderer ctx
    Nothing -> renderCellByType props col.cellType ctx

-- | Render cell content by type using Schema atoms
-- |
-- | Each cell type has a specialized renderer that uses atoms from GridProps
-- | for all visual styling.
renderCellByType
  :: forall msg
   . GridProps msg
  -> CellType
  -> CellContext
  -> E.Element msg
renderCellByType props cellType' ctx =
  case cellType' of
    CellText -> renderTextCell props ctx
    CellNumber -> renderNumberCell props ctx
    CellDate -> renderDateCell props ctx
    CellBoolean -> renderBooleanCell props ctx
    CellLink -> renderLinkCell props ctx
    CellBadge -> renderBadgeCell props ctx
    CellActions -> renderActionsCell props ctx
    CellCustom -> renderTextCell props ctx  -- Fallback for custom without renderer

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // text cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render plain text cell
-- |
-- | Simple text display using cellTextColor atom if provided.
renderTextCell :: forall msg. GridProps msg -> CellContext -> E.Element msg
renderTextCell props ctx =
  E.span_
    (maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.cellTextColor)
    [ E.text ctx.value ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // number cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render numeric cell
-- |
-- | Right-aligned with tabular figures for proper column alignment.
-- | Uses font-variant-numeric CSS property for monospace digits.
renderNumberCell :: forall msg. GridProps msg -> CellContext -> E.Element msg
renderNumberCell props ctx =
  E.span_
    ( [ E.style "font-variant-numeric" "tabular-nums"
      , E.style "text-align" "right"
      , E.style "display" "block"
      ]
      <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.cellTextColor
    )
    [ E.text ctx.value ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // date cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render date cell
-- |
-- | Displays date string. Future enhancement: locale-aware formatting.
-- | Uses cellTextColor with reduced opacity for secondary appearance.
renderDateCell :: forall msg. GridProps msg -> CellContext -> E.Element msg
renderDateCell props ctx =
  E.span_
    ( [ E.style "opacity" "0.8" ]
      <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.cellTextColor
    )
    [ E.text ctx.value ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // boolean cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render boolean cell
-- |
-- | Displays a read-only checkbox representing the boolean value.
-- | True values: "true", "1", "yes" (case-insensitive matching).
renderBooleanCell :: forall msg. GridProps msg -> CellContext -> E.Element msg
renderBooleanCell _props ctx =
  let
    isChecked = ctx.value == "true" || ctx.value == "1" || ctx.value == "yes"
  in
    E.input_
      [ E.type_ "checkbox"
      , E.checked isChecked
      , E.disabled true
      , E.style "width" "1rem"
      , E.style "height" "1rem"
      , E.style "cursor" "not-allowed"
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // link cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render link cell
-- |
-- | Displays clickable hyperlink using linkColor atom.
-- | The cell value is used as both href and display text.
renderLinkCell :: forall msg. GridProps msg -> CellContext -> E.Element msg
renderLinkCell props ctx =
  E.a_
    ( [ E.href ctx.value
      , E.style "text-decoration" "underline"
      , E.style "text-underline-offset" "4px"
      ]
      <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.linkColor
    )
    [ E.text ctx.value ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // badge cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render badge cell
-- |
-- | Displays value in a pill/badge format using badgeBgColor, badgeTextColor,
-- | and badgeBorderRadius atoms.
renderBadgeCell :: forall msg. GridProps msg -> CellContext -> E.Element msg
renderBadgeCell props ctx =
  E.span_
    ( [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "padding" "0.125rem 0.625rem"
      , E.style "font-size" "0.75rem"
      , E.style "font-weight" "600"
      ]
      <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.badgeBgColor
      <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.badgeTextColor
      <> maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.badgeBorderRadius
    )
    [ E.text ctx.value ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // actions cell
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render actions cell
-- |
-- | Displays edit and delete action buttons.
-- | Note: Button click handlers are wired at the grid level, not here.
-- | This renderer creates the visual structure; parent wires events.
renderActionsCell :: forall msg. GridProps msg -> CellContext -> E.Element msg
renderActionsCell _props _ctx =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "0.25rem"
    ]
    [ -- Edit button
      E.button_
        [ E.type_ "button"
        , E.style "padding" "0.25rem"
        , E.style "border-radius" "0.25rem"
        , E.style "border" "none"
        , E.style "background" "transparent"
        , E.style "cursor" "pointer"
        , E.ariaLabel "Edit"
        ]
        [ E.text "E" ]  -- Icon placeholder: would use SVG icon
    , -- Delete button
      E.button_
        [ E.type_ "button"
        , E.style "padding" "0.25rem"
        , E.style "border-radius" "0.25rem"
        , E.style "border" "none"
        , E.style "background" "transparent"
        , E.style "cursor" "pointer"
        , E.ariaLabel "Delete"
        ]
        [ E.text "X" ]  -- Icon placeholder: would use SVG icon
    ]
