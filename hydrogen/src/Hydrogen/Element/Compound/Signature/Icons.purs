-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // component // signature // icons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Signature Icons — SVG icons as pure Element data.
-- |
-- | Icons for signature pad toolbar: eraser, undo, clear (trash), pen.
-- | All icons are 18x18 with stroke-based rendering for consistent styling.

module Hydrogen.Element.Compound.Signature.Icons
  ( -- * Toolbar Icons
    eraserIcon
  , undoIcon
  , trashIcon
  , penIcon
  , colorPickerIcon
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Eraser icon — for eraser mode toggle.
eraserIcon :: forall msg. E.Element msg
eraserIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "18"
    , E.attr "height" "18"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.path_
        [ E.attr "d" "M20 20H9.2l-6.1-6.1a1.5 1.5 0 0 1 0-2.1L15 3.3a1.5 1.5 0 0 1 2.1 0l6.1 6.1a1.5 1.5 0 0 1 0 2.1L17 17.7" ]
    , E.path_
        [ E.attr "d" "M12 12l3-3" ]
    ]

-- | Undo icon — for undo last stroke.
undoIcon :: forall msg. E.Element msg
undoIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "18"
    , E.attr "height" "18"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.path_
        [ E.attr "d" "M3 7v6h6" ]
    , E.path_
        [ E.attr "d" "M21 17a9 9 0 0 0-9-9 9 9 0 0 0-6 2.3L3 13" ]
    ]

-- | Trash icon — for clear signature.
trashIcon :: forall msg. E.Element msg
trashIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "18"
    , E.attr "height" "18"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.polyline_
        [ E.attr "points" "3 6 5 6 21 6" ]
    , E.path_
        [ E.attr "d" "M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2" ]
    ]

-- | Pen icon — for pen mode indicator.
penIcon :: forall msg. E.Element msg
penIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "18"
    , E.attr "height" "18"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.path_
        [ E.attr "d" "M12 19l7-7 3 3-7 7-3-3z" ]
    , E.path_
        [ E.attr "d" "M18 13l-1.5-7.5L2 2l3.5 14.5L13 18l5-5z" ]
    , E.path_
        [ E.attr "d" "M2 2l7.586 7.586" ]
    , E.circle_
        [ E.attr "cx" "11"
        , E.attr "cy" "11"
        , E.attr "r" "2"
        ]
    ]

-- | Color picker icon — for color selection.
colorPickerIcon :: forall msg. E.Element msg
colorPickerIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "18"
    , E.attr "height" "18"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.circle_
        [ E.attr "cx" "13.5"
        , E.attr "cy" "6.5"
        , E.attr "r" "0.5"
        ]
    , E.circle_
        [ E.attr "cx" "17.5"
        , E.attr "cy" "10.5"
        , E.attr "r" "0.5"
        ]
    , E.circle_
        [ E.attr "cx" "8.5"
        , E.attr "cy" "7.5"
        , E.attr "r" "0.5"
        ]
    , E.circle_
        [ E.attr "cx" "6.5"
        , E.attr "cy" "12.5"
        , E.attr "r" "0.5"
        ]
    , E.path_
        [ E.attr "d" "M12 2C6.5 2 2 6.5 2 12s4.5 10 10 10c.926 0 1.648-.746 1.648-1.688 0-.437-.18-.835-.437-1.125-.29-.289-.438-.652-.438-1.125a1.64 1.64 0 0 1 1.668-1.668h1.996c3.051 0 5.555-2.503 5.555-5.555C21.965 6.012 17.461 2 12 2z" ]
    ]
