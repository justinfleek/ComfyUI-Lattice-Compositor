-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // motion // property // property-link
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PropertyLink — Property Connection/Expression Handle
-- |
-- | A draggable handle for creating links between layer properties.
-- | The core of motion graphics expression systems (like After Effects).
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Motion.Property.PropertyLink as Link
-- |
-- | -- Unlinked property
-- | Link.propertyLink
-- |   [ Link.layerId "layer-1"
-- |   , Link.propertyPath "transform.position.x"
-- |   , Link.onLink HandleLink
-- |   ]
-- |
-- | -- Linked property
-- | Link.propertyLink
-- |   [ Link.layerId "layer-1"
-- |   , Link.propertyPath "transform.position.x"
-- |   , Link.linkedTo (Just { layerId: "layer-2", property: "transform.position.x" })
-- |   , Link.onLink HandleLink
-- |   , Link.onUnlink HandleUnlink
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Motion.Property.PropertyLink
  ( -- * Component
    propertyLink
    
  -- * Props
  , PropertyLinkProps
  , PropertyLinkProp
  , LinkTarget
  , defaultProps
  
  -- * Prop Builders
  , layerId
  , propertyPath
  , linkedTo
  , onLink
  , onUnlink
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), isJust)

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Target of a property link
type LinkTarget =
  { layerId :: String
  , property :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | PropertyLink properties
type PropertyLinkProps msg =
  { layerId :: String          -- Source layer ID
  , propertyPath :: String     -- Source property path
  , linkedTo :: Maybe LinkTarget  -- Target if linked
  , onLink :: Maybe (LinkTarget -> msg)  -- Called when link established
  , onUnlink :: Maybe msg      -- Called when link removed
  }

-- | Property modifier function
type PropertyLinkProp msg = PropertyLinkProps msg -> PropertyLinkProps msg

-- | Default properties
defaultProps :: forall msg. PropertyLinkProps msg
defaultProps =
  { layerId: ""
  , propertyPath: ""
  , linkedTo: Nothing
  , onLink: Nothing
  , onUnlink: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set source layer ID
layerId :: forall msg. String -> PropertyLinkProp msg
layerId id props = props { layerId = id }

-- | Set source property path
propertyPath :: forall msg. String -> PropertyLinkProp msg
propertyPath path props = props { propertyPath = path }

-- | Set linked target
linkedTo :: forall msg. Maybe LinkTarget -> PropertyLinkProp msg
linkedTo target props = props { linkedTo = target }

-- | Link handler
onLink :: forall msg. (LinkTarget -> msg) -> PropertyLinkProp msg
onLink handler props = props { onLink = Just handler }

-- | Unlink handler
onUnlink :: forall msg. msg -> PropertyLinkProp msg
onUnlink handler props = props { onUnlink = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | PropertyLink component
-- |
-- | A draggable handle for creating property links.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- |
-- | The visual appearance changes based on link state:
-- | - Unlinked: Gray dot with crosshairs
-- | - Linked: Green dot with connection lines
propertyLink :: forall msg. Array (PropertyLinkProp msg) -> E.Element msg
propertyLink propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    hasLink = isJust props.linkedTo
    
    -- Container styles
    containerStyles =
      [ E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      ]
    
    -- Link handle (the draggable part)
    linkHandle =
      E.div_
        [ E.class_ "link-handle"
        , E.style "width" "16px"
        , E.style "height" "16px"
        , E.style "cursor" "crosshair"
        , E.style "color" (if hasLink then "#2ecc71" else "#666")
        , E.style "transition" "color 0.15s, transform 0.15s"
        , E.style "user-select" "none"
        , E.dataAttr "link-source" "true"
        , E.dataAttr "link-layer-id" props.layerId
        , E.dataAttr "link-property" props.propertyPath
        ]
        [ linkIcon hasLink ]
    
    -- Clear button (shown when linked)
    clearBtn = if hasLink
      then
        [ E.button_
            [ E.class_ "clear-link-btn"
            , E.style "width" "14px"
            , E.style "height" "14px"
            , E.style "padding" "0"
            , E.style "border" "none"
            , E.style "background" "#e74c3c"
            , E.style "color" "white"
            , E.style "border-radius" "50%"
            , E.style "font-size" "12px"
            , E.style "line-height" "1"
            , E.style "cursor" "pointer"
            , E.style "display" "flex"
            , E.style "align-items" "center"
            , E.style "justify-content" "center"
            , E.title "Remove link"
            ]
            [ E.text "×" ]
        ]
      else []
  in
    E.div_
      (containerStyles <> [ E.class_ "property-link-container" ])
      ([ linkHandle ] <> clearBtn)

-- | Link icon (changes based on state)
linkIcon :: forall msg. Boolean -> E.Element msg
linkIcon hasLink =
  E.svg_
    [ E.class_ "link-icon"
    , E.attr "viewBox" "0 0 16 16"
    , E.style "width" "100%"
    , E.style "height" "100%"
    ]
    ( [ -- Center dot (always present)
        E.circle_ 
          [ E.attr "cx" "8"
          , E.attr "cy" "8"
          , E.attr "r" "3"
          , E.attr "fill" "currentColor"
          ]
      ] <> (if hasLink then linkedPaths else unlinkedPaths)
    )

-- | Crosshair paths for unlinked state
unlinkedPaths :: forall msg. Array (E.Element msg)
unlinkedPaths =
  [ E.path_
      [ E.attr "d" "M8 5 L8 2 M8 11 L8 14 M5 8 L2 8 M11 8 L14 8"
      , E.attr "stroke" "currentColor"
      , E.attr "stroke-width" "1.5"
      , E.attr "fill" "none"
      ]
  ]

-- | Connection lines for linked state
linkedPaths :: forall msg. Array (E.Element msg)
linkedPaths =
  [ E.path_
      [ E.attr "d" "M11 5 L14 2 M11 11 L14 14"
      , E.attr "stroke" "currentColor"
      , E.attr "stroke-width" "1.5"
      , E.attr "fill" "none"
      ]
  ]
