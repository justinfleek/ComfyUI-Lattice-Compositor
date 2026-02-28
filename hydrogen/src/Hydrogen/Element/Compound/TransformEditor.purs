-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // transform-editor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TransformEditor — Property panel for 2D and 3D transforms.
-- |
-- | Provides unified UI for editing transforms with clear visual differentiation
-- | between 2D operations (X, Y, rotation) and 3D operations (Z axis, perspective,
-- | gimbal controls).
-- |
-- | ## Design Philosophy
-- |
-- | At billion-agent scale, transform editing must be:
-- | - **Type-safe**: 2D and 3D are distinct types with distinct UI
-- | - **Bounded**: All values clamped to valid ranges
-- | - **Visual**: 3D includes gimbal preview, 2D shows transform origin
-- | - **Composable**: Each section can be used independently
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.TransformEditor as TE
-- | 
-- | -- 2D transform editor
-- | TE.transform2DEditor
-- |   [ TE.transform2D state.transform
-- |   , TE.onTransform2DChange UpdateTransform
-- |   ]
-- |
-- | -- 3D transform editor with gimbal
-- | TE.transform3DEditor
-- |   [ TE.transform3D state.transform3D
-- |   , TE.onTransform3DChange UpdateTransform3D
-- |   , TE.showGimbal true
-- |   ]
-- |
-- | -- Standalone sections
-- | TE.translateSection2D state.translate ChangeTranslate
-- | TE.rotateSection3D state.rotate ChangeRotate  -- shows gimbal
-- | ```
module Hydrogen.Element.Compound.TransformEditor
  ( -- * Complete Editors
    transform2DEditor
  , transform3DEditor
  
  -- * Individual Sections (2D)
  , translateSection2D
  , rotateSection2D
  , scaleSection2D
  , skewSection2D
  , originSection
  
  -- * Individual Sections (3D)
  , translateSection3D
  , rotateSection3D
  , scaleSection3D
  , perspectiveSection
  
  -- * Props
  , Transform2DEditorProps
  , Transform2DEditorProp
  , Transform3DEditorProps
  , Transform3DEditorProp
  , defaultProps2D
  , defaultProps3D
  
  -- * Prop Builders
  , transform2D
  , onTransform2DChange
  , transform3D
  , onTransform3DChange
  , showGimbal
  , showOriginPreview
  , compactMode
  , className
  ) where

import Prelude
  ( show
  , (<>)
  , ($)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (&&)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Transform as T2D
import Hydrogen.Schema.Geometry.Transform3D as T3D
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)
import Hydrogen.Element.Compound.PropertySection as Section

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Transform Editor properties
type Transform2DEditorProps msg =
  { transform :: Maybe T2D.Transform2D
  , onChange :: Maybe (T2D.Transform2D -> msg)
  , showOriginPreview :: Boolean
  , compact :: Boolean
  , className :: String
  }

-- | 2D property modifier
type Transform2DEditorProp msg = Transform2DEditorProps msg -> Transform2DEditorProps msg

-- | Default 2D properties
defaultProps2D :: forall msg. Transform2DEditorProps msg
defaultProps2D =
  { transform: Nothing
  , onChange: Nothing
  , showOriginPreview: true
  , compact: false
  , className: ""
  }

-- | 3D Transform Editor properties
type Transform3DEditorProps msg =
  { transform :: Maybe T3D.Transform3D
  , onChange :: Maybe (T3D.Transform3D -> msg)
  , showGimbal :: Boolean
  , compact :: Boolean
  , className :: String
  }

-- | 3D property modifier
type Transform3DEditorProp msg = Transform3DEditorProps msg -> Transform3DEditorProps msg

-- | Default 3D properties
defaultProps3D :: forall msg. Transform3DEditorProps msg
defaultProps3D =
  { transform: Nothing
  , onChange: Nothing
  , showGimbal: true
  , compact: false
  , className: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set 2D transform
transform2D :: forall msg. T2D.Transform2D -> Transform2DEditorProp msg
transform2D t props = props { transform = Just t }

-- | Set 2D change handler
onTransform2DChange :: forall msg. (T2D.Transform2D -> msg) -> Transform2DEditorProp msg
onTransform2DChange handler props = props { onChange = Just handler }

-- | Set 3D transform
transform3D :: forall msg. T3D.Transform3D -> Transform3DEditorProp msg
transform3D t props = props { transform = Just t }

-- | Set 3D change handler
onTransform3DChange :: forall msg. (T3D.Transform3D -> msg) -> Transform3DEditorProp msg
onTransform3DChange handler props = props { onChange = Just handler }

-- | Show gimbal preview for 3D rotation
showGimbal :: forall msg. Boolean -> Transform3DEditorProp msg
showGimbal g props = props { showGimbal = g }

-- | Show origin preview for 2D transforms
showOriginPreview :: forall msg. Boolean -> Transform2DEditorProp msg
showOriginPreview o props = props { showOriginPreview = o }

-- | Enable compact mode
compactMode :: forall a. { compact :: Boolean | a } -> { compact :: Boolean | a }
compactMode props = props { compact = true }

-- | Add custom class
className :: forall msg. String -> Transform2DEditorProp msg
className c props = props { className = props.className <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 2D complete editor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 2D Transform Editor
-- |
-- | Renders all 2D transform properties: translate, rotate, scale, skew, origin.
-- | Each section shows the appropriate controls with bounded values.
-- |
-- | Pure Element — can be rendered to any target.
transform2DEditor :: forall msg. Array (Transform2DEditorProp msg) -> E.Element msg
transform2DEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps2D propMods
    
    t = case props.transform of
      Just tr -> tr
      Nothing -> T2D.identityTransform
    
    T2D.Transform2D rec = t
  in
    E.div_
      [ E.classes 
          [ "transform-2d-editor"
          , "space-y-2"
          , props.className
          ]
      ]
      [ -- Position/Translate section
        Section.section
          [ Section.label "Position"
          , Section.isOpen true
          ]
          [ case rec.translate of
              Just tr -> 
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" (show $ T2D.getTranslateX tr) "px"
                  , numberField "Y" (show $ T2D.getTranslateY tr) "px"
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" "0" "px"
                  , numberField "Y" "0" "px"
                  ]
          ]
      
      -- Scale section
      , Section.section
          [ Section.label "Scale"
          , Section.isOpen true
          ]
          [ case rec.scale of
              Just sc ->
                E.div_
                  [ E.class_ "space-y-2" ]
                  [ E.div_
                      [ E.class_ "grid grid-cols-2 gap-2" ]
                      [ numberField "W" (show $ T2D.getScaleX sc) "%"
                      , numberField "H" (show $ T2D.getScaleY sc) "%"
                      ]
                  , linkedToggle (T2D.isUniformScale sc)
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "W" "100" "%"
                  , numberField "H" "100" "%"
                  ]
          ]
      
      -- Rotation section
      , Section.section
          [ Section.label "Rotation"
          , Section.isOpen true
          ]
          [ case rec.rotate of
              Just r ->
                numberField "Angle" (show $ unwrapDegrees $ T2D.getRotation r) "°"
              Nothing ->
                numberField "Angle" "0" "°"
          ]
      
      -- Skew section (collapsed by default)
      , Section.section
          [ Section.label "Skew"
          , Section.isOpen false
          ]
          [ case rec.skew of
              Just sk ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" (show $ T2D.getSkewX sk) "°"
                  , numberField "Y" (show $ T2D.getSkewY sk) "°"
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-2 gap-2" ]
                  [ numberField "X" "0" "°"
                  , numberField "Y" "0" "°"
                  ]
          ]
      
      -- Origin section with visual preview
      , Section.section
          [ Section.label "Transform Origin"
          , Section.isOpen false
          ]
          [ originPreview rec.origin props.showOriginPreview
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 3D complete editor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D Transform Editor
-- |
-- | Renders all 3D transform properties with gimbal control for rotation.
-- | Clearly differentiates from 2D by showing Z axis and perspective.
-- |
-- | Pure Element — can be rendered to any target.
transform3DEditor :: forall msg. Array (Transform3DEditorProp msg) -> E.Element msg
transform3DEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps3D propMods
    
    t = case props.transform of
      Just tr -> tr
      Nothing -> T3D.identity3D
    
    T3D.Transform3D rec = t
  in
    E.div_
      [ E.classes 
          [ "transform-3d-editor"
          , "space-y-2"
          , props.className
          ]
      ]
      [ -- 3D badge to differentiate from 2D
        E.div_
          [ E.class_ "flex items-center gap-2 mb-2" ]
          [ E.span_
              [ E.classes 
                  [ "inline-flex items-center"
                  , "px-2 py-0.5"
                  , "bg-blue-500/10 text-blue-500"
                  , "text-xs font-medium rounded"
                  ]
              ]
              [ E.text "3D" ]
          , E.span_
              [ E.class_ "text-xs text-muted-foreground" ]
              [ E.text "Z-axis and perspective enabled" ]
          ]
      
      -- Position section (X, Y, Z)
      , Section.section
          [ Section.label "Position"
          , Section.isOpen true
          ]
          [ case rec.translate of
              Just tr ->
                E.div_
                  [ E.class_ "grid grid-cols-3 gap-2" ]
                  [ numberField "X" (show $ T3D.getTranslate3DX tr) "px"
                  , numberField "Y" (show $ T3D.getTranslate3DY tr) "px"
                  , numberField3D "Z" (show $ T3D.getTranslate3DZ tr) "px"
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-3 gap-2" ]
                  [ numberField "X" "0" "px"
                  , numberField "Y" "0" "px"
                  , numberField3D "Z" "0" "px"
                  ]
          ]
      
      -- Rotation section with gimbal
      , Section.section
          [ Section.label "Rotation"
          , Section.isOpen true
          ]
          [ case rec.rotate of
              Just r ->
                E.div_
                  [ E.class_ "space-y-3" ]
                  [ -- Gimbal visualization
                    if props.showGimbal
                      then gimbalPreview 
                             (unwrapDegrees $ T3D.getRotateX r) 
                             (unwrapDegrees $ T3D.getRotateY r) 
                             (unwrapDegrees $ T3D.getRotateZ r)
                      else E.empty
                  -- Numeric inputs for precise control
                  , E.div_
                      [ E.class_ "grid grid-cols-3 gap-2" ]
                      [ numberFieldRotation "Pitch" (show $ unwrapDegrees $ T3D.getRotateX r)
                      , numberFieldRotation "Yaw" (show $ unwrapDegrees $ T3D.getRotateY r)
                      , numberFieldRotation "Roll" (show $ unwrapDegrees $ T3D.getRotateZ r)
                      ]
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "space-y-3" ]
                  [ if props.showGimbal then gimbalPreview 0.0 0.0 0.0 else E.empty
                  , E.div_
                      [ E.class_ "grid grid-cols-3 gap-2" ]
                      [ numberFieldRotation "Pitch" "0"
                      , numberFieldRotation "Yaw" "0"
                      , numberFieldRotation "Roll" "0"
                      ]
                  ]
          ]
      
      -- Scale section (X, Y, Z)
      , Section.section
          [ Section.label "Scale"
          , Section.isOpen true
          ]
          [ case rec.scale of
              Just sc ->
                E.div_
                  [ E.class_ "space-y-2" ]
                  [ E.div_
                      [ E.class_ "grid grid-cols-3 gap-2" ]
                      [ numberField "X" (show $ T3D.getScale3DX sc) "%"
                      , numberField "Y" (show $ T3D.getScale3DY sc) "%"
                      , numberField3D "Z" (show $ T3D.getScale3DZ sc) "%"
                      ]
                  , linkedToggle3D (isUniformScale3D sc)
                  ]
              Nothing ->
                E.div_
                  [ E.class_ "grid grid-cols-3 gap-2" ]
                  [ numberField "X" "100" "%"
                  , numberField "Y" "100" "%"
                  , numberField3D "Z" "100" "%"
                  ]
          ]
      
      -- Perspective section (3D only)
      , Section.section
          [ Section.label "Perspective"
          , Section.isOpen false
          ]
          [ perspectiveFields rec.perspective rec.perspectiveOrigin
          ]
      ]

-- | Helper for perspective fields
perspectiveFields :: forall msg. Maybe T3D.Perspective -> T3D.PerspectiveOrigin -> E.Element msg
perspectiveFields maybePerspective origin =
  let
    distanceStr = case maybePerspective of
      Just p -> show $ T3D.getPerspective p
      Nothing -> "1000"
    originX = show $ T3D.getPerspectiveOriginX origin
    originY = show $ T3D.getPerspectiveOriginY origin
  in
    E.div_
      [ E.class_ "space-y-2" ]
      [ numberField "Distance" distanceStr "px"
      , E.div_
          [ E.class_ "grid grid-cols-2 gap-2" ]
          [ numberField "Origin X" originX "%"
          , numberField "Origin Y" originY "%"
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // individual sections
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Translate section
translateSection2D :: forall msg. T2D.Translate -> (T2D.Translate -> msg) -> E.Element msg
translateSection2D tr _onChange =
  Section.section
    [ Section.label "Position" ]
    [ E.div_
        [ E.class_ "grid grid-cols-2 gap-2" ]
        [ numberField "X" (show $ T2D.getTranslateX tr) "px"
        , numberField "Y" (show $ T2D.getTranslateY tr) "px"
        ]
    ]

-- | 2D Rotate section
rotateSection2D :: forall msg. T2D.Rotate -> (T2D.Rotate -> msg) -> E.Element msg
rotateSection2D r _onChange =
  Section.section
    [ Section.label "Rotation" ]
    [ numberField "Angle" (show $ unwrapDegrees $ T2D.getRotation r) "°"
    ]

-- | 2D Scale section
scaleSection2D :: forall msg. T2D.Scale -> (T2D.Scale -> msg) -> E.Element msg
scaleSection2D sc _onChange =
  Section.section
    [ Section.label "Scale" ]
    [ E.div_
        [ E.class_ "grid grid-cols-2 gap-2" ]
        [ numberField "W" (show $ T2D.getScaleX sc) "%"
        , numberField "H" (show $ T2D.getScaleY sc) "%"
        ]
    ]

-- | 2D Skew section
skewSection2D :: forall msg. T2D.Skew -> (T2D.Skew -> msg) -> E.Element msg
skewSection2D sk _onChange =
  Section.section
    [ Section.label "Skew" ]
    [ E.div_
        [ E.class_ "grid grid-cols-2 gap-2" ]
        [ numberField "X" (show $ T2D.getSkewX sk) "°"
        , numberField "Y" (show $ T2D.getSkewY sk) "°"
        ]
    ]

-- | Origin section with visual preview
originSection :: forall msg. T2D.Origin -> (T2D.Origin -> msg) -> E.Element msg
originSection o _onChange =
  Section.section
    [ Section.label "Transform Origin" ]
    [ originPreview o true
    ]

-- | 3D Translate section
translateSection3D :: forall msg. T3D.Translate3D -> (T3D.Translate3D -> msg) -> E.Element msg
translateSection3D tr _onChange =
  Section.section
    [ Section.label "Position" ]
    [ E.div_
        [ E.class_ "grid grid-cols-3 gap-2" ]
        [ numberField "X" (show $ T3D.getTranslate3DX tr) "px"
        , numberField "Y" (show $ T3D.getTranslate3DY tr) "px"
        , numberField3D "Z" (show $ T3D.getTranslate3DZ tr) "px"
        ]
    ]

-- | 3D Rotate section with gimbal
rotateSection3D :: forall msg. T3D.Rotate3D -> (T3D.Rotate3D -> msg) -> E.Element msg
rotateSection3D r _onChange =
  Section.section
    [ Section.label "Rotation" ]
    [ gimbalPreview (unwrapDegrees $ T3D.getRotateX r) (unwrapDegrees $ T3D.getRotateY r) (unwrapDegrees $ T3D.getRotateZ r)
    , E.div_
        [ E.class_ "grid grid-cols-3 gap-2 mt-2" ]
        [ numberFieldRotation "Pitch" (show $ unwrapDegrees $ T3D.getRotateX r)
        , numberFieldRotation "Yaw" (show $ unwrapDegrees $ T3D.getRotateY r)
        , numberFieldRotation "Roll" (show $ unwrapDegrees $ T3D.getRotateZ r)
        ]
    ]

-- | 3D Scale section
scaleSection3D :: forall msg. T3D.Scale3D -> (T3D.Scale3D -> msg) -> E.Element msg
scaleSection3D sc _onChange =
  Section.section
    [ Section.label "Scale" ]
    [ E.div_
        [ E.class_ "grid grid-cols-3 gap-2" ]
        [ numberField "X" (show $ T3D.getScale3DX sc) "%"
        , numberField "Y" (show $ T3D.getScale3DY sc) "%"
        , numberField3D "Z" (show $ T3D.getScale3DZ sc) "%"
        ]
    ]

-- | Perspective section
perspectiveSection :: forall msg. T3D.Perspective -> (T3D.Perspective -> msg) -> E.Element msg
perspectiveSection p _onChange =
  Section.section
    [ Section.label "Perspective" ]
    [ numberField "Distance" (show $ T3D.getPerspective p) "px"
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // helper elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number field with label and unit
numberField :: forall msg. String -> String -> String -> E.Element msg
numberField labelText valueStr unit =
  E.div_
    [ E.class_ "flex flex-col gap-1" ]
    [ E.label_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text labelText ]
    , E.div_
        [ E.class_ "flex items-center" ]
        [ E.input_
            [ E.class_ "h-7 w-full rounded-l border border-input bg-background px-2 text-xs text-right focus:outline-none focus:ring-1 focus:ring-ring"
            , E.type_ "text"
            , E.value valueStr
            , E.attr "inputmode" "numeric"
            ]
        , E.span_
            [ E.class_ "h-7 px-2 flex items-center rounded-r border border-l-0 border-input bg-muted text-xs text-muted-foreground" ]
            [ E.text unit ]
        ]
    ]

-- | Number field for 3D values (blue tinted to indicate Z axis)
numberField3D :: forall msg. String -> String -> String -> E.Element msg
numberField3D labelText valueStr unit =
  E.div_
    [ E.class_ "flex flex-col gap-1" ]
    [ E.label_
        [ E.class_ "text-xs text-blue-500" ]
        [ E.text labelText ]
    , E.div_
        [ E.class_ "flex items-center" ]
        [ E.input_
            [ E.class_ "h-7 w-full rounded-l border border-blue-500/50 bg-blue-500/5 px-2 text-xs text-right focus:outline-none focus:ring-1 focus:ring-blue-500"
            , E.type_ "text"
            , E.value valueStr
            , E.attr "inputmode" "numeric"
            ]
        , E.span_
            [ E.class_ "h-7 px-2 flex items-center rounded-r border border-l-0 border-blue-500/50 bg-blue-500/10 text-xs text-blue-500" ]
            [ E.text unit ]
        ]
    ]

-- | Number field for rotation (with circular slider potential)
numberFieldRotation :: forall msg. String -> String -> E.Element msg
numberFieldRotation labelText valueStr =
  E.div_
    [ E.class_ "flex flex-col gap-1" ]
    [ E.label_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text labelText ]
    , E.div_
        [ E.class_ "flex items-center" ]
        [ E.input_
            [ E.class_ "h-7 w-full rounded-l border border-input bg-background px-2 text-xs text-right focus:outline-none focus:ring-1 focus:ring-ring"
            , E.type_ "text"
            , E.value valueStr
            , E.attr "inputmode" "numeric"
            ]
        , E.span_
            [ E.class_ "h-7 px-2 flex items-center rounded-r border border-l-0 border-input bg-muted text-xs text-muted-foreground" ]
            [ E.text "°" ]
        ]
    ]

-- | Check if 3D scale is uniform (same X, Y, Z)
isUniformScale3D :: T3D.Scale3D -> Boolean
isUniformScale3D sc = 
  let x = T3D.getScale3DX sc
      y = T3D.getScale3DY sc
      z = T3D.getScale3DZ sc
  in x == y && y == z

-- | Linked scale toggle
linkedToggle :: forall msg. Boolean -> E.Element msg
linkedToggle isLinked =
  E.div_
    [ E.class_ "flex items-center gap-2" ]
    [ E.button_
        [ E.classes 
            [ "flex items-center justify-center"
            , "w-6 h-6 rounded"
            , if isLinked then "bg-primary text-primary-foreground" else "bg-muted text-muted-foreground"
            ]
        , E.attr "type" "button"
        ]
        [ linkIcon ]
    , E.span_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text "Constrain proportions" ]
    ]

-- | Linked scale toggle for 3D
linkedToggle3D :: forall msg. Boolean -> E.Element msg
linkedToggle3D isLinked =
  E.div_
    [ E.class_ "flex items-center gap-2" ]
    [ E.button_
        [ E.classes 
            [ "flex items-center justify-center"
            , "w-6 h-6 rounded"
            , if isLinked then "bg-blue-500 text-white" else "bg-muted text-muted-foreground"
            ]
        , E.attr "type" "button"
        ]
        [ linkIcon ]
    , E.span_
        [ E.class_ "text-xs text-muted-foreground" ]
        [ E.text "Constrain proportions (3D)" ]
    ]

-- | Origin preview with 9-point grid
originPreview :: forall msg. T2D.Origin -> Boolean -> E.Element msg
originPreview o showPreview =
  let
    x = T2D.getOriginX o
    y = T2D.getOriginY o
  in
    E.div_
      [ E.class_ "space-y-2" ]
      [ -- Visual grid
        if showPreview
          then E.div_
            [ E.classes 
                [ "grid grid-cols-3 gap-1"
                , "w-20 h-20"
                , "border border-border rounded"
                , "p-1"
                ]
            ]
            [ originDot (x < 17.0) (y < 17.0)
            , originDot (x >= 17.0) (y < 17.0)
            , originDot (x > 83.0) (y < 17.0)
            , originDot (x < 17.0) (y >= 17.0)
            , originDot (x >= 17.0) (y >= 17.0)
            , originDot (x > 83.0) (y >= 17.0)
            , originDot (x < 17.0) (y > 83.0)
            , originDot (x >= 17.0) (y > 83.0)
            , originDot (x > 83.0) (y > 83.0)
            ]
          else E.empty
      -- Numeric inputs
      , E.div_
          [ E.class_ "grid grid-cols-2 gap-2" ]
          [ numberField "X" (show x) "%"
          , numberField "Y" (show y) "%"
          ]
      ]

-- | Origin dot
originDot :: forall msg. Boolean -> Boolean -> E.Element msg
originDot xMatch _yMatch =
  let
    isActive = xMatch
  in
    E.div_
      [ E.classes 
          [ "w-5 h-5 rounded-full"
          , "flex items-center justify-center"
          , "cursor-pointer"
          , if isActive then "bg-primary" else "bg-muted hover:bg-muted-foreground/20"
          ]
      ]
      []

-- | Gimbal preview widget
-- |
-- | Visual 3D orientation indicator showing pitch, yaw, roll as three rings.
-- | Runtime will make this interactive for drag-to-rotate.
gimbalPreview :: forall msg. Number -> Number -> Number -> E.Element msg
gimbalPreview pitch yaw roll =
  E.div_
    [ E.classes 
        [ "gimbal-preview"
        , "relative"
        , "w-24 h-24"
        , "mx-auto"
        , "border border-border rounded-full"
        , "bg-muted/20"
        ]
    , E.dataAttr "gimbal" "true"
    , E.dataAttr "pitch" (show pitch)
    , E.dataAttr "yaw" (show yaw)
    , E.dataAttr "roll" (show roll)
    ]
    [ -- Pitch ring (X-axis, red)
      E.div_
        [ E.classes 
            [ "absolute inset-2"
            , "border-2 border-red-500/50 rounded-full"
            , "pointer-events-none"
            ]
        , E.attr "style" ("transform: rotateX(" <> show pitch <> "deg)")
        ]
        []
    -- Yaw ring (Y-axis, green)  
    , E.div_
        [ E.classes 
            [ "absolute inset-4"
            , "border-2 border-green-500/50 rounded-full"
            , "pointer-events-none"
            ]
        , E.attr "style" ("transform: rotateY(" <> show yaw <> "deg)")
        ]
        []
    -- Roll ring (Z-axis, blue)
    , E.div_
        [ E.classes 
            [ "absolute inset-6"
            , "border-2 border-blue-500/50 rounded-full"
            , "pointer-events-none"
            ]
        , E.attr "style" ("transform: rotateZ(" <> show roll <> "deg)")
        ]
        []
    -- Center reference
    , E.div_
        [ E.classes 
            [ "absolute"
            , "left-1/2 top-1/2"
            , "-translate-x-1/2 -translate-y-1/2"
            , "w-2 h-2"
            , "bg-foreground rounded-full"
            ]
        ]
        []
    -- Axis labels
    , E.span_ [ E.class_ "absolute -top-5 left-1/2 -translate-x-1/2 text-[10px] text-red-500" ] [ E.text "P" ]
    , E.span_ [ E.class_ "absolute top-1/2 -right-5 -translate-y-1/2 text-[10px] text-green-500" ] [ E.text "Y" ]
    , E.span_ [ E.class_ "absolute -bottom-5 left-1/2 -translate-x-1/2 text-[10px] text-blue-500" ] [ E.text "R" ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Link icon for proportional scaling
linkIcon :: forall msg. E.Element msg
linkIcon =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "width" "14"
    , E.attr "height" "14"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.path_ [ E.attr "d" "M10 13a5 5 0 0 0 7.54.54l3-3a5 5 0 0 0-7.07-7.07l-1.72 1.71" ]
    , E.path_ [ E.attr "d" "M14 11a5 5 0 0 0-7.54-.54l-3 3a5 5 0 0 0 7.07 7.07l1.71-1.71" ]
    ]
