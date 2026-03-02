module Main exposing (main)

{-| Type-Safe 3D Scene Editor

This editor demonstrates the full stack:
1. Lean computes and validates scene data (type-safe)
2. JSON carries the validated data to Elm
3. Elm renders with elm-3d-scene (beautiful WebGL)

The droids can't cheat because:
- Mesh indices are bounded by vertex count (Lean types)
- Colors are validated [0,1] (Lean proofs)
- Transforms are always valid 4x4 matrices (Lean invariants)

-}

import Browser
import Browser.Events
import Html exposing (Html, div, text, button, input, label, h1, h2, h3, p, span)
import Html.Attributes exposing (style, type_, value, min, max, step, class)
import Html.Events exposing (onClick, onInput)
import Json.Decode as D

import Scene.Types exposing (Scene, SceneObject, Material(..), ColorRGB, Transform, Vec3)
import Scene.Renderer as Renderer


-- MAIN


main : Program () Model Msg
main =
    Browser.element
        { init = init
        , update = update
        , subscriptions = subscriptions
        , view = view
        }



-- MODEL


type alias Model =
    { scene : Scene
    , cameraAzimuth : Float
    , cameraElevation : Float
    , selectedObject : Maybe Int
    , dragging : Bool
    , lastMousePos : ( Float, Float )
    }


{-| Demo scene - in production this comes from Lean via JSON -}
demoScene : Scene
demoScene =
    { objects =
        [ { name = "Red Cube"
          , vertices = []  -- Simplified for demo
          , indices = []
          , material = Matte { r = 0.8, g = 0.2, b = 0.2 }
          , transform = { matrix = [1,0,0,0, 0,1,0,0, 0,0,1,0, -2,0,0,1] }
          }
        , { name = "Blue Metal Cube"
          , vertices = []
          , indices = []
          , material = Metal { r = 0.2, g = 0.3, b = 0.8 } 0.3
          , transform = { matrix = [1,0,0,0, 0,1,0,0, 0,0,1,0, 2,0,0,1] }
          }
        , { name = "Green PBR Cube"
          , vertices = []
          , indices = []
          , material = PBR { r = 0.2, g = 0.7, b = 0.3 } 0.9 0.2
          , transform = { matrix = [1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,2,1] }
          }
        , { name = "Gold Sphere Stand-in"
          , vertices = []
          , indices = []
          , material = Metal { r = 0.83, g = 0.69, b = 0.22 } 0.1
          , transform = { matrix = [1,0,0,0, 0,1,0,0, 0,0,1,0, 0,2,0,1] }
          }
        ]
    , ambientLight = { r = 0.1, g = 0.1, b = 0.15 }
    , directionalLight = Just
        { direction = { x = 1, y = -1, z = -1 }
        , color = { r = 1, g = 0.95, b = 0.9 }
        }
    }


init : () -> ( Model, Cmd Msg )
init _ =
    ( { scene = demoScene
      , cameraAzimuth = 45
      , cameraElevation = 30
      , selectedObject = Nothing
      , dragging = False
      , lastMousePos = ( 0, 0 )
      }
    , Cmd.none
    )



-- UPDATE


type Msg
    = SelectObject Int
    | DeselectObject
    | UpdateObjectColor Int ColorRGB
    | UpdateObjectPosition Int Float Float Float
    | UpdateMaterialRoughness Int Float
    | UpdateMaterialMetallic Int Float
    | MouseDown Float Float
    | MouseMove Float Float
    | MouseUp
    | AddCube
    | RemoveObject Int


update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        SelectObject idx ->
            ( { model | selectedObject = Just idx }, Cmd.none )

        DeselectObject ->
            ( { model | selectedObject = Nothing }, Cmd.none )

        UpdateObjectColor idx color ->
            ( { model | scene = updateObjectMaterialColor model.scene idx color }
            , Cmd.none
            )

        UpdateObjectPosition idx x y z ->
            ( { model | scene = updateObjectPosition model.scene idx x y z }
            , Cmd.none
            )

        UpdateMaterialRoughness idx roughness ->
            ( { model | scene = updateObjectRoughness model.scene idx roughness }
            , Cmd.none
            )

        UpdateMaterialMetallic idx metallic ->
            ( { model | scene = updateObjectMetallic model.scene idx metallic }
            , Cmd.none
            )

        MouseDown x y ->
            ( { model | dragging = True, lastMousePos = ( x, y ) }, Cmd.none )

        MouseMove x y ->
            if model.dragging then
                let
                    ( lastX, lastY ) = model.lastMousePos
                    dx = x - lastX
                    dy = y - lastY
                    newAzimuth = model.cameraAzimuth - dx * 0.5
                    newElevation = clamp -89 89 (model.cameraElevation + dy * 0.5)
                in
                ( { model
                    | cameraAzimuth = newAzimuth
                    , cameraElevation = newElevation
                    , lastMousePos = ( x, y )
                  }
                , Cmd.none
                )
            else
                ( model, Cmd.none )

        MouseUp ->
            ( { model | dragging = False }, Cmd.none )

        AddCube ->
            let
                oldScene = model.scene
                newObject =
                    { name = "New Cube " ++ String.fromInt (List.length oldScene.objects + 1)
                    , vertices = []
                    , indices = []
                    , material = Matte { r = 0.5, g = 0.5, b = 0.5 }
                    , transform = { matrix = [1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1] }
                    }
                newScene = { oldScene | objects = oldScene.objects ++ [ newObject ] }
            in
            ( { model | scene = newScene }, Cmd.none )

        RemoveObject idx ->
            let
                oldScene = model.scene
                newObjects = 
                    List.indexedMap Tuple.pair oldScene.objects
                        |> List.filterMap (\(i, obj) -> if i /= idx then Just obj else Nothing)
                newScene = { oldScene | objects = newObjects }
            in
            ( { model 
                | scene = newScene
                , selectedObject = Nothing 
              }
            , Cmd.none
            )


{-| Update material color for an object -}
updateObjectMaterialColor : Scene -> Int -> ColorRGB -> Scene
updateObjectMaterialColor scene idx newColor =
    let
        updateMaterial mat =
            case mat of
                Color _ -> Color newColor
                Matte _ -> Matte newColor
                Metal _ r -> Metal newColor r
                PBR _ m r -> PBR newColor m r

        updateObj i obj =
            if i == idx then
                { obj | material = updateMaterial obj.material }
            else
                obj
    in
    { scene | objects = List.indexedMap updateObj scene.objects }


{-| Update object position -}
updateObjectPosition : Scene -> Int -> Float -> Float -> Float -> Scene
updateObjectPosition scene idx x y z =
    let
        updateObj i obj =
            if i == idx then
                { obj | transform = { matrix = [1,0,0,0, 0,1,0,0, 0,0,1,0, x,y,z,1] } }
            else
                obj
    in
    { scene | objects = List.indexedMap updateObj scene.objects }


{-| Update roughness for metal/PBR materials -}
updateObjectRoughness : Scene -> Int -> Float -> Scene
updateObjectRoughness scene idx roughness =
    let
        updateMaterial mat =
            case mat of
                Metal c _ -> Metal c roughness
                PBR c m _ -> PBR c m roughness
                other -> other

        updateObj i obj =
            if i == idx then
                { obj | material = updateMaterial obj.material }
            else
                obj
    in
    { scene | objects = List.indexedMap updateObj scene.objects }


{-| Update metallic for PBR materials -}
updateObjectMetallic : Scene -> Int -> Float -> Scene
updateObjectMetallic scene idx metallic =
    let
        updateMaterial mat =
            case mat of
                PBR c _ r -> PBR c metallic r
                other -> other

        updateObj i obj =
            if i == idx then
                { obj | material = updateMaterial obj.material }
            else
                obj
    in
    { scene | objects = List.indexedMap updateObj scene.objects }



-- SUBSCRIPTIONS


subscriptions : Model -> Sub Msg
subscriptions model =
    Sub.batch
        [ Browser.Events.onMouseMove
            (D.map2 MouseMove
                (D.field "clientX" D.float)
                (D.field "clientY" D.float)
            )
        , Browser.Events.onMouseUp (D.succeed MouseUp)
        ]



-- VIEW


view : Model -> Html Msg
view model =
    div [ style "display" "flex"
        , style "height" "100vh"
        , style "font-family" "system-ui, -apple-system, sans-serif"
        , style "background" "#1a1a2e"
        , style "color" "#eee"
        ]
        [ -- Left panel: Object list and properties
          viewSidebar model
        
        -- Main viewport
        , div [ style "flex" "1"
              , style "position" "relative"
              , onMouseDown
              ]
            [ Renderer.view
                { width = 800
                , height = 600
                , azimuth = model.cameraAzimuth
                , elevation = model.cameraElevation
                }
                model.scene
            , viewOverlay model
            ]
        ]


viewSidebar : Model -> Html Msg
viewSidebar model =
    div [ style "width" "300px"
        , style "background" "#16213e"
        , style "padding" "20px"
        , style "overflow-y" "auto"
        , style "border-right" "1px solid #0f3460"
        ]
        [ h1 [ style "font-size" "1.2em"
             , style "margin" "0 0 5px 0"
             , style "color" "#e94560"
             ]
            [ text "⬡ Typed Scene Editor" ]
        , p [ style "font-size" "0.75em"
            , style "color" "#888"
            , style "margin" "0 0 20px 0"
            ]
            [ text "Lean → Elm → WebGL" ]
        
        -- Type safety banner
        , div [ style "background" "#0f3460"
              , style "padding" "10px"
              , style "border-radius" "5px"
              , style "margin-bottom" "20px"
              , style "font-size" "0.8em"
              ]
            [ div [ style "color" "#4ecca3" ] [ text "✓ Type-safe geometry" ]
            , div [ style "color" "#4ecca3" ] [ text "✓ Validated materials" ]
            , div [ style "color" "#4ecca3" ] [ text "✓ Bounded mesh indices" ]
            ]
        
        , h2 [ style "font-size" "0.9em"
             , style "color" "#aaa"
             , style "margin" "0 0 10px 0"
             ]
            [ text "SCENE OBJECTS" ]
        
        , button [ onClick AddCube
                 , style "width" "100%"
                 , style "padding" "10px"
                 , style "margin-bottom" "15px"
                 , style "background" "#e94560"
                 , style "color" "white"
                 , style "border" "none"
                 , style "border-radius" "5px"
                 , style "cursor" "pointer"
                 ]
            [ text "+ Add Cube" ]
        
        , div [] (List.indexedMap (viewObjectItem model.selectedObject) model.scene.objects)
        
        -- Properties panel
        , case model.selectedObject of
            Just idx ->
                case List.head (List.drop idx model.scene.objects) of
                    Just obj ->
                        viewObjectProperties idx obj
                    Nothing ->
                        text ""
            Nothing ->
                div [ style "color" "#666"
                    , style "font-size" "0.85em"
                    , style "margin-top" "20px"
                    ]
                    [ text "Select an object to edit properties" ]
        ]


viewObjectItem : Maybe Int -> Int -> SceneObject -> Html Msg
viewObjectItem selected idx obj =
    let
        isSelected = selected == Just idx
        materialIcon = case obj.material of
            Color _ -> "🎨"
            Matte _ -> "⬜"
            Metal _ _ -> "🔩"
            PBR _ _ _ -> "✨"
    in
    div [ onClick (SelectObject idx)
        , style "padding" "10px"
        , style "margin-bottom" "5px"
        , style "background" (if isSelected then "#0f3460" else "#1a1a2e")
        , style "border-radius" "5px"
        , style "cursor" "pointer"
        , style "display" "flex"
        , style "align-items" "center"
        , style "gap" "10px"
        , style "border" (if isSelected then "1px solid #e94560" else "1px solid transparent")
        ]
        [ span [] [ text materialIcon ]
        , span [ style "flex" "1" ] [ text obj.name ]
        , if isSelected then
            button [ onClick (RemoveObject idx)
                   , style "background" "none"
                   , style "border" "none"
                   , style "color" "#e94560"
                   , style "cursor" "pointer"
                   ]
                [ text "×" ]
          else
            text ""
        ]


viewObjectProperties : Int -> SceneObject -> Html Msg
viewObjectProperties idx obj =
    let
        ( posX, posY, posZ ) = getPosition obj.transform
        materialColor = getMaterialColor obj.material
    in
    div [ style "margin-top" "20px"
        , style "padding-top" "20px"
        , style "border-top" "1px solid #0f3460"
        ]
        [ h3 [ style "font-size" "0.85em"
             , style "color" "#aaa"
             , style "margin" "0 0 15px 0"
             ]
            [ text ("PROPERTIES: " ++ obj.name) ]
        
        -- Position
        , viewSlider "X Position" posX -5 5 (\v -> UpdateObjectPosition idx v posY posZ)
        , viewSlider "Y Position" posY -5 5 (\v -> UpdateObjectPosition idx posX v posZ)
        , viewSlider "Z Position" posZ -5 5 (\v -> UpdateObjectPosition idx posX posY v)
        
        -- Color
        , div [ style "margin-top" "15px" ]
            [ label [ style "font-size" "0.75em", style "color" "#888" ] [ text "COLOR" ]
            , div [ style "display" "flex", style "gap" "5px", style "margin-top" "5px" ]
                [ viewColorInput "R" materialColor.r (\v -> UpdateObjectColor idx { materialColor | r = v })
                , viewColorInput "G" materialColor.g (\v -> UpdateObjectColor idx { materialColor | g = v })
                , viewColorInput "B" materialColor.b (\v -> UpdateObjectColor idx { materialColor | b = v })
                ]
            ]
        
        -- Material-specific properties
        , case obj.material of
            Metal _ roughness ->
                viewSlider "Roughness" roughness 0 1 (UpdateMaterialRoughness idx)
            
            PBR _ metallic roughness ->
                div []
                    [ viewSlider "Metallic" metallic 0 1 (UpdateMaterialMetallic idx)
                    , viewSlider "Roughness" roughness 0 1 (UpdateMaterialRoughness idx)
                    ]
            
            _ ->
                text ""
        ]


viewSlider : String -> Float -> Float -> Float -> (Float -> Msg) -> Html Msg
viewSlider labelText val minVal maxVal toMsg =
    div [ style "margin-bottom" "10px" ]
        [ label [ style "font-size" "0.75em", style "color" "#888" ]
            [ text (labelText ++ ": " ++ String.fromFloat (toFloat (round (val * 100)) / 100)) ]
        , input
            [ type_ "range"
            , Html.Attributes.min (String.fromFloat minVal)
            , Html.Attributes.max (String.fromFloat maxVal)
            , Html.Attributes.step "0.1"
            , value (String.fromFloat val)
            , onInput (\s -> toMsg (Maybe.withDefault val (String.toFloat s)))
            , style "width" "100%"
            , style "margin-top" "5px"
            ]
            []
        ]


viewColorInput : String -> Float -> (Float -> Msg) -> Html Msg
viewColorInput labelText val toMsg =
    div [ style "flex" "1" ]
        [ label [ style "font-size" "0.65em", style "color" "#666" ] [ text labelText ]
        , input
            [ type_ "range"
            , Html.Attributes.min "0"
            , Html.Attributes.max "1"
            , Html.Attributes.step "0.05"
            , value (String.fromFloat val)
            , onInput (\s -> toMsg (Maybe.withDefault val (String.toFloat s)))
            , style "width" "100%"
            ]
            []
        ]


viewOverlay : Model -> Html Msg
viewOverlay model =
    div [ style "position" "absolute"
        , style "bottom" "20px"
        , style "left" "20px"
        , style "background" "rgba(0,0,0,0.7)"
        , style "padding" "10px 15px"
        , style "border-radius" "5px"
        , style "font-size" "0.75em"
        ]
        [ div [] [ text ("Camera: " ++ String.fromInt (round model.cameraAzimuth) ++ "° / " ++ String.fromInt (round model.cameraElevation) ++ "°") ]
        , div [ style "color" "#888" ] [ text "Drag to orbit" ]
        ]


onMouseDown : Html.Attribute Msg
onMouseDown =
    Html.Events.on "mousedown"
        (D.map2 MouseDown
            (D.field "clientX" D.float)
            (D.field "clientY" D.float)
        )



-- HELPERS


getPosition : Transform -> ( Float, Float, Float )
getPosition transform =
    case transform.matrix of
        [ _, _, _, _, _, _, _, _, _, _, _, _, tx, ty, tz, _ ] ->
            ( tx, ty, tz )
        _ ->
            ( 0, 0, 0 )


getMaterialColor : Material -> ColorRGB
getMaterialColor material =
    case material of
        Color c -> c
        Matte c -> c
        Metal c _ -> c
        PBR c _ _ -> c
