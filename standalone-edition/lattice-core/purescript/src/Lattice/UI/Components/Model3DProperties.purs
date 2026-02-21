-- | Model 3D Properties Panel Component
-- |
-- | Properties editor for 3D model and point cloud layers.
-- | Features:
-- | - Model info (source file, vertex/face count)
-- | - Transform: position, rotation, scale (uniform/non-uniform)
-- | - Material assignment
-- | - Display options: wireframe, bounding box, shadows
-- | - Point cloud specific: point size, color, vertex colors, attenuation
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/Model3DProperties.vue
module Lattice.UI.Components.Model3DProperties
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , Model3DLayerData
  , PointCloudLayerData
  ) where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..), fromMaybe)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)
import Lattice.UI.Utils as Utils

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { layerId :: String
  , layerType :: LayerType
  , layerData :: Maybe LayerDataUnion
  , transform :: Transform3D
  , availableMaterials :: Array MaterialInfo
  }

data LayerType = ModelLayer | PointCloudLayer

derive instance eqLayerType :: Eq LayerType

data LayerDataUnion
  = ModelData Model3DLayerData
  | PointCloudData PointCloudLayerData

type Model3DLayerData =
  { sourceFile :: String
  , vertexCount :: Maybe Int
  , faceCount :: Maybe Int
  , materialId :: Maybe String
  , wireframe :: Boolean
  , showBoundingBox :: Boolean
  , castShadows :: Boolean
  , receiveShadows :: Boolean
  }

type PointCloudLayerData =
  { sourceFile :: String
  , vertexCount :: Maybe Int
  , pointSize :: Number
  , pointColor :: String
  , useVertexColors :: Boolean
  , sizeAttenuation :: Boolean
  , materialId :: Maybe String
  , wireframe :: Boolean
  , showBoundingBox :: Boolean
  , castShadows :: Boolean
  , receiveShadows :: Boolean
  }

type Transform3D =
  { position :: Vec3
  , rotation :: Vec3
  , scale :: Vec3
  }

type Vec3 = { x :: Number, y :: Number, z :: Number }

type MaterialInfo =
  { id :: String
  , name :: String
  }

data Output
  = TransformUpdated Transform3D
  | MaterialAssigned (Maybe String)
  | DisplayOptionChanged DisplayOption Boolean
  | PointCloudSettingChanged PointCloudSetting
  | OpenMaterialEditorRequested

data DisplayOption
  = Wireframe
  | BoundingBox
  | CastShadows
  | ReceiveShadows

data PointCloudSetting
  = PointSize Number
  | PointColor String
  | UseVertexColors Boolean
  | SizeAttenuation Boolean

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { layerId :: String
  , layerType :: LayerType
  , layerData :: Maybe LayerDataUnion
  , transform :: Transform3D
  , availableMaterials :: Array MaterialInfo
  , expandedSections :: ExpandedSections
  , uniformScale :: Boolean
  , selectedMaterialId :: Maybe String
  -- Display options (local state synced from input)
  , wireframe :: Boolean
  , showBoundingBox :: Boolean
  , castShadows :: Boolean
  , receiveShadows :: Boolean
  -- Point cloud options
  , pointSize :: Number
  , pointColor :: String
  , useVertexColors :: Boolean
  , sizeAttenuation :: Boolean
  }

type ExpandedSections =
  { transform :: Boolean
  , material :: Boolean
  , display :: Boolean
  , pointCloud :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | ToggleSection String
  -- Transform
  | SetPositionX String | SetPositionY String | SetPositionZ String
  | SetRotationX String | SetRotationY String | SetRotationZ String
  | SetScaleX String | SetScaleY String | SetScaleZ String
  | ToggleUniformScale
  -- Material
  | SetMaterial String
  | OpenMaterialEditor
  -- Display
  | ToggleWireframe
  | ToggleBoundingBox
  | ToggleCastShadows
  | ToggleReceiveShadows
  -- Point cloud
  | SetPointSize String
  | SetPointColor String
  | ToggleVertexColors
  | ToggleSizeAttenuation

type Slots = ()

-- =============================================================================
--                                                                  // component
-- =============================================================================

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { layerId: input.layerId
  , layerType: input.layerType
  , layerData: input.layerData
  , transform: input.transform
  , availableMaterials: input.availableMaterials
  , expandedSections: defaultExpandedSections
  , uniformScale: true
  , selectedMaterialId: extractMaterialId input.layerData
  , wireframe: extractWireframe input.layerData
  , showBoundingBox: extractBoundingBox input.layerData
  , castShadows: extractCastShadows input.layerData
  , receiveShadows: extractReceiveShadows input.layerData
  , pointSize: extractPointSize input.layerData
  , pointColor: extractPointColor input.layerData
  , useVertexColors: extractUseVertexColors input.layerData
  , sizeAttenuation: extractSizeAttenuation input.layerData
  }

defaultExpandedSections :: ExpandedSections
defaultExpandedSections =
  { transform: true
  , material: true
  , display: false
  , pointCloud: true
  }

-- =============================================================================
--                                                           // data extractors
-- =============================================================================

extractMaterialId :: Maybe LayerDataUnion -> Maybe String
extractMaterialId = case _ of
  Just (ModelData d) -> d.materialId
  Just (PointCloudData d) -> d.materialId
  Nothing -> Nothing

extractWireframe :: Maybe LayerDataUnion -> Boolean
extractWireframe = case _ of
  Just (ModelData d) -> d.wireframe
  Just (PointCloudData d) -> d.wireframe
  Nothing -> false

extractBoundingBox :: Maybe LayerDataUnion -> Boolean
extractBoundingBox = case _ of
  Just (ModelData d) -> d.showBoundingBox
  Just (PointCloudData d) -> d.showBoundingBox
  Nothing -> false

extractCastShadows :: Maybe LayerDataUnion -> Boolean
extractCastShadows = case _ of
  Just (ModelData d) -> d.castShadows
  Just (PointCloudData d) -> d.castShadows
  Nothing -> true

extractReceiveShadows :: Maybe LayerDataUnion -> Boolean
extractReceiveShadows = case _ of
  Just (ModelData d) -> d.receiveShadows
  Just (PointCloudData d) -> d.receiveShadows
  Nothing -> true

extractPointSize :: Maybe LayerDataUnion -> Number
extractPointSize = case _ of
  Just (PointCloudData d) -> d.pointSize
  _ -> 2.0

extractPointColor :: Maybe LayerDataUnion -> String
extractPointColor = case _ of
  Just (PointCloudData d) -> d.pointColor
  _ -> "#ffffff"

extractUseVertexColors :: Maybe LayerDataUnion -> Boolean
extractUseVertexColors = case _ of
  Just (PointCloudData d) -> d.useVertexColors
  _ -> true

extractSizeAttenuation :: Maybe LayerDataUnion -> Boolean
extractSizeAttenuation = case _ of
  Just (PointCloudData d) -> d.sizeAttenuation
  _ -> true

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "model-3d-properties" ]
    , HP.attr (HH.AttrName "style") panelStyle
    ]
    [ renderInfoSection state
    , renderTransformSection state
    , renderMaterialSection state
    , renderDisplaySection state
    , if state.layerType == PointCloudLayer
        then renderPointCloudSection state
        else HH.text ""
    ]

renderInfoSection :: forall m. State -> H.ComponentHTML Action Slots m
renderInfoSection state =
  HH.div
    [ cls [ "property-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.span_ [ HH.text "3D Model Properties" ] ]
    , case state.layerData of
        Just dataUnion -> renderInfoRows dataUnion
        Nothing -> HH.text ""
    ]

renderInfoRows :: forall m. LayerDataUnion -> H.ComponentHTML Action Slots m
renderInfoRows dataUnion =
  let 
    sourceFile = case dataUnion of
      ModelData d -> d.sourceFile
      PointCloudData d -> d.sourceFile
    vertexCount = case dataUnion of
      ModelData d -> d.vertexCount
      PointCloudData d -> d.vertexCount
    faceCount = case dataUnion of
      ModelData d -> d.faceCount
      PointCloudData _ -> Nothing
  in HH.div [ cls [ "property-group" ] ]
    [ infoRow "Source" sourceFile
    , case vertexCount of
        Just vc -> infoRow "Vertices" (Utils.formatNumber 0 (Utils.toNumber vc))
        Nothing -> HH.text ""
    , case faceCount of
        Just fc -> infoRow "Faces" (Utils.formatNumber 0 (Utils.toNumber fc))
        Nothing -> HH.text ""
    ]

infoRow :: forall m. String -> String -> H.ComponentHTML Action Slots m
infoRow label value =
  HH.div [ cls [ "info-row" ], HP.attr (HH.AttrName "style") infoRowStyle ]
    [ HH.span [ cls [ "label" ], HP.attr (HH.AttrName "style") infoLabelStyle ] [ HH.text label ]
    , HH.span [ cls [ "value" ] ] [ HH.text value ]
    ]

renderTransformSection :: forall m. State -> H.ComponentHTML Action Slots m
renderTransformSection state =
  collapsibleSection "Transform" "transform" state.expandedSections.transform
    [ -- Position
      propertyGroup "Position"
        [ xyzInputs "position"
            [ { label: "X", value: state.transform.position.x, onInput: SetPositionX }
            , { label: "Y", value: state.transform.position.y, onInput: SetPositionY }
            , { label: "Z", value: state.transform.position.z, onInput: SetPositionZ }
            ]
        ]
    
    -- Rotation
    , propertyGroup "Rotation"
        [ xyzInputs "rotation"
            [ { label: "X", value: state.transform.rotation.x, onInput: SetRotationX }
            , { label: "Y", value: state.transform.rotation.y, onInput: SetRotationY }
            , { label: "Z", value: state.transform.rotation.z, onInput: SetRotationZ }
            ]
        ]
    
    -- Scale
    , propertyGroup "Scale"
        [ xyzInputs "scale"
            [ { label: "X", value: state.transform.scale.x, onInput: SetScaleX }
            , { label: "Y", value: state.transform.scale.y, onInput: SetScaleY }
            , { label: "Z", value: state.transform.scale.z, onInput: SetScaleZ }
            ]
        , checkboxRow "Uniform Scale" state.uniformScale ToggleUniformScale
        ]
    ]

renderMaterialSection :: forall m. State -> H.ComponentHTML Action Slots m
renderMaterialSection state =
  collapsibleSection "Material" "material" state.expandedSections.material
    [ propertyGroup "Assigned Material"
        [ HH.select
            [ cls [ "material-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueChange SetMaterial
            ]
            ([ HH.option [ HP.value "", HP.selected (state.selectedMaterialId == Nothing) ]
                 [ HH.text "None (Use Model Default)" ]
             ] <> map (materialOption state.selectedMaterialId) state.availableMaterials)
        ]
    , HH.button
        [ cls [ "action-btn" ]
        , HP.attr (HH.AttrName "style") actionBtnStyle
        , HE.onClick \_ -> OpenMaterialEditor
        ]
        [ HH.text "Open Material Editor" ]
    ]

materialOption :: forall m. Maybe String -> MaterialInfo -> H.ComponentHTML Action Slots m
materialOption selected mat =
  HH.option 
    [ HP.value mat.id, HP.selected (selected == Just mat.id) ]
    [ HH.text mat.name ]

renderDisplaySection :: forall m. State -> H.ComponentHTML Action Slots m
renderDisplaySection state =
  collapsibleSection "Display" "display" state.expandedSections.display
    [ checkboxRow "Show Wireframe" state.wireframe ToggleWireframe
    , checkboxRow "Show Bounding Box" state.showBoundingBox ToggleBoundingBox
    , checkboxRow "Cast Shadows" state.castShadows ToggleCastShadows
    , checkboxRow "Receive Shadows" state.receiveShadows ToggleReceiveShadows
    ]

renderPointCloudSection :: forall m. State -> H.ComponentHTML Action Slots m
renderPointCloudSection state =
  collapsibleSection "Point Cloud" "pointCloud" state.expandedSections.pointCloud
    [ propertyGroup "Point Size"
        [ sliderInput state.pointSize 0.1 20.0 0.1 SetPointSize ]
    , propertyGroup "Point Color"
        [ colorInput state.pointColor SetPointColor ]
    , checkboxRow "Use Vertex Colors" state.useVertexColors ToggleVertexColors
    , checkboxRow "Size Attenuation" state.sizeAttenuation ToggleSizeAttenuation
    ]

-- =============================================================================
--                                                               // ui helpers
-- =============================================================================

collapsibleSection :: forall m. String -> String -> Boolean -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
collapsibleSection title sectionId isExpanded children =
  HH.div
    [ cls [ "property-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        , HE.onClick \_ -> ToggleSection sectionId
        , ARIA.role "button"
        , HP.attr (HH.AttrName "aria-expanded") (if isExpanded then "true" else "false")
        ]
        [ HH.i 
            [ cls [ "icon" ]
            , HP.attr (HH.AttrName "style") (iconStyle isExpanded)
            ]
            [ HH.text "\x{25B8}" ]  -- Right pointing triangle
        , HH.span_ [ HH.text title ]
        ]
    , if isExpanded
        then HH.div [ cls [ "section-content" ], HP.attr (HH.AttrName "style") sectionContentStyle ]
               children
        else HH.text ""
    ]

propertyGroup :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
propertyGroup labelText children =
  HH.div [ cls [ "property-group" ], HP.attr (HH.AttrName "style") propertyGroupStyle ]
    ([ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text labelText ] ] <> children)

type XYZInput = { label :: String, value :: Number, onInput :: String -> Action }

xyzInputs :: forall m. String -> Array XYZInput -> H.ComponentHTML Action Slots m
xyzInputs category inputs =
  HH.div [ cls [ "vector3-input" ], HP.attr (HH.AttrName "style") vector3Style ]
    (map (xyzSingleInput category) inputs)

xyzSingleInput :: forall m. String -> XYZInput -> H.ComponentHTML Action Slots m
xyzSingleInput category { label, value, onInput } =
  let unit = case category of
        "rotation" -> "\x{00B0}"
        "scale" -> "%"
        _ -> ""
  in HH.div [ cls [ "input-item" ], HP.attr (HH.AttrName "style") inputItemStyle ]
    [ HH.span [ cls [ "axis" ], HP.attr (HH.AttrName "style") (axisStyle label) ]
        [ HH.text label ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (Utils.formatNumber 1 value)
        , HP.attr (HH.AttrName "style") numberInputStyle
        , HE.onValueInput onInput
        ]
    , if unit /= ""
        then HH.span [ cls [ "unit" ], HP.attr (HH.AttrName "style") unitStyle ] [ HH.text unit ]
        else HH.text ""
    ]

sliderInput :: forall m. Number -> Number -> Number -> Number -> (String -> Action) -> H.ComponentHTML Action Slots m
sliderInput value minVal maxVal stepVal onInput =
  HH.div [ cls [ "slider-row" ], HP.attr (HH.AttrName "style") sliderRowStyle ]
    [ HH.input
        [ HP.type_ HP.InputRange
        , HP.value (show value)
        , HP.attr (HH.AttrName "min") (show minVal)
        , HP.attr (HH.AttrName "max") (show maxVal)
        , HP.attr (HH.AttrName "step") (show stepVal)
        , HP.attr (HH.AttrName "style") sliderStyle
        , HE.onValueInput onInput
        ]
    , HH.span [ cls [ "slider-value" ], HP.attr (HH.AttrName "style") sliderValueStyle ]
        [ HH.text (Utils.formatNumber 1 value) ]
    ]

colorInput :: forall m. String -> (String -> Action) -> H.ComponentHTML Action Slots m
colorInput value onInput =
  HH.div [ cls [ "color-row" ], HP.attr (HH.AttrName "style") colorRowStyle ]
    [ HH.input
        [ HP.type_ HP.InputColor
        , HP.value value
        , HP.attr (HH.AttrName "style") colorInputStyle
        , HE.onValueInput onInput
        ]
    , HH.span [ cls [ "color-hex" ], HP.attr (HH.AttrName "style") colorHexStyle ]
        [ HH.text value ]
    ]

checkboxRow :: forall m. String -> Boolean -> Action -> H.ComponentHTML Action Slots m
checkboxRow labelText checked action =
  HH.div [ cls [ "property-row" ], HP.attr (HH.AttrName "style") propertyRowStyle ]
    [ HH.label [ cls [ "checkbox-label" ], HP.attr (HH.AttrName "style") checkboxLabelStyle ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked checked
            , HE.onChecked \_ -> action
            ]
        , HH.text labelText
        ]
    ]

-- =============================================================================
--                                                                     // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; " <>
  "background: #1E1E1E; color: #E0E0E0; font-size: 13px;"

sectionStyle :: String
sectionStyle =
  "border-bottom: 1px solid #2A2A2A;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "display: flex; align-items: center; gap: 6px; padding: 8px 12px; " <>
  "background: #222; cursor: pointer; user-select: none; " <>
  "font-size: 13px; font-weight: 500; color: #CCC;"

iconStyle :: Boolean -> String
iconStyle isExpanded =
  "font-size: 11px; color: #666; transition: transform 0.2s; " <>
  "transform: rotate(" <> (if isExpanded then "90deg" else "0deg") <> ");"

sectionContentStyle :: String
sectionContentStyle =
  "padding: 12px; display: flex; flex-direction: column; gap: 12px;"

propertyGroupStyle :: String
propertyGroupStyle =
  "display: flex; flex-direction: column; gap: 6px;"

labelStyle :: String
labelStyle =
  "color: #888; font-size: 12px; text-transform: uppercase;"

vector3Style :: String
vector3Style =
  "display: flex; gap: 8px;"

inputItemStyle :: String
inputItemStyle =
  "flex: 1; display: flex; align-items: center; gap: 4px;"

axisStyle :: String -> String
axisStyle label =
  let color = case label of
        "X" -> "#FF6B6B"
        "Y" -> "#69DB7C"
        _ -> "#74C0FC"
  in "font-size: 12px; font-weight: 600; width: 14px; color: " <> color <> ";"

numberInputStyle :: String
numberInputStyle =
  "flex: 1; width: 100%; padding: 4px 6px; background: #111; " <>
  "border: 1px solid #333; border-radius: 3px; color: #E0E0E0; font-size: 12px;"

unitStyle :: String
unitStyle =
  "color: #888; font-size: 11px;"

selectStyle :: String
selectStyle =
  "width: 100%; padding: 6px 8px; background: #111; " <>
  "border: 1px solid #333; border-radius: 3px; color: #E0E0E0; font-size: 13px;"

actionBtnStyle :: String
actionBtnStyle =
  "display: flex; align-items: center; justify-content: center; gap: 6px; " <>
  "padding: 8px 12px; background: #333; border: 1px solid #444; " <>
  "color: #CCC; border-radius: 4px; cursor: pointer;"

infoRowStyle :: String
infoRowStyle =
  "display: flex; justify-content: space-between; padding: 4px 12px;"

infoLabelStyle :: String
infoLabelStyle =
  "color: #888;"

propertyRowStyle :: String
propertyRowStyle =
  "display: flex; align-items: center; justify-content: space-between;"

checkboxLabelStyle :: String
checkboxLabelStyle =
  "display: flex; align-items: center; gap: 6px; cursor: pointer; color: #CCC;"

sliderRowStyle :: String
sliderRowStyle =
  "display: flex; align-items: center; gap: 8px;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px; appearance: none; " <>
  "background: #222; border-radius: 2px;"

sliderValueStyle :: String
sliderValueStyle =
  "min-width: 45px; text-align: right; color: #9CA3AF; font-family: monospace;"

colorRowStyle :: String
colorRowStyle =
  "display: flex; align-items: center; gap: 8px;"

colorInputStyle :: String
colorInputStyle =
  "width: 32px; height: 24px; padding: 0; border: 1px solid #333; " <>
  "border-radius: 3px; cursor: pointer;"

colorHexStyle :: String
colorHexStyle =
  "font-size: 11px; font-family: monospace; color: #9CA3AF;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ 
      { layerId = input.layerId
      , layerType = input.layerType
      , layerData = input.layerData
      , transform = input.transform
      , availableMaterials = input.availableMaterials
      , selectedMaterialId = extractMaterialId input.layerData
      , wireframe = extractWireframe input.layerData
      , showBoundingBox = extractBoundingBox input.layerData
      , castShadows = extractCastShadows input.layerData
      , receiveShadows = extractReceiveShadows input.layerData
      , pointSize = extractPointSize input.layerData
      , pointColor = extractPointColor input.layerData
      , useVertexColors = extractUseVertexColors input.layerData
      , sizeAttenuation = extractSizeAttenuation input.layerData
      }
  
  ToggleSection sectionId ->
    H.modify_ \s -> s { expandedSections = toggleSectionState sectionId s.expandedSections }
  
  -- Position
  SetPositionX val -> updateTransformVec3 "position" "x" val
  SetPositionY val -> updateTransformVec3 "position" "y" val
  SetPositionZ val -> updateTransformVec3 "position" "z" val
  
  -- Rotation
  SetRotationX val -> updateTransformVec3 "rotation" "x" val
  SetRotationY val -> updateTransformVec3 "rotation" "y" val
  SetRotationZ val -> updateTransformVec3 "rotation" "z" val
  
  -- Scale (with uniform scale support)
  SetScaleX val -> updateScale "x" val
  SetScaleY val -> updateScale "y" val
  SetScaleZ val -> updateScale "z" val
  
  ToggleUniformScale -> H.modify_ \s -> s { uniformScale = not s.uniformScale }
  
  -- Material
  SetMaterial val -> do
    let matId = if val == "" then Nothing else Just val
    H.modify_ _ { selectedMaterialId = matId }
    H.raise (MaterialAssigned matId)
  
  OpenMaterialEditor -> H.raise OpenMaterialEditorRequested
  
  -- Display options
  ToggleWireframe -> do
    state <- H.get
    let newVal = not state.wireframe
    H.modify_ _ { wireframe = newVal }
    H.raise (DisplayOptionChanged Wireframe newVal)
  
  ToggleBoundingBox -> do
    state <- H.get
    let newVal = not state.showBoundingBox
    H.modify_ _ { showBoundingBox = newVal }
    H.raise (DisplayOptionChanged BoundingBox newVal)
  
  ToggleCastShadows -> do
    state <- H.get
    let newVal = not state.castShadows
    H.modify_ _ { castShadows = newVal }
    H.raise (DisplayOptionChanged CastShadows newVal)
  
  ToggleReceiveShadows -> do
    state <- H.get
    let newVal = not state.receiveShadows
    H.modify_ _ { receiveShadows = newVal }
    H.raise (DisplayOptionChanged ReceiveShadows newVal)
  
  -- Point cloud settings
  SetPointSize val -> do
    state <- H.get
    let newVal = Utils.parseFloatOr state.pointSize val
    H.modify_ _ { pointSize = newVal }
    H.raise (PointCloudSettingChanged (PointSize newVal))
  
  SetPointColor val -> do
    H.modify_ _ { pointColor = val }
    H.raise (PointCloudSettingChanged (PointColor val))
  
  ToggleVertexColors -> do
    state <- H.get
    let newVal = not state.useVertexColors
    H.modify_ _ { useVertexColors = newVal }
    H.raise (PointCloudSettingChanged (UseVertexColors newVal))
  
  ToggleSizeAttenuation -> do
    state <- H.get
    let newVal = not state.sizeAttenuation
    H.modify_ _ { sizeAttenuation = newVal }
    H.raise (PointCloudSettingChanged (SizeAttenuation newVal))

-- =============================================================================
--                                                            // update helpers
-- =============================================================================

toggleSectionState :: String -> ExpandedSections -> ExpandedSections
toggleSectionState sectionId sections =
  case sectionId of
    "transform" -> sections { transform = not sections.transform }
    "material" -> sections { material = not sections.material }
    "display" -> sections { display = not sections.display }
    "pointCloud" -> sections { pointCloud = not sections.pointCloud }
    _ -> sections

updateTransformVec3 :: forall m. MonadAff m => String -> String -> String -> H.HalogenM State Action Slots Output m Unit
updateTransformVec3 field axis val = do
  state <- H.get
  let
    vec = case field of
      "position" -> state.transform.position
      "rotation" -> state.transform.rotation
      _ -> state.transform.scale
    newVec = case axis of
      "x" -> vec { x = Utils.parseFloatOr vec.x val }
      "y" -> vec { y = Utils.parseFloatOr vec.y val }
      _ -> vec { z = Utils.parseFloatOr vec.z val }
    newTransform = case field of
      "position" -> state.transform { position = newVec }
      "rotation" -> state.transform { rotation = newVec }
      _ -> state.transform { scale = newVec }
  H.modify_ _ { transform = newTransform }
  H.raise (TransformUpdated newTransform)

updateScale :: forall m. MonadAff m => String -> String -> H.HalogenM State Action Slots Output m Unit
updateScale axis val = do
  state <- H.get
  let
    oldVal = case axis of
      "x" -> state.transform.scale.x
      "y" -> state.transform.scale.y
      _ -> state.transform.scale.z
    newVal = Utils.parseFloatOr oldVal val
    newScale = 
      if state.uniformScale
        then { x: newVal, y: newVal, z: newVal }
        else case axis of
          "x" -> state.transform.scale { x = newVal }
          "y" -> state.transform.scale { y = newVal }
          _ -> state.transform.scale { z = newVal }
    newTransform = state.transform { scale = newScale }
  H.modify_ _ { transform = newTransform }
  H.raise (TransformUpdated newTransform)
