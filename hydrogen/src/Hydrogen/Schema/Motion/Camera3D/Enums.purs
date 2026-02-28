-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // camera3d // enums
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D Enumerations: All enumeration types for 3D camera system.
-- |
-- | Includes camera types, orientation modes, view types, interpolation, etc.

module Hydrogen.Schema.Motion.Camera3D.Enums
  ( -- * Camera Type
    CameraType(..)
  , allCameraTypes
  , cameraTypeToString
  , cameraTypeFromString
  
    -- * Auto Orient Mode
  , AutoOrientMode(..)
  , allAutoOrientModes
  , autoOrientModeToString
  , autoOrientModeFromString
  
    -- * Measure Film Size
  , MeasureFilmSize(..)
  , allMeasureFilmSizes
  , measureFilmSizeToString
  , measureFilmSizeFromString
  
    -- * Wireframe Visibility
  , WireframeVisibility(..)
  , allWireframeVisibilities
  , wireframeVisibilityToString
  , wireframeVisibilityFromString
  
    -- * View Type
  , ViewType(..)
  , allViewTypes
  , viewTypeToString
  , viewTypeFromString
  
    -- * View Layout
  , ViewLayout(..)
  , allViewLayouts
  , viewLayoutToString
  , viewLayoutFromString
  
    -- * Spatial Interpolation
  , SpatialInterpolation(..)
  , allSpatialInterpolations
  , spatialInterpolationToString
  , spatialInterpolationFromString
  
    -- * Temporal Interpolation
  , TemporalInterpolation(..)
  , allTemporalInterpolations
  , temporalInterpolationToString
  , temporalInterpolationFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // camera // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera type: one-node or two-node.
-- |
-- | - One-node: Free camera with orientation controls
-- | - Two-node: Camera always looks at point of interest
data CameraType
  = CTOneNode   -- ^ Free camera with orientation
  | CTTwoNode   -- ^ Camera looks at point of interest

derive instance eqCameraType :: Eq CameraType
derive instance ordCameraType :: Ord CameraType

instance showCameraType :: Show CameraType where
  show CTOneNode = "CTOneNode"
  show CTTwoNode = "CTTwoNode"

-- | All camera types for enumeration.
allCameraTypes :: Array CameraType
allCameraTypes = [CTOneNode, CTTwoNode]

cameraTypeToString :: CameraType -> String
cameraTypeToString CTOneNode = "one-node"
cameraTypeToString CTTwoNode = "two-node"

cameraTypeFromString :: String -> Maybe CameraType
cameraTypeFromString "one-node" = Just CTOneNode
cameraTypeFromString "two-node" = Just CTTwoNode
cameraTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // auto-orient // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Auto-orientation mode for camera.
data AutoOrientMode
  = AOMOff              -- ^ No auto-orientation
  | AOMOrientAlongPath  -- ^ Orient along motion path
  | AOMOrientTowardsPOI -- ^ Orient towards point of interest

derive instance eqAutoOrientMode :: Eq AutoOrientMode
derive instance ordAutoOrientMode :: Ord AutoOrientMode

instance showAutoOrientMode :: Show AutoOrientMode where
  show AOMOff = "AOMOff"
  show AOMOrientAlongPath = "AOMOrientAlongPath"
  show AOMOrientTowardsPOI = "AOMOrientTowardsPOI"

-- | All auto-orient modes for enumeration.
allAutoOrientModes :: Array AutoOrientMode
allAutoOrientModes = [AOMOff, AOMOrientAlongPath, AOMOrientTowardsPOI]

autoOrientModeToString :: AutoOrientMode -> String
autoOrientModeToString AOMOff = "off"
autoOrientModeToString AOMOrientAlongPath = "along-path"
autoOrientModeToString AOMOrientTowardsPOI = "towards-poi"

autoOrientModeFromString :: String -> Maybe AutoOrientMode
autoOrientModeFromString "off" = Just AOMOff
autoOrientModeFromString "along-path" = Just AOMOrientAlongPath
autoOrientModeFromString "towards-poi" = Just AOMOrientTowardsPOI
autoOrientModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // measure-film // size
-- ═════════════════════════════════════════════════════════════════════════════

-- | How film size is measured for lens calculations.
data MeasureFilmSize
  = MFSHorizontal  -- ^ Measure horizontally
  | MFSVertical    -- ^ Measure vertically
  | MFSDiagonal    -- ^ Measure diagonally

derive instance eqMeasureFilmSize :: Eq MeasureFilmSize
derive instance ordMeasureFilmSize :: Ord MeasureFilmSize

instance showMeasureFilmSize :: Show MeasureFilmSize where
  show MFSHorizontal = "MFSHorizontal"
  show MFSVertical = "MFSVertical"
  show MFSDiagonal = "MFSDiagonal"

-- | All measure film sizes for enumeration.
allMeasureFilmSizes :: Array MeasureFilmSize
allMeasureFilmSizes = [MFSHorizontal, MFSVertical, MFSDiagonal]

measureFilmSizeToString :: MeasureFilmSize -> String
measureFilmSizeToString MFSHorizontal = "horizontal"
measureFilmSizeToString MFSVertical = "vertical"
measureFilmSizeToString MFSDiagonal = "diagonal"

measureFilmSizeFromString :: String -> Maybe MeasureFilmSize
measureFilmSizeFromString "horizontal" = Just MFSHorizontal
measureFilmSizeFromString "vertical" = Just MFSVertical
measureFilmSizeFromString "diagonal" = Just MFSDiagonal
measureFilmSizeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // wireframe // visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wireframe visibility mode for 3D objects.
data WireframeVisibility
  = WVAlways    -- ^ Always show wireframes
  | WVSelected  -- ^ Show wireframes only when selected
  | WVOff       -- ^ Never show wireframes

derive instance eqWireframeVisibility :: Eq WireframeVisibility
derive instance ordWireframeVisibility :: Ord WireframeVisibility

instance showWireframeVisibility :: Show WireframeVisibility where
  show WVAlways = "WVAlways"
  show WVSelected = "WVSelected"
  show WVOff = "WVOff"

-- | All wireframe visibilities for enumeration.
allWireframeVisibilities :: Array WireframeVisibility
allWireframeVisibilities = [WVAlways, WVSelected, WVOff]

wireframeVisibilityToString :: WireframeVisibility -> String
wireframeVisibilityToString WVAlways = "always"
wireframeVisibilityToString WVSelected = "selected"
wireframeVisibilityToString WVOff = "off"

wireframeVisibilityFromString :: String -> Maybe WireframeVisibility
wireframeVisibilityFromString "always" = Just WVAlways
wireframeVisibilityFromString "selected" = Just WVSelected
wireframeVisibilityFromString "off" = Just WVOff
wireframeVisibilityFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // view // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | View type for 3D viewport.
data ViewType
  = VTActiveCamera  -- ^ View through active camera
  | VTCustom1       -- ^ Custom view 1
  | VTCustom2       -- ^ Custom view 2
  | VTCustom3       -- ^ Custom view 3
  | VTFront         -- ^ Front orthographic view
  | VTBack          -- ^ Back orthographic view
  | VTLeft          -- ^ Left orthographic view
  | VTRight         -- ^ Right orthographic view
  | VTTop           -- ^ Top orthographic view
  | VTBottom        -- ^ Bottom orthographic view

derive instance eqViewType :: Eq ViewType
derive instance ordViewType :: Ord ViewType

instance showViewType :: Show ViewType where
  show VTActiveCamera = "VTActiveCamera"
  show VTCustom1 = "VTCustom1"
  show VTCustom2 = "VTCustom2"
  show VTCustom3 = "VTCustom3"
  show VTFront = "VTFront"
  show VTBack = "VTBack"
  show VTLeft = "VTLeft"
  show VTRight = "VTRight"
  show VTTop = "VTTop"
  show VTBottom = "VTBottom"

-- | All view types for enumeration.
allViewTypes :: Array ViewType
allViewTypes = 
  [ VTActiveCamera
  , VTCustom1
  , VTCustom2
  , VTCustom3
  , VTFront
  , VTBack
  , VTLeft
  , VTRight
  , VTTop
  , VTBottom
  ]

viewTypeToString :: ViewType -> String
viewTypeToString VTActiveCamera = "active-camera"
viewTypeToString VTCustom1 = "custom-1"
viewTypeToString VTCustom2 = "custom-2"
viewTypeToString VTCustom3 = "custom-3"
viewTypeToString VTFront = "front"
viewTypeToString VTBack = "back"
viewTypeToString VTLeft = "left"
viewTypeToString VTRight = "right"
viewTypeToString VTTop = "top"
viewTypeToString VTBottom = "bottom"

viewTypeFromString :: String -> Maybe ViewType
viewTypeFromString "active-camera" = Just VTActiveCamera
viewTypeFromString "custom-1" = Just VTCustom1
viewTypeFromString "custom-2" = Just VTCustom2
viewTypeFromString "custom-3" = Just VTCustom3
viewTypeFromString "front" = Just VTFront
viewTypeFromString "back" = Just VTBack
viewTypeFromString "left" = Just VTLeft
viewTypeFromString "right" = Just VTRight
viewTypeFromString "top" = Just VTTop
viewTypeFromString "bottom" = Just VTBottom
viewTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // view // layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport layout for multiple views.
data ViewLayout
  = VLOneView           -- ^ Single view
  | VLTwoViewHorizontal -- ^ Two views side by side
  | VLTwoViewVertical   -- ^ Two views stacked
  | VLFourView          -- ^ Four views in grid

derive instance eqViewLayout :: Eq ViewLayout
derive instance ordViewLayout :: Ord ViewLayout

instance showViewLayout :: Show ViewLayout where
  show VLOneView = "VLOneView"
  show VLTwoViewHorizontal = "VLTwoViewHorizontal"
  show VLTwoViewVertical = "VLTwoViewVertical"
  show VLFourView = "VLFourView"

-- | All view layouts for enumeration.
allViewLayouts :: Array ViewLayout
allViewLayouts = [VLOneView, VLTwoViewHorizontal, VLTwoViewVertical, VLFourView]

viewLayoutToString :: ViewLayout -> String
viewLayoutToString VLOneView = "one-view"
viewLayoutToString VLTwoViewHorizontal = "two-view-horizontal"
viewLayoutToString VLTwoViewVertical = "two-view-vertical"
viewLayoutToString VLFourView = "four-view"

viewLayoutFromString :: String -> Maybe ViewLayout
viewLayoutFromString "one-view" = Just VLOneView
viewLayoutFromString "two-view-horizontal" = Just VLTwoViewHorizontal
viewLayoutFromString "two-view-vertical" = Just VLTwoViewVertical
viewLayoutFromString "four-view" = Just VLFourView
viewLayoutFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // spatial // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial interpolation type for 3D motion paths.
data SpatialInterpolation
  = SILinear          -- ^ Linear interpolation
  | SIBezier          -- ^ Manual bezier handles
  | SIAutoBezier      -- ^ Automatic bezier calculation
  | SIContinuousBezier -- ^ Continuous (smooth) bezier

derive instance eqSpatialInterpolation :: Eq SpatialInterpolation
derive instance ordSpatialInterpolation :: Ord SpatialInterpolation

instance showSpatialInterpolation :: Show SpatialInterpolation where
  show SILinear = "SILinear"
  show SIBezier = "SIBezier"
  show SIAutoBezier = "SIAutoBezier"
  show SIContinuousBezier = "SIContinuousBezier"

-- | All spatial interpolations for enumeration.
allSpatialInterpolations :: Array SpatialInterpolation
allSpatialInterpolations = [SILinear, SIBezier, SIAutoBezier, SIContinuousBezier]

spatialInterpolationToString :: SpatialInterpolation -> String
spatialInterpolationToString SILinear = "linear"
spatialInterpolationToString SIBezier = "bezier"
spatialInterpolationToString SIAutoBezier = "auto-bezier"
spatialInterpolationToString SIContinuousBezier = "continuous-bezier"

spatialInterpolationFromString :: String -> Maybe SpatialInterpolation
spatialInterpolationFromString "linear" = Just SILinear
spatialInterpolationFromString "bezier" = Just SIBezier
spatialInterpolationFromString "auto-bezier" = Just SIAutoBezier
spatialInterpolationFromString "continuous-bezier" = Just SIContinuousBezier
spatialInterpolationFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // temporal // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal interpolation type for keyframes.
data TemporalInterpolation
  = TILinear  -- ^ Linear interpolation
  | TIBezier  -- ^ Bezier easing
  | TIHold    -- ^ Hold until next keyframe

derive instance eqTemporalInterpolation :: Eq TemporalInterpolation
derive instance ordTemporalInterpolation :: Ord TemporalInterpolation

instance showTemporalInterpolation :: Show TemporalInterpolation where
  show TILinear = "TILinear"
  show TIBezier = "TIBezier"
  show TIHold = "TIHold"

-- | All temporal interpolations for enumeration.
allTemporalInterpolations :: Array TemporalInterpolation
allTemporalInterpolations = [TILinear, TIBezier, TIHold]

temporalInterpolationToString :: TemporalInterpolation -> String
temporalInterpolationToString TILinear = "linear"
temporalInterpolationToString TIBezier = "bezier"
temporalInterpolationToString TIHold = "hold"

temporalInterpolationFromString :: String -> Maybe TemporalInterpolation
temporalInterpolationFromString "linear" = Just TILinear
temporalInterpolationFromString "bezier" = Just TIBezier
temporalInterpolationFromString "hold" = Just TIHold
temporalInterpolationFromString _ = Nothing
