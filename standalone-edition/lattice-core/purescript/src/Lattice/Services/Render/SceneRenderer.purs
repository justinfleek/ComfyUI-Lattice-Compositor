-- | Lattice.Services.Render.SceneRenderer - 3D Scene Visualization
-- |
-- | Generates geometry for camera wireframes, frustums, grids, and guides.
-- | Port of: comfyui/ui/src/services/camera3DVisualization.ts
-- |
-- | Used by the ViewportRenderer component to draw 3D scene visualization
-- | with multiple camera views (ortho, perspective, custom orbit).

module Lattice.Services.Render.SceneRenderer
  ( -- * Types
    LineSegment
  , ViewMatrices
  , CameraVisualization
  , CustomViewState
  , ViewType(..)
  , ViewLayout(..)
    -- * Grid and Axes
  , generateGrid
  , generate3DAxes
    -- * Camera Visualization
  , generateCameraBody
  , generateFrustum
  , generateCompositionBounds
    -- * View Matrices
  , getCameraViewMatrices
  , getOrthoViewMatrices
    -- * Projection
  , projectToScreen
  , ScreenPoint
  ) where

import Prelude

import Data.Array (concat, (..), (:))
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Lattice.Services.Math3D.Vec3 (Vec3, vec3, add, sub, scale, normalize, cross)
import Lattice.Services.Math3D.Mat4 (Mat4, lookAt, multiply, orthographic, perspective, transformPoint4)
import Data.Number (cos, sin, tan, pi, atan)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | A line segment in 3D space with color
type LineSegment =
  { start :: Vec3
  , end :: Vec3
  , color :: String
  }

-- | View and projection matrices for rendering
type ViewMatrices =
  { view :: Mat4
  , projection :: Mat4
  , viewProjection :: Mat4
  }

-- | Camera visualization geometry
type CameraVisualization =
  { body :: Array LineSegment           -- Camera body wireframe
  , frustum :: Array LineSegment        -- View frustum cone
  , compositionBounds :: Array LineSegment  -- Comp as 3D rectangle
  , poiLine :: Maybe LineSegment        -- Point of Interest connection
  , focalPlane :: Array LineSegment     -- DOF focus plane indicator
  }

-- | Custom view orbit state
type CustomViewState =
  { orbitCenter :: Vec3
  , orbitDistance :: Number
  , orbitPhi :: Number      -- Vertical angle (0-180)
  , orbitTheta :: Number    -- Horizontal angle
  , orthoZoom :: Number
  , orthoOffset :: { x :: Number, y :: Number }
  }

-- | View type selector
data ViewType
  = ViewActiveCamera
  | ViewCustom1
  | ViewCustom2
  | ViewCustom3
  | ViewFront
  | ViewBack
  | ViewLeft
  | ViewRight
  | ViewTop
  | ViewBottom

derive instance eqViewType :: Eq ViewType

-- | Viewport layout
data ViewLayout
  = Layout1View
  | Layout2ViewHorizontal
  | Layout2ViewVertical
  | Layout4View

derive instance eqViewLayout :: Eq ViewLayout

-- | Projected screen point
type ScreenPoint =
  { x :: Number
  , y :: Number
  , visible :: Boolean
  }

-- | Camera data (simplified from full Camera3D type)
type Camera3D =
  { position :: Vec3
  , pointOfInterest :: Vec3
  , focalLength :: Number
  , filmSize :: Number
  , nearClip :: Number
  , farClip :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera body dimensions in world units
cameraBodySize :: Number
cameraBodySize = 40.0

cameraLensLength :: Number
cameraLensLength = 30.0

-- | Grid defaults
gridColor :: String
gridColor = "#333333"

gridSubColor :: String
gridSubColor = "#1a1a1a"

-- | Axis colors
axisColorX :: String
axisColorX = "#ff4444"

axisColorY :: String
axisColorY = "#44ff44"

axisColorZ :: String
axisColorZ = "#4444ff"

-- ────────────────────────────────────────────────────────────────────────────
-- Grid and Axes
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate a ground plane grid
-- | @param width - Composition width
-- | @param height - Composition height
generateGrid :: Int -> Int -> Array LineSegment
generateGrid width height =
  let
    w = toNumber width
    h = toNumber height
    step = 100.0
    halfW = w / 2.0
    halfH = h / 2.0
    
    -- Generate vertical lines
    numVertical = width / 100
    verticalLines = map (\i -> 
      let x = toNumber (i * 100) - halfW
      in { start: vec3 x (-halfH) 0.0
         , end: vec3 x halfH 0.0
         , color: if i `mod` 5 == 0 then gridColor else gridSubColor
         }
    ) (0 .. numVertical)
    
    -- Generate horizontal lines
    numHorizontal = height / 100
    horizontalLines = map (\i -> 
      let y = toNumber (i * 100) - halfH
      in { start: vec3 (-halfW) y 0.0
         , end: vec3 halfW y 0.0
         , color: if i `mod` 5 == 0 then gridColor else gridSubColor
         }
    ) (0 .. numHorizontal)
    
  in verticalLines <> horizontalLines

-- | Generate 3D reference axes at origin
-- | @param origin - Center point for axes
generate3DAxes :: Vec3 -> Array LineSegment
generate3DAxes origin =
  let
    axisLength = 200.0
  in
    [ -- X axis (red)
      { start: origin
      , end: add origin (vec3 axisLength 0.0 0.0)
      , color: axisColorX
      }
    , -- Y axis (green)
      { start: origin
      , end: add origin (vec3 0.0 axisLength 0.0)
      , color: axisColorY
      }
    , -- Z axis (blue)
      { start: origin
      , end: add origin (vec3 0.0 0.0 axisLength)
      , color: axisColorZ
      }
    ]

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Visualization
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate camera body wireframe geometry
generateCameraBody :: Camera3D -> Array LineSegment
generateCameraBody camera =
  let
    color = "#ffcc00"  -- Yellow for camera
    pos = camera.position
    
    -- Get camera forward direction (from position to POI)
    forward = normalize (sub camera.pointOfInterest pos)
    
    -- Get right and up vectors
    worldUp = vec3 0.0 (-1.0) 0.0  -- Y-down in AE coordinate system
    right = normalize (cross forward worldUp)
    up = normalize (cross right forward)
    
    halfSize = cameraBodySize / 2.0
    bodyBack = add pos (scale forward (-cameraBodySize))
    
    -- Generate 8 corners of the body box
    corner :: Number -> Number -> Vec3 -> Vec3
    corner xSign ySign base = 
      add (add base (scale right (xSign * halfSize))) 
          (scale up (ySign * halfSize))
    
    -- Front face corners (at pos)
    c0 = corner (-1.0) (-1.0) pos
    c1 = corner 1.0 (-1.0) pos
    c2 = corner (-1.0) 1.0 pos
    c3 = corner 1.0 1.0 pos
    
    -- Back face corners (at bodyBack)
    c4 = corner (-1.0) (-1.0) bodyBack
    c5 = corner 1.0 (-1.0) bodyBack
    c6 = corner (-1.0) 1.0 bodyBack
    c7 = corner 1.0 1.0 bodyBack
    
    -- Front face edges
    frontFace =
      [ { start: c0, end: c1, color }
      , { start: c1, end: c3, color }
      , { start: c3, end: c2, color }
      , { start: c2, end: c0, color }
      ]
    
    -- Back face edges
    backFace =
      [ { start: c4, end: c5, color }
      , { start: c5, end: c7, color }
      , { start: c7, end: c6, color }
      , { start: c6, end: c4, color }
      ]
    
    -- Connecting edges
    connecting =
      [ { start: c0, end: c4, color }
      , { start: c1, end: c5, color }
      , { start: c2, end: c6, color }
      , { start: c3, end: c7, color }
      ]
    
    -- Lens cone (simplified - just the tip)
    lensEnd = add pos (scale forward cameraLensLength)
    lensTip =
      [ { start: c0, end: lensEnd, color }
      , { start: c1, end: lensEnd, color }
      , { start: c2, end: lensEnd, color }
      , { start: c3, end: lensEnd, color }
      ]
    
  in frontFace <> backFace <> connecting <> lensTip

-- | Generate view frustum wireframe
generateFrustum :: Camera3D -> Int -> Int -> Array LineSegment
generateFrustum camera compWidth compHeight =
  let
    color = "#7c9cff"  -- Blue for frustum
    
    -- Convert focal length to field of view
    fovY = focalLengthToFOV camera.focalLength camera.filmSize
    aspect = toNumber compWidth / toNumber compHeight
    
    pos = camera.position
    forward = normalize (sub camera.pointOfInterest pos)
    worldUp = vec3 0.0 (-1.0) 0.0
    right = normalize (cross forward worldUp)
    up = normalize (cross right forward)
    
    near = camera.nearClip
    far = min camera.farClip 2000.0
    
    -- Calculate frustum half-dimensions
    nearHalfHeight = near * tan (fovY * pi / 360.0)
    nearHalfWidth = nearHalfHeight * aspect
    farHalfHeight = far * tan (fovY * pi / 360.0)
    farHalfWidth = farHalfHeight * aspect
    
    nearCenter = add pos (scale forward near)
    farCenter = add pos (scale forward far)
    
    -- Near plane corners
    n0 = add (add nearCenter (scale right (-nearHalfWidth))) (scale up nearHalfHeight)
    n1 = add (add nearCenter (scale right nearHalfWidth)) (scale up nearHalfHeight)
    n2 = add (add nearCenter (scale right nearHalfWidth)) (scale up (-nearHalfHeight))
    n3 = add (add nearCenter (scale right (-nearHalfWidth))) (scale up (-nearHalfHeight))
    
    -- Far plane corners
    f0 = add (add farCenter (scale right (-farHalfWidth))) (scale up farHalfHeight)
    f1 = add (add farCenter (scale right farHalfWidth)) (scale up farHalfHeight)
    f2 = add (add farCenter (scale right farHalfWidth)) (scale up (-farHalfHeight))
    f3 = add (add farCenter (scale right (-farHalfWidth))) (scale up (-farHalfHeight))
    
    -- Near plane edges
    nearPlane =
      [ { start: n0, end: n1, color }
      , { start: n1, end: n2, color }
      , { start: n2, end: n3, color }
      , { start: n3, end: n0, color }
      ]
    
    -- Far plane edges
    farPlane =
      [ { start: f0, end: f1, color }
      , { start: f1, end: f2, color }
      , { start: f2, end: f3, color }
      , { start: f3, end: f0, color }
      ]
    
    -- Connecting edges
    connecting =
      [ { start: n0, end: f0, color }
      , { start: n1, end: f1, color }
      , { start: n2, end: f2, color }
      , { start: n3, end: f3, color }
      ]
    
  in nearPlane <> farPlane <> connecting

-- | Generate composition bounds as 3D rectangle at z=0
generateCompositionBounds :: Int -> Int -> Array LineSegment
generateCompositionBounds width height =
  let
    color = "#666666"
    w = toNumber width
    h = toNumber height
    
    c0 = vec3 0.0 0.0 0.0
    c1 = vec3 w 0.0 0.0
    c2 = vec3 w h 0.0
    c3 = vec3 0.0 h 0.0
  in
    [ { start: c0, end: c1, color }
    , { start: c1, end: c2, color }
    , { start: c2, end: c3, color }
    , { start: c3, end: c0, color }
    ]

-- ────────────────────────────────────────────────────────────────────────────
-- View Matrices
-- ────────────────────────────────────────────────────────────────────────────

-- | Get view matrices for camera perspective view
getCameraViewMatrices :: Camera3D -> Int -> Int -> ViewMatrices
getCameraViewMatrices camera compWidth compHeight =
  let
    fovY = focalLengthToFOV camera.focalLength camera.filmSize
    aspect = toNumber compWidth / toNumber compHeight
    
    view = lookAt camera.position camera.pointOfInterest (vec3 0.0 (-1.0) 0.0)
    projection = perspective fovY aspect camera.nearClip camera.farClip
    viewProjection = multiply projection view
  in
    { view, projection, viewProjection }

-- | Get view matrices for orthographic views (front, top, etc.)
getOrthoViewMatrices :: ViewType -> Int -> Int -> Maybe CustomViewState -> ViewMatrices
getOrthoViewMatrices viewType compWidth compHeight mCustomState =
  let
    w = toNumber compWidth
    h = toNumber compHeight
    halfW = w / 2.0
    halfH = h / 2.0
    center = vec3 halfW halfH 0.0
    
    -- Get camera position and up vector based on view type
    { eye, upVec } = case viewType of
      ViewFront -> { eye: add center (vec3 0.0 0.0 (-2000.0)), upVec: vec3 0.0 (-1.0) 0.0 }
      ViewBack -> { eye: add center (vec3 0.0 0.0 2000.0), upVec: vec3 0.0 (-1.0) 0.0 }
      ViewLeft -> { eye: add center (vec3 (-2000.0) 0.0 0.0), upVec: vec3 0.0 (-1.0) 0.0 }
      ViewRight -> { eye: add center (vec3 2000.0 0.0 0.0), upVec: vec3 0.0 (-1.0) 0.0 }
      ViewTop -> { eye: add center (vec3 0.0 (-2000.0) 0.0), upVec: vec3 0.0 0.0 1.0 }
      ViewBottom -> { eye: add center (vec3 0.0 2000.0 0.0), upVec: vec3 0.0 0.0 (-1.0) }
      ViewCustom1 -> getCustomViewParams mCustomState
      ViewCustom2 -> getCustomViewParams mCustomState
      ViewCustom3 -> getCustomViewParams mCustomState
      ViewActiveCamera -> { eye: center, upVec: vec3 0.0 (-1.0) 0.0 }  -- Fallback
    
    view = lookAt eye center upVec
    
    -- Use orthographic projection for non-camera views
    orthoSize = case mCustomState of
      Just state -> state.orbitDistance
      Nothing -> max w h * 0.6
    
    aspect = w / h
    projection = orthographic (-orthoSize * aspect) (orthoSize * aspect) (-orthoSize) orthoSize 0.1 10000.0
    viewProjection = multiply projection view
  in
    { view, projection, viewProjection }

-- | Calculate custom view camera parameters from orbit state
getCustomViewParams :: Maybe CustomViewState -> { eye :: Vec3, upVec :: Vec3 }
getCustomViewParams mState =
  case mState of
    Nothing -> { eye: vec3 0.0 0.0 (-2000.0), upVec: vec3 0.0 (-1.0) 0.0 }
    Just state ->
      let
        -- Spherical to Cartesian conversion
        phiRad = state.orbitPhi * pi / 180.0
        thetaRad = state.orbitTheta * pi / 180.0
        
        x = state.orbitDistance * sin phiRad * cos thetaRad
        y = state.orbitDistance * cos phiRad
        z = state.orbitDistance * sin phiRad * sin thetaRad
        
        eye = add state.orbitCenter (vec3 x y z)
        
        -- Up vector based on phi (tilts when looking down/up)
        upVec = if state.orbitPhi < 10.0 || state.orbitPhi > 170.0
             then vec3 0.0 0.0 (if state.orbitPhi < 90.0 then 1.0 else (-1.0))
             else vec3 0.0 (-1.0) 0.0
      in
        { eye, upVec }

-- ────────────────────────────────────────────────────────────────────────────
-- Projection
-- ────────────────────────────────────────────────────────────────────────────

-- | Project a 3D point to screen coordinates
projectToScreen :: Vec3 -> Mat4 -> Number -> Number -> ScreenPoint
projectToScreen point viewProjection screenWidth screenHeight =
  let
    -- Transform point by view-projection matrix (get Vec4 for perspective divide)
    projected = transformPoint4 viewProjection point
    
    -- Check if point is in front of camera (w > 0)
    visible = projected.w > 0.0
    
    -- Perspective divide
    ndcX = if visible then projected.x / projected.w else 0.0
    ndcY = if visible then projected.y / projected.w else 0.0
    
    -- Convert NDC (-1 to 1) to screen coordinates
    screenX = (ndcX + 1.0) * 0.5 * screenWidth
    screenY = (1.0 - ndcY) * 0.5 * screenHeight  -- Flip Y for screen coords
  in
    { x: screenX, y: screenY, visible }

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert focal length (mm) to vertical field of view (degrees)
focalLengthToFOV :: Number -> Number -> Number
focalLengthToFOV focalLength filmSize =
  let
    -- filmSize is typically 36mm for full frame
    -- FOV = 2 * atan(filmSize / (2 * focalLength))
    halfAngle = atan (filmSize / (2.0 * focalLength))
  in
    2.0 * halfAngle * 180.0 / pi
