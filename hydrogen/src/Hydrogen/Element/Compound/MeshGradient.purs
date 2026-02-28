-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // mesh-gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MeshGradient — Schema-native mesh gradient component.
-- |
-- | ## Architecture
-- |
-- | A mesh gradient is defined as pure data:
-- | - A 2D mesh with vertices containing position and color
-- | - Triangulation for smooth interpolation
-- | - Bounds for clipping
-- |
-- | This component does NOT render directly. It produces an Element that
-- | rendering targets (WebGPU, Canvas, SVG) can interpret.
-- |
-- | ## Schema Atoms
-- |
-- | | Property     | Pillar    | Type                      | Purpose              |
-- | |--------------|-----------|---------------------------|----------------------|
-- | | mesh         | Geometry  | Mesh2D                    | Vertex/triangle data |
-- | | width        | Dimension | Pixel                     | Output width         |
-- | | height       | Dimension | Pixel                     | Output height        |
-- | | subdivisions | Dimension | Int                       | Quality level        |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.MeshGradient as MeshGrad
-- | import Hydrogen.Schema.Color.RGB (rgb)
-- |
-- | -- Simple 4-corner mesh gradient
-- | MeshGrad.meshGradient
-- |   [ MeshGrad.corners
-- |       (rgb 255 0 0)    -- top-left: red
-- |       (rgb 0 255 0)    -- top-right: green
-- |       (rgb 0 0 255)    -- bottom-left: blue
-- |       (rgb 255 255 0)  -- bottom-right: yellow
-- |   , MeshGrad.width 400
-- |   , MeshGrad.height 300
-- |   ]
-- |
-- | -- High-quality subdivided mesh
-- | MeshGrad.meshGradient
-- |   [ MeshGrad.corners red green blue yellow
-- |   , MeshGrad.subdivisions 4  -- 4 levels of subdivision
-- |   , MeshGrad.width 800
-- |   , MeshGrad.height 600
-- |   ]
-- | ```
-- |
-- | ## Rendering Targets
-- |
-- | - **WebGPU**: Direct triangle rendering with vertex colors
-- | - **Canvas 2D**: Per-pixel sampling from mesh
-- | - **SVG**: Polygon approximation with fill gradients
-- | - **Fallback**: CSS gradient approximation (lossy)

module Hydrogen.Element.Compound.MeshGradient
  ( -- * Component
    meshGradient
  
  -- * Props
  , MeshGradientProps
  , MeshGradientProp
  , defaultProps
  
  -- * Mesh Configuration
  , corners
  , mesh
  , subdivisions
  
  -- * Dimensions
  , width
  , height
  
  -- * Behavior
  , onClick
  
  -- * Accessibility
  , ariaLabel
  
  -- * Escape Hatch
  , extraAttributes
  
  -- * Mesh Building
  , buildMeshFromCorners
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (-)
  , (*)
  , (==)
  , (>)
  )

import Data.Array (foldl)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Geometry.Mesh2D 
  ( Mesh2D
  , emptyMesh2D
  , mesh2DFromGrid
  , meshVertex2DColored
  , getColor
  , subdivide
  , lerpVertex
  )
import Hydrogen.Schema.Geometry.Point (Point2D, point2D)

-- Submodule for SVG rendering
import Hydrogen.Element.Compound.MeshGradient.SVG (renderMeshAsSVG)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | MeshGradient properties
type MeshGradientProps msg =
  { -- Mesh data
    mesh :: Mesh2D
  
  -- Corner colors (convenience for simple gradients)
  , topLeft :: Maybe RGB
  , topRight :: Maybe RGB
  , bottomLeft :: Maybe RGB
  , bottomRight :: Maybe RGB
  
  -- Dimensions
  , width :: Int
  , height :: Int
  
  -- Quality
  , subdivisions :: Int
  
  -- Behavior
  , onClick :: Maybe msg
  
  -- Accessibility
  , ariaLabel :: Maybe String
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type MeshGradientProp msg = MeshGradientProps msg -> MeshGradientProps msg

-- | Default properties
defaultProps :: forall msg. MeshGradientProps msg
defaultProps =
  { mesh: emptyMesh2D
  , topLeft: Nothing
  , topRight: Nothing
  , bottomLeft: Nothing
  , bottomRight: Nothing
  , width: 400
  , height: 300
  , subdivisions: 0
  , onClick: Nothing
  , ariaLabel: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // prop builders: mesh config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set all four corner colors at once.
-- |
-- | This is the simplest way to create a mesh gradient.
-- | The mesh will be generated automatically from these colors.
corners :: forall msg. RGB -> RGB -> RGB -> RGB -> MeshGradientProp msg
corners tl tr bl br props = props 
  { topLeft = Just tl
  , topRight = Just tr
  , bottomLeft = Just bl
  , bottomRight = Just br
  }

-- | Set a custom mesh directly.
-- |
-- | Use this for complex gradients with more than 4 control points.
mesh :: forall msg. Mesh2D -> MeshGradientProp msg
mesh m props = props { mesh = m }

-- | Set subdivision level for smoother interpolation.
-- |
-- | Each level quadruples the triangle count:
-- | - 0: 2 triangles (quad)
-- | - 1: 8 triangles
-- | - 2: 32 triangles
-- | - 3: 128 triangles
-- | - 4: 512 triangles
subdivisions :: forall msg. Int -> MeshGradientProp msg
subdivisions n props = props { subdivisions = if n > 0 then n else 0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set output width in pixels.
width :: forall msg. Int -> MeshGradientProp msg
width w props = props { width = if w > 0 then w else 1 }

-- | Set output height in pixels.
height :: forall msg. Int -> MeshGradientProp msg
height h props = props { height = if h > 0 then h else 1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set click handler.
onClick :: forall msg. msg -> MeshGradientProp msg
onClick msg props = props { onClick = Just msg }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // prop builders: accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set accessible label.
ariaLabel :: forall msg. String -> MeshGradientProp msg
ariaLabel label props = props { ariaLabel = Just label }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // prop builders: escape hatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add extra attributes.
extraAttributes :: forall msg. Array (E.Attribute msg) -> MeshGradientProp msg
extraAttributes attrs props = props { extraAttributes = attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a mesh gradient element.
-- |
-- | The element describes the mesh gradient as pure data. Rendering targets
-- | interpret this data differently:
-- |
-- | - WebGPU: Renders triangles directly with vertex colors
-- | - Canvas: Samples mesh at each pixel
-- | - SVG: Creates polygon elements with gradient fills
-- | - Fallback: Uses CSS gradient approximation
meshGradient :: forall msg. Array (MeshGradientProp msg) -> E.Element msg
meshGradient propModifiers =
  let
    props = foldl (\p f -> f p) defaultProps propModifiers
    
    -- Build mesh from corners if not provided
    finalMesh = buildFinalMesh props
    
    -- Dimensions
    widthStr = show props.width <> "px"
    heightStr = show props.height <> "px"
    
    -- Build base styles
    baseStyles =
      [ E.style "display" "block"
      , E.style "position" "relative"
      , E.style "width" widthStr
      , E.style "height" heightStr
      , E.style "overflow" "hidden"
      ]
    
    -- Interaction styles
    interactionStyles = case props.onClick of
      Nothing -> []
      Just _ -> [ E.style "cursor" "pointer" ]
    
    -- Accessibility
    accessibilityAttrs = buildAccessibilityAttrs props
    
    -- Event handlers
    eventHandlers = buildEventHandlers props
    
    -- All attributes
    allAttrs = 
      baseStyles 
      <> interactionStyles 
      <> accessibilityAttrs 
      <> eventHandlers
      <> props.extraAttributes
    
  in
    E.div_ allAttrs
      [ -- SVG rendering of the mesh
        renderMeshAsSVG props.width props.height finalMesh
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mesh construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build mesh from corner colors.
-- |
-- | Creates a simple quad mesh with bilinear color interpolation.
buildMeshFromCorners :: RGB -> RGB -> RGB -> RGB -> Int -> Int -> Mesh2D
buildMeshFromCorners topLeft' topRight' bottomLeft' bottomRight' w h =
  let
    wNum = Int.toNumber w
    hNum = Int.toNumber h
    
    -- Position function: maps UV (0-1, 0-1) to pixel coordinates
    positionFn :: Number -> Number -> Point2D
    positionFn u v = point2D (u * wNum) (v * hNum)
    
    -- Color function: bilinear interpolation of corner colors
    colorFn :: Number -> Number -> RGB
    colorFn u v = bilinearInterpolate u v topLeft' topRight' bottomLeft' bottomRight'
  in
    mesh2DFromGrid 1 1 positionFn colorFn

-- | Build final mesh from props, with subdivision.
buildFinalMesh :: forall msg. MeshGradientProps msg -> Mesh2D
buildFinalMesh props =
  let
    baseMesh = case props.topLeft of
      Nothing -> props.mesh
      Just tl -> case props.topRight of
        Nothing -> props.mesh
        Just tr -> case props.bottomLeft of
          Nothing -> props.mesh
          Just bl -> case props.bottomRight of
            Nothing -> props.mesh
            Just br -> buildMeshFromCorners tl tr bl br props.width props.height
    
    -- Apply subdivisions
    subdivided = applySubdivisions props.subdivisions baseMesh
  in
    subdivided

-- | Apply N levels of subdivision.
applySubdivisions :: Int -> Mesh2D -> Mesh2D
applySubdivisions n m =
  if n == 0 then m
  else applySubdivisions (n - 1) (subdivide m)

-- | Bilinear interpolation of colors.
bilinearInterpolate :: Number -> Number -> RGB -> RGB -> RGB -> RGB -> RGB
bilinearInterpolate u v tl tr bl br =
  let
    -- Interpolate top edge
    topColor = lerpRGB u tl tr
    -- Interpolate bottom edge
    bottomColor = lerpRGB u bl br
    -- Interpolate vertically
    finalColor = lerpRGB v topColor bottomColor
  in
    finalColor

-- | Linear interpolation of RGB colors.
-- |
-- | Delegates to Mesh2D.lerpVertex color interpolation.
lerpRGB :: Number -> RGB -> RGB -> RGB
lerpRGB t c1 c2 =
  -- Re-use the color interpolation logic
  let
    -- We need access to channel functions
    -- For now, use a simple weighted average via mesh vertex lerp
    v1 = meshVertex2DColored (point2D 0.0 0.0) c1
    v2 = meshVertex2DColored (point2D 1.0 1.0) c2
    interpolated = lerpVertex t v1 v2
  in
    getColor interpolated

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build accessibility attributes.
buildAccessibilityAttrs :: forall msg. MeshGradientProps msg -> Array (E.Attribute msg)
buildAccessibilityAttrs props =
  let
    roleAttr = case props.onClick of
      Nothing -> [ E.role "img" ]
      Just _ -> [ E.role "button" ]
    
    labelAttr = case props.ariaLabel of
      Nothing -> [ E.ariaLabel "Mesh gradient" ]
      Just label -> [ E.ariaLabel label ]
  in
    roleAttr <> labelAttr

-- | Build event handlers.
buildEventHandlers :: forall msg. MeshGradientProps msg -> Array (E.Attribute msg)
buildEventHandlers props =
  case props.onClick of
    Nothing -> []
    Just msg -> [ E.onClick msg ]
