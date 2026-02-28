-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // geometry // mesh2d // vertex
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh2D vertex types — atoms and molecules for mesh vertices.
-- |
-- | ## Atoms
-- |
-- | - `VertexIndex`: Index into vertex array (non-negative Int)
-- | - `UV`: Texture coordinates (normalized 0-1)
-- |
-- | ## Molecules
-- |
-- | - `MeshVertex2D`: Position + Color + UV

module Hydrogen.Schema.Geometry.Mesh2D.Vertex
  ( -- * Atoms
    VertexIndex(VertexIndex)
  , vertexIndex
  , unwrapVertexIndex
  
  , UV(UV)
  , uv
  , uvOrigin
  , uvTopRight
  , uvBottomLeft
  , uvBottomRight
  , getU
  , getV
  , lerpUV
  
  -- * Molecules
  , MeshVertex2D(MeshVertex2D)
  , meshVertex2D
  , meshVertex2DColored
  , meshVertex2DTextured
  , getPosition
  , getColor
  , getUV
  , setPosition
  , setColor
  , setUV
  , lerpVertex
  , lerpColor
  , roundToInt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (<>)
  , (<)
  )

import Data.Int (round) as Int

import Hydrogen.Schema.Color.Channel (channel)
import Hydrogen.Schema.Color.Channel (toNumber) as Channel
import Hydrogen.Schema.Color.RGB (RGB, rgb, rgbFromChannels, red, green, blue)
import Hydrogen.Schema.Geometry.Point (Point2D, point2D, getX, getY, lerp2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // vertex index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index into vertex array.
-- |
-- | Non-negative integer referencing a vertex in the mesh.
-- | Validity is checked at mesh construction time, not in the type.
newtype VertexIndex = VertexIndex Int

derive instance eqVertexIndex :: Eq VertexIndex
derive instance ordVertexIndex :: Ord VertexIndex

instance showVertexIndex :: Show VertexIndex where
  show (VertexIndex i) = "(VertexIndex " <> show i <> ")"

-- | Create a vertex index (clamps negative values to 0).
vertexIndex :: Int -> VertexIndex
vertexIndex i = if i < 0 then VertexIndex 0 else VertexIndex i

-- | Extract raw Int value.
unwrapVertexIndex :: VertexIndex -> Int
unwrapVertexIndex (VertexIndex i) = i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // uv coordinates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture coordinates (U, V) in normalized space.
-- |
-- | - U: horizontal position (0.0 = left, 1.0 = right)
-- | - V: vertical position (0.0 = top, 1.0 = bottom)
-- |
-- | Values outside [0, 1] indicate tiling/wrapping behavior.
newtype UV = UV { u :: Number, v :: Number }

derive instance eqUV :: Eq UV
derive instance ordUV :: Ord UV

instance showUV :: Show UV where
  show (UV c) = "(UV " <> show c.u <> " " <> show c.v <> ")"

-- | Create UV coordinates.
uv :: Number -> Number -> UV
uv u' v' = UV { u: u', v: v' }

-- | Origin UV (top-left corner).
uvOrigin :: UV
uvOrigin = UV { u: 0.0, v: 0.0 }

-- | Top-right corner.
uvTopRight :: UV
uvTopRight = UV { u: 1.0, v: 0.0 }

-- | Bottom-left corner.
uvBottomLeft :: UV
uvBottomLeft = UV { u: 0.0, v: 1.0 }

-- | Bottom-right corner.
uvBottomRight :: UV
uvBottomRight = UV { u: 1.0, v: 1.0 }

-- | Get U coordinate.
getU :: UV -> Number
getU (UV c) = c.u

-- | Get V coordinate.
getV :: UV -> Number
getV (UV c) = c.v

-- | Linear interpolation of UV coordinates.
lerpUV :: Number -> UV -> UV -> UV
lerpUV t (UV from) (UV to) = UV
  { u: from.u + (to.u - from.u) * t
  , v: from.v + (to.v - from.v) * t
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // mesh vertex 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | A vertex in a 2D mesh.
-- |
-- | Combines:
-- | - Position (Point2D)
-- | - Color (RGB) for gradient interpolation
-- | - UV coordinates for texture mapping
-- |
-- | This is a molecule composed from Schema atoms.
newtype MeshVertex2D = MeshVertex2D
  { position :: Point2D
  , color :: RGB
  , texCoord :: UV
  }

derive instance eqMeshVertex2D :: Eq MeshVertex2D

instance showMeshVertex2D :: Show MeshVertex2D where
  show (MeshVertex2D v) = "(MeshVertex2D position:" <> show v.position 
    <> " color:" <> show v.color
    <> " uv:" <> show v.texCoord <> ")"

-- | Create a mesh vertex with all attributes.
meshVertex2D :: Point2D -> RGB -> UV -> MeshVertex2D
meshVertex2D pos col tc = MeshVertex2D
  { position: pos
  , color: col
  , texCoord: tc
  }

-- | Create a vertex with position and color, default UV from position.
-- |
-- | UV is derived from position assuming a unit square [0,1] x [0,1].
meshVertex2DColored :: Point2D -> RGB -> MeshVertex2D
meshVertex2DColored pos col = MeshVertex2D
  { position: pos
  , color: col
  , texCoord: uv (getX pos) (getY pos)
  }

-- | Create a vertex with position and UV, white color.
meshVertex2DTextured :: Point2D -> UV -> MeshVertex2D
meshVertex2DTextured pos tc = MeshVertex2D
  { position: pos
  , color: rgb 255 255 255
  , texCoord: tc
  }

-- | Get position from vertex.
getPosition :: MeshVertex2D -> Point2D
getPosition (MeshVertex2D v) = v.position

-- | Get color from vertex.
getColor :: MeshVertex2D -> RGB
getColor (MeshVertex2D v) = v.color

-- | Get UV from vertex.
getUV :: MeshVertex2D -> UV
getUV (MeshVertex2D v) = v.texCoord

-- | Set vertex position.
setPosition :: Point2D -> MeshVertex2D -> MeshVertex2D
setPosition pos (MeshVertex2D v) = MeshVertex2D (v { position = pos })

-- | Set vertex color.
setColor :: RGB -> MeshVertex2D -> MeshVertex2D
setColor col (MeshVertex2D v) = MeshVertex2D (v { color = col })

-- | Set vertex UV coordinates.
setUV :: UV -> MeshVertex2D -> MeshVertex2D
setUV tc (MeshVertex2D v) = MeshVertex2D (v { texCoord = tc })

-- | Linear interpolation between two vertices.
-- |
-- | Interpolates position, color, and UV independently.
lerpVertex :: Number -> MeshVertex2D -> MeshVertex2D -> MeshVertex2D
lerpVertex t (MeshVertex2D from) (MeshVertex2D to) = MeshVertex2D
  { position: lerp2D t from.position to.position
  , color: lerpColor t from.color to.color
  , texCoord: lerpUV t from.texCoord to.texCoord
  }

-- | Linear interpolation of RGB colors.
lerpColor :: Number -> RGB -> RGB -> RGB
lerpColor t c1 c2 =
  let
    r1 = Channel.toNumber (red c1)
    g1 = Channel.toNumber (green c1)
    b1 = Channel.toNumber (blue c1)
    r2 = Channel.toNumber (red c2)
    g2 = Channel.toNumber (green c2)
    b2 = Channel.toNumber (blue c2)
    rFinal = r1 + (r2 - r1) * t
    gFinal = g1 + (g2 - g1) * t
    bFinal = b1 + (b2 - b1) * t
  in
    rgbFromChannels 
      (channel (roundToInt rFinal))
      (channel (roundToInt gFinal))
      (channel (roundToInt bFinal))

-- | Round Number to Int using standard rounding.
roundToInt :: Number -> Int
roundToInt = Int.round
