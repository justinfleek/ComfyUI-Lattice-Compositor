-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // gpu // webgpu // scene3d // geometry // basic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Basic geometry generators: Plane and Box.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry.Basic
  ( generatePlane
  , generateBox
  , generateBoxFace
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing))
import Hydrogen.GPU.Scene3D.Mesh (BoxMeshParams, PlaneMeshParams)
import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Core
  ( MeshData
  , combineMeshData
  , generateGridIndices
  )
import Hydrogen.Schema.Dimension.Physical.SI (Meter, unwrapMeter)
import Hydrogen.Schema.Dimension.Vector.Vec2 (vec2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, addVec3, scaleVec3)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PLANE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a plane (XY plane, facing +Z).
generatePlane :: PlaneMeshParams -> MeshData
generatePlane params =
  let
    -- Extract dimensions from Schema types
    widthM :: Meter
    widthM = params.width
    heightM :: Meter
    heightM = params.height
    w = unwrapMeter widthM
    h = unwrapMeter heightM
    wSegs = params.widthSegments
    hSegs = params.heightSegments
    
    halfW = w / 2.0
    halfH = h / 2.0
    
    -- Generate grid of vertices
    vertices = do
      iy <- Array.range 0 hSegs
      ix <- Array.range 0 wSegs
      let
        u = toNumber ix / toNumber wSegs
        v = toNumber iy / toNumber hSegs
        x = u * w - halfW
        y = v * h - halfH
      pure { pos: vec3 x y 0.0, uv: vec2 u v }
    
    positions = map _.pos vertices
    uvs = map _.uv vertices
    normals = map (\_ -> vec3 0.0 0.0 1.0) positions
    indices = generateGridIndices wSegs hSegs (wSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BOX GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a box (axis-aligned, centered at origin).
generateBox :: BoxMeshParams -> MeshData
generateBox params =
  let
    w = unwrapMeter params.width
    h = unwrapMeter params.height
    d = unwrapMeter params.depth
    wSegs = params.widthSegments
    hSegs = params.heightSegments
    dSegs = params.depthSegments
    
    halfW = w / 2.0
    halfH = h / 2.0
    halfD = d / 2.0
    
    -- Generate each face, then combine
    frontFace = generateBoxFace 
      { width: w, height: h, depth: halfD
      , widthSegs: wSegs, heightSegs: hSegs
      , normal: vec3 0.0 0.0 1.0
      , u: vec3 1.0 0.0 0.0
      , v: vec3 0.0 1.0 0.0
      }
    
    backFace = generateBoxFace
      { width: w, height: h, depth: (-halfD)
      , widthSegs: wSegs, heightSegs: hSegs
      , normal: vec3 0.0 0.0 (-1.0)
      , u: vec3 (-1.0) 0.0 0.0
      , v: vec3 0.0 1.0 0.0
      }
    
    topFace = generateBoxFace
      { width: w, height: d, depth: halfH
      , widthSegs: wSegs, heightSegs: dSegs
      , normal: vec3 0.0 1.0 0.0
      , u: vec3 1.0 0.0 0.0
      , v: vec3 0.0 0.0 (-1.0)
      }
    
    bottomFace = generateBoxFace
      { width: w, height: d, depth: (-halfH)
      , widthSegs: wSegs, heightSegs: dSegs
      , normal: vec3 0.0 (-1.0) 0.0
      , u: vec3 1.0 0.0 0.0
      , v: vec3 0.0 0.0 1.0
      }
    
    rightFace = generateBoxFace
      { width: d, height: h, depth: halfW
      , widthSegs: dSegs, heightSegs: hSegs
      , normal: vec3 1.0 0.0 0.0
      , u: vec3 0.0 0.0 (-1.0)
      , v: vec3 0.0 1.0 0.0
      }
    
    leftFace = generateBoxFace
      { width: d, height: h, depth: (-halfW)
      , widthSegs: dSegs, heightSegs: hSegs
      , normal: vec3 (-1.0) 0.0 0.0
      , u: vec3 0.0 0.0 1.0
      , v: vec3 0.0 1.0 0.0
      }
  in
    combineMeshData [frontFace, backFace, topFace, bottomFace, rightFace, leftFace]

-- | Generate a single box face.
generateBoxFace 
  :: { width :: Number, height :: Number, depth :: Number
     , widthSegs :: Int, heightSegs :: Int
     , normal :: Vec3 Number
     , u :: Vec3 Number
     , v :: Vec3 Number
     }
  -> MeshData
generateBoxFace params =
  let
    halfW = params.width / 2.0
    halfH = params.height / 2.0
    
    vertices = do
      iy <- Array.range 0 params.heightSegs
      ix <- Array.range 0 params.widthSegs
      let
        uvx = toNumber ix / toNumber params.widthSegs
        uvy = toNumber iy / toNumber params.heightSegs
        localX = uvx * params.width - halfW
        localY = uvy * params.height - halfH
        pos = addVec3 (addVec3 (scaleVec3 localX params.u) (scaleVec3 localY params.v))
                      (scaleVec3 params.depth params.normal)
      pure { pos, uv: vec2 uvx uvy }
    
    positions = map _.pos vertices
    uvs = map _.uv vertices
    normals = map (\_ -> params.normal) positions
    indices = generateGridIndices params.widthSegs params.heightSegs (params.widthSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }
