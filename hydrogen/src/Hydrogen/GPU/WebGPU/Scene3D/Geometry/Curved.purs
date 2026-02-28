-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // gpu // webgpu // scene3d // geometry // curved
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Curved geometry generators: Sphere, Cylinder, Cone, Circle, Ring, Torus, Capsule.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry.Curved
  ( generateSphere
  , generateCylinder
  , generateCone
  , generateCircle
  , generateRing
  , generateTorus
  , generateCapsule
  , generateCircleCap
  , generateHemisphere
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing))
import Hydrogen.GPU.Scene3D.Mesh
  ( CapsuleMeshParams
  , CircleMeshParams
  , ConeMeshParams
  , CylinderMeshParams
  , RingMeshParams
  , SphereMeshParams
  , TorusMeshParams
  )
import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Core
  ( MeshData
  , emptyMeshData
  , combineMeshData
  , generateGridIndices
  , pi
  , degToRad
  )
import Hydrogen.Math.Core (cos, sin, sqrt)
import Hydrogen.Schema.Dimension.Physical.SI (meter, unwrapMeter)
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees)
import Hydrogen.Schema.Dimension.Vector.Vec2 (vec2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (vec3)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SPHERE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a UV sphere with optional phi/theta limits.
-- |
-- | Phi (horizontal): 0-360° for full sphere, partial for wedges
-- | Theta (vertical): 0-180° for full sphere, partial for bands/caps
generateSphere :: SphereMeshParams -> MeshData
generateSphere params =
  let
    radius = unwrapMeter params.radius
    wSegs = params.widthSegments
    hSegs = params.heightSegments
    
    -- Extract angle params from Schema types
    phiStartDeg :: Degrees
    phiStartDeg = params.phiStart
    phiLengthDeg :: Degrees
    phiLengthDeg = params.phiLength
    thetaStartDeg :: Degrees
    thetaStartDeg = params.thetaStart
    thetaLengthDeg :: Degrees
    thetaLengthDeg = params.thetaLength
    
    -- Convert to radians
    phiStart = unwrapDegrees phiStartDeg * degToRad
    phiLength = unwrapDegrees phiLengthDeg * degToRad
    thetaStart = unwrapDegrees thetaStartDeg * degToRad
    thetaLength = unwrapDegrees thetaLengthDeg * degToRad
    
    -- Generate vertices using spherical coordinates
    vertices = do
      iy <- Array.range 0 hSegs
      ix <- Array.range 0 wSegs
      let
        u = toNumber ix / toNumber wSegs
        v = toNumber iy / toNumber hSegs
        
        -- Spherical angles with phi/theta limits
        phi = phiStart + u * phiLength
        theta = thetaStart + v * thetaLength
        
        sinTheta = sin theta
        cosTheta = cos theta
        sinPhi = sin phi
        cosPhi = cos phi
        
        x = radius * sinTheta * cosPhi
        y = radius * cosTheta
        z = radius * sinTheta * sinPhi
        
        -- Normal = position / radius (unit sphere direction)
        nx = sinTheta * cosPhi
        ny = cosTheta
        nz = sinTheta * sinPhi
      
      pure { pos: vec3 x y z, normal: vec3 nx ny nz, uv: vec2 u (1.0 - v) }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices wSegs hSegs (wSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CYLINDER GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a cylinder (along Y axis) with optional arc.
-- |
-- | Theta controls the arc: 360° for full cylinder, less for partial arcs.
generateCylinder :: CylinderMeshParams -> MeshData
generateCylinder params =
  let
    radiusTop = unwrapMeter params.radiusTop
    radiusBottom = unwrapMeter params.radiusBottom
    height = unwrapMeter params.height
    radSegs = params.radialSegments
    hSegs = params.heightSegments
    
    -- Convert angle params to radians
    thetaStart = unwrapDegrees params.thetaStart * degToRad
    thetaLength = unwrapDegrees params.thetaLength * degToRad
    
    halfH = height / 2.0
    
    -- Generate body vertices
    bodyVerts = do
      iy <- Array.range 0 hSegs
      ix <- Array.range 0 radSegs
      let
        u = toNumber ix / toNumber radSegs
        v = toNumber iy / toNumber hSegs
        r = radiusBottom + (radiusTop - radiusBottom) * v
        theta = thetaStart + u * thetaLength
        x = r * cos theta
        z = r * sin theta
        y = v * height - halfH
        
        slope = (radiusBottom - radiusTop) / height
        nx = cos theta
        ny = slope
        nz = sin theta
        len = sqrt (nx * nx + ny * ny + nz * nz)
      
      pure { pos: vec3 x y z
           , normal: vec3 (nx / len) (ny / len) (nz / len)
           , uv: vec2 u v
           }
    
    bodyPositions = map _.pos bodyVerts
    bodyNormals = map _.normal bodyVerts
    bodyUvs = map _.uv bodyVerts
    bodyIndices = generateGridIndices radSegs hSegs (radSegs + 1)
    
    bodyMesh = { positions: bodyPositions, normals: bodyNormals, uvs: bodyUvs
               , indices: bodyIndices, tangents: Nothing }
    
    -- Only generate caps for full cylinders (thetaLength ≈ 360°)
    isFullCylinder = thetaLength >= 2.0 * pi - 0.001
    
    topCap = if params.openEnded || not isFullCylinder then emptyMeshData
             else generateCircleCap radiusTop halfH radSegs true
    
    bottomCap = if params.openEnded || not isFullCylinder then emptyMeshData
                else generateCircleCap radiusBottom (-halfH) radSegs false
  in
    combineMeshData [bodyMesh, topCap, bottomCap]

-- | Generate a circle cap for cylinder/cone.
generateCircleCap :: Number -> Number -> Int -> Boolean -> MeshData
generateCircleCap radius y segments isTop =
  let
    centerPos = vec3 0.0 y 0.0
    centerNormal = if isTop then vec3 0.0 1.0 0.0 else vec3 0.0 (-1.0) 0.0
    centerUv = vec2 0.5 0.5
    
    edgeVerts = do
      i <- Array.range 0 segments
      let
        theta = (toNumber i / toNumber segments) * 2.0 * pi
        x = radius * cos theta
        z = radius * sin theta
        uvU = 0.5 + 0.5 * cos theta
        uvV = 0.5 + 0.5 * sin theta
      pure { pos: vec3 x y z, normal: centerNormal, uv: vec2 uvU uvV }
    
    positions = [centerPos] <> map _.pos edgeVerts
    normals = [centerNormal] <> map _.normal edgeVerts
    uvs = [centerUv] <> map _.uv edgeVerts
    
    indices = do
      i <- Array.range 0 (segments - 1)
      let
        a = 0
        b = i + 1
        c = i + 2
      if isTop then [a, b, c] else [a, c, b]
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CONE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a cone.
-- |
-- | A cone is a cylinder with radiusTop = 0. The apex is at the top,
-- | the base circle is at the bottom.
generateCone :: ConeMeshParams -> MeshData
generateCone params =
  generateCylinder
    { radiusTop: meter 0.0           -- Apex at top
    , radiusBottom: params.radius    -- Base circle at bottom
    , height: params.height
    , radialSegments: params.radialSegments
    , heightSegments: params.heightSegments
    , openEnded: params.openEnded
    , thetaStart: params.thetaStart
    , thetaLength: params.thetaLength
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CIRCLE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a circle (flat disk on XZ plane).
generateCircle :: CircleMeshParams -> MeshData
generateCircle params =
  let
    radius = unwrapMeter params.radius
    segments = params.segments
    thetaStart = unwrapDegrees params.thetaStart * degToRad
    thetaLength = unwrapDegrees params.thetaLength * degToRad
    
    centerPos = vec3 0.0 0.0 0.0
    centerNormal = vec3 0.0 1.0 0.0
    centerUv = vec2 0.5 0.5
    
    edgeVerts = do
      i <- Array.range 0 segments
      let
        theta = thetaStart + (toNumber i / toNumber segments) * thetaLength
        x = radius * cos theta
        z = radius * sin theta
        uvU = 0.5 + 0.5 * cos theta
        uvV = 0.5 + 0.5 * sin theta
      pure { pos: vec3 x 0.0 z, uv: vec2 uvU uvV }
    
    positions = [centerPos] <> map _.pos edgeVerts
    normals = map (\_ -> centerNormal) positions
    uvs = [centerUv] <> map _.uv edgeVerts
    
    indices = do
      i <- Array.range 0 (segments - 1)
      [0, i + 1, i + 2]
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RING GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a ring (annulus on XZ plane).
generateRing :: RingMeshParams -> MeshData
generateRing params =
  let
    innerR = unwrapMeter params.innerRadius
    outerR = unwrapMeter params.outerRadius
    thetaSegs = params.thetaSegments
    phiSegs = params.phiSegments
    thetaStart = unwrapDegrees params.thetaStart * degToRad
    thetaLength = unwrapDegrees params.thetaLength * degToRad
    
    vertices = do
      ip <- Array.range 0 phiSegs
      it <- Array.range 0 thetaSegs
      let
        u = toNumber it / toNumber thetaSegs
        v = toNumber ip / toNumber phiSegs
        theta = thetaStart + u * thetaLength
        r = innerR + v * (outerR - innerR)
        x = r * cos theta
        z = r * sin theta
      pure { pos: vec3 x 0.0 z, uv: vec2 u v }
    
    positions = map _.pos vertices
    normals = map (\_ -> vec3 0.0 1.0 0.0) positions
    uvs = map _.uv vertices
    indices = generateGridIndices thetaSegs phiSegs (thetaSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- TORUS GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a torus.
generateTorus :: TorusMeshParams -> MeshData
generateTorus params =
  let
    radius = unwrapMeter params.radius
    tube = unwrapMeter params.tube
    radSegs = params.radialSegments
    tubSegs = params.tubularSegments
    arc = unwrapDegrees params.arc * degToRad
    
    vertices = do
      j <- Array.range 0 radSegs
      i <- Array.range 0 tubSegs
      let
        u = toNumber i / toNumber tubSegs * arc
        v = toNumber j / toNumber radSegs * 2.0 * pi
        
        x = (radius + tube * cos v) * cos u
        y = tube * sin v
        z = (radius + tube * cos v) * sin u
        
        cx = radius * cos u
        cz = radius * sin u
        
        nx = x - cx
        ny = y
        nz = z - cz
        len = sqrt (nx * nx + ny * ny + nz * nz)
      
      pure { pos: vec3 x y z
           , normal: vec3 (nx / len) (ny / len) (nz / len)
           , uv: vec2 (toNumber i / toNumber tubSegs) (toNumber j / toNumber radSegs)
           }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices tubSegs radSegs (tubSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CAPSULE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a capsule (cylinder with hemispherical caps).
generateCapsule :: CapsuleMeshParams -> MeshData
generateCapsule params =
  let
    radius = unwrapMeter params.radius
    len = unwrapMeter params.length
    capSegs = params.capSegments
    radSegs = params.radialSegments
    
    halfLen = len / 2.0
    
    topHemi = generateHemisphere radius halfLen capSegs radSegs true
    bottomHemi = generateHemisphere radius (-halfLen) capSegs radSegs false
    
    body = generateCylinder
      { radiusTop: params.radius
      , radiusBottom: params.radius
      , height: params.length
      , radialSegments: radSegs
      , heightSegments: 1
      , openEnded: true
      , thetaStart: degrees 0.0
      , thetaLength: degrees 360.0
      }
  in
    combineMeshData [topHemi, body, bottomHemi]

-- | Generate a hemisphere for capsule caps.
generateHemisphere :: Number -> Number -> Int -> Int -> Boolean -> MeshData
generateHemisphere radius yOffset capSegs radSegs isTop =
  let
    vertices = do
      iy <- Array.range 0 capSegs
      ix <- Array.range 0 radSegs
      let
        u = toNumber ix / toNumber radSegs
        v = toNumber iy / toNumber capSegs
        
        theta = if isTop then v * (pi / 2.0) else (pi / 2.0) + v * (pi / 2.0)
        phi = u * 2.0 * pi
        
        sinTheta = sin theta
        cosTheta = cos theta
        sinPhi = sin phi
        cosPhi = cos phi
        
        x = radius * sinTheta * cosPhi
        y = radius * cosTheta + yOffset
        z = radius * sinTheta * sinPhi
        
        nx = sinTheta * cosPhi
        ny = cosTheta
        nz = sinTheta * sinPhi
      
      pure { pos: vec3 x y z, normal: vec3 nx ny nz, uv: vec2 u v }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices radSegs capSegs (radSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }
