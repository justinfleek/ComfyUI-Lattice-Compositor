-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // gpu // webgpu // scene3d // geometry // procedural
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Procedural geometry generators: TorusKnot and Lathe.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry.Procedural
  ( generateTorusKnot
  , generateLathe
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.GPU.Scene3D.Mesh
  ( LatheMeshParams
  , Point2DProfile
  , TorusKnotMeshParams
  )
import Hydrogen.GPU.WebGPU.Scene3D.Geometry.Core
  ( MeshData
  , generateGridIndices
  , pi
  , degToRad
  )
import Hydrogen.Math.Core (cos, sin, sqrt)
import Hydrogen.Schema.Dimension.Physical.SI (meter, unwrapMeter)
import Hydrogen.Schema.Dimension.Vector.Vec2 (vec2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (vec3)
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- TORUS KNOT GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a torus knot.
-- |
-- | A torus knot winds around a torus p times through the hole
-- | and q times around the tube. The (2,3) knot is the trefoil.
generateTorusKnot :: TorusKnotMeshParams -> MeshData
generateTorusKnot params =
  let
    radius = unwrapMeter params.radius
    tube = unwrapMeter params.tube
    tubSegs = params.tubularSegments
    radSegs = params.radialSegments
    p = toNumber params.p
    q = toNumber params.q
    
    -- Parametric torus knot curve
    -- P(t) = ((2 + cos(q*t)) * cos(p*t), (2 + cos(q*t)) * sin(p*t), sin(q*t))
    -- We trace this curve and build a tube around it
    
    vertices = do
      i <- Array.range 0 tubSegs
      j <- Array.range 0 radSegs
      let
        u = toNumber i / toNumber tubSegs * 2.0 * pi
        v = toNumber j / toNumber radSegs * 2.0 * pi
        
        -- Point on torus knot curve
        cu = cos (p * u)
        su = sin (p * u)
        cqu = cos (q * u)
        squ = sin (q * u)
        
        -- Scale factor for knot size
        r = radius * (2.0 + cqu) / 3.0
        
        -- Center of tube at this point
        cx = r * cu
        cy = r * su
        cz = radius * squ / 3.0
        
        -- Tangent vector (derivative)
        dx = (-p * r * su) + ((-q * radius * squ / 3.0) * cu)
        dy = (p * r * cu) + ((-q * radius * squ / 3.0) * su)
        dz = q * radius * cqu / 3.0
        
        -- Normalize tangent
        tlen = sqrt (dx * dx + dy * dy + dz * dz)
        tx = dx / tlen
        ty = dy / tlen
        tz = dz / tlen
        
        -- Build orthonormal frame using cross products
        -- Binormal: cross(tangent, (0, 1, 0)) if tangent not parallel to Y
        bx = ty
        by = (-tx)
        bz = 0.0
        blen = sqrt (bx * bx + by * by + bz * bz)
        bnx = if blen > 0.001 then bx / blen else 1.0
        bny = if blen > 0.001 then by / blen else 0.0
        bnz = if blen > 0.001 then bz / blen else 0.0
        
        -- Normal: cross(binormal, tangent)
        nx = bny * tz - bnz * ty
        ny = bnz * tx - bnx * tz
        nz = bnx * ty - bny * tx
        
        -- Point on tube surface
        cv = cos v
        sv = sin v
        x = cx + tube * (cv * nx + sv * bnx)
        y = cy + tube * (cv * ny + sv * bny)
        z = cz + tube * (cv * nz + sv * bnz)
        
        -- Surface normal at this point
        snx = cv * nx + sv * bnx
        sny = cv * ny + sv * bny
        snz = cv * nz + sv * bnz
        
        uvU = toNumber i / toNumber tubSegs
        uvV = toNumber j / toNumber radSegs
      
      pure { pos: vec3 x y z, normal: vec3 snx sny snz, uv: vec2 uvU uvV }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices tubSegs radSegs (radSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- LATHE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a lathe (surface of revolution).
-- |
-- | Takes a 2D profile in XY plane and rotates it around the Y axis.
generateLathe :: LatheMeshParams -> MeshData
generateLathe params =
  let
    points = params.points
    segments = params.segments
    phiStart = unwrapDegrees params.phiStart * degToRad
    phiLength = unwrapDegrees params.phiLength * degToRad
    
    numPoints = Array.length points
    
    vertices = do
      i <- Array.range 0 segments
      j <- Array.range 0 (numPoints - 1)
      let
        phi = phiStart + (toNumber i / toNumber segments) * phiLength
        
        -- Get profile point
        point :: Point2DProfile
        point = case Array.index points j of
          Nothing -> { x: meter 0.0, y: meter 0.0 }
          Just pt -> pt
        
        r = unwrapMeter point.x
        y = unwrapMeter point.y
        
        x = r * cos phi
        z = r * sin phi
        
        -- Normal: perpendicular to profile, rotated
        -- Approximate using finite differences
        nextIdx = min (j + 1) (numPoints - 1)
        prevIdx = max (j - 1) 0
        
        nextPoint = case Array.index points nextIdx of
          Nothing -> point
          Just pt -> pt
        prevPoint = case Array.index points prevIdx of
          Nothing -> point
          Just pt -> pt
        
        dx = unwrapMeter nextPoint.x - unwrapMeter prevPoint.x
        dy = unwrapMeter nextPoint.y - unwrapMeter prevPoint.y
        
        -- Profile tangent is (dx, dy), normal is (-dy, dx) in profile plane
        pnx = (-dy)
        pny = dx
        pnLen = sqrt (pnx * pnx + pny * pny)
        normalizedPnx = if pnLen > 0.001 then pnx / pnLen else 1.0
        normalizedPny = if pnLen > 0.001 then pny / pnLen else 0.0
        
        -- Rotate normal around Y axis
        nx = normalizedPnx * cos phi
        ny = normalizedPny
        nz = normalizedPnx * sin phi
        
        uvU = toNumber i / toNumber segments
        uvV = toNumber j / toNumber (numPoints - 1)
      
      pure { pos: vec3 x y z, normal: vec3 nx ny nz, uv: vec2 uvU uvV }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices segments (numPoints - 1) numPoints
  in
    { positions, normals, uvs, indices, tangents: Nothing }
